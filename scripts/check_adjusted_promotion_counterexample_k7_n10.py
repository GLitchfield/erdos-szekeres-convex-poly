#!/usr/bin/env python3
"""Independently replay the n=10 adjusted-promotion counterexample.

The checker imports no new producer code.  It reconstructs the explicit tree
with the independent row-height implementation, recomputes local ranks by
subset enumeration, and obtains promotions directly from consecutive child
vertices.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

import check_allocated_span_pascal_demand as independent
from check_rank_two_gap_promotion_k7 import direct_promoted_groups


Tree = int | tuple["Tree", "Tree"] | list["Tree"]


def boundary_slot(ideal: tuple[int, ...], columns: int) -> int:
    return sum(
        1 << (row + columns - height)
        for row, height in enumerate(ideal)
    )


def candidate_slots(
    local: dict[tuple[int, int, int], int],
    vertices: tuple[int, ...],
    span: tuple[int, int],
    color: int,
    rank: int,
    strong_size: int,
) -> set[int]:
    ideals = independent.replay_transition_candidates(
        local, vertices, (span,), color, rank, strong_size
    )[0][0]
    columns = strong_size - rank - 1
    return {boundary_slot(ideal, columns) for ideal in ideals}


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_revision(repo: Path) -> str:
    completed = subprocess.run(
        ["git", "--git-dir=.git-data", "--work-tree=.", "rev-parse", "HEAD"],
        cwd=repo,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return completed.stdout.strip()


def is_ancestor(repo: Path, ancestor: str, descendant: str) -> bool:
    completed = subprocess.run(
        [
            "git",
            "--git-dir=.git-data",
            "--work-tree=.",
            "merge-base",
            "--is-ancestor",
            ancestor,
            descendant,
        ],
        cwd=repo,
        check=False,
    )
    return completed.returncode == 0


def tree_coloring(
    tree: Tree, machine: independent.Replay
) -> tuple[int, int]:
    if isinstance(tree, int):
        return 1 << tree, 0
    if len(tree) != 2:
        raise AssertionError("tree node must have two children")
    lower_mask, lower_bits = tree_coloring(tree[0], machine)
    upper_mask, upper_bits = tree_coloring(tree[1], machine)
    support = lower_mask | upper_mask
    return support, lower_bits | upper_bits | machine.crossing(support, lower_mask)


def validate_sources(repo: Path, manifest: dict[str, object]) -> None:
    for source in manifest["sources"].values():
        path = repo / source["path"]
        if file_sha256(path) != source["sha256"]:
            raise SystemExit(f"source digest mismatch: {source['path']}")


def replay(certificate: dict[str, object]) -> None:
    maximum_n = certificate["maximum_n"]
    strong_size = certificate["strong_size"]
    if certificate["open"] is not True:
        raise SystemExit("certificate does not claim an open context")
    if certificate["color"] != "cap" or certificate["rank"] != 3:
        raise SystemExit("certificate does not record the cap/rank-three layer")
    machine = independent.Replay(maximum_n, strong_size)
    lower, lower_bits = tree_coloring(certificate["lower_tree"], machine)
    upper, upper_bits = tree_coloring(certificate["upper_tree"], machine)
    support = lower | upper
    bits = lower_bits | upper_bits | machine.crossing(support, lower)

    if support != int(certificate["support_mask_hex"], 16):
        raise SystemExit("support mask mismatch")
    if lower != int(certificate["lower_mask_hex"], 16):
        raise SystemExit("lower mask mismatch")
    if upper != int(certificate["upper_mask_hex"], 16):
        raise SystemExit("upper mask mismatch")
    if bits != int(certificate["coloring_hex"], 16):
        raise SystemExit("coloring mismatch")

    local = machine.ranks(bits, support)
    if local is None:
        raise SystemExit("certificate contains a strong seven-set")
    groups, promotions = direct_promoted_groups(local, support, lower, maximum_n)
    spans = next(
        group
        for color, rank, group in groups
        if color == 0 and rank == certificate["rank"]
    )
    recorded = tuple(tuple(span) for span in certificate["adjusted_spans"])
    if spans != recorded:
        raise SystemExit("adjusted group mismatch")
    if tuple(promotions) != tuple(certificate["promotions"]):
        raise SystemExit("promotion records mismatch")
    recorded_groups = tuple(
        (
            1 if group["color"] == "cup" else 0,
            group["rank"],
            tuple(tuple(span) for span in group["spans"]),
        )
        for group in certificate["adjusted_groups"]
    )
    if groups != recorded_groups:
        raise SystemExit("all-rank adjusted groups mismatch")
    if any(
        len(group) != record["cardinality"]
        for (_, _, group), record in zip(groups, certificate["adjusted_groups"])
    ):
        raise SystemExit("adjusted group cardinality mismatch")

    crossing = tuple(
        span
        for span in spans
        if bool(lower & (1 << span[0])) != bool(lower & (1 << span[1]))
    )
    promoted = tuple(span for span in spans if span not in crossing)
    if crossing != tuple(tuple(span) for span in certificate["crossing_spans"]):
        raise SystemExit("crossing summand mismatch")
    if promoted != tuple(tuple(span) for span in certificate["promoted_spans"]):
        raise SystemExit("promoted summand mismatch")

    capacity = independent.pascal(strong_size - 2, certificate["rank"] - 1)
    if capacity != certificate["pascal_capacity"]:
        raise SystemExit("Pascal capacity mismatch")
    if len(spans) != certificate["adjusted_cardinality"]:
        raise SystemExit("adjusted cardinality mismatch")
    if len(spans) <= capacity or certificate["capacity_holds"]:
        raise SystemExit("recorded capacity refutation is false")
    total_adjusted = sum(len(group) for _, _, group in groups)
    untagged_pascal_window = sum(
        independent.pascal(strong_size - 2, rank - 1)
        for rank in range(2, strong_size)
    )
    if total_adjusted != certificate["total_adjusted_cardinality"]:
        raise SystemExit("all-rank aggregate cardinality mismatch")
    if untagged_pascal_window != certificate["untagged_pascal_window"]:
        raise SystemExit("untagged Pascal-window capacity mismatch")
    if (
        total_adjusted <= untagged_pascal_window
        or certificate["untagged_aggregate_capacity_holds"]
    ):
        raise SystemExit("recorded all-rank aggregate refutation is false")

    gate = certificate["exclusive_choice_gate"]
    vertices = tuple(range(maximum_n))
    families: list[set[int]] = []
    for charge in gate["charges"]:
        span = tuple(charge["span"])
        kind = charge["kind"]
        if kind == "hidden-source-exclusive-choice":
            color = 1 if charge["color"] == "cup" else 0
            transition = tuple(charge["alternative_transition"])
            family = candidate_slots(
                local, vertices, span, color, 3, strong_size
            ) | candidate_slots(
                local, vertices, transition, 1 - color, 2, strong_size
            )
        elif kind == "initial-crossing-with-sentinel":
            family = (
                candidate_slots(local, vertices, span, 0, 2, strong_size)
                | candidate_slots(local, vertices, span, 1, 2, strong_size)
                | {0}
            )
        elif kind == "higher-rank-crossing":
            color = 1 if charge["color"] == "cup" else 0
            family = candidate_slots(
                local, vertices, span, color, charge["rank"], strong_size
            )
        else:
            raise SystemExit(f"unknown exclusive-choice charge kind: {kind}")
        recorded_mask = int(charge["candidate_slot_mask_hex"], 16)
        recorded_family = {
            slot for slot in range(1 << (strong_size - 2))
            if recorded_mask & (1 << slot)
        }
        if family != recorded_family:
            raise SystemExit("exclusive-choice candidate family mismatch")
        families.append(family)

    if len(families) != gate["charge_count"]:
        raise SystemExit("exclusive-choice charge count mismatch")
    matched: dict[int, int] = {}

    def augment(charge: int, seen: set[int]) -> bool:
        for slot in sorted(families[charge], reverse=True):
            if slot in seen:
                continue
            seen.add(slot)
            if slot not in matched or augment(matched[slot], seen):
                matched[slot] = charge
                return True
        return False

    for charge in reversed(range(len(families))):
        augment(charge, set())
    if len(matched) != gate["maximum_matching_cardinality"]:
        raise SystemExit("exclusive-choice maximum matching mismatch")
    if len(matched) == len(families) or gate["matching_exists"]:
        raise SystemExit("exclusive-choice graph unexpectedly has an SDR")

    hall_demands = gate["hall_witness_demand_indices"]
    neighbors = set().union(*(families[index] for index in hall_demands))
    recorded_neighbor_mask = int(
        gate["hall_witness_neighbor_slot_mask_hex"], 16
    )
    recorded_neighbors = {
        slot for slot in range(1 << (strong_size - 2))
        if recorded_neighbor_mask & (1 << slot)
    }
    if neighbors != recorded_neighbors:
        raise SystemExit("exclusive-choice Hall neighborhood mismatch")
    if len(hall_demands) != gate["hall_witness_demand_cardinality"]:
        raise SystemExit("exclusive-choice Hall demand cardinality mismatch")
    if len(neighbors) != gate["hall_witness_neighbor_cardinality"]:
        raise SystemExit("exclusive-choice Hall neighbor cardinality mismatch")
    if len(neighbors) >= len(hall_demands):
        raise SystemExit("exclusive-choice Hall witness is not deficient")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent.parent
    manifest = json.loads(args.manifest.read_text())
    validate_sources(repo, manifest)
    head = git_revision(repo)
    base_revision = manifest["generation_base_revision"]
    if not is_ancestor(repo, base_revision, head):
        raise SystemExit("generation base revision is not an ancestor of HEAD")
    if not args.source_only:
        replay(manifest["certificate"])
    print("independent adjusted-promotion counterexample replay passed")


if __name__ == "__main__":
    main()
