#!/usr/bin/env python3
"""Independently replay the bounded common-span cross-color reuse gate."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import subprocess
from pathlib import Path

import check_allocated_span_pascal_demand as independent
from check_rank_two_gap_promotion_k7 import direct_promoted_groups


Tree = int | tuple["Tree", "Tree"] | list["Tree"]
LOWER_TREE: Tree = ((((8, 4), 6), 2), 0)
UPPER_TREE: Tree = ((((9, 7), 5), 3), 1)


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
    return subprocess.run(
        ["git", "--git-dir=.git-data", "--work-tree=.", "merge-base",
         "--is-ancestor", ancestor, descendant],
        cwd=repo,
        check=False,
    ).returncode == 0


def tree_coloring(tree: Tree, machine: independent.Replay) -> tuple[int, int]:
    if isinstance(tree, int):
        return 1 << tree, 0
    lower, lower_bits = tree_coloring(tree[0], machine)
    upper, upper_bits = tree_coloring(tree[1], machine)
    support = lower | upper
    return support, lower_bits | upper_bits | machine.crossing(support, lower)


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
    return {
        boundary_slot(ideal, strong_size - rank - 1) for ideal in ideals
    }


def family_from_mask(mask: str) -> set[int]:
    value = int(mask, 16)
    return {slot for slot in range(32) if value & (1 << slot)}


def threshold(a: int, u: int, k: int) -> int:
    if a == 1 or u == 1:
        return 0
    if a + u <= k + 3:
        return math.comb(a + u - 4, a - 2)
    return sum(math.comb(k - 2, j) for j in range(k - a, u - 1))


def maximum_matching(families: list[set[int]]) -> int:
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
    return len(matched)


def validate_sources(repo: Path, manifest: dict[str, object]) -> None:
    for source in manifest["sources"].values():
        if file_sha256(repo / source["path"]) != source["sha256"]:
            raise SystemExit(f"source digest mismatch: {source['path']}")


def replay(certificate: dict[str, object]) -> None:
    maximum_n = certificate["maximum_n"]
    strong_size = certificate["strong_size"]
    machine = independent.Replay(maximum_n, strong_size)
    lower, lower_bits = tree_coloring(LOWER_TREE, machine)
    upper, upper_bits = tree_coloring(UPPER_TREE, machine)
    support = lower | upper
    bits = lower_bits | upper_bits | machine.crossing(support, lower)
    for actual, field in (
        (support, "support_mask_hex"),
        (lower, "lower_mask_hex"),
        (upper, "upper_mask_hex"),
        (bits, "coloring_hex"),
    ):
        if actual != int(certificate[field], 16):
            raise SystemExit(f"{field} mismatch")
    if lower & upper or int(certificate["active_child_intersection_mask_hex"], 16):
        raise SystemExit("active child supports are not disjoint")

    local = machine.ranks(bits, support)
    if local is None or certificate["open"] is not True:
        raise SystemExit("certificate is not an open context")
    groups, promotions = direct_promoted_groups(
        local, support, lower, maximum_n
    )
    crossing_by_color: dict[int, set[tuple[int, int]]] = {}
    for color in (0, 1):
        spans = next(
            group for group_color, rank, group in groups
            if group_color == color and rank == 3
        )
        crossing_by_color[color] = {
            span for span in spans
            if bool(lower & (1 << span[0])) != bool(lower & (1 << span[1]))
        }
    common = tuple(sorted(crossing_by_color[0] & crossing_by_color[1]))
    if common != tuple(tuple(span) for span in certificate["common_rank_three_spans"]):
        raise SystemExit("common rank-three spans mismatch")
    if len(common) != certificate["common_span_count"]:
        raise SystemExit("common span count mismatch")

    vertices = tuple(range(maximum_n))
    families: list[set[int]] = []
    for charge in certificate["quotient_charges"]:
        span = tuple(charge["span"])
        kind = charge["kind"]
        if kind == "hidden-source-exclusive-choice":
            color = 1 if charge["color"] == "cup" else 0
            family = candidate_slots(
                local, vertices, span, color, 3, strong_size
            ) | candidate_slots(
                local, vertices, tuple(charge["alternative_transition"]),
                1 - color, 2, strong_size
            )
        elif kind == "initial-crossing-with-sentinel":
            family = candidate_slots(
                local, vertices, span, 0, 2, strong_size
            ) | candidate_slots(
                local, vertices, span, 1, 2, strong_size
            ) | {0}
        elif kind == "cross-color-common-span":
            cap_family = candidate_slots(
                local, vertices, span, 0, 3, strong_size
            )
            cup_family = candidate_slots(
                local, vertices, span, 1, 3, strong_size
            )
            if cap_family != family_from_mask(charge["cap_candidate_slot_mask_hex"]):
                raise SystemExit("cap common-span family mismatch")
            if cup_family != family_from_mask(charge["cup_candidate_slot_mask_hex"]):
                raise SystemExit("cup common-span family mismatch")
            family = cap_family & cup_family
            left_in_lower = bool(lower & (1 << span[0]))
            expected_cup_direction = "right" if left_in_lower else "left"
            expected_cap_direction = "left" if left_in_lower else "right"
            if charge["cup_active_child"] != "lower" or charge["cap_active_child"] != "upper":
                raise SystemExit("active child ownership mismatch")
            if charge["cup_ray_direction"] != expected_cup_direction:
                raise SystemExit("cup ray direction mismatch")
            if charge["cap_ray_direction"] != expected_cap_direction:
                raise SystemExit("cap ray direction mismatch")
        elif kind == "higher-rank-crossing":
            color = 1 if charge["color"] == "cup" else 0
            family = candidate_slots(
                local, vertices, span, color, charge["rank"], strong_size
            )
        else:
            raise SystemExit(f"unknown quotient charge kind: {kind}")
        if family != family_from_mask(charge["candidate_slot_mask_hex"]):
            raise SystemExit("quotient candidate family mismatch")
        families.append(family)

    if len(families) != certificate["quotient_charge_count"]:
        raise SystemExit("quotient charge count mismatch")
    matching_size = maximum_matching(families)
    if matching_size != certificate["maximum_matching_cardinality"]:
        raise SystemExit("maximum matching mismatch")
    assignment = certificate["perfect_matching"]
    if len(assignment) != len(families):
        raise SystemExit("recorded assignment is not perfect")
    if len({charge for charge, _ in assignment}) != len(families):
        raise SystemExit("recorded assignment repeats a charge")
    if len({slot for _, slot in assignment}) != len(families):
        raise SystemExit("recorded assignment repeats a slot")
    if any(slot not in families[charge] for charge, slot in assignment):
        raise SystemExit("recorded assignment uses a forbidden edge")

    arithmetic = certificate["published_arithmetic"]
    successor = threshold(7, 4, 7) + threshold(4, 7, 7)
    base = threshold(7, 3, 7) + threshold(3, 7, 7)
    demand = math.comb(5, 2)
    if successor != arithmetic["successor_threshold_total"]:
        raise SystemExit("successor threshold total mismatch")
    if base != arithmetic["base_threshold_total"]:
        raise SystemExit("base threshold total mismatch")
    if demand != arithmetic["single_pascal_demand"]:
        raise SystemExit("Pascal demand mismatch")
    if base + demand != arithmetic["single_demand_total"]:
        raise SystemExit("single-demand total mismatch")
    if successor <= base + demand or arithmetic["single_demand_suffices"]:
        raise SystemExit("single-demand refutation is false")
    if successor - base - demand != arithmetic["deficit"]:
        raise SystemExit("single-demand deficit mismatch")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent.parent
    manifest = json.loads(args.manifest.read_text())
    validate_sources(repo, manifest)
    head = git_revision(repo)
    if not is_ancestor(repo, manifest["generation_base_revision"], head):
        raise SystemExit("generation base revision is not an ancestor of HEAD")
    if not args.source_only:
        replay(manifest["certificate"])
    print("independent cross-color common-span gate replay passed")


if __name__ == "__main__":
    main()
