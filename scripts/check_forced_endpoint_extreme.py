#!/usr/bin/env python3
"""Test fixed forced endpoint extremes on the frozen k=7 root."""

from __future__ import annotations

import argparse
from collections import Counter
import itertools
from pathlib import Path

from check_block_large_reached_owner import frozen_groups
from check_owner_star_expansion import enumerate_owner_maps
from enumerate_allocated_span_pascal_demand import file_sha256, git_revision, write_atomic
from enumerate_reflected_transition_hall import reflected_ideal


def normalized_roles(
    geometry: dict[str, object], rows: int, columns: int
) -> tuple[tuple[str, int], ...]:
    answer = []
    for lane in ("left_lane", "right_lane"):
        for time in ("past", "future"):
            ideal = int(geometry[lane][time]["ideal_hex"], 16)
            if geometry["reflected"]:
                ideal = reflected_ideal(ideal, rows, columns)
            answer.append((f"{lane.removesuffix('_lane')}_{time}", ideal))
    return tuple(answer)


def first_deficient_anchor(
    hole: int, candidates: tuple[tuple[int, ...], ...]
) -> tuple[tuple[int, ...], tuple[int, ...]] | None:
    hole_family = tuple(sorted(candidates[hole]))
    block_size = len(candidates)
    small_owners = tuple(
        owner
        for owner, family in enumerate(candidates)
        if owner != hole and len(family) < block_size
    )
    for size in range(1, len(hole_family) + 1):
        for anchors in itertools.combinations(hole_family, size):
            neighbors = tuple(
                owner
                for owner in small_owners
                if any(ideal in candidates[owner] for ideal in anchors)
            )
            if len(neighbors) < len(anchors):
                return anchors, neighbors
    return None


def analyze() -> dict[str, object]:
    strong_size = 7
    totals: Counter[str] = Counter()
    patterns: Counter[str] = Counter()
    first_forced_endpoint_failure = None
    first_left_future_failure = None
    groups = []
    for group_index, group in enumerate(frozen_groups()):
        rank = int(group["rank"])
        rows = rank - 1
        columns = strong_size - rank - 1
        frontier = tuple(tuple(span) for span in group["frontier"])
        candidates = tuple(group["candidates"])
        geometry = tuple(group["geometry"])
        group_counts: Counter[str] = Counter()
        size = len(frontier)
        for start in range(size):
            for stop in range(start + 1, size + 1):
                block = candidates[start:stop]
                block_size = len(block)
                for hole in range(block_size):
                    maps = enumerate_owner_maps(hole, block, rows, columns)
                    if not maps:
                        group_counts["vacuous_holes"] += 1
                        continue
                    group_counts["nonvacuous_holes"] += 1
                    small_owners = tuple(
                        owner
                        for owner, family in enumerate(block)
                        if owner != hole and len(family) < block_size
                    )
                    roles = normalized_roles(geometry[start + hole], rows, columns)
                    anchor = first_deficient_anchor(hole, block)
                    if anchor is None:
                        raise AssertionError("block-large pass has no deficient anchor")
                    anchors, neighbors = anchor
                    group_counts[f"minimum_anchor_size_{len(anchors)}"] += 1
                    group_counts[
                        f"minimum_anchor_deficiency_{len(anchors) - len(neighbors)}"
                    ] += 1
                    forced = tuple(
                        role
                        for role, ideal in roles
                        if ideal in block[hole]
                        and all(ideal not in block[owner] for owner in small_owners)
                    )
                    if not forced:
                        group_counts["no_forced_endpoint_holes"] += 1
                    patterns["|".join(forced)] += 1
                    for role in forced:
                        group_counts[f"forced_{role}"] += 1
                    role_records = [
                        {
                            "role": role,
                            "ideal_hex": f"{ideal:x}",
                            "compatible_small_owner_indices": [
                                owner
                                for owner in small_owners
                                if ideal in block[owner]
                            ],
                        }
                        for role, ideal in roles
                    ]
                    failure = {
                        "group_index": group_index,
                        "color": group["color"],
                        "rank": rank,
                        "start_index": start,
                        "stop_index": stop,
                        "hole_index": hole,
                        "block_frontier": [list(span) for span in frontier[start:stop]],
                        "candidate_families_hex": [
                            [f"{ideal:x}" for ideal in family] for family in block
                        ],
                        "forced_roles": list(forced),
                        "normalized_endpoint_roles": role_records,
                        "minimum_deficient_anchor_hex": [
                            f"{ideal:x}" for ideal in anchors
                        ],
                        "minimum_deficient_anchor_neighbor_indices": list(neighbors),
                    }
                    if not forced and first_forced_endpoint_failure is None:
                        first_forced_endpoint_failure = failure
                    if "left_future" not in forced and first_left_future_failure is None:
                        first_left_future_failure = failure
        totals.update(group_counts)
        groups.append(
            {
                "color": group["color"],
                "rank": rank,
                "frontier_size": size,
                "statistics": dict(sorted(group_counts.items())),
            }
        )
    return {
        "strong_size": strong_size,
        "group_count": len(groups),
        "statistics": dict(sorted(totals.items())),
        "forced_role_pattern_histogram": dict(sorted(patterns.items())),
        "all_nonvacuous_holes_have_forced_endpoint": (
            first_forced_endpoint_failure is None
        ),
        "first_forced_endpoint_failure": first_forced_endpoint_failure,
        "all_nonvacuous_holes_force_left_future": first_left_future_failure is None,
        "first_left_future_failure": first_left_future_failure,
        "groups": groups,
    }


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_forced_endpoint_extreme.py"
    return {
        "schema_version": 1,
        "experiment": "frozen-forced-endpoint-extreme-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "domain": (
                "every nonempty consecutive block and nonvacuous hole of the "
                "four frozen n=12, k=7 reflected endpoint groups"
            ),
            "proposed_claim": (
                "some normalized past/future ideal at the hole's two endpoints "
                "occurs in no compatible owner whose family is smaller than "
                "the block"
            ),
            "secondary_fixed_role_claim": (
                "the normalized future ideal at the hole's left endpoint has "
                "that property"
            ),
            "claim_boundary": (
                "bounded frozen-root evidence only, not the arbitrary forced-"
                "extreme theorem"
            ),
        },
        "frozen_n12_k7": analyze(),
        "sources": {
            "producer": {
                "path": str(producer.relative_to(repo)),
                "sha256": file_sha256(producer),
            },
            "checker": {
                "path": str(checker.relative_to(repo)),
                "sha256": file_sha256(checker),
            },
            "mask_base": {
                "path": "scripts/check_block_large_reached_owner.py",
                "sha256": file_sha256(repo / "scripts/check_block_large_reached_owner.py"),
            },
            "height_base": {
                "path": "scripts/replay_block_large_reached_owner.py",
                "sha256": file_sha256(repo / "scripts/replay_block_large_reached_owner.py"),
            },
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent.parent
    write_atomic(args.output, produce(repo))
    print(args.output)


if __name__ == "__main__":
    main()
