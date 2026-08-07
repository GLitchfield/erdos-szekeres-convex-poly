#!/usr/bin/env python3
"""Independently replay fixed forced endpoint extremes on the frozen root."""

from __future__ import annotations

import argparse
from collections import Counter
import itertools
import json
from pathlib import Path

from check_allocated_span_pascal_demand import file_sha256, height_mask_hex
from replay_block_large_reached_owner import enumerate_owner_maps, frozen_groups
from replay_singleton_large_owner_profile import reflected


Ideal = tuple[int, ...]


def check_sources(manifest: dict[str, object], repo: Path) -> None:
    for name, source in manifest["sources"].items():
        path = repo / source["path"]
        actual = file_sha256(path)
        if actual != source["sha256"]:
            raise SystemExit(
                f"stale {name} source: expected {source['sha256']}, got {actual}"
            )


def normalized_roles(
    geometry: dict[str, object], columns: int
) -> tuple[tuple[str, Ideal], ...]:
    answer = []
    for lane in ("left_lane", "right_lane"):
        for time in ("past", "future"):
            slots = geometry[lane][time]["boundary_slot"]
            ideal = tuple(
                row + columns - int(slot) for row, slot in enumerate(slots)
            )
            if geometry["reflected"]:
                ideal = reflected(ideal, columns)
            answer.append((f"{lane.removesuffix('_lane')}_{time}", ideal))
    return tuple(answer)


def first_deficient_anchor(
    hole: int,
    candidates: tuple[tuple[Ideal, ...], ...],
    columns: int,
) -> tuple[tuple[Ideal, ...], tuple[int, ...]] | None:
    hole_family = tuple(
        sorted(
            candidates[hole],
            key=lambda ideal: int(height_mask_hex(ideal, columns), 16),
        )
    )
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
                    maps = enumerate_owner_maps(hole, block)
                    if not maps:
                        group_counts["vacuous_holes"] += 1
                        continue
                    group_counts["nonvacuous_holes"] += 1
                    small_owners = tuple(
                        owner
                        for owner, family in enumerate(block)
                        if owner != hole and len(family) < block_size
                    )
                    roles = normalized_roles(geometry[start + hole], columns)
                    anchor = first_deficient_anchor(hole, block, columns)
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
                            "ideal_hex": height_mask_hex(ideal, columns),
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
                            sorted(
                                (height_mask_hex(ideal, columns) for ideal in family),
                                key=lambda encoded: int(encoded, 16),
                            )
                            for family in block
                        ],
                        "forced_roles": list(forced),
                        "normalized_endpoint_roles": role_records,
                        "minimum_deficient_anchor_hex": [
                            height_mask_hex(ideal, columns) for ideal in anchors
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    repo = Path(__file__).resolve().parent.parent
    check_sources(manifest, repo)
    actual = analyze()
    if actual != manifest["frozen_n12_k7"]:
        raise SystemExit("independent forced-extreme replay disagrees")
    print(f"verified {args.manifest} ({file_sha256(args.manifest)})")


if __name__ == "__main__":
    main()
