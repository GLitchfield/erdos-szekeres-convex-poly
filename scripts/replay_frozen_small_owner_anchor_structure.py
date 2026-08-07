#!/usr/bin/env python3
"""Independently replay the frozen minimum-anchor classification."""

from __future__ import annotations

import argparse
from collections import Counter
import itertools
import json
from pathlib import Path

from check_allocated_span_pascal_demand import (
    file_sha256,
    height_ideals,
    height_interval,
    height_mask_hex,
)
from replay_block_large_reached_owner import enumerate_owner_maps, frozen_groups
from replay_singleton_large_owner_profile import reflected


Ideal = tuple[int, ...]

PREDICATES = (
    "chain",
    "saturated_chain",
    "lattice_interval",
    "relative_lattice_interval",
    "boundary_consecutive",
    "contained_in_one_lane",
    "one_lane_saturated_interval",
    "one_lane_boundary_consecutive_relative_interval",
)


def check_sources(manifest: dict[str, object], repo: Path) -> None:
    for name, source in manifest["sources"].items():
        path = repo / source["path"]
        actual = file_sha256(path)
        if actual != source["sha256"]:
            raise SystemExit(
                f"stale {name} source: expected {source['sha256']}, got {actual}"
            )


def normalized_lanes(
    geometry: dict[str, object], columns: int
) -> dict[str, frozenset[Ideal]]:
    lanes = {}
    for name in ("left", "right"):
        masks = {
            str(encoded)
            for encoded in geometry[f"{name}_lane"]["raw_interval_hex"]
        }
        all_rows = len(geometry[f"{name}_lane"]["past"]["boundary_slot"])
        ideals = tuple(
            ideal
            for ideal in height_ideals(all_rows, columns)
            if height_mask_hex(ideal, columns) in masks
        )
        if geometry["reflected"]:
            ideals = tuple(reflected(ideal, columns) for ideal in ideals)
        lanes[name] = frozenset(ideals)
    return lanes


def normalized_extremes(
    geometry: dict[str, object], columns: int
) -> frozenset[Ideal]:
    answer = set()
    for name in ("left", "right"):
        for time in ("past", "future"):
            slots = geometry[f"{name}_lane"][time]["boundary_slot"]
            ideal = tuple(
                row + columns - int(slot)
                for row, slot in enumerate(slots)
            )
            if geometry["reflected"]:
                ideal = reflected(ideal, columns)
            answer.add(ideal)
    return frozenset(answer)


def minimum_deficient_anchors(
    hole: int, candidates: tuple[tuple[Ideal, ...], ...]
) -> tuple[tuple[tuple[Ideal, ...], tuple[int, ...]], ...]:
    family = tuple(
        sorted(candidates[hole], key=lambda ideal: tuple(reversed(ideal)))
    )
    block_size = len(candidates)
    small_owners = tuple(
        owner
        for owner, owner_family in enumerate(candidates)
        if owner != hole and len(owner_family) < block_size
    )
    for size in range(1, len(family) + 1):
        answer = []
        for anchors in itertools.combinations(family, size):
            neighbors = tuple(
                owner
                for owner in small_owners
                if any(ideal in candidates[owner] for ideal in anchors)
            )
            if len(neighbors) < len(anchors):
                answer.append((anchors, neighbors))
        if answer:
            return tuple(answer)
    return ()


def classify_anchor(
    anchors: tuple[Ideal, ...],
    neighbors: tuple[int, ...],
    candidates: tuple[tuple[Ideal, ...], ...],
    hole_family: tuple[Ideal, ...],
    lanes: dict[str, frozenset[Ideal]],
    extremes: frozenset[Ideal],
    ideals: tuple[Ideal, ...],
    columns: int,
) -> dict[str, object]:
    ordered = tuple(sorted(anchors, key=lambda ideal: (sum(ideal), ideal)))
    chain = all(
        all(a <= b for a, b in zip(first, second, strict=True))
        or all(b <= a for a, b in zip(first, second, strict=True))
        for first, second in itertools.combinations(ordered, 2)
    )
    saturated = chain and all(
        sum(second) - sum(first) == 1
        and all(a <= b for a, b in zip(first, second, strict=True))
        for first, second in zip(ordered, ordered[1:])
    )
    lower = tuple(min(values) for values in zip(*anchors, strict=True))
    upper = tuple(max(values) for values in zip(*anchors, strict=True))
    lattice_interval = set(height_interval(ideals, lower, upper)) == set(anchors)
    relative_lattice_interval = (
        set(height_interval(ideals, lower, upper)) & set(hole_family)
    ) == set(anchors)
    ideal_order = sorted(
        ideals,
        key=lambda ideal: tuple(
            row + columns - height for row, height in enumerate(ideal)
        ),
    )
    positions = sorted(ideal_order.index(ideal) for ideal in anchors)
    boundary_consecutive = positions[-1] - positions[0] + 1 == len(positions)
    lane_names = [
        name for name, lane in lanes.items() if set(anchors) <= lane
    ]
    incidence = {
        str(owner): [
            height_mask_hex(ideal, columns)
            for ideal in anchors
            if ideal in candidates[owner]
        ]
        for owner in neighbors
    }
    return {
        "anchors_hex": [height_mask_hex(ideal, columns) for ideal in anchors],
        "anchor_boundary_slots": [
            [row + columns - height for row, height in enumerate(ideal)]
            for ideal in anchors
        ],
        "neighbor_indices": list(neighbors),
        "neighbor_anchor_incidence": incidence,
        "deficiency": len(anchors) - len(neighbors),
        "chain": chain,
        "saturated_chain": saturated,
        "lattice_interval": lattice_interval,
        "relative_lattice_interval": relative_lattice_interval,
        "boundary_consecutive": boundary_consecutive,
        "contained_in_one_lane": bool(lane_names),
        "containing_lanes": lane_names,
        "one_lane_saturated_interval": (
            bool(lane_names) and saturated and lattice_interval
        ),
        "one_lane_boundary_consecutive_relative_interval": (
            bool(lane_names)
            and boundary_consecutive
            and relative_lattice_interval
        ),
        "all_anchors_endpoint_extremes": set(anchors) <= extremes,
        "endpoint_extreme_count": len(set(anchors) & extremes),
    }


def analyze() -> dict[str, object]:
    strong_size = 7
    totals: Counter[str] = Counter()
    first_existence_failures: dict[str, dict[str, object] | None] = {
        predicate: None for predicate in PREDICATES
    }
    first_universal_failures: dict[str, dict[str, object] | None] = {
        predicate: None for predicate in PREDICATES
    }
    multi_anchor_holes = []
    for group_index, group in enumerate(frozen_groups()):
        rank = int(group["rank"])
        rows = rank - 1
        columns = strong_size - rank - 1
        ideals = height_ideals(rows, columns)
        frontier = tuple(tuple(span) for span in group["frontier"])
        candidates = tuple(group["candidates"])
        geometry = tuple(group["geometry"])
        for start in range(len(frontier)):
            for stop in range(start + 1, len(frontier) + 1):
                block = candidates[start:stop]
                for hole in range(len(block)):
                    if not enumerate_owner_maps(hole, block):
                        totals["vacuous_holes"] += 1
                        continue
                    totals["nonvacuous_holes"] += 1
                    anchor_pairs = minimum_deficient_anchors(hole, block)
                    if not anchor_pairs:
                        raise AssertionError("nonvacuous passing hole has no deficiency")
                    lanes = normalized_lanes(
                        geometry[start + hole], columns
                    )
                    extremes = normalized_extremes(
                        geometry[start + hole], columns
                    )
                    records = [
                        classify_anchor(
                            anchors,
                            neighbors,
                            block,
                            block[hole],
                            lanes,
                            extremes,
                            ideals,
                            columns,
                        )
                        for anchors, neighbors in anchor_pairs
                    ]
                    anchor_size = len(anchor_pairs[0][0])
                    totals[f"minimum_anchor_size_{anchor_size}"] += 1
                    totals[f"minimum_anchor_count_{len(records)}"] += 1
                    if all(record["deficiency"] == 1 for record in records):
                        totals["all_minimum_anchors_deficiency_one"] += 1
                    context = {
                        "group_index": group_index,
                        "color": group["color"],
                        "rank": rank,
                        "start_index": start,
                        "stop_index": stop,
                        "hole_index": hole,
                        "hole_span": list(frontier[start + hole]),
                        "block_frontier": [
                            list(span) for span in frontier[start:stop]
                        ],
                        "hole_family_hex": [
                            height_mask_hex(ideal, columns)
                            for ideal in block[hole]
                        ],
                        "minimum_anchors": records,
                    }
                    for predicate in PREDICATES:
                        if any(record[predicate] for record in records):
                            totals[f"has_{predicate}"] += 1
                        elif first_existence_failures[predicate] is None:
                            first_existence_failures[predicate] = context
                        if all(record[predicate] for record in records):
                            totals[f"all_minimum_anchors_have_{predicate}"] += 1
                        elif first_universal_failures[predicate] is None:
                            first_universal_failures[predicate] = context
                    if anchor_size > 1:
                        multi_anchor_holes.append(context)
    return {
        "strong_size": strong_size,
        "statistics": dict(sorted(totals.items())),
        "every_nonvacuous_hole_has_some_minimum_anchor_with": {
            predicate: first_existence_failures[predicate] is None
            for predicate in PREDICATES
        },
        "every_nonvacuous_hole_has_only_minimum_anchors_with": {
            predicate: first_universal_failures[predicate] is None
            for predicate in PREDICATES
        },
        "first_existence_failures": first_existence_failures,
        "first_universal_failures": first_universal_failures,
        "multi_anchor_holes": multi_anchor_holes,
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
        raise SystemExit("independent anchor-structure replay disagrees")
    print(f"verified {args.manifest} ({file_sha256(args.manifest)})")


if __name__ == "__main__":
    main()
