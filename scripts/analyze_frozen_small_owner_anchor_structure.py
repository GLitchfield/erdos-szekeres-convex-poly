#!/usr/bin/env python3
"""Classify minimum small-owner deficient anchors on the frozen k=7 root.

This bounded producer uses cell-mask ideals.  Its independent replay uses
row-height ideals and reconstructs the frozen root separately.
"""

from __future__ import annotations

import argparse
from collections import Counter
import itertools
from pathlib import Path

from check_block_large_reached_owner import frozen_groups
from check_owner_star_expansion import enumerate_owner_maps
from enumerate_allocated_span_pascal_demand import (
    file_sha256,
    git_revision,
    ideal_interval,
    rectangular_lower_ideals,
    write_atomic,
)
from enumerate_reflected_transition_hall import reflected_ideal


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


def boundary_slot(mask: int, rows: int, columns: int) -> list[int]:
    row_mask = (1 << columns) - 1
    return [
        row + columns - ((mask >> (row * columns)) & row_mask).bit_count()
        for row in range(rows)
    ]


def normalized_lanes(
    geometry: dict[str, object], rows: int, columns: int
) -> dict[str, frozenset[int]]:
    lanes = {}
    for name in ("left", "right"):
        masks = tuple(
            int(encoded, 16)
            for encoded in geometry[f"{name}_lane"]["raw_interval_hex"]
        )
        if geometry["reflected"]:
            masks = tuple(
                reflected_ideal(mask, rows, columns) for mask in masks
            )
        lanes[name] = frozenset(masks)
    return lanes


def normalized_extremes(
    geometry: dict[str, object], rows: int, columns: int
) -> frozenset[int]:
    answer = set()
    for name in ("left", "right"):
        for time in ("past", "future"):
            ideal = int(geometry[f"{name}_lane"][time]["ideal_hex"], 16)
            if geometry["reflected"]:
                ideal = reflected_ideal(ideal, rows, columns)
            answer.add(ideal)
    return frozenset(answer)


def minimum_deficient_anchors(
    hole: int, candidates: tuple[tuple[int, ...], ...]
) -> tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]:
    family = tuple(sorted(candidates[hole]))
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
    anchors: tuple[int, ...],
    neighbors: tuple[int, ...],
    candidates: tuple[tuple[int, ...], ...],
    hole_family: tuple[int, ...],
    lanes: dict[str, frozenset[int]],
    extremes: frozenset[int],
    ideals: tuple[int, ...],
    rows: int,
    columns: int,
) -> dict[str, object]:
    ordered = tuple(sorted(anchors, key=lambda ideal: (ideal.bit_count(), ideal)))
    chain = all(
        first & second in (first, second)
        for first, second in itertools.combinations(ordered, 2)
    )
    saturated = chain and all(
        (second.bit_count() - first.bit_count() == 1)
        and first & second == first
        for first, second in zip(ordered, ordered[1:])
    )
    lower = anchors[0]
    upper = anchors[0]
    for ideal in anchors[1:]:
        lower &= ideal
        upper |= ideal
    lattice_interval = set(ideal_interval(ideals, lower, upper)) == set(anchors)
    relative_lattice_interval = (
        set(ideal_interval(ideals, lower, upper)) & set(hole_family)
    ) == set(anchors)
    ideal_order = sorted(
        ideals, key=lambda ideal: tuple(boundary_slot(ideal, rows, columns))
    )
    positions = sorted(ideal_order.index(ideal) for ideal in anchors)
    boundary_consecutive = positions[-1] - positions[0] + 1 == len(positions)
    lane_names = [
        name for name, lane in lanes.items() if set(anchors) <= lane
    ]
    incidence = {
        str(owner): [
            f"{ideal:x}" for ideal in anchors if ideal in candidates[owner]
        ]
        for owner in neighbors
    }
    return {
        "anchors_hex": [f"{ideal:x}" for ideal in anchors],
        "anchor_boundary_slots": [
            boundary_slot(ideal, rows, columns) for ideal in anchors
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
        ideals = rectangular_lower_ideals(rows, columns)
        frontier = tuple(tuple(span) for span in group["frontier"])
        candidates = tuple(group["candidates"])
        geometry = tuple(group["geometry"])
        for start in range(len(frontier)):
            for stop in range(start + 1, len(frontier) + 1):
                block = candidates[start:stop]
                for hole in range(len(block)):
                    if not enumerate_owner_maps(hole, block, rows, columns):
                        totals["vacuous_holes"] += 1
                        continue
                    totals["nonvacuous_holes"] += 1
                    anchor_pairs = minimum_deficient_anchors(hole, block)
                    if not anchor_pairs:
                        raise AssertionError("nonvacuous passing hole has no deficiency")
                    lanes = normalized_lanes(
                        geometry[start + hole], rows, columns
                    )
                    extremes = normalized_extremes(
                        geometry[start + hole], rows, columns
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
                            rows,
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
                            f"{ideal:x}" for ideal in block[hole]
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


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_frozen_small_owner_anchor_structure.py"
    return {
        "schema_version": 1,
        "experiment": "frozen-small-owner-anchor-structure",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "domain": (
                "every nonvacuous hole in every consecutive block of the four "
                "frozen n=12, k=7 reflected endpoint groups"
            ),
            "question": (
                "can a minimum-cardinality deficient anchor always be chosen "
                "as a saturated lattice interval contained in one normalized "
                "endpoint lane?"
            ),
            "claim_boundary": (
                "bounded classification evidence only; no arbitrary geometry "
                "or small-owner-deficiency theorem"
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
                "sha256": file_sha256(
                    repo / "scripts/check_block_large_reached_owner.py"
                ),
            },
            "height_base": {
                "path": "scripts/replay_block_large_reached_owner.py",
                "sha256": file_sha256(
                    repo / "scripts/replay_block_large_reached_owner.py"
                ),
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
