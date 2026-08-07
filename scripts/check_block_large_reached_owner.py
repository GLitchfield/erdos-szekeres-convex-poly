#!/usr/bin/env python3
"""Produce the frozen block-large reached-owner gate.

For every feasible owner map from experiment 0041, test the stronger condition
that at least one mapped owner has a candidate family as large as the block.
The witness retains the genuine endpoint lanes and reflection orientation so
the normalized family is not mistaken for an arbitrary lattice interval.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path

from check_owner_star_expansion import enumerate_owner_maps, priority
from check_singleton_large_owner_profile import (
    DecomposableColorings,
    FROZEN_LOWER_TREE,
    FROZEN_TREE,
    LocalSpanAnalysis,
    tree_coloring_bits,
    tree_support,
)
from enumerate_allocated_span_pascal_demand import (
    context_groups,
    endpoint_rank_ideal,
    endpoint_transition_candidates,
    file_sha256,
    git_revision,
    write_atomic,
)
from enumerate_reflected_transition_hall import oriented_candidates


OwnerMap = tuple[int, ...]


def boundary_slot(mask: int, rows: int, columns: int) -> list[int]:
    """Horizontal-step positions of a rectangular ideal boundary."""
    row_mask = (1 << columns) - 1
    return [
        row + columns - ((mask >> (row * columns)) & row_mask).bit_count()
        for row in range(rows)
    ]


def ideal_record(mask: int, rows: int, columns: int) -> dict[str, object]:
    return {
        "ideal_hex": f"{mask:x}",
        "boundary_slot": boundary_slot(mask, rows, columns),
    }


def span_geometry(
    local: dict[tuple[int, int, int], int],
    vertices: tuple[int, ...],
    span: tuple[int, int],
    color: int,
    rank: int,
    strong_size: int,
    lower: int,
    left_interval: tuple[int, ...],
    right_interval: tuple[int, ...],
) -> dict[str, object]:
    rows = rank - 1
    columns = strong_size - rank - 1

    def endpoint_record(endpoint: int, interval: tuple[int, ...]) -> dict[str, object]:
        past = endpoint_rank_ideal(
            local, vertices, endpoint, color, rank, strong_size, True
        )
        future = endpoint_rank_ideal(
            local, vertices, endpoint, color, rank, strong_size, False
        )
        return {
            "endpoint": endpoint,
            "past": ideal_record(past, rows, columns),
            "future": ideal_record(future, rows, columns),
            "raw_interval_hex": [f"{ideal:x}" for ideal in interval],
        }

    return {
        "span": list(span),
        "reflected": not bool(lower & (1 << span[0])),
        "left_lane": endpoint_record(span[0], left_interval),
        "right_lane": endpoint_record(span[1], right_interval),
    }


def witness_record(
    hole_family: tuple[int, ...],
    owners: OwnerMap,
    candidates: tuple[tuple[int, ...], ...],
    frontier: tuple[tuple[int, int], ...],
    geometry: tuple[dict[str, object], ...],
) -> dict[str, object]:
    mapped = [
        {
            "ideal_hex": f"{ideal:x}",
            "owner_index": owner,
            "owner_span": list(frontier[owner]),
            "owner_family_size": len(candidates[owner]),
        }
        for ideal, owner in zip(hole_family, owners, strict=True)
    ]
    maximum = max(entry["owner_family_size"] for entry in mapped)
    selected = min(
        (entry for entry in mapped if entry["owner_family_size"] == maximum),
        key=lambda entry: (int(entry["ideal_hex"], 16), entry["owner_index"]),
    )
    owner_index = int(selected["owner_index"])
    return {
        "owner_map": mapped,
        "selected_owner": {
            **selected,
            "candidate_family_hex": [
                f"{ideal:x}" for ideal in candidates[owner_index]
            ],
            "geometry": geometry[owner_index],
        },
    }


def analyze_hole(
    hole: int,
    candidates: tuple[tuple[int, ...], ...],
    frontier: tuple[tuple[int, int], ...],
    geometry: tuple[dict[str, object], ...],
    rows: int,
    columns: int,
) -> dict[str, object]:
    maps = enumerate_owner_maps(hole, candidates, rows, columns)
    histogram: Counter[int] = Counter()
    minimum = None
    first_minimum = None
    first_failure = None
    for hole_family, owners in maps:
        if not owners:
            slack = -len(candidates)
            record = {"owner_map": [], "selected_owner": None}
        else:
            maximum = max(len(candidates[owner]) for owner in owners)
            slack = maximum - len(candidates)
            record = witness_record(
                hole_family, owners, candidates, frontier, geometry
            )
        histogram[slack] += 1
        if minimum is None or slack < minimum:
            minimum = slack
            first_minimum = {"slack": slack, **record}
        if slack < 0 and first_failure is None:
            first_failure = {"slack": slack, **record}
    return {
        "hole_index": hole,
        "hole_span": list(frontier[hole]),
        "candidate_family_hex": [
            f"{ideal:x}"
            for ideal in sorted(
                candidates[hole], key=lambda value: priority(value, rows, columns)
            )
        ],
        "feasible_owner_map_count": len(maps),
        "max_owner_family_slack_histogram": {
            str(slack): count for slack, count in sorted(histogram.items())
        },
        "minimum_max_owner_family_slack": minimum,
        "all_feasible_maps_reach_block_large_owner": first_failure is None,
        "first_minimum_witness": first_minimum,
        "first_failure": first_failure,
    }


def analyze_block(
    group: dict[str, object], start: int, stop: int, strong_size: int
) -> dict[str, object]:
    rank = int(group["rank"])
    rows = rank - 1
    columns = strong_size - rank - 1
    frontier = tuple(tuple(span) for span in group["frontier"][start:stop])
    candidates = tuple(group["candidates"][start:stop])
    geometry = tuple(group["geometry"][start:stop])
    holes = [
        analyze_hole(
            hole, candidates, frontier, geometry, rows, columns
        )
        for hole in range(len(candidates))
    ]
    nonvacuous = [
        hole for hole in holes if hole["feasible_owner_map_count"] > 0
    ]
    first_failure = next(
        (
            hole
            for hole in holes
            if not hole["all_feasible_maps_reach_block_large_owner"]
        ),
        None,
    )
    return {
        "start_index": start,
        "stop_index": stop,
        "block_size": stop - start,
        "frontier": [list(span) for span in frontier],
        "candidate_families_hex": [
            [f"{ideal:x}" for ideal in family] for family in candidates
        ],
        "feasible_owner_map_count": sum(
            hole["feasible_owner_map_count"] for hole in holes
        ),
        "minimum_max_owner_family_slack": (
            min(hole["minimum_max_owner_family_slack"] for hole in nonvacuous)
            if nonvacuous
            else None
        ),
        "all_feasible_maps_reach_block_large_owner": first_failure is None,
        "first_failure": first_failure,
        "holes": holes,
    }


def analyze_group(group: dict[str, object], strong_size: int) -> dict[str, object]:
    size = len(group["frontier"])
    blocks = [
        analyze_block(group, start, stop, strong_size)
        for start in range(size)
        for stop in range(start + 1, size + 1)
    ]
    nonvacuous = [
        block for block in blocks if block["feasible_owner_map_count"] > 0
    ]
    first_failure = next(
        (
            block
            for block in blocks
            if not block["all_feasible_maps_reach_block_large_owner"]
        ),
        None,
    )
    return {
        "color": group["color"],
        "rank": group["rank"],
        "full_frontier": group["frontier"],
        "full_span_geometry": list(group["geometry"]),
        "full_block_size": size,
        "consecutive_block_count": len(blocks),
        "feasible_owner_map_count": sum(
            block["feasible_owner_map_count"] for block in blocks
        ),
        "minimum_max_owner_family_slack": (
            min(block["minimum_max_owner_family_slack"] for block in nonvacuous)
            if nonvacuous
            else None
        ),
        "all_feasible_maps_reach_block_large_owner": first_failure is None,
        "first_failing_block": first_failure,
        "blocks": blocks,
    }


def frozen_groups() -> tuple[dict[str, object], ...]:
    maximum_n = 12
    strong_size = 7
    colorings = DecomposableColorings(maximum_n)
    analyzer = LocalSpanAnalysis(maximum_n, strong_size)
    support = tree_support(FROZEN_TREE)
    lower = tree_support(FROZEN_LOWER_TREE)
    bits = tree_coloring_bits(FROZEN_TREE, colorings)
    local = analyzer.analyze(bits, support)
    if local is None:
        raise AssertionError("frozen root unexpectedly contains a strong seven")
    vertices = tuple(
        vertex for vertex in range(maximum_n) if support & (1 << vertex)
    )
    groups = []
    for color, rank, frontier in context_groups(
        local, support, lower, maximum_n
    ):
        original, left_only, right_only, _ = endpoint_transition_candidates(
            local, vertices, frontier, color, rank, strong_size
        )
        candidates = oriented_candidates(
            original,
            frontier,
            lower,
            rank - 1,
            strong_size - rank - 1,
        )
        geometry = tuple(
            span_geometry(
                local,
                vertices,
                span,
                color,
                rank,
                strong_size,
                lower,
                left_interval,
                right_interval,
            )
            for span, left_interval, right_interval in zip(
                frontier, left_only, right_only, strict=True
            )
        )
        groups.append(
            {
                "color": "cup" if color else "cap",
                "rank": rank,
                "frontier": [list(span) for span in frontier],
                "candidates": candidates,
                "geometry": geometry,
            }
        )
    return tuple(groups)


def frozen_record() -> dict[str, object]:
    maximum_n = 12
    strong_size = 7
    support = tree_support(FROZEN_TREE)
    lower = tree_support(FROZEN_LOWER_TREE)
    bits = tree_coloring_bits(FROZEN_TREE, DecomposableColorings(maximum_n))
    groups = [analyze_group(group, strong_size) for group in frozen_groups()]
    nonvacuous = [
        group for group in groups if group["feasible_owner_map_count"] > 0
    ]
    return {
        "maximum_n": maximum_n,
        "strong_size": strong_size,
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "group_count": len(groups),
        "consecutive_block_count": sum(
            group["consecutive_block_count"] for group in groups
        ),
        "feasible_owner_map_count": sum(
            group["feasible_owner_map_count"] for group in groups
        ),
        "minimum_max_owner_family_slack": min(
            group["minimum_max_owner_family_slack"] for group in nonvacuous
        ),
        "all_feasible_maps_reach_block_large_owner": all(
            group["all_feasible_maps_reach_block_large_owner"]
            for group in groups
        ),
        "groups": groups,
    }


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_block_large_reached_owner.py"
    return {
        "schema_version": 1,
        "experiment": "frozen-block-large-reached-owner-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "domain": (
                "every nonempty consecutive frozen block, every hole, and every "
                "injective membership-feasible owner map"
            ),
            "success": (
                "at least one mapped owner has candidate-family cardinality at "
                "least the block cardinality"
            ),
            "interpretation": (
                "a stronger sufficient profile for feasible owner-star expansion"
            ),
            "claim_boundary": (
                "bounded frozen-n12-k7 evidence; no arbitrary genuine-frontier "
                "profile, Hall theorem, or exact-formula conclusion"
            ),
        },
        "frozen_n12_k7": frozen_record(),
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
                "path": "scripts/enumerate_allocated_span_pascal_demand.py",
                "sha256": file_sha256(
                    repo / "scripts/enumerate_allocated_span_pascal_demand.py"
                ),
            },
            "height_base": {
                "path": "scripts/check_allocated_span_pascal_demand.py",
                "sha256": file_sha256(
                    repo / "scripts/check_allocated_span_pascal_demand.py"
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
