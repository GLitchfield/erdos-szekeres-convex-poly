#!/usr/bin/env python3
"""Independently replay the frozen block-large reached-owner gate."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

from check_allocated_span_pascal_demand import (
    Replay,
    endpoint_rank_heights,
    file_sha256,
    groups,
    height_mask_hex,
    replay_transition_candidates,
)
from replay_singleton_large_owner_profile import (
    LOWER_TREE,
    TREE,
    coloring_bits,
    reflected,
    vertices,
)


Ideal = tuple[int, ...]
OwnerMap = tuple[int, ...]


def enumerate_owner_maps(
    hole: int, candidates: tuple[tuple[Ideal, ...], ...]
) -> tuple[tuple[tuple[Ideal, ...], OwnerMap], ...]:
    hole_family = tuple(sorted(candidates[hole]))
    domains = tuple(
        tuple(
            owner
            for owner, family in enumerate(candidates)
            if owner != hole and ideal in family
        )
        for ideal in hole_family
    )
    answer: list[tuple[tuple[Ideal, ...], OwnerMap]] = []

    def visit(position: int, used: frozenset[int], owners: tuple[int, ...]) -> None:
        if position == len(hole_family):
            answer.append((hole_family, owners))
            return
        for owner in domains[position]:
            if owner not in used:
                visit(position + 1, used | {owner}, owners + (owner,))

    visit(0, frozenset(), ())
    return tuple(answer)


def ideal_record(ideal: Ideal, columns: int) -> dict[str, object]:
    return {
        "ideal_hex": height_mask_hex(ideal, columns),
        "boundary_slot": [
            row + columns - height for row, height in enumerate(ideal)
        ],
    }


def span_geometry(
    local: dict[tuple[int, int, int], int],
    support_vertices: tuple[int, ...],
    span: tuple[int, int],
    color: int,
    rank: int,
    strong_size: int,
    lower: int,
    left_interval: tuple[Ideal, ...],
    right_interval: tuple[Ideal, ...],
) -> dict[str, object]:
    columns = strong_size - rank - 1

    def endpoint_record(
        endpoint: int, interval: tuple[Ideal, ...]
    ) -> dict[str, object]:
        past = endpoint_rank_heights(
            local,
            support_vertices,
            endpoint,
            color,
            rank,
            strong_size,
            True,
        )
        future = endpoint_rank_heights(
            local,
            support_vertices,
            endpoint,
            color,
            rank,
            strong_size,
            False,
        )
        return {
            "endpoint": endpoint,
            "past": ideal_record(past, columns),
            "future": ideal_record(future, columns),
            "raw_interval_hex": sorted(
                (height_mask_hex(ideal, columns) for ideal in interval),
                key=lambda encoded: int(encoded, 16),
            ),
        }

    return {
        "span": list(span),
        "reflected": not bool(lower & (1 << span[0])),
        "left_lane": endpoint_record(span[0], left_interval),
        "right_lane": endpoint_record(span[1], right_interval),
    }


def witness_record(
    hole_family: tuple[Ideal, ...],
    owners: OwnerMap,
    candidates: tuple[tuple[Ideal, ...], ...],
    frontier: tuple[tuple[int, int], ...],
    geometry: tuple[dict[str, object], ...],
    columns: int,
) -> dict[str, object]:
    mapped = [
        {
            "ideal_hex": height_mask_hex(ideal, columns),
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
            "candidate_family_hex": sorted(
                (
                    height_mask_hex(ideal, columns)
                    for ideal in candidates[owner_index]
                ),
                key=lambda encoded: int(encoded, 16),
            ),
            "geometry": geometry[owner_index],
        },
    }


def analyze_hole(
    hole: int,
    candidates: tuple[tuple[Ideal, ...], ...],
    frontier: tuple[tuple[int, int], ...],
    geometry: tuple[dict[str, object], ...],
    columns: int,
) -> dict[str, object]:
    maps = enumerate_owner_maps(hole, candidates)
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
                hole_family,
                owners,
                candidates,
                frontier,
                geometry,
                columns,
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
            height_mask_hex(ideal, columns) for ideal in sorted(candidates[hole])
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
    columns = strong_size - rank - 1
    frontier = tuple(tuple(span) for span in group["frontier"][start:stop])
    candidates = tuple(group["candidates"][start:stop])
    geometry = tuple(group["geometry"][start:stop])
    holes = [
        analyze_hole(hole, candidates, frontier, geometry, columns)
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
            sorted(
                (height_mask_hex(ideal, columns) for ideal in family),
                key=lambda encoded: int(encoded, 16),
            )
            for family in candidates
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
    machine = Replay(maximum_n, strong_size)
    support_vertices = vertices(TREE)
    support = sum(1 << vertex for vertex in support_vertices)
    lower = sum(1 << vertex for vertex in vertices(LOWER_TREE))
    bits = coloring_bits(TREE, machine)
    local = machine.ranks(bits, support)
    if local is None:
        raise AssertionError("frozen root unexpectedly contains a strong seven")
    records = []
    for color, rank, frontier in groups(
        local, support, lower, maximum_n
    ):
        original, left_only, right_only, _ = replay_transition_candidates(
            local,
            support_vertices,
            frontier,
            color,
            rank,
            strong_size,
        )
        columns = strong_size - rank - 1
        candidates = []
        for span, family in zip(frontier, original, strict=True):
            if lower & (1 << span[0]):
                oriented = family
            else:
                oriented = tuple(sorted(reflected(ideal, columns) for ideal in family))
            candidates.append(oriented)
        geometry = tuple(
            span_geometry(
                local,
                support_vertices,
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
        records.append(
            {
                "color": "cup" if color else "cap",
                "rank": rank,
                "frontier": [list(span) for span in frontier],
                "candidates": tuple(candidates),
                "geometry": geometry,
            }
        )
    return tuple(records)


def frozen_record() -> dict[str, object]:
    maximum_n = 12
    strong_size = 7
    machine = Replay(maximum_n, strong_size)
    support_vertices = vertices(TREE)
    support = sum(1 << vertex for vertex in support_vertices)
    lower = sum(1 << vertex for vertex in vertices(LOWER_TREE))
    bits = coloring_bits(TREE, machine)
    groups_record = [
        analyze_group(group, strong_size) for group in frozen_groups()
    ]
    nonvacuous = [
        group
        for group in groups_record
        if group["feasible_owner_map_count"] > 0
    ]
    return {
        "maximum_n": maximum_n,
        "strong_size": strong_size,
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "group_count": len(groups_record),
        "consecutive_block_count": sum(
            group["consecutive_block_count"] for group in groups_record
        ),
        "feasible_owner_map_count": sum(
            group["feasible_owner_map_count"] for group in groups_record
        ),
        "minimum_max_owner_family_slack": min(
            group["minimum_max_owner_family_slack"] for group in nonvacuous
        ),
        "all_feasible_maps_reach_block_large_owner": all(
            group["all_feasible_maps_reach_block_large_owner"]
            for group in groups_record
        ),
        "groups": groups_record,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    if manifest.get("schema_version") != 1:
        parser.error("unsupported schema")
    repo = Path(__file__).resolve().parent.parent
    for source in manifest["sources"].values():
        path = repo / source["path"]
        if file_sha256(path) != source["sha256"]:
            raise AssertionError(f"source hash mismatch: {source['path']}")
    replay = frozen_record()
    if replay != manifest["frozen_n12_k7"]:
        raise AssertionError("independent block-large-owner replay differs")
    print(
        "blocks=", replay["consecutive_block_count"],
        "owner_maps=", replay["feasible_owner_map_count"],
        "minimum_slack=", replay["minimum_max_owner_family_slack"],
        "all_reach_block_large_owner=",
        replay["all_feasible_maps_reach_block_large_owner"],
    )


if __name__ == "__main__":
    main()
