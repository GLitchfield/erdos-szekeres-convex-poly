#!/usr/bin/env python3
"""Independently replay the feasible-owner-star expansion gate."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

from check_allocated_span_pascal_demand import file_sha256, height_mask_hex
from replay_singleton_large_owner_profile import frozen_record as height_profiles


Ideal = tuple[int, ...]
OwnerMap = tuple[int, ...]


def mask_heights(encoded: str, rows: int, columns: int) -> Ideal:
    mask = int(encoded, 16)
    heights = tuple(
        sum(bool(mask & (1 << (row * columns + column))) for column in range(columns))
        for row in range(rows)
    )
    if any(heights[index] < heights[index + 1] for index in range(len(heights) - 1)):
        raise AssertionError("serialized mask is not a lower ideal")
    return heights


def enumerate_owner_maps(
    hole: int,
    candidates: tuple[tuple[Ideal, ...], ...],
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


def witness_record(
    hole_family: tuple[Ideal, ...],
    owners: OwnerMap,
    star: set[Ideal],
    columns: int,
) -> dict[str, object]:
    return {
        "owner_map": [
            {"ideal_hex": height_mask_hex(ideal, columns), "owner_index": owner}
            for ideal, owner in zip(hole_family, owners, strict=True)
        ],
        "owner_star_union_hex": [
            height_mask_hex(ideal, columns) for ideal in sorted(star)
        ],
    }


def analyze_hole(
    hole: int,
    candidates: tuple[tuple[Ideal, ...], ...],
    columns: int,
) -> dict[str, object]:
    maps = enumerate_owner_maps(hole, candidates)
    histogram: Counter[int] = Counter()
    minimum = None
    first_minimum = None
    first_failure = None
    for hole_family, owners in maps:
        star = set(hole_family)
        for owner in owners:
            star.update(candidates[owner])
        slack = len(star) - len(candidates)
        histogram[slack] += 1
        record = witness_record(hole_family, owners, star, columns)
        if minimum is None or slack < minimum:
            minimum = slack
            first_minimum = {"slack": slack, **record}
        if slack < 0 and first_failure is None:
            first_failure = {"slack": slack, **record}
    return {
        "hole_index": hole,
        "candidate_family_hex": [
            height_mask_hex(ideal, columns) for ideal in sorted(candidates[hole])
        ],
        "feasible_owner_map_count": len(maps),
        "owner_star_slack_histogram": {
            str(slack): count for slack, count in sorted(histogram.items())
        },
        "minimum_owner_star_slack": minimum,
        "all_feasible_owner_maps_expand": first_failure is None,
        "first_minimum_witness": first_minimum,
        "first_failure": first_failure,
    }


def analyze_block(
    group: dict[str, object],
    start: int,
    stop: int,
    strong_size: int,
) -> dict[str, object]:
    rank = int(group["rank"])
    rows = rank - 1
    columns = strong_size - rank - 1
    encoded_families = group["candidate_families_hex"][start:stop]
    candidates = tuple(
        tuple(mask_heights(encoded, rows, columns) for encoded in family)
        for family in encoded_families
    )
    holes = [
        analyze_hole(hole, candidates, columns)
        for hole in range(len(candidates))
    ]
    nonvacuous = [
        hole for hole in holes if hole["feasible_owner_map_count"] > 0
    ]
    first_failure = next(
        (hole for hole in holes if not hole["all_feasible_owner_maps_expand"]),
        None,
    )
    return {
        "start_index": start,
        "stop_index": stop,
        "block_size": stop - start,
        "frontier": group["frontier"][start:stop],
        "candidate_families_hex": encoded_families,
        "family_sizes": group["family_sizes"][start:stop],
        "hole_count": len(holes),
        "nonvacuous_hole_count": len(nonvacuous),
        "feasible_owner_map_count": sum(
            hole["feasible_owner_map_count"] for hole in holes
        ),
        "minimum_owner_star_slack": (
            min(hole["minimum_owner_star_slack"] for hole in nonvacuous)
            if nonvacuous else None
        ),
        "all_feasible_owner_maps_expand": first_failure is None,
        "first_failure": first_failure,
        "holes": holes,
    }


def analyze_group(group: dict[str, object], strong_size: int) -> dict[str, object]:
    size = int(group["block_size"])
    blocks = [
        analyze_block(group, start, stop, strong_size)
        for start in range(size)
        for stop in range(start + 1, size + 1)
    ]
    nonvacuous = [
        block for block in blocks if block["feasible_owner_map_count"] > 0
    ]
    first_failure = next(
        (block for block in blocks if not block["all_feasible_owner_maps_expand"]),
        None,
    )
    return {
        "color": group["color"],
        "rank": group["rank"],
        "full_frontier": group["frontier"],
        "full_block_size": size,
        "consecutive_block_count": len(blocks),
        "feasible_owner_map_count": sum(
            block["feasible_owner_map_count"] for block in blocks
        ),
        "minimum_owner_star_slack": (
            min(block["minimum_owner_star_slack"] for block in nonvacuous)
            if nonvacuous else None
        ),
        "all_feasible_owner_maps_expand": first_failure is None,
        "first_failing_block": first_failure,
        "blocks": blocks,
    }


def frozen_record() -> dict[str, object]:
    profiles = height_profiles()
    groups = [
        analyze_group(group, profiles["strong_size"])
        for group in profiles["groups"]
    ]
    nonvacuous = [
        group for group in groups if group["feasible_owner_map_count"] > 0
    ]
    return {
        "maximum_n": profiles["maximum_n"],
        "strong_size": profiles["strong_size"],
        "support_mask_hex": profiles["support_mask_hex"],
        "lower_mask_hex": profiles["lower_mask_hex"],
        "coloring_hex": profiles["coloring_hex"],
        "group_count": len(groups),
        "consecutive_block_count": sum(
            group["consecutive_block_count"] for group in groups
        ),
        "feasible_owner_map_count": sum(
            group["feasible_owner_map_count"] for group in groups
        ),
        "minimum_owner_star_slack": (
            min(group["minimum_owner_star_slack"] for group in nonvacuous)
            if nonvacuous else None
        ),
        "all_feasible_owner_maps_expand": all(
            group["all_feasible_owner_maps_expand"] for group in groups
        ),
        "groups": groups,
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
        raise AssertionError("independent owner-star replay differs")
    print(
        "blocks=", replay["consecutive_block_count"],
        "owner_maps=", replay["feasible_owner_map_count"],
        "minimum_slack=", replay["minimum_owner_star_slack"],
        "all_feasible_owner_maps_expand=", replay["all_feasible_owner_maps_expand"],
    )


if __name__ == "__main__":
    main()
