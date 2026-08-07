#!/usr/bin/env python3
"""Produce the frozen feasible-owner-star expansion gate.

For every consecutive block and hole, enumerate every injective map from the
hole's candidates to distinct non-hole spans that contain the mapped ideal.
This is stronger than enumerating actual state-induced owners: every actual
owner map is feasible, but a feasible map need not extend to a one-hole state.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path

from check_singleton_large_owner_profile import frozen_record as mask_profiles
from check_stable_ownership_hole_descent import ideal_boundary
from enumerate_allocated_span_pascal_demand import file_sha256, git_revision, write_atomic


OwnerMap = tuple[int, ...]


def priority(mask: int, rows: int, columns: int) -> tuple[object, ...]:
    return ideal_boundary(mask, rows, columns) + (mask,)


def enumerate_owner_maps(
    hole: int,
    candidates: tuple[tuple[int, ...], ...],
    rows: int,
    columns: int,
) -> tuple[tuple[tuple[int, ...], OwnerMap], ...]:
    hole_family = tuple(sorted(
        candidates[hole], key=lambda ideal: priority(ideal, rows, columns)
    ))
    domains = tuple(
        tuple(
            owner
            for owner, family in enumerate(candidates)
            if owner != hole and ideal in family
        )
        for ideal in hole_family
    )
    answer: list[tuple[tuple[int, ...], OwnerMap]] = []

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
    hole_family: tuple[int, ...],
    owners: OwnerMap,
    star: set[int],
    rows: int,
    columns: int,
) -> dict[str, object]:
    return {
        "owner_map": [
            {"ideal_hex": f"{ideal:x}", "owner_index": owner}
            for ideal, owner in zip(hole_family, owners, strict=True)
        ],
        "owner_star_union_hex": [
            f"{ideal:x}"
            for ideal in sorted(star, key=lambda value: priority(value, rows, columns))
        ],
    }


def analyze_hole(
    hole: int,
    candidates: tuple[tuple[int, ...], ...],
    rows: int,
    columns: int,
) -> dict[str, object]:
    maps = enumerate_owner_maps(hole, candidates, rows, columns)
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
        record = witness_record(hole_family, owners, star, rows, columns)
        if minimum is None or slack < minimum:
            minimum = slack
            first_minimum = {"slack": slack, **record}
        if slack < 0 and first_failure is None:
            first_failure = {"slack": slack, **record}
    return {
        "hole_index": hole,
        "candidate_family_hex": [
            f"{ideal:x}" for ideal in sorted(
                candidates[hole], key=lambda value: priority(value, rows, columns)
            )
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
        tuple(int(encoded, 16) for encoded in family)
        for family in encoded_families
    )
    holes = [
        analyze_hole(hole, candidates, rows, columns)
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
    profiles = mask_profiles()
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


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_owner_star_expansion.py"
    return {
        "schema_version": 1,
        "experiment": "frozen-feasible-owner-star-expansion-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "domain": (
                "every nonempty consecutive frozen block, every hole, and every "
                "injective membership-feasible map from its candidate ideals to "
                "distinct non-hole spans; the empty map is included"
            ),
            "success": (
                "the hole family union all mapped-owner families has cardinality "
                "at least the block cardinality"
            ),
            "interpretation": (
                "a stronger owner-map falsification gate containing every blocked "
                "state-induced actual-owner map"
            ),
            "claim_boundary": (
                "bounded frozen-n12-k7 evidence; no arbitrary reflected owner-star "
                "expansion, Hall theorem, or exact-formula conclusion"
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
            "mask_profile": {
                "path": "scripts/check_singleton_large_owner_profile.py",
                "sha256": file_sha256(repo / "scripts/check_singleton_large_owner_profile.py"),
            },
            "height_profile": {
                "path": "scripts/replay_singleton_large_owner_profile.py",
                "sha256": file_sha256(repo / "scripts/replay_singleton_large_owner_profile.py"),
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
