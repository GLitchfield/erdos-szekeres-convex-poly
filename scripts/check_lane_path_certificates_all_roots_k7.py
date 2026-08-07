#!/usr/bin/env python3
"""Independently replay the exact all-hole reflected lane-path k=7 gate."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import check_block_large_reached_owner_all_roots as base
from check_allocated_span_pascal_demand import file_sha256


Ideal = tuple[int, ...]


def first_gap_owner_matching(
    anchors: tuple[Ideal, ...],
    neighbors: tuple[int, ...],
    block: tuple[tuple[Ideal, ...], ...],
) -> tuple[int, ...] | None:
    domains = tuple(
        tuple(
            owner
            for owner in neighbors
            if anchors[index] in block[owner] and anchors[index + 1] in block[owner]
        )
        for index in range(len(anchors) - 1)
    )

    def search(index: int, answer: tuple[int, ...]):
        if index == len(domains):
            return answer
        for owner in domains[index]:
            if owner in answer:
                continue
            result = search(index + 1, answer + (owner,))
            if result is not None:
                return result
        return None

    return search(0, ())


def ideal_le(first: Ideal, second: Ideal) -> bool:
    return all(left <= right for left, right in zip(first, second, strict=True))


def first_lane_path_certificate(
    hole: int,
    block: tuple[tuple[Ideal, ...], ...],
    geometry: dict[str, object],
    rows: int,
    columns: int,
    require_exact_trace: bool = False,
) -> dict[str, object] | None:
    all_ideals = base.height_ideals(rows, columns)
    hole_family = frozenset(block[hole])
    block_size = len(block)
    small_owners = tuple(
        owner
        for owner, family in enumerate(block)
        if owner != hole and len(family) < block_size
    )
    lanes = base.normalized_endpoint_lanes(geometry, rows, columns)
    for side, lane in enumerate(lanes):
        eligible = tuple(
            sorted(
                (
                    ideal
                    for ideal in hole_family
                    if base.ideal_key(ideal, columns) in lane
                ),
                key=lambda ideal: (sum(ideal), ideal),
            )
        )
        for lower in eligible:
            for upper in eligible:
                if not ideal_le(lower, upper):
                    continue
                anchors = tuple(
                    sorted(
                        base.height_interval(all_ideals, lower, upper),
                        key=lambda ideal: (sum(ideal), ideal),
                    )
                )
                anchor_set = frozenset(anchors)
                if not anchor_set <= hole_family:
                    continue
                if not all(
                    base.ideal_key(ideal, columns) in lane for ideal in anchors
                ):
                    continue
                if not all(
                    ideal_le(first, second) or ideal_le(second, first)
                    for index, first in enumerate(anchors)
                    for second in anchors[index + 1 :]
                ):
                    continue
                if not all(
                    ideal_le(first, second) and sum(second) == sum(first) + 1
                    for first, second in zip(anchors, anchors[1:])
                ):
                    continue
                neighbors = tuple(
                    owner
                    for owner in small_owners
                    if any(anchor in block[owner] for anchor in anchors)
                )
                if len(neighbors) != len(anchors) - 1:
                    continue
                owners = first_gap_owner_matching(anchors, neighbors, block)
                if owners is None:
                    continue
                singleton_neighbors = tuple(
                    tuple(owner for owner in small_owners if anchor in block[owner])
                    for anchor in anchors
                )
                trace_exact = all(
                    set(actual)
                    == set(owners[max(0, index - 1) : min(len(owners), index + 1)])
                    for index, actual in enumerate(singleton_neighbors)
                )
                if require_exact_trace and not trace_exact:
                    continue
                return {
                    "side": "left" if side == 0 else "right",
                    "anchors_hex": [
                        base.height_mask_hex(anchor, columns) for anchor in anchors
                    ],
                    "owners": list(owners),
                    "singleton_neighbors": [
                        list(value) for value in singleton_neighbors
                    ],
                    "singleton_trace_exact": trace_exact,
                }
    return None


ORIGINAL_ANALYZE_GROUP = base.analyze_group


def analyze_group(
    support: int,
    lower: int,
    bits: int,
    color: int,
    rank: int,
    frontier: tuple[tuple[int, int], ...],
    candidates: tuple[tuple[Ideal, ...], ...],
    geometry: tuple[dict[str, object], ...],
    rows: int,
    columns: int,
):
    counts, slacks, anchor_stats, blocks, base_failure = ORIGINAL_ANALYZE_GROUP(
        support,
        lower,
        bits,
        color,
        rank,
        frontier,
        candidates,
        geometry,
        rows,
        columns,
    )
    path_digest = []
    first_failure = base_failure
    for start in range(len(frontier)):
        for stop in range(start + 1, len(frontier) + 1):
            block = candidates[start:stop]
            hole_records = []
            for hole in range(len(block)):
                counts["lane_path_hole_checks"] += 1
                feasible = (
                    base.bottleneck_owner_map(hole, block, columns) is not None
                )
                counts[
                    "lane_path_feasible_owner_map_holes"
                    if feasible
                    else "lane_path_zero_feasible_owner_map_holes"
                ] += 1
                certificate = first_lane_path_certificate(
                    hole, block, geometry[start + hole], rows, columns
                )
                if certificate is None:
                    hole_records.append([hole, None, None])
                    counts["lane_path_certificate_failures"] += 1
                    if first_failure is None:
                        deficient = base.first_deficient_anchor(hole, block, columns)
                        first_failure = {
                            **base.base_example(support, lower, bits, frontier),
                            "reason": "no_reflected_lane_path_certificate",
                            "color": "cup" if color else "cap",
                            "rank": rank,
                            "start_index": start,
                            "stop_index": stop,
                            "block_size": len(block),
                            "block_frontier": [
                                list(span) for span in frontier[start:stop]
                            ],
                            "block_candidate_families_hex": [
                                [
                                    base.height_mask_hex(ideal, columns)
                                    for ideal in family
                                ]
                                for family in block
                            ],
                            "hole_index": hole,
                            "hole_frontier_index": start + hole,
                            "owner_map_feasible": feasible,
                            "first_deficient_anchor": None
                            if deficient is None
                            else [
                                [
                                    base.height_mask_hex(ideal, columns)
                                    for ideal in deficient[0]
                                ],
                                list(deficient[1]),
                            ],
                            "hole_geometry": geometry[start + hole],
                        }
                else:
                    exact_trace_certificate = (
                        certificate
                        if certificate["singleton_trace_exact"]
                        else first_lane_path_certificate(
                            hole,
                            block,
                            geometry[start + hole],
                            rows,
                            columns,
                            require_exact_trace=True,
                        )
                    )
                    hole_records.append(
                        [hole, certificate, exact_trace_certificate]
                    )
                    counts["lane_path_certificates"] += 1
                    length = len(certificate["anchors_hex"]) - 1
                    counts[f"lane_path_length_{length}"] += 1
                    counts[
                        "lane_path_singleton_trace_exact"
                        if certificate["singleton_trace_exact"]
                        else "lane_path_singleton_trace_inexact"
                    ] += 1
                    counts[
                        "lane_path_exact_trace_certificate_exists"
                        if exact_trace_certificate is not None
                        else "lane_path_exact_trace_certificate_absent"
                    ] += 1
            path_digest.append([start, stop, hole_records])
    return counts, slacks, anchor_stats, [blocks, path_digest], first_failure


def census(maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    previous = base.analyze_group
    base.analyze_group = analyze_group
    try:
        result = base.census(maximum_n, 2, maximum_n, stop_on_failure, 7)
    finally:
        base.analyze_group = previous
    result["all_holes_have_lane_path_certificate"] = result.pop(
        "all_feasible_maps_reach_block_large_owner"
    )
    result["first_lane_path_failure"] = result.pop("first_profile_failure")
    return result


def replay(manifest: dict[str, object]) -> dict[str, object]:
    expected = manifest["k7_all_hole_census"]
    return census(int(expected["maximum_n"]), bool(expected["stop_on_failure"]))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    repo = Path(__file__).resolve().parent.parent
    for source in manifest["sources"].values():
        path = repo / source["path"]
        if file_sha256(path) != source["sha256"]:
            raise SystemExit(f"source hash disagrees for {source['path']}")
    if args.source_only:
        print(f"verified sources for {args.manifest} ({file_sha256(args.manifest)})")
        return
    actual = replay(manifest)
    expected = manifest["k7_all_hole_census"]
    if actual != expected:
        details = "\n".join(
            base.first_differences(expected, actual, "k7_all_hole_census")
        )
        raise SystemExit(
            f"independent all-hole lane-path replay disagrees\n{details}"
        )
    print(f"verified {args.manifest} ({file_sha256(args.manifest)})")


if __name__ == "__main__":
    main()
