#!/usr/bin/env python3
"""Test the exact all-hole reflected lane-path contract for k=7.

This cell-mask producer audits every hole, including holes for which no
membership-feasible owner map exists. It searches both normalized endpoint
lanes for a complete saturated ideal interval whose adjacent gaps have
distinct block-small owners exhausting the interval's small-owner
neighborhood.
"""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

import enumerate_block_large_reached_owner_all_roots as base
from enumerate_allocated_span_pascal_demand import file_sha256, git_revision, write_atomic


def first_gap_owner_matching(
    anchors: tuple[int, ...],
    neighbors: tuple[int, ...],
    block: tuple[tuple[int, ...], ...],
) -> tuple[int, ...] | None:
    """Match each adjacent anchor gap to a distinct neighboring owner."""
    domains = tuple(
        tuple(
            owner
            for owner in neighbors
            if anchors[index] in block[owner] and anchors[index + 1] in block[owner]
        )
        for index in range(len(anchors) - 1)
    )

    def visit(index: int, used: frozenset[int], answer: tuple[int, ...]):
        if index == len(domains):
            return answer
        for owner in domains[index]:
            if owner in used:
                continue
            result = visit(index + 1, used | {owner}, answer + (owner,))
            if result is not None:
                return result
        return None

    return visit(0, frozenset(), ())


def first_lane_path_certificate(
    hole: int,
    block: tuple[tuple[int, ...], ...],
    geometry: dict[str, object],
    rows: int,
    columns: int,
    require_exact_trace: bool = False,
) -> dict[str, object] | None:
    """Return the first exact lane-path certificate in deterministic order."""
    all_ideals = base.rectangular_lower_ideals(rows, columns)
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
            sorted(hole_family & lane, key=lambda ideal: (ideal.bit_count(), ideal))
        )
        for lower in eligible:
            for upper in eligible:
                if lower & upper != lower:
                    continue
                anchors = tuple(
                    sorted(
                        base.ideal_interval(all_ideals, lower, upper),
                        key=lambda ideal: (ideal.bit_count(), ideal),
                    )
                )
                anchor_set = frozenset(anchors)
                if not anchor_set <= hole_family or not anchor_set <= lane:
                    continue
                if not all(
                    first & second in (first, second)
                    for first, second in itertools.combinations(anchors, 2)
                ):
                    continue
                if not all(
                    first & second == first
                    and second.bit_count() == first.bit_count() + 1
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
                    "anchors_hex": [f"{anchor:x}" for anchor in anchors],
                    "owners": list(owners),
                    "singleton_neighbors": [list(value) for value in singleton_neighbors],
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
    candidates: tuple[tuple[int, ...], ...],
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
                feasible = base.bottleneck_owner_map(hole, block) is not None
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
                        deficient = base.first_deficient_anchor(hole, block)
                        first_failure = {
                            **base.example(support, lower, bits, frontier),
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
                                [f"{ideal:x}" for ideal in family] for family in block
                            ],
                            "hole_index": hole,
                            "hole_frontier_index": start + hole,
                            "owner_map_feasible": feasible,
                            "first_deficient_anchor": None
                            if deficient is None
                            else [
                                [f"{ideal:x}" for ideal in deficient[0]],
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


def produce(repo: Path, maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_lane_path_certificates_all_roots_k7.py"
    mask_base = repo / "scripts/enumerate_block_large_reached_owner_all_roots.py"
    height_base = repo / "scripts/check_block_large_reached_owner_all_roots.py"
    return {
        "schema_version": 1,
        "experiment": "all-root-all-hole-reflected-lane-path-k7-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "domain": (
                "every recursively decomposable k=7 root through the recorded support "
                "size, every reflected exact-rank consecutive block, and every hole"
            ),
            "success": (
                "some complete saturated interval in one normalized hole lane has "
                "distinct adjacent-gap block-small owners exhausting its neighborhood"
            ),
            "claim_boundary": (
                "bounded computational evidence only; no arbitrary path-certificate, "
                "Hall, geometric bridge, or exact-formula theorem"
            ),
        },
        "k7_all_hole_census": census(maximum_n, stop_on_failure),
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
                "path": str(mask_base.relative_to(repo)),
                "sha256": file_sha256(mask_base),
            },
            "height_base": {
                "path": str(height_base.relative_to(repo)),
                "sha256": file_sha256(height_base),
            },
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--maximum-n", type=int, default=8)
    parser.add_argument("--no-stop-on-failure", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 2 <= args.maximum_n <= 8:
        parser.error("maximum-n must lie between 2 and 8")
    repo = Path(__file__).resolve().parent.parent
    write_atomic(
        args.output,
        produce(repo, args.maximum_n, not args.no_stop_on_failure),
    )
    print(args.output)


if __name__ == "__main__":
    main()
