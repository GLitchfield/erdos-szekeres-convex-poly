#!/usr/bin/env python3
"""Gate the block-large reached-owner profile on every bounded root.

For each consecutive reflected exact-rank frontier block and each hole, this
producer computes the least possible maximum owner-family size over all
injective membership-feasible owner maps.  It does so with a sequence of small
bipartite matching tests instead of enumerating all owner maps.

This is bounded computational evidence, not a proof of the general profile.
The independent checker uses row-height ideals and a separate coloring replay.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path

from enumerate_allocated_span_pascal_demand import (
    DecomposableColorings,
    LocalSpanAnalysis,
    context_groups,
    endpoint_rank_ideal,
    endpoint_transition_candidates,
    example,
    file_sha256,
    git_revision,
    ideal_interval,
    nonempty_proper_submasks,
    rectangular_lower_ideals,
    write_atomic,
)
from enumerate_reflected_transition_hall import oriented_candidates, reflected_ideal


OwnerMap = tuple[int, ...]


def first_matching(
    hole_family: tuple[int, ...],
    candidates: tuple[tuple[int, ...], ...],
    hole: int,
    maximum_family_size: int,
) -> OwnerMap | None:
    """Return the first injective owner map using only bounded-size owners."""
    domains = tuple(
        tuple(
            owner
            for owner, family in enumerate(candidates)
            if owner != hole
            and len(family) <= maximum_family_size
            and ideal in family
        )
        for ideal in hole_family
    )

    def visit(
        position: int, used: frozenset[int], owners: OwnerMap
    ) -> OwnerMap | None:
        if position == len(hole_family):
            return owners
        for owner in domains[position]:
            if owner in used:
                continue
            answer = visit(position + 1, used | {owner}, owners + (owner,))
            if answer is not None:
                return answer
        return None

    return visit(0, frozenset(), ())


def bottleneck_owner_map(
    hole: int, candidates: tuple[tuple[int, ...], ...]
) -> tuple[int, tuple[int, ...], OwnerMap] | None:
    """Minimize the maximum family size reached by a feasible owner map."""
    hole_family = tuple(sorted(candidates[hole]))
    if not hole_family:
        return 0, hole_family, ()
    thresholds = sorted(
        {len(family) for owner, family in enumerate(candidates) if owner != hole}
    )
    for threshold in thresholds:
        owners = first_matching(hole_family, candidates, hole, threshold)
        if owners is not None:
            return threshold, hole_family, owners
    return None


def first_deficient_anchor(
    hole: int, candidates: tuple[tuple[int, ...], ...]
) -> tuple[tuple[int, ...], tuple[int, ...]] | None:
    """Find the first hole subset with too few block-small neighbors."""
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


def boundary_slot(mask: int, rows: int, columns: int) -> list[int]:
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


def normalized_endpoint_extremes(
    geometry: dict[str, object], rows: int, columns: int
) -> frozenset[int]:
    return frozenset(
        ideal
        for _, ideal in normalized_endpoint_roles(geometry, rows, columns)
    )


def normalized_endpoint_roles(
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


def normalized_endpoint_lanes(
    geometry: dict[str, object], rows: int, columns: int
) -> tuple[frozenset[int], frozenset[int]]:
    answer = []
    for lane in ("left_lane", "right_lane"):
        ideals = tuple(
            int(encoded, 16) for encoded in geometry[lane]["raw_interval_hex"]
        )
        if geometry["reflected"]:
            ideals = tuple(
                reflected_ideal(ideal, rows, columns) for ideal in ideals
            )
        answer.append(frozenset(ideals))
    return tuple(answer)


def selected_anchor_shape(
    anchors: tuple[int, ...],
    geometry: dict[str, object],
    rows: int,
    columns: int,
) -> dict[str, bool]:
    ordered = tuple(sorted(anchors, key=lambda ideal: (ideal.bit_count(), ideal)))
    chain = all(
        first & second in (first, second)
        for first, second in itertools.combinations(ordered, 2)
    )
    saturated = chain and all(
        first & second == first
        and second.bit_count() - first.bit_count() == 1
        for first, second in zip(ordered, ordered[1:])
    )
    lower = anchors[0]
    upper = anchors[0]
    for ideal in anchors[1:]:
        lower &= ideal
        upper |= ideal
    ideals = rectangular_lower_ideals(rows, columns)
    lattice_interval = set(ideal_interval(ideals, lower, upper)) == set(anchors)
    lanes = normalized_endpoint_lanes(geometry, rows, columns)
    one_lane = any(set(anchors) <= lane for lane in lanes)
    return {
        "chain": chain,
        "saturated_chain": saturated,
        "lattice_interval": lattice_interval,
        "contained_in_one_lane": one_lane,
        "one_lane_saturated_interval": one_lane and saturated and lattice_interval,
    }


def failure_record(
    support: int,
    lower: int,
    bits: int,
    color: int,
    rank: int,
    frontier: tuple[tuple[int, int], ...],
    candidates: tuple[tuple[int, ...], ...],
    geometry: tuple[dict[str, object], ...],
    start: int,
    stop: int,
    hole: int,
    bottleneck: int,
    hole_family: tuple[int, ...],
    owners: OwnerMap,
) -> dict[str, object]:
    block_frontier = frontier[start:stop]
    block_candidates = candidates[start:stop]
    return {
        **example(support, lower, bits, frontier),
        "color": "cup" if color else "cap",
        "rank": rank,
        "start_index": start,
        "stop_index": stop,
        "block_size": stop - start,
        "block_frontier": [list(span) for span in block_frontier],
        "block_candidate_families_hex": [
            [f"{ideal:x}" for ideal in family] for family in block_candidates
        ],
        "block_family_sizes": [len(family) for family in block_candidates],
        "hole_index": hole,
        "hole_frontier_index": start + hole,
        "hole_family_hex": [f"{ideal:x}" for ideal in hole_family],
        "minimum_max_owner_family_size": bottleneck,
        "minimum_max_owner_family_slack": bottleneck - (stop - start),
        "owner_map": [
            {
                "ideal_hex": f"{ideal:x}",
                "owner_index": owner,
                "owner_frontier_index": start + owner,
                "owner_span": list(block_frontier[owner]),
                "owner_family_size": len(block_candidates[owner]),
            }
            for ideal, owner in zip(hole_family, owners, strict=True)
        ],
        "block_span_geometry": list(geometry[start:stop]),
    }


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
) -> tuple[
    Counter[str],
    Counter[int],
    Counter[str],
    list[object],
    dict[str, object] | None,
]:
    counts: Counter[str] = Counter(group_checks=1)
    slacks: Counter[int] = Counter()
    anchor_stats: Counter[str] = Counter()
    digest_blocks: list[object] = []
    first_failure = None
    size = len(frontier)
    for start in range(size):
        for stop in range(start + 1, size + 1):
            counts["consecutive_block_checks"] += 1
            block = candidates[start:stop]
            block_size = stop - start
            digest_holes = []
            for hole in range(block_size):
                counts["hole_checks"] += 1
                if not block[hole]:
                    counts["empty_hole_families"] += 1
                result = bottleneck_owner_map(hole, block)
                if result is None:
                    counts["vacuous_holes"] += 1
                    digest_holes.append([hole, None])
                    continue
                bottleneck, hole_family, owners = result
                counts["nonvacuous_holes"] += 1
                slack = bottleneck - block_size
                slacks[slack] += 1
                anchor_record = None
                if slack >= 0:
                    anchor_record = first_deficient_anchor(hole, block)
                    if anchor_record is None:
                        raise AssertionError("passing hole has no deficient anchor")
                    anchors, neighbors = anchor_record
                    anchor_stats[f"size,{len(anchors)}"] += 1
                    anchor_stats[
                        f"deficiency,{len(anchors) - len(neighbors)}"
                    ] += 1
                    for label, holds in selected_anchor_shape(
                        anchors, geometry[start + hole], rows, columns
                    ).items():
                        anchor_stats[f"selected_{label},{'yes' if holds else 'no'}"] += 1
                    endpoints = normalized_endpoint_extremes(
                        geometry[start + hole], rows, columns
                    )
                    shape = (
                        "endpoint_only"
                        if set(anchors) <= endpoints
                        else "uses_nonendpoint"
                    )
                    anchor_stats[f"shape,{shape}"] += 1
                    small_owners = tuple(
                        owner
                        for owner, family in enumerate(block)
                        if owner != hole and len(family) < block_size
                    )
                    has_endpoint_singleton = any(
                        ideal in endpoints
                        and all(ideal not in block[owner] for owner in small_owners)
                        for ideal in hole_family
                    )
                    anchor_stats[
                        "endpoint_singleton,yes"
                        if has_endpoint_singleton
                        else "endpoint_singleton,no"
                    ] += 1
                    forced_roles = tuple(
                        role
                        for role, ideal in normalized_endpoint_roles(
                            geometry[start + hole], rows, columns
                        )
                        if ideal in hole_family
                        and all(ideal not in block[owner] for owner in small_owners)
                    )
                    if forced_roles:
                        anchor_stats["forced_endpoint,yes"] += 1
                        anchor_stats[f"first_forced_role,{forced_roles[0]}"] += 1
                        anchor_stats[
                            f"forced_role_pattern,{'|'.join(forced_roles)}"
                        ] += 1
                    else:
                        anchor_stats["forced_endpoint,no"] += 1
                    anchor_stats[
                        "whole_hole,yes"
                        if len(anchors) == len(hole_family)
                        else "whole_hole,no"
                    ] += 1
                digest_holes.append(
                    [
                        hole,
                        bottleneck,
                        list(owners),
                        None
                        if anchor_record is None
                        else [list(anchor_record[0]), list(anchor_record[1])],
                    ]
                )
                if slack < 0:
                    counts["profile_failures"] += 1
                    if first_failure is None:
                        first_failure = failure_record(
                            support,
                            lower,
                            bits,
                            color,
                            rank,
                            frontier,
                            candidates,
                            geometry,
                            start,
                            stop,
                            hole,
                            bottleneck,
                            hole_family,
                            owners,
                        )
            digest_blocks.append([start, stop, digest_holes])
    return counts, slacks, anchor_stats, digest_blocks, first_failure


def labeled_histogram(stats: Counter[str], label: str) -> dict[str, int]:
    prefix = f"{label},"
    return {
        key.removeprefix(prefix): value
        for key, value in sorted(stats.items())
        if key.startswith(prefix)
    }


def census(
    maximum_n: int,
    minimum_support_size: int,
    maximum_support_size: int,
    stop_on_failure: bool,
    strong_size: int = 6,
) -> dict[str, object]:
    colorings = DecomposableColorings(maximum_n)
    colorings.enumerate()
    analyzer = LocalSpanAnalysis(maximum_n, strong_size)
    totals: Counter[str] = Counter()
    total_slacks: Counter[int] = Counter()
    total_anchor_stats: Counter[str] = Counter()
    by_size: dict[str, Counter[str]] = {}
    by_size_slacks: dict[str, Counter[int]] = {}
    by_size_anchor_stats: dict[str, Counter[str]] = {}
    digest = hashlib.sha256()
    first_failure = None
    stopped = False

    for size in range(minimum_support_size, maximum_support_size + 1):
        row: Counter[str] = Counter()
        row_slacks: Counter[int] = Counter()
        row_anchor_stats: Counter[str] = Counter()
        for support in range(1, 1 << maximum_n):
            if support.bit_count() != size:
                continue
            for lower in nonempty_proper_submasks(support):
                upper = support ^ lower
                fixed = colorings.crossing_bits(support, lower)
                for lower_bits in sorted(colorings.states[lower]):
                    for upper_bits in sorted(colorings.states[upper]):
                        bits = lower_bits | upper_bits | fixed
                        row["root_contexts"] += 1
                        local = analyzer.analyze(bits, support)
                        if local is None:
                            row["terminal_contexts"] += 1
                            continue
                        row["open_contexts"] += 1
                        vertices = tuple(
                            vertex
                            for vertex in range(maximum_n)
                            if support & (1 << vertex)
                        )
                        for color, rank, frontier in context_groups(
                            local, support, lower, maximum_n
                        ):
                            original, left_only, right_only, _ = (
                                endpoint_transition_candidates(
                                    local,
                                    vertices,
                                    frontier,
                                    color,
                                    rank,
                                    strong_size,
                                )
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
                                    frontier,
                                    left_only,
                                    right_only,
                                    strict=True,
                                )
                            )
                            (
                                group_counts,
                                slacks,
                                anchor_stats,
                                blocks,
                                failure,
                            ) = analyze_group(
                                support,
                                lower,
                                bits,
                                color,
                                rank,
                                frontier,
                                candidates,
                                geometry,
                                rank - 1,
                                strong_size - rank - 1,
                            )
                            row.update(group_counts)
                            row["maximum_frontier_size"] = max(
                                row["maximum_frontier_size"], len(frontier)
                            )
                            row_slacks.update(slacks)
                            row_anchor_stats.update(anchor_stats)
                            digest_record = [
                                support,
                                lower,
                                bits,
                                color,
                                rank,
                                [list(span) for span in frontier],
                                [[f"{ideal:x}" for ideal in family] for family in candidates],
                                blocks,
                            ]
                            digest.update(
                                json.dumps(
                                    digest_record, separators=(",", ":")
                                ).encode()
                            )
                            digest.update(b"\n")
                            if failure is not None and first_failure is None:
                                first_failure = failure
                                if stop_on_failure:
                                    stopped = True
                                    break
                        if stopped:
                            break
                    if stopped:
                        break
                if stopped:
                    break
            if stopped:
                break
        by_size[str(size)] = row
        by_size_slacks[str(size)] = row_slacks
        by_size_anchor_stats[str(size)] = row_anchor_stats
        total_maximum_frontier_size = max(
            totals["maximum_frontier_size"], row["maximum_frontier_size"]
        )
        totals.update(row)
        totals["maximum_frontier_size"] = total_maximum_frontier_size
        total_slacks.update(row_slacks)
        total_anchor_stats.update(row_anchor_stats)
        if stopped:
            break

    return {
        "maximum_n": maximum_n,
        "strong_size": strong_size,
        "minimum_support_size": minimum_support_size,
        "maximum_support_size": maximum_support_size,
        "stop_on_failure": stop_on_failure,
        "stopped_early": stopped,
        "complete": not stopped,
        "all_feasible_maps_reach_block_large_owner": first_failure is None,
        "statistics": {
            "totals": dict(sorted(totals.items())),
            "by_support_size": {
                key: dict(sorted(row.items())) for key, row in by_size.items()
            },
            "minimum_bottleneck_slack_histogram": {
                str(slack): count for slack, count in sorted(total_slacks.items())
            },
            "minimum_deficient_anchor_size_histogram": labeled_histogram(
                total_anchor_stats, "size"
            ),
            "small_owner_deficiency_histogram": labeled_histogram(
                total_anchor_stats, "deficiency"
            ),
            "anchor_endpoint_shape_counts": labeled_histogram(
                total_anchor_stats, "shape"
            ),
            "anchor_whole_hole_counts": labeled_histogram(
                total_anchor_stats, "whole_hole"
            ),
            "endpoint_singleton_deficiency_counts": labeled_histogram(
                total_anchor_stats, "endpoint_singleton"
            ),
            "first_forced_endpoint_role_histogram": labeled_histogram(
                total_anchor_stats, "first_forced_role"
            ),
            "forced_endpoint_role_pattern_histogram": labeled_histogram(
                total_anchor_stats, "forced_role_pattern"
            ),
            "forced_endpoint_existence_counts": labeled_histogram(
                total_anchor_stats, "forced_endpoint"
            ),
            "selected_anchor_shape_counts": {
                label: labeled_histogram(total_anchor_stats, f"selected_{label}")
                for label in (
                    "chain",
                    "saturated_chain",
                    "lattice_interval",
                    "contained_in_one_lane",
                    "one_lane_saturated_interval",
                )
            },
            "by_support_size_anchor_statistics": {
                key: {
                    "minimum_deficient_anchor_size_histogram": labeled_histogram(
                        row, "size"
                    ),
                    "small_owner_deficiency_histogram": labeled_histogram(
                        row, "deficiency"
                    ),
                    "anchor_endpoint_shape_counts": labeled_histogram(
                        row, "shape"
                    ),
                    "anchor_whole_hole_counts": labeled_histogram(
                        row, "whole_hole"
                    ),
                    "endpoint_singleton_deficiency_counts": labeled_histogram(
                        row, "endpoint_singleton"
                    ),
                    "first_forced_endpoint_role_histogram": labeled_histogram(
                        row, "first_forced_role"
                    ),
                    "forced_endpoint_role_pattern_histogram": labeled_histogram(
                        row, "forced_role_pattern"
                    ),
                    "forced_endpoint_existence_counts": labeled_histogram(
                        row, "forced_endpoint"
                    ),
                    "selected_anchor_shape_counts": {
                        label: labeled_histogram(row, f"selected_{label}")
                        for label in (
                            "chain",
                            "saturated_chain",
                            "lattice_interval",
                            "contained_in_one_lane",
                            "one_lane_saturated_interval",
                        )
                    },
                }
                for key, row in by_size_anchor_stats.items()
            },
            "by_support_size_slack_histogram": {
                key: {
                    str(slack): count for slack, count in sorted(row.items())
                }
                for key, row in by_size_slacks.items()
            },
            "analyzed_local_states": len(analyzer.cache),
        },
        "first_profile_failure": first_failure,
        "checked_prefix_sha256": digest.hexdigest(),
    }


def produce(
    maximum_n: int,
    minimum_support_size: int,
    maximum_support_size: int,
    stop_on_failure: bool,
) -> dict[str, object]:
    repo = Path(__file__).resolve().parent.parent
    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_block_large_reached_owner_all_roots.py"
    base_producer = repo / "scripts/enumerate_allocated_span_pascal_demand.py"
    base_checker = repo / "scripts/check_allocated_span_pascal_demand.py"
    return {
        "schema_version": 1,
        "experiment": "all-root-block-large-reached-owner-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "domain": (
                "every recursively decomposable root with support size in the "
                "recorded interval, every reflected exact-rank consecutive "
                "frontier block, every hole, and every injective membership-"
                "feasible owner map"
            ),
            "success": (
                "every feasible owner map reaches an owner whose complete "
                "candidate family is at least as large as the block"
            ),
            "matching_reduction": (
                "the minimum possible maximum reached-owner family size is the "
                "least family-size threshold whose eligible owners admit a "
                "matching of the entire hole family"
            ),
            "claim_boundary": (
                "bounded k=6 computational evidence only; no arbitrary genuine-"
                "frontier profile, Hall theorem, or exact-formula conclusion"
            ),
        },
        "k6_census": census(
            maximum_n,
            minimum_support_size,
            maximum_support_size,
            stop_on_failure,
        ),
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
                "path": str(base_producer.relative_to(repo)),
                "sha256": file_sha256(base_producer),
            },
            "height_base": {
                "path": str(base_checker.relative_to(repo)),
                "sha256": file_sha256(base_checker),
            },
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--maximum-n", type=int, default=8)
    parser.add_argument("--minimum-support-size", type=int, default=2)
    parser.add_argument("--maximum-support-size", type=int)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--no-stop-on-failure", action="store_true")
    args = parser.parse_args()
    maximum_support_size = args.maximum_support_size or args.maximum_n
    if not 2 <= args.maximum_n <= 8:
        parser.error("--maximum-n must lie between 2 and 8")
    if not 2 <= args.minimum_support_size <= maximum_support_size <= args.maximum_n:
        parser.error("support sizes must satisfy 2 <= minimum <= maximum <= maximum-n")
    write_atomic(
        args.output,
        produce(
            args.maximum_n,
            args.minimum_support_size,
            maximum_support_size,
            not args.no_stop_on_failure,
        ),
    )
    print(args.output)


if __name__ == "__main__":
    main()
