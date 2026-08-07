#!/usr/bin/env python3
"""Independently replay the all-root block-large reached-owner gate."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path

from check_allocated_span_pascal_demand import (
    Replay,
    endpoint_rank_heights,
    file_sha256,
    groups,
    height_ideals,
    height_interval,
    height_mask_hex,
    proper_parts,
    replay_transition_candidates,
)


Ideal = tuple[int, ...]
OwnerMap = tuple[int, ...]


def ideal_key(ideal: Ideal, columns: int) -> int:
    return int(height_mask_hex(ideal, columns), 16)


def reflected(ideal: Ideal, columns: int) -> Ideal:
    return tuple(columns - height for height in reversed(ideal))


def oriented_candidates(
    candidates: tuple[tuple[Ideal, ...], ...],
    frontier: tuple[tuple[int, int], ...],
    lower: int,
    columns: int,
) -> tuple[tuple[Ideal, ...], ...]:
    answer = []
    for family, (left, _) in zip(candidates, frontier, strict=True):
        if lower & (1 << left):
            answer.append(tuple(sorted(family, key=lambda ideal: ideal_key(ideal, columns))))
        else:
            answer.append(
                tuple(
                    sorted(
                        (reflected(ideal, columns) for ideal in family),
                        key=lambda ideal: ideal_key(ideal, columns),
                    )
                )
            )
    return tuple(answer)


def first_matching(
    hole_family: tuple[Ideal, ...],
    candidates: tuple[tuple[Ideal, ...], ...],
    hole: int,
    maximum_family_size: int,
) -> OwnerMap | None:
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

    def search(position: int, owners: OwnerMap) -> OwnerMap | None:
        if position == len(hole_family):
            return owners
        for owner in domains[position]:
            if owner in owners:
                continue
            answer = search(position + 1, owners + (owner,))
            if answer is not None:
                return answer
        return None

    return search(0, ())


def bottleneck_owner_map(
    hole: int, candidates: tuple[tuple[Ideal, ...], ...], columns: int
) -> tuple[int, tuple[Ideal, ...], OwnerMap] | None:
    hole_family = tuple(
        sorted(candidates[hole], key=lambda ideal: ideal_key(ideal, columns))
    )
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
    hole: int,
    candidates: tuple[tuple[Ideal, ...], ...],
    columns: int,
) -> tuple[tuple[Ideal, ...], tuple[int, ...]] | None:
    hole_family = tuple(
        sorted(candidates[hole], key=lambda ideal: ideal_key(ideal, columns))
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


def ideal_record(ideal: Ideal, columns: int) -> dict[str, object]:
    return {
        "ideal_hex": height_mask_hex(ideal, columns),
        "boundary_slot": [
            row + columns - height for row, height in enumerate(ideal)
        ],
    }


def span_geometry(
    local: dict[tuple[int, int, int], int],
    vertices: tuple[int, ...],
    span: tuple[int, int],
    color: int,
    rank: int,
    strong_size: int,
    lower: int,
    left_interval: tuple[Ideal, ...],
    right_interval: tuple[Ideal, ...],
) -> dict[str, object]:
    columns = strong_size - rank - 1

    def endpoint_record(endpoint: int, interval: tuple[Ideal, ...]) -> dict[str, object]:
        past = endpoint_rank_heights(
            local, vertices, endpoint, color, rank, strong_size, True
        )
        future = endpoint_rank_heights(
            local, vertices, endpoint, color, rank, strong_size, False
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


def reflected_mask(mask: int, rows: int, columns: int) -> int:
    answer = 0
    for target in range(rows * columns):
        row, column = divmod(target, columns)
        source = (rows - 1 - row) * columns + (columns - 1 - column)
        if not mask & (1 << source):
            answer |= 1 << target
    return answer


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
                ideal = reflected_mask(ideal, rows, columns)
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
                reflected_mask(ideal, rows, columns) for ideal in ideals
            )
        answer.append(frozenset(ideals))
    return tuple(answer)


def selected_anchor_shape(
    anchors: tuple[Ideal, ...],
    geometry: dict[str, object],
    rows: int,
    columns: int,
) -> dict[str, bool]:
    anchor_masks = tuple(ideal_key(ideal, columns) for ideal in anchors)
    ordered = tuple(
        sorted(anchor_masks, key=lambda ideal: (ideal.bit_count(), ideal))
    )
    chain = all(
        first & second in (first, second)
        for first, second in itertools.combinations(ordered, 2)
    )
    saturated = chain and all(
        first & second == first
        and second.bit_count() - first.bit_count() == 1
        for first, second in zip(ordered, ordered[1:])
    )
    lower = tuple(min(values) for values in zip(*anchors, strict=True))
    upper = tuple(max(values) for values in zip(*anchors, strict=True))
    interval_masks = {
        ideal_key(ideal, columns)
        for ideal in height_interval(height_ideals(rows, columns), lower, upper)
    }
    lattice_interval = interval_masks == set(anchor_masks)
    lanes = normalized_endpoint_lanes(geometry, rows, columns)
    one_lane = any(set(anchor_masks) <= lane for lane in lanes)
    return {
        "chain": chain,
        "saturated_chain": saturated,
        "lattice_interval": lattice_interval,
        "contained_in_one_lane": one_lane,
        "one_lane_saturated_interval": one_lane and saturated and lattice_interval,
    }


def base_example(
    support: int,
    lower: int,
    bits: int,
    frontier: tuple[tuple[int, int], ...],
) -> dict[str, object]:
    return {
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "frontier": [list(pair) for pair in frontier],
    }


def failure_record(
    support: int,
    lower: int,
    bits: int,
    color: int,
    rank: int,
    frontier: tuple[tuple[int, int], ...],
    candidates: tuple[tuple[Ideal, ...], ...],
    geometry: tuple[dict[str, object], ...],
    start: int,
    stop: int,
    hole: int,
    bottleneck: int,
    hole_family: tuple[Ideal, ...],
    owners: OwnerMap,
    columns: int,
) -> dict[str, object]:
    block_frontier = frontier[start:stop]
    block_candidates = candidates[start:stop]
    return {
        **base_example(support, lower, bits, frontier),
        "color": "cup" if color else "cap",
        "rank": rank,
        "start_index": start,
        "stop_index": stop,
        "block_size": stop - start,
        "block_frontier": [list(span) for span in block_frontier],
        "block_candidate_families_hex": [
            [height_mask_hex(ideal, columns) for ideal in family]
            for family in block_candidates
        ],
        "block_family_sizes": [len(family) for family in block_candidates],
        "hole_index": hole,
        "hole_frontier_index": start + hole,
        "hole_family_hex": [
            height_mask_hex(ideal, columns) for ideal in hole_family
        ],
        "minimum_max_owner_family_size": bottleneck,
        "minimum_max_owner_family_slack": bottleneck - (stop - start),
        "owner_map": [
            {
                "ideal_hex": height_mask_hex(ideal, columns),
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
    candidates: tuple[tuple[Ideal, ...], ...],
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
                result = bottleneck_owner_map(hole, block, columns)
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
                    anchor_record = first_deficient_anchor(hole, block, columns)
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
                    anchor_masks = {
                        ideal_key(ideal, columns) for ideal in anchors
                    }
                    shape = (
                        "endpoint_only"
                        if anchor_masks <= endpoints
                        else "uses_nonendpoint"
                    )
                    anchor_stats[f"shape,{shape}"] += 1
                    small_owners = tuple(
                        owner
                        for owner, family in enumerate(block)
                        if owner != hole and len(family) < block_size
                    )
                    has_endpoint_singleton = any(
                        ideal_key(ideal, columns) in endpoints
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
                        for role, mask in normalized_endpoint_roles(
                            geometry[start + hole], rows, columns
                        )
                        if any(
                            ideal_key(ideal, columns) == mask
                            for ideal in hole_family
                        )
                        and all(
                            all(ideal_key(ideal, columns) != mask for ideal in block[owner])
                            for owner in small_owners
                        )
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
                        else [
                            [ideal_key(ideal, columns) for ideal in anchor_record[0]],
                            list(anchor_record[1]),
                        ],
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
                            columns,
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
    machine = Replay(maximum_n, strong_size)
    full = (1 << maximum_n) - 1
    machine.colorings(full)
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
        for support in range(1, full + 1):
            if support.bit_count() != size:
                continue
            for lower in proper_parts(support):
                upper = support ^ lower
                fixed = machine.crossing(support, lower)
                for lower_bits in machine.colorings(lower):
                    for upper_bits in machine.colorings(upper):
                        bits = lower_bits | upper_bits | fixed
                        row["root_contexts"] += 1
                        local = machine.ranks(bits, support)
                        if local is None:
                            row["terminal_contexts"] += 1
                            continue
                        row["open_contexts"] += 1
                        vertices = tuple(
                            vertex
                            for vertex in range(maximum_n)
                            if support & (1 << vertex)
                        )
                        for color, rank, frontier in groups(
                            local, support, lower, maximum_n
                        ):
                            original, left_only, right_only, _ = (
                                replay_transition_candidates(
                                    local,
                                    vertices,
                                    frontier,
                                    color,
                                    rank,
                                    strong_size,
                                )
                            )
                            columns = strong_size - rank - 1
                            candidates = oriented_candidates(
                                original, frontier, lower, columns
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
                                columns,
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
                                [
                                    [height_mask_hex(ideal, columns) for ideal in family]
                                    for family in candidates
                                ],
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
            "analyzed_local_states": len(machine.analysis_cache),
        },
        "first_profile_failure": first_failure,
        "checked_prefix_sha256": digest.hexdigest(),
    }


def replay(manifest: dict[str, object]) -> dict[str, object]:
    expected = manifest["k6_census"]
    return census(
        int(expected["maximum_n"]),
        int(expected["minimum_support_size"]),
        int(expected["maximum_support_size"]),
        bool(expected["stop_on_failure"]),
    )


def first_differences(
    expected: object, actual: object, path: str = "k6_census"
) -> list[str]:
    if type(expected) is not type(actual):
        return [f"{path}: expected {type(expected).__name__}, got {type(actual).__name__}"]
    if isinstance(expected, dict):
        differences = []
        for key in sorted(set(expected) | set(actual)):
            if key not in expected:
                differences.append(f"{path}.{key}: unexpected key")
            elif key not in actual:
                differences.append(f"{path}.{key}: missing key")
            else:
                differences.extend(
                    first_differences(expected[key], actual[key], f"{path}.{key}")
                )
            if len(differences) >= 20:
                break
        return differences[:20]
    if isinstance(expected, list):
        if len(expected) != len(actual):
            return [f"{path}: expected length {len(expected)}, got {len(actual)}"]
        differences = []
        for index, (left, right) in enumerate(zip(expected, actual, strict=True)):
            differences.extend(first_differences(left, right, f"{path}[{index}]"))
            if len(differences) >= 20:
                break
        return differences[:20]
    if expected != actual:
        return [f"{path}: expected {expected!r}, got {actual!r}"]
    return []


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
    if actual != manifest["k6_census"]:
        details = "\n".join(first_differences(manifest["k6_census"], actual))
        raise SystemExit(f"independent replay disagrees with manifest\n{details}")
    print(f"verified {args.manifest} ({file_sha256(args.manifest)})")


if __name__ == "__main__":
    main()
