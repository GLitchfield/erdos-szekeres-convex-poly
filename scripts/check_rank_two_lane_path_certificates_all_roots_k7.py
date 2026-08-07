#!/usr/bin/env python3
"""Independently replay the exact rank-two reflected lane-path k=7 gate."""

from __future__ import annotations

import argparse
import itertools
import json
from collections import defaultdict
from pathlib import Path

import check_allocated_span_pascal_demand as frontier_base
import check_lane_path_certificates_all_roots_k7 as path_base
from check_allocated_span_pascal_demand import file_sha256


def rank_two_groups(
    local: dict[tuple[int, int, int], int],
    support: int,
    lower: int,
    maximum_n: int,
) -> tuple[tuple[int, int, tuple[tuple[int, int], ...]], ...]:
    """Reconstruct only rank-two frontiers with the skyline algorithm."""
    vertices = tuple(
        vertex for vertex in range(maximum_n) if support & (1 << vertex)
    )
    grouped: defaultdict[int, list[tuple[int, int]]] = defaultdict(list)
    for left, right in itertools.combinations(vertices, 2):
        if bool(lower & (1 << left)) == bool(lower & (1 << right)):
            continue
        for color in (0, 1):
            if local[color, left, right] == 2:
                grouped[color].append((left, right))
    return tuple(
        (color, 2, frontier_base.interval_frontier(pairs))
        for color, pairs in sorted(grouped.items())
        if pairs
    )


def census(maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    previous_groups = path_base.base.groups
    previous_analysis = path_base.ORIGINAL_ANALYZE_GROUP

    def analyze_without_profile_failure(*args, **kwargs):
        counts, slacks, anchor_stats, blocks, _ = previous_analysis(
            *args, **kwargs
        )
        return counts, slacks, anchor_stats, blocks, None

    path_base.base.groups = rank_two_groups
    path_base.ORIGINAL_ANALYZE_GROUP = analyze_without_profile_failure
    try:
        return path_base.census(maximum_n, stop_on_failure)
    finally:
        path_base.ORIGINAL_ANALYZE_GROUP = previous_analysis
        path_base.base.groups = previous_groups


def replay(manifest: dict[str, object]) -> dict[str, object]:
    expected = manifest["k7_rank_two_all_hole_census"]
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
    expected = manifest["k7_rank_two_all_hole_census"]
    if actual != expected:
        details = "\n".join(
            path_base.base.first_differences(
                expected, actual, "k7_rank_two_all_hole_census"
            )
        )
        raise SystemExit(f"independent rank-two lane-path replay disagrees\n{details}")
    print(f"verified {args.manifest} ({file_sha256(args.manifest)})")


if __name__ == "__main__":
    main()
