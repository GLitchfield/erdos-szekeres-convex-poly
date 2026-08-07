#!/usr/bin/env python3
"""Test the exact rank-two reflected lane-path contract for k=7.

The preceding all-hole census deliberately started at rank three. This
cell-mask producer selects exactly rank-two crossing frontiers, then reuses
the all-hole path predicate and records every consecutive block and hole.
"""

from __future__ import annotations

import argparse
import itertools
from collections import defaultdict
from pathlib import Path

import enumerate_allocated_span_pascal_demand as frontier_base
import enumerate_lane_path_certificates_all_roots_k7 as path_base
from enumerate_allocated_span_pascal_demand import file_sha256, git_revision, write_atomic


def rank_two_context_groups(
    local: dict[tuple[int, int, int], int],
    support: int,
    lower: int,
    maximum_n: int,
) -> tuple[tuple[int, int, tuple[tuple[int, int], ...]], ...]:
    """Return only inclusion-minimal exact-rank-two crossing spans."""
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
        (color, 2, frontier_base.nondominated_intervals(pairs))
        for color, pairs in sorted(grouped.items())
        if pairs
    )


def census(maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    previous_groups = path_base.base.context_groups
    previous_analysis = path_base.ORIGINAL_ANALYZE_GROUP

    def analyze_without_profile_failure(*args, **kwargs):
        counts, slacks, anchor_stats, blocks, _ = previous_analysis(
            *args, **kwargs
        )
        return counts, slacks, anchor_stats, blocks, None

    path_base.base.context_groups = rank_two_context_groups
    path_base.ORIGINAL_ANALYZE_GROUP = analyze_without_profile_failure
    try:
        return path_base.census(maximum_n, stop_on_failure)
    finally:
        path_base.ORIGINAL_ANALYZE_GROUP = previous_analysis
        path_base.base.context_groups = previous_groups


def produce(repo: Path, maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_rank_two_lane_path_certificates_all_roots_k7.py"
    path_producer = repo / "scripts/enumerate_lane_path_certificates_all_roots_k7.py"
    path_checker = repo / "scripts/check_lane_path_certificates_all_roots_k7.py"
    mask_base = repo / "scripts/enumerate_block_large_reached_owner_all_roots.py"
    height_base = repo / "scripts/check_block_large_reached_owner_all_roots.py"
    return {
        "schema_version": 1,
        "experiment": "all-root-rank-two-reflected-lane-path-k7-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "domain": (
                "every recursively decomposable k=7 root through the recorded "
                "support size, every reflected exact-rank-two consecutive block, "
                "and every hole"
            ),
            "success": (
                "some complete saturated interval in one normalized hole lane has "
                "an exact singleton-neighborhood trace"
            ),
            "claim_boundary": (
                "bounded computational evidence only; no arbitrary rank-two trace, "
                "Hall, geometric bridge, or exact-formula theorem"
            ),
        },
        "k7_rank_two_all_hole_census": census(maximum_n, stop_on_failure),
        "sources": {
            "producer": {
                "path": str(producer.relative_to(repo)),
                "sha256": file_sha256(producer),
            },
            "checker": {
                "path": str(checker.relative_to(repo)),
                "sha256": file_sha256(checker),
            },
            "path_producer": {
                "path": str(path_producer.relative_to(repo)),
                "sha256": file_sha256(path_producer),
            },
            "path_checker": {
                "path": str(path_checker.relative_to(repo)),
                "sha256": file_sha256(path_checker),
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
