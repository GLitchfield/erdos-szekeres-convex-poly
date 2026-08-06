#!/usr/bin/env python3
"""Gate block expansion for the reflected interval incident to the active ray.

Every consecutive block is checked directly against the union of its active
candidate intervals.  The frozen n=12, k=7 root is checked first, followed by
every k=6 frontier group through ``maximum_n``.  This is bounded computational
evidence, not a general proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

from enumerate_allocated_span_pascal_demand import (
    DecomposableColorings,
    LocalSpanAnalysis,
    context_groups,
    endpoint_transition_candidates,
    file_sha256,
    git_revision,
    has_distinct_representatives,
    nonempty_proper_submasks,
    write_atomic,
)
from enumerate_reflected_transition_hall import oriented_candidates


Tree = int | tuple["Tree", "Tree"]

FROZEN_LOWER_TREE: Tree = ((8, (2, 1)), ((4, 7), 10))
FROZEN_UPPER_TREE: Tree = (((0, 3), ((6, 9), 5)), 11)
FROZEN_TREE: Tree = (FROZEN_LOWER_TREE, FROZEN_UPPER_TREE)


def tree_support(tree: Tree) -> int:
    if isinstance(tree, int):
        return 1 << tree
    return tree_support(tree[0]) | tree_support(tree[1])


def tree_coloring_bits(tree: Tree, colorings: DecomposableColorings) -> int:
    if isinstance(tree, int):
        return 0
    lower, upper = tree
    support = tree_support(tree)
    lower_support = tree_support(lower)
    return (
        tree_coloring_bits(lower, colorings)
        | tree_coloring_bits(upper, colorings)
        | colorings.crossing_bits(support, lower_support)
    )


def active_reflected_candidates(
    local: dict[tuple[int, int, int], int],
    vertices: tuple[int, ...],
    frontier: tuple[tuple[int, int], ...],
    lower: int,
    color: int,
    rank: int,
    strong_size: int,
) -> tuple[tuple[int, ...], ...]:
    _, left_intervals, right_intervals, _ = endpoint_transition_candidates(
        local, vertices, frontier, color, rank, strong_size
    )
    active = tuple(
        left_family if (color == 1) == bool(lower & (1 << left)) else right_family
        for (left, _), left_family, right_family in zip(
            frontier, left_intervals, right_intervals, strict=True
        )
    )
    return oriented_candidates(
        active, frontier, lower, rank - 1, strong_size - rank - 1
    )


def first_consecutive_block_defect(
    frontier: tuple[tuple[int, int], ...],
    candidates: tuple[tuple[int, ...], ...],
) -> dict[str, object] | None:
    for first in range(len(frontier)):
        candidate_union: set[int] = set()
        for last in range(first, len(frontier)):
            candidate_union.update(candidates[last])
            block_card = last - first + 1
            if block_card > len(candidate_union):
                return {
                    "first_index": first,
                    "last_index": last,
                    "spans": [list(span) for span in frontier[first : last + 1]],
                    "candidate_families_hex": [
                        [f"{ideal:x}" for ideal in family]
                        for family in candidates[first : last + 1]
                    ],
                    "block_card": block_card,
                    "candidate_union_hex": [
                        f"{ideal:x}" for ideal in sorted(candidate_union)
                    ],
                    "candidate_union_card": len(candidate_union),
                }
    return None


def group_record(
    support: int,
    lower: int,
    bits: int,
    color: int,
    rank: int,
    frontier: tuple[tuple[int, int], ...],
    candidates: tuple[tuple[int, ...], ...],
) -> dict[str, object]:
    candidate_union = sorted({ideal for family in candidates for ideal in family})
    defect = first_consecutive_block_defect(frontier, candidates)
    return {
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "color": "cup" if color else "cap",
        "rank": rank,
        "frontier": [list(span) for span in frontier],
        "active_reflected_candidates_hex": [
            [f"{ideal:x}" for ideal in family] for family in candidates
        ],
        "frontier_card": len(frontier),
        "candidate_union_card": len(candidate_union),
        "consecutive_block_expansion": defect is None,
        "first_consecutive_block_defect": defect,
        "full_frontier_matching": has_distinct_representatives(candidates),
    }


def analyze_root(
    analyzer: LocalSpanAnalysis,
    bits: int,
    support: int,
    lower: int,
) -> tuple[list[dict[str, object]] | None, dict[str, object] | None]:
    local = analyzer.analyze(bits, support)
    if local is None:
        return None, None
    vertices = tuple(
        vertex
        for vertex in range(analyzer.maximum_n)
        if support & (1 << vertex)
    )
    records = []
    first_failure = None
    for color, rank, frontier in context_groups(
        local, support, lower, analyzer.maximum_n
    ):
        candidates = active_reflected_candidates(
            local,
            vertices,
            frontier,
            lower,
            color,
            rank,
            analyzer.strong_size,
        )
        record = group_record(
            support, lower, bits, color, rank, frontier, candidates
        )
        records.append(record)
        if not record["consecutive_block_expansion"] and first_failure is None:
            first_failure = record
    return records, first_failure


def frozen_gate() -> dict[str, object]:
    colorings = DecomposableColorings(12)
    analyzer = LocalSpanAnalysis(12, 7)
    support = tree_support(FROZEN_TREE)
    lower = tree_support(FROZEN_LOWER_TREE)
    bits = tree_coloring_bits(FROZEN_TREE, colorings)
    records, failure = analyze_root(analyzer, bits, support, lower)
    if records is None:
        raise AssertionError("frozen collision unexpectedly contains a strong seven")
    return {
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "rank_group_checks": len(records),
        "consecutive_block_expansion": failure is None,
        "first_block_failure": failure,
    }


def k6_gate(maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    colorings = DecomposableColorings(maximum_n)
    colorings.enumerate()
    analyzer = LocalSpanAnalysis(maximum_n, 6)
    totals: Counter[str] = Counter()
    by_size: dict[str, Counter[str]] = {}
    digest = hashlib.sha256()
    first_failure = None
    stopped = False

    for size in range(2, maximum_n + 1):
        row: Counter[str] = Counter()
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
                        records, failure = analyze_root(
                            analyzer, bits, support, lower
                        )
                        if records is None:
                            row["terminal_contexts"] += 1
                            continue
                        row["open_contexts"] += 1
                        for record in records:
                            row["rank_group_checks"] += 1
                            row["max_frontier"] = max(
                                row["max_frontier"], int(record["frontier_card"])
                            )
                            if record["frontier_card"] == record["candidate_union_card"]:
                                row["tight_union_groups"] += 1
                            digest.update(json.dumps(record, sort_keys=True).encode())
                            digest.update(b"\n")
                        if failure is not None and first_failure is None:
                            first_failure = failure
                            row["block_expansion_failures"] += 1
                            if stop_on_failure:
                                stopped = True
                                break
                    if stopped:
                        break
                if stopped:
                    break
            if stopped:
                break
        by_size[str(size)] = row
        totals.update(row)
        if stopped:
            break

    return {
        "maximum_n": maximum_n,
        "strong_size": 6,
        "stop_on_failure": stop_on_failure,
        "stopped_early": stopped,
        "complete": not stopped,
        "statistics": {
            "totals": dict(sorted(totals.items())),
            "by_support_size": {
                size: dict(sorted(row.items())) for size, row in by_size.items()
            },
            "analyzed_local_states": len(analyzer.cache),
        },
        "first_block_failure": first_failure,
        "checked_prefix_sha256": digest.hexdigest(),
    }


def produce(maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    repo = Path(__file__).resolve().parent.parent
    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_active_reflected_transition_hall.py"
    base_producer = repo / "scripts/enumerate_allocated_span_pascal_demand.py"
    base_checker = repo / "scripts/check_allocated_span_pascal_demand.py"
    reflection_producer = repo / "scripts/enumerate_reflected_transition_hall.py"
    reflection_checker = repo / "scripts/check_reflected_transition_hall.py"
    frozen = frozen_gate()
    k6 = None
    if frozen["consecutive_block_expansion"]:
        k6 = k6_gate(maximum_n, stop_on_failure)
    return {
        "schema_version": 1,
        "experiment": "active-reflected-transition-hall-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "active_endpoint": (
                "use the left endpoint interval exactly when color is cup iff "
                "the span's left endpoint lies in the lower child; otherwise "
                "use the right endpoint interval"
            ),
            "orientation": (
                "leave the active interval unchanged iff the left endpoint is "
                "lower; otherwise rotate-complement every ideal"
            ),
            "block_test": (
                "for every ordered frontier interval, compare its number of "
                "spans directly with the union of its active candidates"
            ),
            "order": (
                "check the frozen n=12, k=7 root first, then all k=6 groups "
                "through maximum_n; stop on the first block-expansion failure"
            ),
            "claim_boundary": "bounded computational evidence only",
        },
        "frozen_n12_k7": frozen,
        "k6_census": k6,
        "sources": {
            "producer": {
                "path": str(producer.relative_to(repo)),
                "sha256": file_sha256(producer),
            },
            "checker": {
                "path": str(checker.relative_to(repo)),
                "sha256": file_sha256(checker),
            },
            "base_producer": {
                "path": str(base_producer.relative_to(repo)),
                "sha256": file_sha256(base_producer),
            },
            "base_checker": {
                "path": str(base_checker.relative_to(repo)),
                "sha256": file_sha256(base_checker),
            },
            "reflection_producer": {
                "path": str(reflection_producer.relative_to(repo)),
                "sha256": file_sha256(reflection_producer),
            },
            "reflection_checker": {
                "path": str(reflection_checker.relative_to(repo)),
                "sha256": file_sha256(reflection_checker),
            },
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--maximum-n", type=int, default=8)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--no-stop-on-failure", action="store_true")
    args = parser.parse_args()
    if not 2 <= args.maximum_n <= 8:
        parser.error("--maximum-n must lie between 2 and 8")
    write_atomic(
        args.output, produce(args.maximum_n, not args.no_stop_on_failure)
    )
    print(args.output)


if __name__ == "__main__":
    main()
