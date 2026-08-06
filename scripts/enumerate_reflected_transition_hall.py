#!/usr/bin/env python3
"""Gate orientation-reflected endpoint-transition Hall candidates.

The frozen n=12, k=7 collision is checked first.  If its complete root
frontier passes, enumerate the existing k=6 contexts through eight vertices
in the same canonical order as the allocated-span census.  Stop at the first
Hall failure; a complete run must cover all 631,474 frontier groups.

This is bounded computational evidence, not a proof of the general Hall
condition.  The independent checker uses row-height ideals and a separate
backtracking matcher.
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
    example,
    file_sha256,
    git_revision,
    has_distinct_representatives,
    nonempty_proper_submasks,
    write_atomic,
)


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


def reflected_ideal(mask: int, rows: int, columns: int) -> int:
    """Rotate a grid mask by 180 degrees and complement it."""
    answer = 0
    for row in range(rows):
        for column in range(columns):
            source = (rows - 1 - row) * columns + (columns - 1 - column)
            if not mask & (1 << source):
                answer |= 1 << (row * columns + column)
    return answer


def oriented_candidates(
    candidates: tuple[tuple[int, ...], ...],
    frontier: tuple[tuple[int, int], ...],
    lower: int,
    rows: int,
    columns: int,
) -> tuple[tuple[int, ...], ...]:
    """Reflect exactly the spans whose left endpoint lies in the upper child."""
    answer = []
    for family, (left, _) in zip(candidates, frontier, strict=True):
        if lower & (1 << left):
            answer.append(family)
        else:
            answer.append(
                tuple(sorted(reflected_ideal(mask, rows, columns) for mask in family))
            )
    return tuple(answer)


def candidate_hex(candidates: tuple[tuple[int, ...], ...]) -> list[list[str]]:
    return [[f"{ideal:x}" for ideal in family] for family in candidates]


def rigid_obstructions(
    original: tuple[tuple[int, ...], ...],
    oriented: tuple[tuple[int, ...], ...],
    frontier: tuple[tuple[int, int], ...],
    lower: int,
    rows: int,
    columns: int,
) -> dict[str, object]:
    rigid = [index for index, family in enumerate(oriented) if len(family) == 1]
    same_orientation = None
    fixed_opposite = None
    opposite = None
    by_label: dict[int, list[int]] = {}
    for index in rigid:
        by_label.setdefault(oriented[index][0], []).append(index)
    triple = next(
        (indices[:3] for indices in by_label.values() if len(indices) >= 3), None
    )
    for offset, first in enumerate(rigid):
        for second in rigid[offset + 1 :]:
            if oriented[first][0] != oriented[second][0]:
                continue
            first_lower = bool(lower & (1 << frontier[first][0]))
            second_lower = bool(lower & (1 << frontier[second][0]))
            if first_lower == second_lower and same_orientation is None:
                same_orientation = [first, second]
            if first_lower != second_lower and opposite is None:
                opposite = [first, second]
            if (
                first_lower != second_lower
                and len(original[first]) == 1
                and len(original[second]) == 1
                and original[first][0] == original[second][0]
                and reflected_ideal(original[first][0], rows, columns)
                == original[first][0]
                and fixed_opposite is None
            ):
                fixed_opposite = [first, second]
    return {
        "same_orientation_rigid_pair": same_orientation,
        "opposite_orientation_rigid_pair": opposite,
        "reflection_fixed_opposite_pair": fixed_opposite,
        "triple_rigid_collision": triple,
    }


def group_record(
    support: int,
    lower: int,
    bits: int,
    color: int,
    rank: int,
    frontier: tuple[tuple[int, int], ...],
    original: tuple[tuple[int, ...], ...],
    oriented: tuple[tuple[int, ...], ...],
    strong_size: int,
) -> dict[str, object]:
    rows = rank - 1
    columns = strong_size - rank - 1
    return {
        **example(support, lower, bits, frontier),
        "color": "cup" if color else "cap",
        "rank": rank,
        "rows": rows,
        "columns": columns,
        "original_candidates_hex": candidate_hex(original),
        "oriented_candidates_hex": candidate_hex(oriented),
        "rigid_obstructions": rigid_obstructions(
            original, oriented, frontier, lower, rows, columns
        ),
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
        original, _, _, _ = endpoint_transition_candidates(
            local, vertices, frontier, color, rank, analyzer.strong_size
        )
        oriented = oriented_candidates(
            original,
            frontier,
            lower,
            rank - 1,
            analyzer.strong_size - rank - 1,
        )
        record = group_record(
            support,
            lower,
            bits,
            color,
            rank,
            frontier,
            original,
            oriented,
            analyzer.strong_size,
        )
        record["hall"] = has_distinct_representatives(oriented)
        records.append(record)
        if not record["hall"] and first_failure is None:
            first_failure = record
    return records, first_failure


def frozen_gate() -> dict[str, object]:
    maximum_n = 12
    strong_size = 7
    colorings = DecomposableColorings(maximum_n)
    analyzer = LocalSpanAnalysis(maximum_n, strong_size)
    support = tree_support(FROZEN_TREE)
    lower = tree_support(FROZEN_LOWER_TREE)
    bits = tree_coloring_bits(FROZEN_TREE, colorings)
    records, first_failure = analyze_root(analyzer, bits, support, lower)
    if records is None:
        raise AssertionError("frozen collision unexpectedly contains a strong seven")
    target = next(
        record
        for record in records
        if record["color"] == "cap"
        and record["rank"] == 3
        and [4, 6] in record["frontier"]
        and [5, 7] in record["frontier"]
    )
    first_index = target["frontier"].index([4, 6])
    second_index = target["frontier"].index([5, 7])
    return {
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "rank_group_checks": len(records),
        "target_pair": {
            "first": [4, 6],
            "second": [5, 7],
            "first_original_hex": target["original_candidates_hex"][first_index],
            "second_original_hex": target["original_candidates_hex"][second_index],
            "first_oriented_hex": target["oriented_candidates_hex"][first_index],
            "second_oriented_hex": target["oriented_candidates_hex"][second_index],
            "pair_separated": (
                target["oriented_candidates_hex"][first_index]
                != target["oriented_candidates_hex"][second_index]
            ),
        },
        "full_frontier_hall": first_failure is None,
        "first_hall_failure": first_failure,
    }


def k6_gate(maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    strong_size = 6
    colorings = DecomposableColorings(maximum_n)
    colorings.enumerate()
    analyzer = LocalSpanAnalysis(maximum_n, strong_size)
    counts: Counter[str] = Counter()
    by_size: dict[str, Counter[str]] = {}
    first_failure = None
    first_targeted: dict[str, dict[str, object]] = {}
    digest = hashlib.sha256()
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
                            digest.update(
                                json.dumps(record, sort_keys=True).encode()
                            )
                            digest.update(b"\n")
                            for label, witness in record[
                                "rigid_obstructions"
                            ].items():
                                if witness is not None:
                                    row[label] += 1
                                    first_targeted.setdefault(label, record)
                        if failure is not None and first_failure is None:
                            first_failure = failure
                            row["hall_failures"] += 1
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
        counts.update(row)
        if stopped:
            break

    return {
        "maximum_n": maximum_n,
        "strong_size": strong_size,
        "stop_on_failure": stop_on_failure,
        "stopped_early": stopped,
        "complete": not stopped,
        "statistics": {
            "totals": dict(sorted(counts.items())),
            "by_support_size": {
                size: dict(sorted(row.items())) for size, row in by_size.items()
            },
            "analyzed_local_states": len(analyzer.cache),
        },
        "first_targeted_obstructions": dict(sorted(first_targeted.items())),
        "first_hall_failure": first_failure,
        "checked_prefix_sha256": digest.hexdigest(),
    }


def produce(maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    repo = Path(__file__).resolve().parent.parent
    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_reflected_transition_hall.py"
    base_producer = repo / "scripts/enumerate_allocated_span_pascal_demand.py"
    base_checker = repo / "scripts/check_allocated_span_pascal_demand.py"
    frozen = frozen_gate()
    k6 = None
    if frozen["full_frontier_hall"]:
        k6 = k6_gate(maximum_n, stop_on_failure)
    return {
        "schema_version": 1,
        "experiment": "orientation-reflected-transition-hall-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "orientation": (
                "leave a span unchanged iff its left endpoint belongs to the "
                "lower child; otherwise rotate-complement every candidate"
            ),
            "carrier": (
                "the same untagged rectangular ideals and hence the same "
                "AllocatedPascalSlot carrier"
            ),
            "order": (
                "check the complete frozen n=12 root frontier first, then all "
                "k=6 groups through maximum_n; stop on the first Hall failure"
            ),
            "claim_boundary": (
                "bounded computational evidence only, not a general Hall proof"
            ),
        },
        "frozen_n12_k7": frozen,
        "k6_census": k6,
        "observed_claim": (
            "The orientation-reflected candidate repair passes every completed "
            "bounded gate exactly when both recorded failure fields are null."
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
            "base_producer": {
                "path": str(base_producer.relative_to(repo)),
                "sha256": file_sha256(base_producer),
            },
            "base_checker": {
                "path": str(base_checker.relative_to(repo)),
                "sha256": file_sha256(base_checker),
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
        args.output,
        produce(args.maximum_n, not args.no_stop_on_failure),
    )
    print(args.output)


if __name__ == "__main__":
    main()
