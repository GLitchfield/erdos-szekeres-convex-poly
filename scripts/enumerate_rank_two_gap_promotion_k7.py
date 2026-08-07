#!/usr/bin/env python3
"""Falsify a root-local cross-rank repair of rank-two Pascal capacity.

For each open decomposable k=7 root, write the lower/upper membership sequence
as alternating runs.  The first crossing transition remains at rank two.  A
later transition entering a lower run is paired with the hidden lower gap
across the preceding upper run and is promoted to that gap's exact ambient cap
rank.  Dually, a transition entering an upper run is promoted to the hidden
upper gap's exact ambient cup rank.

For each color and exact rank, combine promoted gaps with the existing
rank-at-least-three crossing frontier and test both raw Pascal capacity and the
existing endpoint-ideal candidate relation.  The latter is only a bounded
falsification test: no theorem currently makes those candidates valid for
noncrossing promoted gaps.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from collections import Counter, defaultdict
from pathlib import Path

import enumerate_allocated_span_pascal_demand as base


def merge_runs(
    vertices: tuple[int, ...], lower: int
) -> tuple[tuple[bool, tuple[int, ...]], ...]:
    runs: list[tuple[bool, list[int]]] = []
    for vertex in vertices:
        label = bool(lower & (1 << vertex))
        if not runs or runs[-1][0] != label:
            runs.append((label, [vertex]))
        else:
            runs[-1][1].append(vertex)
    return tuple((label, tuple(run)) for label, run in runs)


def promoted_groups(
    local: dict[tuple[int, int, int], int],
    support: int,
    lower: int,
    maximum_n: int,
) -> tuple[
    tuple[tuple[int, int, tuple[tuple[int, int], ...]], ...],
    tuple[dict[str, object], ...],
]:
    """Return the adjusted groups and their explicit promotion records."""
    vertices = tuple(
        vertex for vertex in range(maximum_n) if support & (1 << vertex)
    )
    runs = merge_runs(vertices, lower)
    transitions = tuple(
        (runs[index - 1][1][-1], runs[index][1][0])
        for index in range(1, len(runs))
    )
    matched: dict[int, set[tuple[int, int]]] = {0: set(), 1: set()}
    additions: defaultdict[tuple[int, int], list[tuple[int, int]]] = defaultdict(list)
    records: list[dict[str, object]] = []

    for index in range(2, len(runs)):
        child_is_lower, current = runs[index]
        previous_same = runs[index - 2][1]
        intervening = runs[index - 1][1]
        hidden = previous_same[-1], current[0]
        entering_transition = transitions[index - 1]
        promoted_color = 0 if child_is_lower else 1
        exact_rank = local[promoted_color, hidden[0], hidden[1]]
        if exact_rank < 3:
            raise AssertionError("hidden gap lacks its forced rank-three witness")
        if entering_transition in matched[promoted_color]:
            raise AssertionError("one transition received two same-color promotions")
        matched[promoted_color].add(entering_transition)
        additions[promoted_color, exact_rank].append(hidden)
        records.append(
            {
                "color": promoted_color,
                "hidden_gap": list(hidden),
                "intervening_run": list(intervening),
                "matched_transition": list(entering_transition),
                "exact_ambient_rank": exact_rank,
            }
        )

    collected: defaultdict[tuple[int, int], list[tuple[int, int]]] = defaultdict(list)
    for color, rank, frontier in base.context_groups(
        local, support, lower, maximum_n
    ):
        collected[color, rank].extend(frontier)
    for color in (0, 1):
        collected[color, 2].extend(
            transition for transition in transitions if transition not in matched[color]
        )
    for key, gaps in additions.items():
        collected[key].extend(gaps)

    groups = tuple(
        (color, rank, tuple(sorted(spans)))
        for (color, rank), spans in sorted(collected.items())
        if spans
    )
    return groups, tuple(records)


def compact_example(
    support: int,
    lower: int,
    bits: int,
    color: int,
    rank: int,
    spans: tuple[tuple[int, int], ...],
    promotions: tuple[dict[str, object], ...],
    capacity: int,
) -> dict[str, object]:
    return {
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "color": "cup" if color else "cap",
        "rank": rank,
        "spans": [list(span) for span in spans],
        "capacity": capacity,
        "promotions": list(promotions),
    }


def census(maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    strong_size = 7
    colorings = base.DecomposableColorings(maximum_n)
    colorings.enumerate()
    analyzer = base.LocalSpanAnalysis(maximum_n, strong_size)
    totals: Counter[str] = Counter()
    by_size: dict[str, Counter[str]] = {}
    by_rank: dict[tuple[int, int], Counter[str]] = {}
    first_capacity_failure = None
    first_candidate_failure = None
    digest = hashlib.sha256()
    stopped = False

    for size in range(2, maximum_n + 1):
        row: Counter[str] = Counter()
        for support in range(1, 1 << maximum_n):
            if support.bit_count() != size:
                continue
            vertices = tuple(
                vertex for vertex in range(maximum_n) if support & (1 << vertex)
            )
            for lower in base.nonempty_proper_submasks(support):
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
                        groups, promotions = promoted_groups(
                            local, support, lower, maximum_n
                        )
                        row["promotion_records"] += len(promotions)
                        record_groups = []
                        for color, rank, spans in groups:
                            row["adjusted_group_checks"] += 1
                            rank_row = by_rank.setdefault((color, rank), Counter())
                            rank_row["group_count"] += 1
                            rank_row["maximum_size"] = max(
                                rank_row["maximum_size"], len(spans)
                            )
                            capacity = math.comb(strong_size - 2, rank - 1)
                            capacity_ok = len(spans) <= capacity
                            candidates, _, _, _ = base.endpoint_transition_candidates(
                                local, vertices, spans, color, rank, strong_size
                            )
                            candidate_ok = base.has_distinct_representatives(candidates)
                            if not capacity_ok:
                                row["capacity_failures"] += 1
                                rank_row["capacity_failures"] += 1
                                if first_capacity_failure is None:
                                    first_capacity_failure = compact_example(
                                        support,
                                        lower,
                                        bits,
                                        color,
                                        rank,
                                        spans,
                                        promotions,
                                        capacity,
                                    )
                            if not candidate_ok:
                                row["candidate_failures"] += 1
                                rank_row["candidate_failures"] += 1
                                if first_candidate_failure is None:
                                    first_candidate_failure = {
                                        **compact_example(
                                            support,
                                            lower,
                                            bits,
                                            color,
                                            rank,
                                            spans,
                                            promotions,
                                            capacity,
                                        ),
                                        "candidate_ideals_hex": [
                                            [f"{ideal:x}" for ideal in family]
                                            for family in candidates
                                        ],
                                    }
                            record_groups.append(
                                [
                                    color,
                                    rank,
                                    [list(span) for span in spans],
                                    capacity_ok,
                                    candidate_ok,
                                ]
                            )
                        digest.update(
                            json.dumps(
                                [
                                    support,
                                    lower,
                                    bits,
                                    record_groups,
                                    promotions,
                                ],
                                separators=(",", ":"),
                                sort_keys=True,
                            ).encode()
                        )
                        digest.update(b"\n")
                        if stop_on_failure and (
                            first_capacity_failure is not None
                            or first_candidate_failure is not None
                        ):
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
        "strong_size": strong_size,
        "stop_on_failure": stop_on_failure,
        "stopped_early": stopped,
        "complete": not stopped,
        "statistics": {
            "totals": dict(sorted(totals.items())),
            "by_support_size": {
                key: dict(sorted(row.items())) for key, row in by_size.items()
            },
            "by_color_rank": {
                f"{'cup' if color else 'cap'}-{rank}": dict(sorted(row.items()))
                for (color, rank), row in sorted(by_rank.items())
            },
            "analyzed_local_states": len(analyzer.cache),
        },
        "first_capacity_failure": first_capacity_failure,
        "first_candidate_failure": first_candidate_failure,
        "checked_prefix_sha256": digest.hexdigest(),
    }


def produce(repo: Path, maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_rank_two_gap_promotion_k7.py"
    return {
        "schema_version": 1,
        "experiment": "rank-two-root-gap-cross-rank-promotion-k7-gate",
        "generation_base_revision": base.git_revision(repo),
        "contract": {
            "domain": (
                "every open recursively decomposable k=7 root through the "
                "recorded support size"
            ),
            "promotion": (
                "all but the first transition are matched by runs; only "
                "hidden lower gaps promote cap requests and hidden upper "
                "gaps promote cup requests, at exact ambient span rank"
            ),
            "success": (
                "for every color/rank adjusted group, raw cardinality fits "
                "the Pascal layer and the explicit endpoint-ideal candidate "
                "families admit distinct representatives"
            ),
            "claim_boundary": (
                "bounded falsification only; the endpoint-ideal relation is "
                "not proved valid for noncrossing promoted gaps"
            ),
        },
        "census": census(maximum_n, stop_on_failure),
        "sources": {
            "producer": {
                "path": str(producer.relative_to(repo)),
                "sha256": base.file_sha256(producer),
            },
            "checker": {
                "path": str(checker.relative_to(repo)),
                "sha256": base.file_sha256(checker),
            },
            "mask_base": {
                "path": "scripts/enumerate_allocated_span_pascal_demand.py",
                "sha256": base.file_sha256(
                    repo / "scripts/enumerate_allocated_span_pascal_demand.py"
                ),
            },
            "height_base": {
                "path": "scripts/check_allocated_span_pascal_demand.py",
                "sha256": base.file_sha256(
                    repo / "scripts/check_allocated_span_pascal_demand.py"
                ),
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
    base.write_atomic(
        args.output,
        produce(repo, args.maximum_n, not args.no_stop_on_failure),
    )
    print(args.output)


if __name__ == "__main__":
    main()
