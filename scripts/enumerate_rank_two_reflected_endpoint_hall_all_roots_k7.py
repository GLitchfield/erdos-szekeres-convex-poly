#!/usr/bin/env python3
"""Test reflected endpoint-transition Hall on bounded rank-two frontiers."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from collections import Counter, defaultdict
from pathlib import Path

import enumerate_allocated_span_pascal_demand as base
import enumerate_reflected_transition_hall as reflection


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
        (color, 2, base.nondominated_intervals(pairs))
        for color, pairs in sorted(grouped.items())
        if pairs
    )


def census(maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    strong_size = 7
    colorings = base.DecomposableColorings(maximum_n)
    colorings.enumerate()
    analyzer = base.LocalSpanAnalysis(maximum_n, strong_size)
    totals: Counter[str] = Counter()
    by_size: dict[str, Counter[str]] = {}
    first_failure = None
    first_capacity_violation = None
    digest = hashlib.sha256()
    stopped = False
    capacity = math.comb(strong_size - 2, 1)

    for size in range(2, maximum_n + 1):
        row: Counter[str] = Counter()
        for support in range(1, 1 << maximum_n):
            if support.bit_count() != size:
                continue
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
                        vertices = tuple(
                            vertex
                            for vertex in range(maximum_n)
                            if support & (1 << vertex)
                        )
                        for color, rank, frontier in rank_two_context_groups(
                            local, support, lower, maximum_n
                        ):
                            original, _, _, _ = base.endpoint_transition_candidates(
                                local, vertices, frontier, color, rank, strong_size
                            )
                            oriented = reflection.oriented_candidates(
                                original, frontier, lower, 1, strong_size - 3
                            )
                            hall = base.has_distinct_representatives(oriented)
                            row["rank_two_group_checks"] += 1
                            row["maximum_frontier_size"] = max(
                                row["maximum_frontier_size"], len(frontier)
                            )
                            if len(frontier) > capacity:
                                row["capacity_violations"] += 1
                                if first_capacity_violation is None:
                                    first_capacity_violation = {
                                        **base.example(
                                            support, lower, bits, frontier
                                        ),
                                        "color": "cup" if color else "cap",
                                        "rank": rank,
                                        "capacity": capacity,
                                    }
                            record = [
                                support,
                                lower,
                                bits,
                                color,
                                [list(span) for span in frontier],
                                reflection.candidate_hex(oriented),
                                hall,
                            ]
                            digest.update(
                                json.dumps(record, separators=(",", ":")).encode()
                            )
                            digest.update(b"\n")
                            if not hall:
                                row["hall_failures"] += 1
                                if first_failure is None:
                                    first_failure = {
                                        **base.example(
                                            support, lower, bits, frontier
                                        ),
                                        "color": "cup" if color else "cap",
                                        "rank": rank,
                                        "capacity": capacity,
                                        "oriented_candidates_hex": (
                                            reflection.candidate_hex(oriented)
                                        ),
                                    }
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
        maximum = max(
            totals["maximum_frontier_size"], row["maximum_frontier_size"]
        )
        totals.update(row)
        totals["maximum_frontier_size"] = maximum
        if stopped:
            break

    return {
        "maximum_n": maximum_n,
        "strong_size": strong_size,
        "rank": 2,
        "capacity": capacity,
        "stop_on_failure": stop_on_failure,
        "stopped_early": stopped,
        "complete": not stopped,
        "statistics": {
            "totals": dict(sorted(totals.items())),
            "by_support_size": {
                key: dict(sorted(row.items())) for key, row in by_size.items()
            },
            "analyzed_local_states": len(analyzer.cache),
        },
        "first_hall_failure": first_failure,
        "first_capacity_violation": first_capacity_violation,
        "checked_prefix_sha256": digest.hexdigest(),
    }


def produce(repo: Path, maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = (
        repo / "scripts/check_rank_two_reflected_endpoint_hall_all_roots_k7.py"
    )
    mask_base = repo / "scripts/enumerate_allocated_span_pascal_demand.py"
    height_base = repo / "scripts/check_allocated_span_pascal_demand.py"
    return {
        "schema_version": 1,
        "experiment": "all-root-rank-two-reflected-endpoint-hall-k7-gate",
        "generation_base_revision": base.git_revision(repo),
        "contract": {
            "domain": (
                "every recursively decomposable k=7 root through the recorded "
                "support size and every exact-rank-two retained frontier"
            ),
            "success": (
                "the full frontier admits distinct representatives from its "
                "orientation-reflected two-endpoint transition candidates"
            ),
            "claim_boundary": (
                "bounded computational evidence only; no arbitrary reflected "
                "Hall, slotting, geometric bridge, or exact-formula theorem"
            ),
        },
        "rank_two_census": census(maximum_n, stop_on_failure),
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
                "path": str(mask_base.relative_to(repo)),
                "sha256": base.file_sha256(mask_base),
            },
            "height_base": {
                "path": str(height_base.relative_to(repo)),
                "sha256": base.file_sha256(height_base),
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
