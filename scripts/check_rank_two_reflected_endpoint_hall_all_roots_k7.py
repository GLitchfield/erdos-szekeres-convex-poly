#!/usr/bin/env python3
"""Independently replay reflected endpoint Hall at exact rank two."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter, defaultdict
from pathlib import Path

import check_allocated_span_pascal_demand as base
import check_reflected_transition_hall as reflection


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
        (color, 2, base.interval_frontier(pairs))
        for color, pairs in sorted(grouped.items())
        if pairs
    )


def census(maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    strong_size = 7
    machine = base.Replay(maximum_n, strong_size)
    full = (1 << maximum_n) - 1
    machine.colorings(full)
    totals: Counter[str] = Counter()
    by_size: dict[str, Counter[str]] = {}
    first_failure = None
    first_capacity_violation = None
    digest = hashlib.sha256()
    stopped = False
    capacity = base.pascal(strong_size - 2, 1)

    for size in range(2, maximum_n + 1):
        row: Counter[str] = Counter()
        for support in range(1, full + 1):
            if support.bit_count() != size:
                continue
            for lower in base.proper_parts(support):
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
                        for color, rank, frontier in rank_two_groups(
                            local, support, lower, maximum_n
                        ):
                            original, _, _, _ = base.replay_transition_candidates(
                                local, vertices, frontier, color, rank, strong_size
                            )
                            oriented = reflection.oriented_candidates(
                                original, frontier, lower, strong_size - 3
                            )
                            hall = base.replay_distinct_representatives(oriented)
                            row["rank_two_group_checks"] += 1
                            row["maximum_frontier_size"] = max(
                                row["maximum_frontier_size"], len(frontier)
                            )
                            if len(frontier) > capacity:
                                row["capacity_violations"] += 1
                                if first_capacity_violation is None:
                                    first_capacity_violation = {
                                        **reflection.make_example(
                                            support, lower, bits, frontier
                                        ),
                                        "color": "cup" if color else "cap",
                                        "rank": rank,
                                        "capacity": capacity,
                                    }
                            encoded = reflection.candidate_hex(
                                oriented, strong_size - 3
                            )
                            record = [
                                support,
                                lower,
                                bits,
                                color,
                                [list(span) for span in frontier],
                                encoded,
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
                                        **reflection.make_example(
                                            support, lower, bits, frontier
                                        ),
                                        "color": "cup" if color else "cap",
                                        "rank": rank,
                                        "capacity": capacity,
                                        "oriented_candidates_hex": encoded,
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
            "analyzed_local_states": len(machine.analysis_cache),
        },
        "first_hall_failure": first_failure,
        "first_capacity_violation": first_capacity_violation,
        "checked_prefix_sha256": digest.hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    repo = Path(__file__).resolve().parent.parent
    source_checks = {
        label: base.file_sha256(repo / metadata["path"]) == metadata["sha256"]
        for label, metadata in manifest["sources"].items()
    }
    checks: dict[str, bool] = {"sources": all(source_checks.values())}
    if not args.source_only:
        expected = manifest["rank_two_census"]
        actual = census(
            int(expected["maximum_n"]), bool(expected["stop_on_failure"])
        )
        checks["rank_two_census"] = actual == expected
    result = {
        "manifest": str(args.manifest),
        "mode": "source-only" if args.source_only else "exhaustive",
        "source_checks": source_checks,
        "checks": checks,
        "ok": all(checks.values()),
    }
    print(json.dumps(result, sort_keys=True))
    if not result["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
