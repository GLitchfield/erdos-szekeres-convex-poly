#!/usr/bin/env python3
"""Enumerate feasible scalar failures in the published E3 induction.

This producer uses ``math.comb`` directly.  The independent checker in
``check_published_offwindow.py`` uses a separate Pascal-table implementation
and does not import this module.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path


def threshold(a: int, u: int, k: int) -> int:
    if a == 1 or u == 1:
        return 0
    if a + u <= k + 3:
        return math.comb(a + u - 4, a - 2)
    return sum(math.comb(k - 2, index) for index in range(k - a, u - 1))


def contribution(a: int, u: int, k: int, a_prime: int, u_prime: int) -> int:
    return (
        threshold(a, u_prime, k)
        + math.comb(k - 2, u_prime - 1)
        + threshold(a_prime, u, k)
        + math.comb(k - 2, a_prime - 1)
    )


def feasible_child_range(
    a: int, u: int, k: int, a_prime: int, u_prime: int
) -> tuple[int, int] | None:
    total = threshold(a, u, k) + 1
    lower = max(
        threshold(a, u_prime, k) + 1,
        total - threshold(a_prime + 1, u, k),
    )
    upper = min(
        threshold(a, u_prime + 1, k),
        total - threshold(a_prime, u, k) - 1,
    )
    return (lower, upper) if lower <= upper else None


def enumerate_summary(max_k: int) -> dict[str, object]:
    rows: list[dict[str, int]] = []
    smallest: dict[str, object] | None = None
    totals = {
        "scalar_failure_states": 0,
        "feasible_failure_states": 0,
        "non_index_one_states": 0,
        "feasible_child_splits": 0,
        "saturation_violations": 0,
    }

    for k in range(5, max_k + 1):
        row = {"k": k, **{key: 0 for key in totals}}
        for a in range(4, k + 1):
            for u in range(4, k + 1):
                if a + u < k + 4:
                    continue
                outer = threshold(a, u, k)
                for a_prime in range(1, a):
                    for u_prime in range(1, u):
                        if a_prime + u_prime > k - 1:
                            continue
                        value = contribution(a, u, k, a_prime, u_prime)
                        if value <= outer:
                            continue
                        row["scalar_failure_states"] += 1
                        child_range = feasible_child_range(
                            a, u, k, a_prime, u_prime
                        )
                        if child_range is None:
                            continue
                        row["feasible_failure_states"] += 1
                        first, last = child_range
                        row["feasible_child_splits"] += last - first + 1
                        if a_prime == 1 or u_prime == 1:
                            continue
                        row["non_index_one_states"] += 1
                        saturated_offwindow = (
                            a_prime == a - 1 and u_prime < k - a + 1
                        ) or (
                            u_prime == u - 1 and a_prime < k - u + 1
                        )
                        if not saturated_offwindow:
                            row["saturation_violations"] += 1
                        if smallest is None:
                            total = outer + 1
                            smallest = {
                                "state": {
                                    "k": k,
                                    "a": a,
                                    "u": u,
                                    "a_prime": a_prime,
                                    "u_prime": u_prime,
                                },
                                "outer_threshold": outer,
                                "scalar_contribution": value,
                                "defect": value - outer,
                                "lower_child_cardinalities": list(range(first, last + 1)),
                                "child_cardinality_pairs": [
                                    [card, total - card]
                                    for card in range(first, last + 1)
                                ],
                                "active_lower_endpoint": k - a + 1,
                            }
        for key in totals:
            totals[key] += row[key]
        rows.append(row)

    assert totals["saturation_violations"] == 0
    assert smallest is not None
    return {
        "schema": "erdos-szekeres-published-offwindow-v1",
        "range": {"min_k": 5, "max_k": max_k},
        "conventions": {
            "active_parent": "4 <= a,u <= k and k+4 <= a+u",
            "auxiliary": "1 <= a'<a, 1 <= u'<u, and a'+u' <= k-1",
            "feasible": "positive child sizes sum to threshold(a,u,k)+1 and realize both maximal indices",
            "resolved_index_one": "a'=1 or u'=1; PublishedInductionSemantics proves that child is a singleton",
        },
        "totals": totals,
        "by_k": rows,
        "smallest_non_index_one": smallest,
        "observed_claim": (
            "Every feasible non-index-one scalar failure has a'=a-1 with "
            "u'<k-a+1 or u'=u-1 with a'<k-u+1."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-k", type=int, default=20)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.max_k < 5:
        raise SystemExit("--max-k must be at least 5")
    encoded = json.dumps(enumerate_summary(args.max_k), indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(encoded, end="")
    else:
        args.output.write_text(encoded, encoding="utf-8")


if __name__ == "__main__":
    main()
