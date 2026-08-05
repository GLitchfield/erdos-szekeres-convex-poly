#!/usr/bin/env python3
"""Independently replay the published off-window classification certificate."""

from __future__ import annotations

import json
import sys
from functools import cache
from pathlib import Path


@cache
def choose_pascal(n: int, r: int) -> int:
    if r < 0 or n < r:
        return 0
    row = [1]
    for _ in range(n):
        row = [1] + [row[index - 1] + row[index] for index in range(1, len(row))] + [1]
    return row[r]


@cache
def source_threshold(a: int, u: int, k: int) -> int:
    if min(a, u) == 1:
        return 0
    if a + u < k + 4:
        return choose_pascal(a + u - 4, u - 2)
    first = k - a
    last = u - 2
    return sum(choose_pascal(k - 2, position) for position in range(first, last + 1))


def direct_second_child_index(a: int, bound: int, k: int, card: int) -> int:
    """Replay ``publishedChildIndex a bound k card`` by its definition."""
    return max(
        index for index in range(bound + 1)
        if source_threshold(a, index, k) < card
    )


def direct_first_child_index(bound: int, u: int, k: int, card: int) -> int:
    """Color-dual greatest index when the first threshold parameter varies."""
    return max(
        index for index in range(bound + 1)
        if source_threshold(index, u, k) < card
    )


def replay(max_k: int) -> dict[str, object]:
    keys = (
        "scalar_failure_states",
        "feasible_failure_states",
        "non_index_one_states",
        "feasible_child_splits",
        "saturation_violations",
    )
    totals = dict.fromkeys(keys, 0)
    rows: list[dict[str, int]] = []
    smallest: dict[str, object] | None = None

    for k in range(5, max_k + 1):
        row = {"k": k, **dict.fromkeys(keys, 0)}
        for a in range(4, k + 1):
            for u in range(4, k + 1):
                if k + 4 > a + u:
                    continue
                outer = source_threshold(a, u, k)
                target = outer + 1
                for a_prime in range(1, a):
                    for u_prime in range(1, u):
                        if k - 1 < a_prime + u_prime:
                            continue
                        scalar = (
                            source_threshold(a, u_prime, k)
                            + choose_pascal(k - 2, u_prime - 1)
                            + source_threshold(a_prime, u, k)
                            + choose_pascal(k - 2, a_prime - 1)
                        )
                        if scalar <= outer:
                            continue
                        row["scalar_failure_states"] += 1
                        lower_min = source_threshold(a, u_prime, k) + 1
                        lower_max = source_threshold(a, u_prime + 1, k)
                        upper_min = source_threshold(a_prime, u, k) + 1
                        upper_max = source_threshold(a_prime + 1, u, k)
                        first = max(lower_min, target - upper_max)
                        last = min(lower_max, target - upper_min)
                        if last < first:
                            continue
                        upper_first = target - last
                        upper_last = target - first
                        # Check the actual greatest-index definitions at both
                        # endpoints.  Greatest indices are monotone in `card`,
                        # so endpoint agreement covers the complete interval
                        # without assuming threshold monotonicity in its index.
                        assert direct_second_child_index(
                            a, u, k, first
                        ) == u_prime
                        assert direct_second_child_index(
                            a, u, k, last
                        ) == u_prime
                        assert direct_first_child_index(
                            a, u, k, upper_first
                        ) == a_prime
                        assert direct_first_child_index(
                            a, u, k, upper_last
                        ) == a_prime
                        row["feasible_failure_states"] += 1
                        row["feasible_child_splits"] += last - first + 1
                        if min(a_prime, u_prime) == 1:
                            continue
                        row["non_index_one_states"] += 1
                        property_holds = (
                            a_prime + 1 == a and u_prime < k - a + 1
                        ) or (
                            u_prime + 1 == u and a_prime < k - u + 1
                        )
                        if not property_holds:
                            row["saturation_violations"] += 1
                        if smallest is None:
                            child_pairs = [
                                [lower_card, target - lower_card]
                                for lower_card in range(first, last + 1)
                            ]
                            smallest = {
                                "state": {
                                    "k": k,
                                    "a": a,
                                    "u": u,
                                    "a_prime": a_prime,
                                    "u_prime": u_prime,
                                },
                                "outer_threshold": outer,
                                "scalar_contribution": scalar,
                                "defect": scalar - outer,
                                "lower_child_cardinalities": [pair[0] for pair in child_pairs],
                                "child_cardinality_pairs": child_pairs,
                                "active_lower_endpoint": k - a + 1,
                            }
        for key in keys:
            totals[key] += row[key]
        rows.append(row)

    return {"totals": totals, "by_k": rows, "smallest_non_index_one": smallest}


def main() -> None:
    path = Path(sys.argv[1]) if len(sys.argv) == 2 else Path(
        "data/derived/e3-published-offwindow-k20.json"
    )
    certificate = json.loads(path.read_text(encoding="utf-8"))
    assert certificate["schema"] == "erdos-szekeres-published-offwindow-v1"
    assert certificate["range"]["min_k"] == 5
    replayed = replay(certificate["range"]["max_k"])
    for key, value in replayed.items():
        assert certificate[key] == value, key
    assert certificate["totals"]["saturation_violations"] == 0
    print(json.dumps(replayed, sort_keys=True))


if __name__ == "__main__":
    main()
