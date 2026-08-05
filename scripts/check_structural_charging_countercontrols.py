#!/usr/bin/env python3
"""Check the sharp separated-cap countercontrol used by structural charging."""

from __future__ import annotations

import itertools
import json


N = 8
MASK = 0xFFF0FC01FFFFF
EARLIER = (1, 2, 3, 4)
LATER = (4, 5, 6, 7)


TRIPLES = tuple(itertools.combinations(range(N), 3))
TRIPLE_INDEX = {triple: index for index, triple in enumerate(TRIPLES)}


def is_left(triple: tuple[int, int, int]) -> bool:
    return bool((MASK >> TRIPLE_INDEX[triple]) & 1)


def is_cup(vertices: tuple[int, ...]) -> bool:
    return all(is_left(triple) for triple in itertools.combinations(vertices, 3))


def is_cap(vertices: tuple[int, ...]) -> bool:
    return all(not is_left(triple) for triple in itertools.combinations(vertices, 3))


def is_strong(vertices: tuple[int, ...]) -> bool:
    for i, j, k, l in itertools.combinations(vertices, 4):
        if is_left((i, j, k)) != is_left((i, j, l)):
            return False
        if is_left((i, k, l)) != is_left((j, k, l)):
            return False
    return True


def one_change() -> bool:
    for i, j, k, l in itertools.combinations(range(N), 4):
        word = (
            is_left((i, j, k)),
            is_left((i, j, l)),
            is_left((i, k, l)),
            is_left((j, k, l)),
        )
        if sum(left != right for left, right in zip(word, word[1:])) > 1:
            return False
    return True


def monochromatic_sets(size: int, predicate) -> list[tuple[int, ...]]:
    return [vertices for vertices in itertools.combinations(range(N), size)
            if predicate(vertices)]


def main() -> None:
    caps_four = monochromatic_sets(4, is_cap)
    cap_spans = [(vertices[0], vertices[-1]) for vertices in caps_four]
    common_cuts = [
        cut for cut in range(N + 1)
        if all(lower < cut <= upper for lower, upper in cap_spans)
    ]
    residual = sorted(set(range(N)) - set(EARLIER) - set(LATER))

    result = {
        "mask": hex(MASK),
        "triple_order": "lexicographic combinations(range(8), 3), LSB first",
        "one_change": one_change(),
        "four_caps": caps_four,
        "earlier_cap": is_cap(EARLIER),
        "later_cap": is_cap(LATER),
        "weakly_separated": max(EARLIER) <= min(LATER),
        "common_cap_span_cuts": common_cuts,
        "residual": residual,
        "has_five_cap": bool(monochromatic_sets(5, is_cap)),
        "has_five_cup": bool(monochromatic_sets(5, is_cup)),
        "has_six_cup": bool(monochromatic_sets(6, is_cup)),
        "has_strong_six": bool(monochromatic_sets(6, is_strong)),
    }

    assert result["one_change"]
    assert result["earlier_cap"] and result["later_cap"]
    assert result["weakly_separated"]
    assert not result["common_cap_span_cuts"]
    assert residual == [0]
    assert not result["has_five_cap"]
    assert not result["has_five_cup"]
    assert not result["has_six_cup"]
    assert not result["has_strong_six"]
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
