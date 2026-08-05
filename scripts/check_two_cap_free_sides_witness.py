#!/usr/bin/env python3
"""Independently check a two-cap-free-sides SAT witness.

This checker intentionally imports no project SAT generator.  A listed triple
is a left turn; every omitted increasing triple is a right turn.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def triples(vertices):
    return tuple(itertools.combinations(vertices, 3))


def is_strong(vertices, left_turns) -> bool:
    for i, j, k, l in itertools.combinations(vertices, 4):
        if (((i, j, k) in left_turns) != ((i, j, l) in left_turns)):
            return False
        if (((i, k, l) in left_turns) != ((j, k, l) in left_turns)):
            return False
    return True


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("witness", type=Path)
    parser.add_argument("--side-cap", type=int, default=4)
    parser.add_argument("--cap", type=int, default=5)
    parser.add_argument("--cup", type=int, default=6)
    parser.add_argument("--strong", type=int, default=7)
    args = parser.parse_args()

    data = json.loads(args.witness.read_text())
    if data.get("schema_version") != 1:
        raise SystemExit("unsupported witness schema")
    n = data["n"]
    cut = data["cut"]
    if not isinstance(n, int) or not isinstance(cut, int) or not 0 < cut < n:
        raise SystemExit("invalid n or cut")
    all_triples = set(triples(range(n)))
    listed = [tuple(value) for value in data["left_triples"]]
    left_turns = set(listed)
    if len(left_turns) != len(listed):
        raise SystemExit("duplicate left triple")
    if not left_turns <= all_triples:
        raise SystemExit("left_triples contains a non-increasing or out-of-range triple")

    for i, j, k, l in itertools.combinations(range(n), 4):
        values = [key in left_turns for key in
                  ((i, j, k), (i, j, l), (i, k, l), (j, k, l))]
        if sum(a != b for a, b in zip(values, values[1:])) > 1:
            raise SystemExit(f"one-change failure on {(i, j, k, l)}")

    for label, side in (("left", range(cut)), ("right", range(cut, n))):
        for vertices in itertools.combinations(side, args.side_cap):
            if all(key not in left_turns for key in triples(vertices)):
                raise SystemExit(f"{label} side has a cap: {vertices}")

    for vertices in itertools.combinations(range(n), args.cap):
        if all(key not in left_turns for key in triples(vertices)):
            raise SystemExit(f"ambient cap: {vertices}")
    for vertices in itertools.combinations(range(n), args.cup):
        if all(key in left_turns for key in triples(vertices)):
            raise SystemExit(f"ambient cup: {vertices}")
    for vertices in itertools.combinations(range(n), args.strong):
        if is_strong(vertices, left_turns):
            raise SystemExit(f"strong subset: {vertices}")

    print(json.dumps({
        "valid": True,
        "n": n,
        "cut": cut,
        "left_turn_triples": len(left_turns),
        "checked_triples": len(all_triples),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
