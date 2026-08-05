#!/usr/bin/env python3
"""Independently verify the fixed pair of crossing `3+3` strong sixes."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


N = 12
CUT = 6
FIRST = (0, 1, 2, 6, 7, 8)
SECOND = (3, 4, 5, 9, 10, 11)


def triples(vertices):
    return tuple(itertools.combinations(vertices, 3))


def parse_model(path: Path, variable_count: int) -> set[int]:
    tokens = []
    for line in path.read_text().splitlines():
        if line.startswith("v "):
            tokens.extend(line.split()[1:])
    assignment = {abs(int(token)): int(token) > 0 for token in tokens if int(token)}
    if set(assignment) != set(range(1, variable_count + 1)):
        raise SystemExit("model does not assign every triple variable exactly once")
    return {index for index, value in assignment.items() if value}


def is_strong(vertices, left_turns) -> bool:
    for i, j, k, l in itertools.combinations(vertices, 4):
        if (((i, j, k) in left_turns) != ((i, j, l) in left_turns)):
            return False
        if (((i, k, l) in left_turns) != ((j, k, l) in left_turns)):
            return False
    return True


def middle_word(vertices, left_turns) -> str:
    return "".join(
        "L" if (vertices[0], middle, vertices[-1]) in left_turns else "R"
        for middle in vertices[1:-1]
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("model", type=Path)
    args = parser.parse_args()
    all_triples = triples(range(N))
    true_variables = parse_model(args.model, len(all_triples))
    left_turns = {triple for index, triple in enumerate(all_triples, start=1)
                  if index in true_variables}

    for i, j, k, l in itertools.combinations(range(N), 4):
        values = [triple in left_turns for triple in
                  ((i, j, k), (i, j, l), (i, k, l), (j, k, l))]
        if sum(a != b for a, b in zip(values, values[1:])) > 1:
            raise SystemExit(f"one-change failure on {(i, j, k, l)}")
    for side in (range(CUT), range(CUT, N)):
        for vertices in itertools.combinations(side, 4):
            if all(triple not in left_turns for triple in triples(vertices)):
                raise SystemExit(f"side cap four on {vertices}")
    for vertices in itertools.combinations(range(N), 5):
        if all(triple not in left_turns for triple in triples(vertices)):
            raise SystemExit(f"ambient cap five on {vertices}")
    for vertices in itertools.combinations(range(N), 6):
        if all(triple in left_turns for triple in triples(vertices)):
            raise SystemExit(f"ambient cup six on {vertices}")
    for vertices in itertools.combinations(range(N), 7):
        if is_strong(vertices, left_turns):
            raise SystemExit(f"ambient strong seven on {vertices}")
    for label, vertices in (("first", FIRST), ("second", SECOND)):
        if not is_strong(vertices, left_turns):
            raise SystemExit(f"{label} fixed polygon is not strong")

    print(json.dumps({
        "valid": True,
        "n": N,
        "cut": CUT,
        "first": FIRST,
        "second": SECOND,
        "first_middle_word": middle_word(FIRST, left_turns),
        "second_middle_word": middle_word(SECOND, left_turns),
        "left_turn_triples": len(left_turns),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
