#!/usr/bin/env python3
"""Independently verify a repeated-residue SAT assignment.

This checker imports no generator code.  DIMACS variables enumerate increasing
triples lexicographically; positive variables are left turns.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def triples(vertices):
    return tuple(itertools.combinations(vertices, 3))


def parse_model(path, variable_count):
    tokens = []
    for line in path.read_text().splitlines():
        if line.startswith("v "):
            tokens.extend(line.split()[1:])
    assignment = {abs(int(token)): int(token) > 0 for token in tokens
                  if int(token)}
    if set(assignment) != set(range(1, variable_count + 1)):
        raise SystemExit("model does not assign every triple variable exactly once")
    return {index for index, value in assignment.items() if value}


def is_strong(vertices, left_turns):
    for i, j, k, l in itertools.combinations(vertices, 4):
        if (((i, j, k) in left_turns) != ((i, j, l) in left_turns)):
            return False
        if (((i, k, l) in left_turns) != ((j, k, l) in left_turns)):
            return False
    return True


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", choices=("cap", "strong"), required=True)
    parser.add_argument("--external-count", type=int, required=True)
    parser.add_argument("--side-size", type=int)
    parser.add_argument("--no-side-strong-six", action="store_true")
    parser.add_argument("model", type=Path)
    args = parser.parse_args()
    if args.external_count < 2:
        parser.error("external-count must be at least two")

    residue_count = 3 if args.case == "cap" else 5
    side_count = args.side_size if args.side_size is not None else residue_count
    if side_count < residue_count:
        parser.error("side-size is smaller than the requested residue")
    n = args.external_count + side_count
    external = tuple(range(args.external_count))
    side = tuple(range(args.external_count, n))
    residue = side[:residue_count]
    all_triples = triples(range(n))
    true_variables = parse_model(args.model, len(all_triples))
    left_turns = {triple for index, triple in enumerate(all_triples, start=1)
                  if index in true_variables}

    for i, j, k, l in itertools.combinations(range(n), 4):
        values = [triple in left_turns for triple in
                  ((i, j, k), (i, j, l), (i, k, l), (j, k, l))]
        if sum(a != b for a, b in zip(values, values[1:])) > 1:
            raise SystemExit(f"one-change failure on {(i, j, k, l)}")

    for block in (external, side):
        for vertices in itertools.combinations(block, 4):
            if all(triple not in left_turns for triple in triples(vertices)):
                raise SystemExit(f"side cap four on {vertices}")
    for vertices in itertools.combinations(range(n), 5):
        if all(triple not in left_turns for triple in triples(vertices)):
            raise SystemExit(f"ambient cap five on {vertices}")
    for vertices in itertools.combinations(range(n), 6):
        if all(triple in left_turns for triple in triples(vertices)):
            raise SystemExit(f"ambient cup six on {vertices}")
    for vertices in itertools.combinations(range(n), 7):
        if is_strong(vertices, left_turns):
            raise SystemExit(f"ambient strong seven on {vertices}")
    if args.no_side_strong_six:
        for vertices in itertools.combinations(side, 6):
            if is_strong(vertices, left_turns):
                raise SystemExit(f"side strong six on {vertices}")

    for q in external:
        witness = tuple(sorted((q, *residue)))
        if args.case == "cap":
            if any(triple in left_turns for triple in triples(witness)):
                raise SystemExit(f"fixed cap residue fails at {q}")
        elif not is_strong(witness, left_turns):
            raise SystemExit(f"fixed strong residue fails at {q}")

    print(json.dumps({
        "valid": True,
        "case": args.case,
        "external_count": args.external_count,
        "side_count": side_count,
        "n": n,
        "left_turn_triples": len(left_turns),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
