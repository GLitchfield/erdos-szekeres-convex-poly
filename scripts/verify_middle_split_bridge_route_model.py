#!/usr/bin/env python3
"""Independently check a middle-split bridge-route SAT model.

This checker imports no CNF generator. It directly checks the geometric-order
color conditions, fixed strong sixes, and the selected route-negation claim.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

from verify_middle_split_pair_model import (
    CUT,
    FIRST,
    N,
    SECOND,
    is_strong,
    middle_word,
    parse_model,
    triples,
)


ROUTES = ("no-shared-first", "no-shared-second", "no-shared-both", "no-extreme")
FIRST_INTERIOR_PROBES = (3, 4, 5)
SECOND_INTERIOR_PROBES = (6, 7, 8)


def common_frames(reference, probes, left_turns):
    result = []
    for x, y, z in itertools.combinations(reference, 3):
        if not all((x < q < y < z) or (x < y < q < z) for q in probes):
            continue
        frame_color = (x, y, z) in left_turns
        if all(((x, q, z) in left_turns) == frame_color for q in probes):
            result.append((x, y, z))
    return result


def extreme_strong_sixes(left_turns):
    return [
        vertices
        for vertices in itertools.combinations(range(N), 6)
        if sum(vertex < CUT for vertex in vertices) in (1, 5)
        and is_strong(vertices, left_turns)
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("model", type=Path)
    parser.add_argument("--route", required=True, choices=ROUTES)
    args = parser.parse_args()

    all_triples = triples(range(N))
    true_variables = parse_model(args.model, len(all_triples))
    left_turns = {
        triple
        for index, triple in enumerate(all_triples, start=1)
        if index in true_variables
    }

    for i, j, k, l in itertools.combinations(range(N), 4):
        values = [
            triple in left_turns
            for triple in ((i, j, k), (i, j, l), (i, k, l), (j, k, l))
        ]
        if sum(first != second for first, second in zip(values, values[1:])) > 1:
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

    first_shared = common_frames(FIRST, FIRST_INTERIOR_PROBES, left_turns)
    second_shared = common_frames(SECOND, SECOND_INTERIOR_PROBES, left_turns)
    extreme = extreme_strong_sixes(left_turns)
    route_valid = {
        "no-shared-first": not first_shared,
        "no-shared-second": not second_shared,
        "no-shared-both": not first_shared and not second_shared,
        "no-extreme": not extreme,
    }[args.route]
    if not route_valid:
        raise SystemExit(f"route negation failed for {args.route}")

    print(json.dumps({
        "valid": True,
        "route": args.route,
        "first_middle_word": middle_word(FIRST, left_turns),
        "second_middle_word": middle_word(SECOND, left_turns),
        "first_shared_frames": first_shared,
        "second_shared_frames": second_shared,
        "extreme_strong_sixes": extreme,
        "left_turn_triples": len(left_turns),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
