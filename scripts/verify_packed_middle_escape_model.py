#!/usr/bin/env python3
"""Directly verify a SAT countermodel to packed middle-split escape."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def triples(vertices):
    return tuple(itertools.combinations(vertices, 3))


def is_strong(vertices, colors) -> bool:
    for i, j, k, l in itertools.combinations(vertices, 4):
        if ((i, j, k) in colors) != ((i, j, l) in colors):
            return False
        if ((i, k, l) in colors) != ((j, k, l) in colors):
            return False
    return True


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("model", type=Path)
    args = parser.parse_args()
    data = json.loads(args.model.read_text())
    n = int(data["n"])
    cut = int(data["cut"])
    mode = data.get("mode", "counterexample")
    colors = {tuple(item) for item in data["left_triples"]}
    selected = [tuple(item) for item in data["selected_deletions"]]
    all_vertices = range(n)
    sixes = tuple(itertools.combinations(all_vertices, 6))

    for i, j, k, l in itertools.combinations(all_vertices, 4):
        word = [
            triple in colors
            for triple in ((i, j, k), (i, j, l), (i, k, l), (j, k, l))
        ]
        if sum(left != right for left, right in zip(word, word[1:])) > 1:
            raise SystemExit(f"one-change failure on {(i, j, k, l)}")
    for side in (range(cut), range(cut, n)):
        for vertices in itertools.combinations(side, 4):
            if all(triple not in colors for triple in triples(vertices)):
                raise SystemExit(f"internal cap four on {vertices}")
    for vertices in itertools.combinations(all_vertices, 5):
        if all(triple not in colors for triple in triples(vertices)):
            raise SystemExit(f"ambient cap five on {vertices}")
    for vertices in sixes:
        if all(triple in colors for triple in triples(vertices)):
            raise SystemExit(f"ambient cup six on {vertices}")

    strong_sixes = [vertices for vertices in sixes if is_strong(vertices, colors)]
    for vertices in strong_sixes:
        left_count = sum(vertex < cut for vertex in vertices)
        if left_count in (0, 6):
            raise SystemExit(f"internal strong six on {vertices}")
    for vertices in itertools.combinations(all_vertices, 7):
        if is_strong(vertices, colors):
            raise SystemExit(f"ambient strong seven on {vertices}")

    uncovered = [
        deleted for deleted in sixes
        if not any(set(deleted).isdisjoint(witness) for witness in strong_sixes)
    ]
    if uncovered:
        raise SystemExit(f"packing failure on {uncovered[0]}")
    if mode == "counterexample" and not selected:
        raise SystemExit("model records no selected bad deletion")
    counterexamples = []
    for deleted in selected:
        disjoint = [
            witness for witness in strong_sixes
            if set(deleted).isdisjoint(witness)
        ]
        extreme = [
            witness for witness in disjoint
            if sum(vertex < cut for vertex in witness) in (1, 5)
        ]
        middle = [
            witness for witness in disjoint
            if sum(vertex < cut for vertex in witness) in (2, 3, 4)
        ]
        if extreme or not middle:
            raise SystemExit(
                f"selected deletion is not a packed middle-only counterexample: {deleted}"
            )
        counterexamples.append({
            "deleted": list(deleted),
            "middle_witness": list(middle[0]),
            "middle_split": sum(vertex < cut for vertex in middle[0]),
        })
    print(json.dumps({
        "valid": True,
        "n": n,
        "cut": cut,
        "mode": mode,
        "strong_sixes": len(strong_sixes),
        "selected_counterexamples": counterexamples,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
