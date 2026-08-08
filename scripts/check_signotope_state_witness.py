#!/usr/bin/env python3
"""Independently check a SAT witness for a signotope extremal state."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def read_assignment(path: Path) -> dict[int, bool]:
    assignment: dict[int, bool] = {}
    for line in path.read_text().splitlines():
        if not line.startswith("v"):
            continue
        for literal_text in line.split()[1:]:
            literal = int(literal_text)
            if literal:
                assignment[abs(literal)] = literal > 0
    return assignment


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("solution", type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    n = manifest["n"]
    triple_list = tuple(itertools.combinations(range(n), 3))
    position = {triple: index + 1 for index, triple in enumerate(triple_list)}
    assignment = read_assignment(args.solution)
    if set(assignment) != set(range(1, len(triple_list) + 1)):
        parser.error("solution does not assign every triple variable exactly once")

    def left(triple) -> bool:
        return assignment[position[tuple(triple)]]

    bad_quadruples = []
    for a, b, c, d in itertools.combinations(range(n), 4):
        sequence = (left((a, b, c)), left((a, b, d)),
                    left((a, c, d)), left((b, c, d)))
        if sum(x != y for x, y in zip(sequence, sequence[1:])) > 1:
            bad_quadruples.append((a, b, c, d))

    caps = [vertices for vertices in itertools.combinations(range(n), manifest["cap"])
            if all(not left(t) for t in itertools.combinations(vertices, 3))]
    cups = [vertices for vertices in itertools.combinations(range(n), manifest["cup"])
            if all(left(t) for t in itertools.combinations(vertices, 3))]

    strong_sets = []
    for vertices in itertools.combinations(range(n), manifest["strong"]):
        strong = True
        for i, j, k, l in itertools.combinations(vertices, 4):
            if left((i, j, k)) != left((i, j, l)):
                strong = False
                break
            if left((i, k, l)) != left((j, k, l)):
                strong = False
                break
        if strong:
            strong_sets.append(vertices)

    forced_blocks = manifest.get("forced_blocks", [])
    bad_forced_blocks = [
        tuple(vertices)
        for vertices in forced_blocks
        if not all(left(triple) for triple in itertools.combinations(vertices, 3))
    ]
    forced_cap_blocks = manifest.get("forced_cap_blocks", [])
    bad_forced_cap_blocks = [
        tuple(vertices)
        for vertices in forced_cap_blocks
        if not all(not left(triple) for triple in itertools.combinations(vertices, 3))
    ]

    forced_split = manifest.get("forced_singleton_lower_split")
    bad_root_crossings = []
    if forced_split is not None:
        root = forced_split["root"]
        upper = set(forced_split["upper"])
        if upper | {root} != set(range(n)) or root in upper:
            parser.error("forced singleton split does not partition the vertices")
        for triple in itertools.combinations(range(n), 3):
            if root not in triple:
                continue
            expected = triple[1] == root
            if left(triple) != expected:
                bad_root_crossings.append(triple)

    checks = {
        "one_change": not bad_quadruples,
        "no_cap": not caps,
        "no_cup": not cups,
        "no_strong": not strong_sets,
        "forced_cup_blocks": not bad_forced_blocks,
        "forced_cap_blocks": not bad_forced_cap_blocks,
        "forced_singleton_lower_split": not bad_root_crossings,
    }
    result = {
        "schema_version": 1,
        "manifest": str(args.manifest),
        "solution": str(args.solution),
        "checks": checks,
        "ok": all(checks.values()),
        "coloring_hex": format(sum(
            (1 << (variable - 1)) for variable, value in assignment.items() if value),
            f"0{max(1, (len(triple_list) + 3) // 4)}x"),
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    if not result["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
