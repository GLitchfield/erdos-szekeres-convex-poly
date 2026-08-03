#!/usr/bin/env python3
"""Independently check the compact k=6 all-gap collision certificate.

The checker imports no producer code and does not trust the producer's search
counts.  It reconstructs both colorings from their explicit decomposition
trees and recomputes the complete child and parent profiles directly.
"""

from __future__ import annotations

import argparse
import functools
import itertools
import json
from pathlib import Path
from typing import TypeAlias


Tree: TypeAlias = int | tuple["Tree", "Tree"]


def parse_tree(value: object) -> Tree:
    if isinstance(value, int):
        return value
    if not isinstance(value, dict) or set(value) != {"lower", "upper"}:
        raise ValueError("invalid tree certificate")
    return parse_tree(value["lower"]), parse_tree(value["upper"])


@functools.cache
def leaves(tree: Tree) -> frozenset[int]:
    if isinstance(tree, int):
        return frozenset((tree,))
    answer = leaves(tree[0]) | leaves(tree[1])
    if len(answer) != len(leaves(tree[0])) + len(leaves(tree[1])):
        raise ValueError("tree children overlap")
    return answer


def turn(tree: Tree, i: int, j: int, k: int) -> bool:
    if isinstance(tree, int):
        raise ValueError("three distinct leaves reached a singleton")
    lower, upper = tree
    memberships = (i in leaves(lower), j in leaves(lower), k in leaves(lower))
    if all(memberships):
        return turn(lower, i, j, k)
    if not any(memberships):
        return turn(upper, i, j, k)
    return memberships[1]


def coloring(tree: Tree, triples: tuple[tuple[int, int, int], ...]) -> int:
    answer = 0
    for position, triple in enumerate(triples):
        if set(triple) <= leaves(tree) and turn(tree, *triple):
            answer |= 1 << position
    return answer


def strong(bits: int, positions: dict[tuple[int, int, int], int], chain) -> bool:
    for a, b, c, d in itertools.combinations(chain, 4):
        if bool(bits & (1 << positions[(a, b, c)])) != bool(
                bits & (1 << positions[(a, b, d)])):
            return False
        if bool(bits & (1 << positions[(a, c, d)])) != bool(
                bits & (1 << positions[(b, c, d)])):
            return False
    return True


def profile(bits: int, vertices: tuple[int, ...], n: int, k: int,
            positions: dict[tuple[int, int, int], int]) -> tuple[tuple[int, ...], ...]:
    maxima = [[0] * 6 for _ in range(n + 1)]
    has_strong = False
    for size in range(1, min(k, len(vertices)) + 1):
        for chain in itertools.combinations(vertices, size):
            triple_positions = tuple(
                positions[triple] for triple in itertools.combinations(chain, 3)
            )
            cup = all(bits & (1 << position) for position in triple_positions)
            cap = all(not bits & (1 << position) for position in triple_positions)
            if size == k:
                has_strong |= strong(bits, positions, chain)
            for gap in range(n + 1):
                relation = 0 if gap <= chain[0] else 1 if gap > chain[-1] else 2
                if cup:
                    maxima[gap][relation] = max(maxima[gap][relation], size)
                if cap:
                    maxima[gap][3 + relation] = max(maxima[gap][3 + relation], size)
    return tuple(tuple(row) + (int(has_strong),) for row in maxima)


def signotope(bits: int, vertices: tuple[int, ...], positions) -> bool:
    for a, b, c, d in itertools.combinations(vertices, 4):
        sequence = (
            bool(bits & (1 << positions[(a, b, c)])),
            bool(bits & (1 << positions[(a, b, d)])),
            bool(bits & (1 << positions[(a, c, d)])),
            bool(bits & (1 << positions[(b, c, d)])),
        )
        if sum(x != y for x, y in zip(sequence, sequence[1:])) > 1:
            return False
    return True


def check(certificate: dict[str, object]) -> dict[str, object]:
    if certificate.get("schema_version") != 1:
        raise ValueError("unsupported schema")
    n = certificate["n"]
    k = certificate["k"]
    if (n, k) != (9, 6):
        raise ValueError("this checker supports only the targeted (n,k)=(9,6) certificate")
    lower_mask = int(certificate["lower_mask_hex"], 16)
    upper_mask = int(certificate["upper_mask_hex"], 16)
    full_mask = (1 << n) - 1
    triples = tuple(itertools.combinations(range(n), 3))
    positions = {triple: index for index, triple in enumerate(triples)}
    upper_vertices = tuple(i for i in range(n) if upper_mask & (1 << i))
    full_vertices = tuple(range(n))
    expected_child_profile = tuple(
        tuple(row) for row in certificate["equal_upper_all_gap_profile"]
    )

    checks: dict[str, bool] = {
        "root_partition": lower_mask == 1 << 1 and lower_mask | upper_mask == full_mask
            and lower_mask & upper_mask == 0,
    }
    computed: list[tuple[tuple[tuple[int, ...], ...], tuple[tuple[int, ...], ...]]] = []
    for name in ("left", "right"):
        entry = certificate[name]
        upper_tree = parse_tree(entry["upper_tree"])
        parent_tree: Tree = (1, upper_tree)
        upper_bits = int(entry["upper_coloring_hex"], 16)
        parent_bits = int(entry["parent_coloring_hex"], 16)
        upper_profile = profile(upper_bits, upper_vertices, n, k, positions)
        parent_profile = profile(parent_bits, full_vertices, n, k, positions)
        computed.append((upper_profile, parent_profile))
        checks[f"{name}_upper_tree_leaves"] = leaves(upper_tree) == frozenset(upper_vertices)
        checks[f"{name}_upper_tree_coloring"] = coloring(upper_tree, triples) == upper_bits
        checks[f"{name}_parent_tree_leaves"] = leaves(parent_tree) == frozenset(full_vertices)
        checks[f"{name}_parent_tree_coloring"] = coloring(parent_tree, triples) == parent_bits
        checks[f"{name}_child_profile"] = upper_profile == expected_child_profile
        checks[f"{name}_parent_profile"] = parent_profile == tuple(
            tuple(row) for row in entry["parent_profile"])
        checks[f"{name}_open"] = all(row[-1] == 0 for row in parent_profile)
        checks[f"{name}_signotope"] = signotope(parent_bits, full_vertices, positions)

    left_child, left_parent = computed[0]
    right_child, right_parent = computed[1]
    checks["equal_child_all_gap_profiles"] = left_child == right_child
    checks["unequal_parent_all_gap_profiles"] = left_parent != right_parent
    difference = certificate["first_difference"]
    gap = difference["gap"]
    checks["first_difference"] = (
        all(left_parent[i] == right_parent[i] for i in range(gap))
        and left_parent[gap] != right_parent[gap]
        and list(left_parent[gap]) == difference["left"]
        and list(right_parent[gap]) == difference["right"]
    )
    return {"checks": checks, "ok": all(checks.values())}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    result = check(json.loads(args.certificate.read_text()))
    result["certificate"] = str(args.certificate)
    print(json.dumps(result, indent=2, sort_keys=True))
    if not result["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
