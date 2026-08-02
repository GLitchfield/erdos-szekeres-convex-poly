#!/usr/bin/env python3
"""Independently replay an exact decomposable-coloring enumeration manifest.

Unlike the producer, this checker enumerates all ordered, leaf-labeled full
binary trees and evaluates each triple by descending the tree.  It imports no
producer code.  The resulting coloring set and all profile summaries must
match the supplied manifest exactly.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
import math
from collections import Counter
from pathlib import Path
from typing import TypeAlias


Tree: TypeAlias = int | tuple["Tree", "Tree"]


@functools.cache
def leaf_set(tree: Tree) -> frozenset[int]:
    if isinstance(tree, int):
        return frozenset((tree,))
    return leaf_set(tree[0]) | leaf_set(tree[1])


@functools.cache
def trees(mask: int) -> tuple[Tree, ...]:
    if mask.bit_count() == 1:
        return ((mask & -mask).bit_length() - 1,)
    result: list[Tree] = []
    lower = (mask - 1) & mask
    while lower:
        upper = mask ^ lower
        if upper:
            result.extend((left, right)
                          for left in trees(lower) for right in trees(upper))
        lower = (lower - 1) & mask
    return tuple(result)


def turn(tree: Tree, i: int, j: int, k: int) -> bool:
    if isinstance(tree, int):
        raise ValueError("three distinct leaves cannot descend to a leaf")
    lower, upper = tree
    lower_leaves = leaf_set(lower)
    membership = (i in lower_leaves, j in lower_leaves, k in lower_leaves)
    if all(membership):
        return turn(lower, i, j, k)
    if not any(membership):
        return turn(upper, i, j, k)
    return membership[1]


def coloring(tree: Tree, triple_list: tuple[tuple[int, int, int], ...]) -> int:
    result = 0
    for position, triple in enumerate(triple_list):
        if turn(tree, *triple):
            result |= 1 << position
    return result


def replay_colorings(n: int) -> frozenset[int]:
    """Second exact implementation used when explicit tree replay is too large."""
    triple_list = tuple(itertools.combinations(range(n), 3))

    @functools.cache
    def visit(mask: int) -> frozenset[int]:
        if mask.bit_count() == 1:
            return frozenset((0,))
        answers: set[int] = set()
        lower = (mask - 1) & mask
        while lower:
            upper = lower ^ mask
            if upper:
                fixed = 0
                for index, (i, j, k) in enumerate(triple_list):
                    selected = (1 << i) | (1 << j) | (1 << k)
                    if selected & mask != selected:
                        continue
                    count_lower = (selected & lower).bit_count()
                    if 0 < count_lower < 3 and lower & (1 << j):
                        fixed |= 1 << index
                answers.update(a | b | fixed for a in visit(lower) for b in visit(upper))
            lower = (lower - 1) & mask
        return frozenset(answers)

    return visit((1 << n) - 1)


def catalan(n: int) -> int:
    return math.comb(2 * n, n) // (n + 1)


def bit(bits: int, positions: dict[tuple[int, int, int], int],
        triple: tuple[int, int, int]) -> bool:
    return bool(bits & (1 << positions[triple]))


def strong(bits: int, positions: dict[tuple[int, int, int], int],
           vertices: tuple[int, ...]) -> bool:
    for i, j, k, l in itertools.combinations(vertices, 4):
        if bit(bits, positions, (i, j, k)) != bit(bits, positions, (i, j, l)):
            return False
        if bit(bits, positions, (i, k, l)) != bit(bits, positions, (j, k, l)):
            return False
    return True


def monochromatic(bits: int, positions: dict[tuple[int, int, int], int],
                  vertices: tuple[int, ...], expected: bool) -> bool:
    return all(bit(bits, positions, triple) == expected
               for triple in itertools.combinations(vertices, 3))


def signotope(bits: int, positions: dict[tuple[int, int, int], int], n: int) -> bool:
    for vertices in itertools.combinations(range(n), 4):
        a, b, c, d = vertices
        sequence = (
            bit(bits, positions, (a, b, c)),
            bit(bits, positions, (a, b, d)),
            bit(bits, positions, (a, c, d)),
            bit(bits, positions, (b, c, d)),
        )
        if sum(a != b for a, b in zip(sequence, sequence[1:])) > 1:
            return False
    return True


def maximum(n: int, predicate) -> int:
    for size in range(n, 0, -1):
        if any(predicate(vertices)
               for vertices in itertools.combinations(range(n), size)):
            return size
    raise AssertionError("unreachable")


def parse_tree(value: object) -> Tree:
    if isinstance(value, int):
        return value
    if not isinstance(value, dict) or set(value) != {"lower", "upper"}:
        raise ValueError("invalid tree certificate")
    return parse_tree(value["lower"]), parse_tree(value["upper"])


def normalized_histogram(counter: Counter[int]) -> dict[str, int]:
    return {str(key): counter[key] for key in sorted(counter)}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    if manifest.get("schema_version") != 1:
        parser.error("unsupported manifest schema")
    n = manifest["n"]
    if not isinstance(n, int) or not 1 <= n <= 8:
        parser.error("the independent replay supports 1 <= n <= 8")

    triple_list = tuple(itertools.combinations(range(n), 3))
    positions = {triple: index for index, triple in enumerate(triple_list)}
    full = (1 << n) - 1
    if n <= 7:
        all_trees = trees(full)
        colorings = sorted({coloring(tree, triple_list) for tree in all_trees})
        ordered_tree_count = len(all_trees)
        replay_method = "explicit ordered labeled trees"
    else:
        colorings = sorted(replay_colorings(n))
        ordered_tree_count = math.factorial(n) * catalan(n - 1)
        replay_method = "independent subset recurrence"
    width = max(1, (len(triple_list) + 3) // 4)
    digest = hashlib.sha256(
        "".join(f"{bits:0{width}x}\n" for bits in colorings).encode()).hexdigest()

    strong_histogram: Counter[int] = Counter()
    cup_histogram: Counter[int] = Counter()
    cap_histogram: Counter[int] = Counter()
    cap_strong_histogram: Counter[tuple[int, int]] = Counter()
    cup_strong_histogram: Counter[tuple[int, int]] = Counter()
    signotope_count = 0
    for bits in colorings:
        strong_maximum = maximum(n, lambda s: strong(bits, positions, s))
        cup_maximum = maximum(
            n, lambda s: monochromatic(bits, positions, s, True))
        cap_maximum = maximum(
            n, lambda s: monochromatic(bits, positions, s, False))
        strong_histogram[strong_maximum] += 1
        cup_histogram[cup_maximum] += 1
        cap_histogram[cap_maximum] += 1
        cap_strong_histogram[(cap_maximum, strong_maximum)] += 1
        cup_strong_histogram[(cup_maximum, strong_maximum)] += 1
        signotope_count += int(signotope(bits, positions, n))

    witness = manifest["minimum_witness"]
    witness_tree = parse_tree(witness["tree"])
    witness_bits = int(witness["coloring_hex"], 16)
    witness_ok = (
        leaf_set(witness_tree) == frozenset(range(n))
        and coloring(witness_tree, triple_list) == witness_bits
        and maximum(n, lambda s: strong(witness_bits, positions, s))
            == manifest["minimum_strong_maximum"]
    )
    checks = {
        "distinct_coloring_count": len(colorings) == manifest["distinct_coloring_count"],
        "distinct_colorings_sha256": digest == manifest["distinct_colorings_sha256"],
        "signotope_count": signotope_count == manifest["signotope_count"],
        "strong_maximum_histogram": normalized_histogram(strong_histogram)
            == manifest["strong_maximum_histogram"],
        "cup_maximum_histogram": normalized_histogram(cup_histogram)
            == manifest["cup_maximum_histogram"],
        "cap_maximum_histogram": normalized_histogram(cap_histogram)
            == manifest["cap_maximum_histogram"],
        "cap_strong_joint_histogram": {
            f"{cap},{strong}": count
            for (cap, strong), count in sorted(cap_strong_histogram.items())
        } == manifest["cap_strong_joint_histogram"],
        "cup_strong_joint_histogram": {
            f"{cup},{strong}": count
            for (cup, strong), count in sorted(cup_strong_histogram.items())
        } == manifest["cup_strong_joint_histogram"],
        "minimum_witness": witness_ok,
    }
    result = {
        "manifest": str(args.manifest),
        "n": n,
        "ordered_tree_count": ordered_tree_count,
        "replay_method": replay_method,
        "distinct_coloring_count": len(colorings),
        "checks": checks,
        "ok": all(checks.values()),
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    if not result["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
