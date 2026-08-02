#!/usr/bin/env python3
"""Explore cup/cap/strong profiles of recursively deep-below colorings.

This is a research aid: a binary decomposition tree partitions the sweep
indices at every node.  A mixed triple is left exactly when its middle index
belongs to the lower child, matching `HasDeepBelowSplit`.
"""

from __future__ import annotations

import argparse
import itertools
import random
from dataclasses import dataclass


@dataclass(frozen=True)
class Node:
    leaves: frozenset[int]
    lower: "Node | None" = None
    upper: "Node | None" = None


def random_tree(leaves: tuple[int, ...], rng: random.Random) -> Node:
    if len(leaves) == 1:
        return Node(frozenset(leaves))
    shuffled = list(leaves)
    rng.shuffle(shuffled)
    cut = rng.randrange(1, len(leaves))
    lower = random_tree(tuple(shuffled[:cut]), rng)
    upper = random_tree(tuple(shuffled[cut:]), rng)
    return Node(frozenset(leaves), lower, upper)


def turn(node: Node, i: int, j: int, k: int) -> bool:
    """True is left; False is right."""
    assert node.lower is not None and node.upper is not None
    in_lower = (i in node.lower.leaves, j in node.lower.leaves, k in node.lower.leaves)
    if all(in_lower):
        return turn(node.lower, i, j, k)
    if not any(in_lower):
        return turn(node.upper, i, j, k)
    return in_lower[1]


def is_cup(node: Node, subset: tuple[int, ...]) -> bool:
    return all(turn(node, *triple) for triple in itertools.combinations(subset, 3))


def is_cap(node: Node, subset: tuple[int, ...]) -> bool:
    return all(not turn(node, *triple) for triple in itertools.combinations(subset, 3))


def is_strong(node: Node, subset: tuple[int, ...]) -> bool:
    for i, j, k, l in itertools.combinations(subset, 4):
        if turn(node, i, j, k) != turn(node, i, j, l):
            return False
        if turn(node, i, k, l) != turn(node, j, k, l):
            return False
    return True


def is_signotope(node: Node) -> bool:
    """The rank-three signotope law: at most one sign change per four-set."""
    for a, b, c, d in itertools.combinations(sorted(node.leaves), 4):
        values = [
            turn(node, a, b, c),
            turn(node, a, b, d),
            turn(node, a, c, d),
            turn(node, b, c, d),
        ]
        if sum(x != y for x, y in zip(values, values[1:])) > 1:
            return False
    return True


def maxima(node: Node) -> tuple[int, int, int]:
    leaves = tuple(sorted(node.leaves))
    cup = cap = strong = 0
    for size in range(1, len(leaves) + 1):
        for subset in itertools.combinations(leaves, size):
            cup = max(cup, size if is_cup(node, subset) else 0)
            cap = max(cap, size if is_cap(node, subset) else 0)
            strong = max(strong, size if is_strong(node, subset) else 0)
    return cup, cap, strong


def tree_profiles(node: Node) -> tuple:
    if node.lower is None:
        return (tuple(sorted(node.leaves)), maxima(node))
    assert node.upper is not None
    return (tuple(sorted(node.leaves)), maxima(node),
            tree_profiles(node.lower), tree_profiles(node.upper))


def pair_ranks(node: Node, u: int, v: int) -> tuple[int, int]:
    cap = cup = 2
    before = [x for x in node.leaves if x < u]
    for size in range(1, len(before) + 1):
        for prefix in itertools.combinations(before, size):
            chain = tuple(sorted(prefix + (u, v)))
            cap = max(cap, len(chain) if is_cap(node, chain) else 0)
            cup = max(cup, len(chain) if is_cup(node, chain) else 0)
    return cap - 1, cup - 1


def vertex_downset(node: Node, v: int) -> frozenset[tuple[int, int]]:
    result: set[tuple[int, int]] = set()
    for u in sorted(x for x in node.leaves if x < v):
        cap, cup = pair_ranks(node, u, v)
        result.update(itertools.product(range(1, cap + 1), range(1, cup + 1)))
    return frozenset(result)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("--samples", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    best = args.n + 1
    examples: list[tuple[tuple[int, int, int], Node]] = []
    accepted = 0
    for _ in range(args.samples):
        tree = random_tree(tuple(range(args.n)), rng)
        if not is_signotope(tree):
            continue
        accepted += 1
        profile = maxima(tree)
        if profile[2] < best:
            best = profile[2]
            examples = [(profile, tree)]
        elif profile[2] == best and len(examples) < 3:
            examples.append((profile, tree))
    print(f"n={args.n} samples={args.samples} signotopes={accepted} minimum_strong={best}")
    for profile, tree in examples:
        print(profile, tree)
        print(tree_profiles(tree))
        if args.n <= 9:
            print([vertex_downset(tree, v) for v in sorted(tree.leaves)])


if __name__ == "__main__":
    main()
