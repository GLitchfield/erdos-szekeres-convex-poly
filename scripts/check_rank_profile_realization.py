#!/usr/bin/env python3
"""Independently check the rational realizations in RankProfileCollision.lean."""

from fractions import Fraction
from itertools import combinations
import json


LEFT_Y = (
    Fraction(0), Fraction(-1765, 112), Fraction(5, 8), Fraction(23, 16),
    Fraction(131, 28), Fraction(17, 16), Fraction(281, 56),
    Fraction(91, 16), Fraction(0),
)
RIGHT_Y = (
    Fraction(0), Fraction(-334, 21), Fraction(1, 3), Fraction(1),
    Fraction(86, 21), Fraction(1, 3), Fraction(29, 7),
    Fraction(14, 3), Fraction(0),
)

LEFT_HEX = "03c300c1a000000c1adff"
RIGHT_HEX = "03c700c1a000000c1adff"
UPPER = frozenset(range(9)) - {1}

LEFT_TREE = (
    1,
    (
        (8, (((5, 0), 2), 3)),
        ((7, 6), 4),
    ),
)
RIGHT_TREE = (
    1,
    (
        (((8, 0), (5, 2)), 3),
        ((7, 6), 4),
    ),
)


def determinant(i, j, k, ordinates):
    """Orientation determinant for points (index, ordinate)."""
    return (j - i) * (ordinates[k] - ordinates[i]) - (
        ordinates[j] - ordinates[i]
    ) * (k - i)


def coloring_from_points(ordinates):
    coloring = {}
    bits = 0
    margins = []
    for position, triple in enumerate(combinations(range(9), 3)):
        value = determinant(*triple, ordinates)
        assert value != 0
        coloring[triple] = value > 0
        bits |= int(value > 0) << position
        margins.append(abs(value))
    return coloring, f"{bits:021x}", min(margins)


def leaves(tree):
    if isinstance(tree, int):
        return frozenset({tree})
    return leaves(tree[0]) | leaves(tree[1])


def tree_turn(tree, triple):
    if isinstance(tree, int):
        return False
    lower, upper = tree
    lower_vertices = leaves(lower)
    upper_vertices = leaves(upper)
    if all(vertex in lower_vertices for vertex in triple):
        return tree_turn(lower, triple)
    if all(vertex in upper_vertices for vertex in triple):
        return tree_turn(upper, triple)
    return triple[1] in lower_vertices


def assert_tree_matches(tree, coloring):
    assert leaves(tree) == frozenset(range(9))
    assert all(tree_turn(tree, triple) == turn for triple, turn in coloring.items())


def is_strong_six(coloring, vertices):
    for a, b, c, d in combinations(vertices, 4):
        if coloring[a, b, c] != coloring[a, b, d]:
            return False
        if coloring[a, c, d] != coloring[b, c, d]:
            return False
    return True


def pair_ranks(coloring, vertices, clip=4):
    ranks = {}
    ordered = sorted(vertices)
    for index, u in enumerate(ordered):
        for v in ordered[index + 1 :]:
            left = right = 1
            for w in ordered:
                if w >= u:
                    break
                predecessor = ranks.get((w, u))
                if predecessor is None:
                    continue
                if coloring[w, u, v]:
                    left = max(left, min(clip, predecessor[0] + 1))
                else:
                    right = max(right, min(clip, predecessor[1] + 1))
            ranks[u, v] = left, right
    return ranks


def main():
    left, left_hex, left_margin = coloring_from_points(LEFT_Y)
    right, right_hex, right_margin = coloring_from_points(RIGHT_Y)
    assert left_hex == LEFT_HEX
    assert right_hex == RIGHT_HEX
    assert left_margin == 1
    assert right_margin == 1
    assert_tree_matches(LEFT_TREE, left)
    assert_tree_matches(RIGHT_TREE, right)
    assert not any(is_strong_six(left, subset) for subset in combinations(range(9), 6))
    assert not any(is_strong_six(right, subset) for subset in combinations(range(9), 6))
    assert pair_ranks(left, UPPER) == pair_ranks(right, UPPER)
    left_parent = pair_ranks(left, frozenset(range(9)))
    right_parent = pair_ranks(right, frozenset(range(9)))
    assert left_parent[5, 8] == (2, 4)
    assert right_parent[5, 8] == (2, 3)
    assert left_parent != right_parent
    print(json.dumps({
        "left_hex": left_hex,
        "right_hex": right_hex,
        "minimum_absolute_determinant": 1,
        "child_pair_rank_state_equal": True,
        "parent_pair_rank_state_equal": False,
        "open_at_six": True,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
