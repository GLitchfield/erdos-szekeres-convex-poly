"""All deep-below root cuts of a complete ordered triple coloring.

Retained source: runs/r25-sol-20261003/root_cut_graph.py; paper argument in
BDL-OBSTRUCTION.md sections39/64. True means cup. This is diagnostic arithmetic,
not a Lean certificate that the coloring or the children are decomposable.

A cup triple directs its endpoints to its middle, a cap directs its middle
to both endpoints. Lower root parts are exactly proper nonempty successor-
closed vertex sets. The SCC order has width at most two: any three allegedly
incomparable components have a triple giving an arrow between two of them.
Thus every root is the union of at most two principal reachability sets.
Every SCC transversal is strong. Its internal cup representatives collapse
to one component, and its internal cap representatives do likewise; hence
any complete coloring has at most four SCCs and four proper root cuts.
"""
from __future__ import annotations

from collections.abc import Mapping
from itertools import combinations
from .triple_metrics import validate_coloring

Triple = tuple[int, int, int]
Profile = tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]


def graph_profile(colors: Mapping[Triple, bool], n: int) -> Profile:
    """Return adjacency, reflexive reachability, SCC masks (immutable tuples).

    Input is complete on range(n), including the empty map for n<3. No
    one-change, realizability, or hereditary-decomposition check is performed.
    The caller owns resource guards and storage. Uses O(n^3) triple/bitset
    operations and O(n^2) bits for graph tables, besides the supplied input.
    SCCs are ordered by their smallest vertex, not topologically.
    """
    validate_coloring(colors, n)
    adjacency = [1 << x for x in range(n)]
    for (a, b, c), cup in colors.items():
        if cup:
            adjacency[a] |= 1 << b
            adjacency[c] |= 1 << b
        else:
            adjacency[b] |= (1 << a) | (1 << c)
    reachability = adjacency.copy()
    # Same bitset Floyd step as scripts/enumerate_local_constraint_hierarchy.py.
    for middle in range(n):
        middle_bit = 1 << middle
        for source in range(n):
            if reachability[source] & middle_bit:
                reachability[source] |= reachability[middle]
    remaining = (1 << n) - 1
    components = []
    while remaining:
        x = (remaining & -remaining).bit_length() - 1
        component = sum(1 << y for y in range(n)
                        if remaining >> y & 1
                        and reachability[x] >> y & 1
                        and reachability[y] >> x & 1)
        components.append(component)
        remaining &= ~component
    return tuple(adjacency), tuple(reachability), tuple(components)


def root_masks(colors: Mapping[Triple, bool], n: int) -> tuple[int, ...]:
    """Return every proper nonempty valid lower root part, as sorted bitmasks.

    Exact for arbitrary complete Boolean triple colorings; a listed root's
    children need not themselves be decomposable. There are at most four roots;
    the one/two-principal candidate family also has constant size.
    """
    _, reachability, components = graph_profile(colors, n)
    principals = {reachability[(C & -C).bit_length() - 1] for C in components}
    candidates = set(principals)
    candidates.update(a | b for a, b in combinations(principals, 2))
    return tuple(sorted(candidates - {0, (1 << n) - 1}))
