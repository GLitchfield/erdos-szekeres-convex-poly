#!/usr/bin/env python3
"""Baek–Balko constructions of 2^(k-2) points with no convex k-gon.

Exact rational/integer realizations of

* ``P(a, u)``: the Erdős–Szekeres sets of ``C(a+u-4, a-2)`` points with no
  ``a``-cap and no ``u``-cup (a translated copy of ``P(a, u-1)`` placed to
  the left of and deep below ``P(a-1, u)``);
* ``P(a, u, k)``: the Erdős–Szekeres construction of ``S(a, u, k)`` points
  with no ``a``-cap, no ``u``-cup, and no convex ``k``-gon: clusters
  ``P(k+2-i, i)`` for ``i = k-a+2, ..., u`` on a cup, each deep below the
  next;
* the point set ``M`` of Definition 17 (Baek–Balko, SoCG 2025) and the
  ``x``-blow-up of Definition 13 / Corollary 15, so Theorem 19's new
  ``2^(k-2)``-point sets, plus the classical Valtr blow-ups of Section 6.1
  for an arbitrary base set ``S`` of at most ``k-1`` points.

Every produced set is verified directly and independently of the
construction: general position, cardinality, and the largest convex subset
(computed by the cup/cap chain dynamic programme over a generic sweep order).
The script then answers the Workstream D/E questions for each set: is it
decomposable in some sweep direction, and does it contain a half-sized
subset with no convex ``(k-1)``-gon.

Coordinates are built with ``fractions.Fraction`` and scaled to integers.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import subprocess
import sys
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

Pt = tuple[Fraction, Fraction]


# ---------------------------------------------------------------- geometry

def orient(a, b, c):
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def general_position(points) -> bool:
    return all(orient(a, b, c) != 0 for a, b, c in itertools.combinations(points, 3))


def distinct_x(points) -> bool:
    return len({p[0] for p in points}) == len(points)


def to_integers(points) -> list[tuple[int, int]]:
    denominators = [Fraction(c).denominator for p in points for c in p]
    scale = 1
    for d in denominators:
        scale = scale * d // math.gcd(scale, d)
    result = [(int(Fraction(p[0]) * scale), int(Fraction(p[1]) * scale)) for p in points]
    g = 0
    for x, y in result:
        g = math.gcd(g, abs(x), abs(y))
    if g > 1:
        result = [(x // g, y // g) for x, y in result]
    return result


def generic_direction(points) -> tuple[int, int]:
    """An integer direction with pairwise distinct projections, close to the
    x-axis (so that it agrees with the x-order whenever x-values are
    distinct)."""
    span = max(abs(p[1] - q[1]) for p, q in itertools.combinations(points, 2))
    return (int(span) + 1, 1)


def sweep_order(points, direction):
    keys = [direction[0] * p[0] + direction[1] * p[1] for p in points]
    if len(set(keys)) != len(keys):
        raise ValueError("direction is not generic")
    return sorted(range(len(points)), key=lambda i: keys[i])


def chain_tables(pts):
    """For points sorted along a sweep, longest left-turning (cup) and
    right-turning (cap) chains ending with each edge, and, for every start
    vertex, the longest such chains from that start.  Returns a function
    ``longest(l, r, left)`` giving the longest chain from ``l`` to ``r``."""
    n = len(pts)
    sign = {}
    for i, j, k in itertools.combinations(range(n), 3):
        sign[(i, j, k)] = orient(pts[i], pts[j], pts[k]) > 0
    tables = {}
    for left in (True, False):
        from_start = {}
        for l in range(n):
            best = {}
            for j in range(l + 1, n):
                best[(l, j)] = 2
            for i in range(l + 1, n):
                for j in range(i + 1, n):
                    value = 0
                    for h in range(l, i):
                        if (h, i) in best and sign[(h, i, j)] == left:
                            value = max(value, best[(h, i)] + 1)
                    if value:
                        best[(i, j)] = value
            from_start[l] = best
        tables[left] = from_start

    def longest(l, r, left):
        best = tables[left][l]
        return max((v for (i, j), v in best.items() if j == r), default=0)

    return sign, longest


def largest_convex_subset(points) -> int:
    """Largest number of points in convex position (general position assumed)."""
    n = len(points)
    if n <= 2:
        return n
    order = sweep_order(points, generic_direction(points))
    pts = [points[i] for i in order]
    _, longest = chain_tables(pts)
    best = 3
    for l in range(n):
        for r in range(l + 2, n):
            cup = longest(l, r, True)
            cap = longest(l, r, False)
            if cup and cap:
                best = max(best, cup + cap - 2)
    return best


def longest_cap_cup_x(points) -> tuple[int, int]:
    """Longest cap and cup with respect to the x-sweep (distinct x required)."""
    if not distinct_x(points):
        raise ValueError("x-coordinates are not distinct")
    order = sorted(range(len(points)), key=lambda i: points[i][0])
    pts = [points[i] for i in order]
    _, longest = chain_tables(pts)
    n = len(pts)
    cap = cup = min(n, 2)
    for l in range(n):
        for r in range(l + 1, n):
            cap = max(cap, longest(l, r, False))
            cup = max(cup, longest(l, r, True))
    return cap, cup


def convex_sets_of_size(points, size):
    """All ``size``-subsets in convex position, via the four-point test."""
    n = len(points)
    conv4 = {}
    for q in itertools.combinations(range(n), 4):
        ok = True
        for x in q:
            a, b, c = [points[y] for y in q if y != x]
            s1, s2, s3 = orient(a, b, points[x]), orient(b, c, points[x]), orient(c, a, points[x])
            if (s1 > 0 and s2 > 0 and s3 > 0) or (s1 < 0 and s2 < 0 and s3 < 0):
                ok = False
                break
        conv4[q] = ok
    result = []
    for subset in itertools.combinations(range(n), size):
        if all(conv4[q] for q in itertools.combinations(subset, 4)):
            result.append(subset)
    return result



def convex_polygons_by_chains(points, size):
    """All ``size``-subsets in convex position, enumerated as a cap and a cup
    sharing the first and last vertex of a generic sweep order.

    A convex polygon in general position splits, between its first and last
    vertex along the sweep, into an upper chain (consecutive right turns) and
    a lower chain (consecutive left turns); conversely any right-turning
    chain and left-turning chain with the same endpoints form a convex
    polygon.  Chains are short in a ``k``-gon-free set, so this scales to the
    64-point sets where the four-point test over all subsets does not.
    Returns sorted index tuples in the original indexing."""
    n = len(points)
    if size < 3 or n < size:
        return []
    order = sweep_order(points, generic_direction(points))
    pts = [points[i] for i in order]
    sign = {}
    for i, j, k in itertools.combinations(range(n), 3):
        sign[(i, j, k)] = orient(pts[i], pts[j], pts[k]) > 0
    interior_max = size - 2
    result = []
    for l in range(n):
        ends = {True: {}, False: {}}
        for left in (True, False):
            table = ends[left]
            for r in range(l + 1, n):
                table.setdefault((r, 0), []).append(())
            stack = [(q,) for q in range(l + 1, n)]
            while stack:
                chain = stack.pop()
                m = len(chain)
                prev = chain[-2] if m >= 2 else l
                last = chain[-1]
                for r in range(last + 1, n):
                    if sign[(prev, last, r)] == left:
                        table.setdefault((r, m), []).append(chain)
                if m < interior_max:
                    for q in range(last + 1, n):
                        if sign[(prev, last, q)] == left:
                            stack.append(chain + (q,))
        for r in range(l + 1, n):
            for a in range(interior_max + 1):
                caps = ends[False].get((r, a))
                cups = ends[True].get((r, interior_max - a))
                if not caps or not cups:
                    continue
                for cap in caps:
                    for cup in cups:
                        result.append(tuple(sorted(order[v] for v in (l, r) + cap + cup)))
    return result

# ------------------------------------------------------- deep-below placing

def slopes(points):
    return [(q[1] - p[1]) / (q[0] - p[0]) for p, q in itertools.combinations(points, 2)]


def is_deep_below(A, B) -> bool:
    if max(a[1] for a in A) >= min(b[1] for b in B):
        return False
    for a1, a2 in itertools.combinations(A, 2):
        for b in B:
            if orient(a1, a2, b) * (a2[0] - a1[0]) <= 0:
                # b must be above the line a1 a2 (line oriented left to right)
                if a1[0] == a2[0]:
                    return False
                if orient(a1, a2, b) * (1 if a2[0] > a1[0] else -1) <= 0:
                    return False
    for b1, b2 in itertools.combinations(B, 2):
        for a in A:
            if b1[0] == b2[0]:
                return False
            if orient(b1, b2, a) * (1 if b2[0] > b1[0] else -1) >= 0:
                return False
    return True


def place_left_deep_below(A, B):
    """Translate A so that it lies entirely to the left of and deep below B."""
    if not A:
        return []
    if not B:
        return list(A)
    L = max(a[0] for a in A) - min(b[0] for b in B) + 1
    shifted_x = [(a[0] - L, a[1]) for a in A]
    H = Fraction(0)
    slopes_a = slopes(shifted_x) if len(A) > 1 else []
    for a in shifted_x:
        for b in B:
            for s in slopes_a:
                H = max(H, a[1] - b[1] + s * (b[0] - a[0]))
            H = max(H, a[1] - b[1])
    for b1, b2 in itertools.combinations(B, 2):
        s = (b2[1] - b1[1]) / (b2[0] - b1[0])
        for a in shifted_x:
            H = max(H, a[1] - b1[1] - s * (a[0] - b1[0]))
    H = H + 1
    result = [(a[0], a[1] - H) for a in shifted_x]
    assert is_deep_below(result, B)
    return result


def flatten_scale(points, scale: Fraction, flatten: Fraction):
    """Scale a cluster about its centroid; ``flatten`` multiplies y."""
    if not points:
        return []
    cx = sum(p[0] for p in points) / len(points)
    cy = sum(p[1] for p in points) / len(points)
    return [(cx + (p[0] - cx) * scale, cy + (p[1] - cy) * scale * flatten) for p in points]


def translate(points, center):
    if not points:
        return []
    cx = sum(p[0] for p in points) / len(points)
    cy = sum(p[1] for p in points) / len(points)
    return [(p[0] - cx + center[0], p[1] - cy + center[1]) for p in points]


# ------------------------------------------------- Erdős–Szekeres sets

@lru_cache(maxsize=None)
def es_set(a: int, u: int) -> tuple[Pt, ...]:
    """P(a, u): no a-cap, no u-cup, size C(a+u-4, a-2); empty if a or u is 1."""
    if a <= 1 or u <= 1:
        return ()
    if a == 2 or u == 2:
        return ((Fraction(0), Fraction(0)),)
    right = list(es_set(a - 1, u))
    left = list(es_set(a, u - 1))
    placed = place_left_deep_below(left, right)
    return tuple(placed + right)


def verify_es_set(a: int, u: int) -> dict:
    pts = list(es_set(a, u))
    expected = math.comb(a + u - 4, a - 2) if a >= 2 and u >= 2 else 0
    result = {"a": a, "u": u, "size": len(pts), "expected": expected}
    if pts:
        result["general_position"] = general_position(pts)
        cap, cup = longest_cap_cup_x(pts)
        result["max_cap"] = cap
        result["max_cup"] = cup
        result["ok"] = (len(pts) == expected and result["general_position"]
                        and cap < a and cup < u)
    else:
        result["ok"] = expected == 0
    return result


def stack_on_cup(clusters: list[list[Pt]]) -> list[Pt]:
    """Place tiny flattened copies of the clusters at the vertices of a cup,
    each deep below the next."""
    clusters = [c for c in clusters if c]
    m = len(clusters)
    if m == 0:
        return []
    if m == 1:
        return list(clusters[0])
    H = Fraction(2)
    scale = Fraction(1, 2)
    while True:
        placed = []
        for i, c in enumerate(clusters):
            center = (Fraction(i), H ** i)
            placed.append(translate(flatten_scale(c, scale, Fraction(1)), center))
        ok = all(is_deep_below(placed[i], placed[j])
                 for i in range(m) for j in range(i + 1, m))
        if ok:
            flat = [p for c in placed for p in c]
            if general_position(flat) and distinct_x(flat):
                return flat
        H *= 2
        scale /= 2


@lru_cache(maxsize=None)
def es_set3(a: int, u: int, k: int) -> tuple[Pt, ...]:
    """P(a, u, k): no a-cap, no u-cup, no convex k-gon, size S(a, u, k)."""
    if a <= 1 or u <= 1:
        return ()
    clusters = [list(es_set(k + 2 - i, i)) for i in range(k - a + 2, u + 1)]
    return tuple(stack_on_cup(clusters))


def threshold(a: int, u: int, k: int) -> int:
    if a <= 1 or u <= 1:
        return 0
    return sum(math.comb(k - 2, i - 2) for i in range(k - a + 2, u + 1))


def verify_es_set3(a: int, u: int, k: int) -> dict:
    pts = list(es_set3(a, u, k))
    result = {"a": a, "u": u, "k": k, "size": len(pts), "expected": threshold(a, u, k)}
    if pts:
        result["general_position"] = general_position(pts)
        cap, cup = longest_cap_cup_x(pts)
        result["max_cap"] = cap
        result["max_cup"] = cup
        result["largest_convex"] = largest_convex_subset(pts)
        result["ok"] = (len(pts) == result["expected"] and result["general_position"]
                        and cap < a and cup < u and result["largest_convex"] < k)
    else:
        result["ok"] = result["expected"] == 0
    return result


# ------------------------------------------------ cluster replacement

def replace_by_clusters(base: list[Pt], clusters: list[list[Pt]],
                        vertical: bool) -> list[Pt]:
    """Replace each base point by a tiny copy of its cluster.

    With ``vertical=False`` the copies are flattened (all internal slopes
    tiny), which is the "sufficiently small neighborhood" regime of
    Definition 17: a point of another cluster is above an internal line iff
    it is higher.  With ``vertical=True`` the clusters are rotated clockwise
    by a right angle and squeezed horizontally (Definition 13); the
    conditions of that definition are checked explicitly and the squeeze is
    refined until they hold.
    """
    n = len(base)
    prepared = []
    for c in clusters:
        if vertical:
            prepared.append([(p[1], -p[0]) for p in c])
        else:
            prepared.append(list(c))
    scale = Fraction(1, 4)
    squeeze = Fraction(1, 4)
    for _ in range(80):
        placed = []
        for i, c in enumerate(prepared):
            if not c:
                placed.append([])
                continue
            if vertical:
                shaped = flatten_scale([(p[0] * squeeze, p[1]) for p in c], scale, Fraction(1))
            else:
                shaped = flatten_scale(c, scale, squeeze)
            placed.append(translate(shaped, base[i]))
        if check_cluster_conditions(base, placed, vertical):
            return [p for c in placed for p in c]
        scale /= 4
        squeeze /= 4
    raise RuntimeError("could not satisfy the cluster conditions")


def check_cluster_conditions(base, placed, vertical) -> bool:
    n = len(base)
    flat = [(p, i) for i, c in enumerate(placed) for p in c]
    # triples from three distinct clusters keep the base orientation
    for (p, i), (q, j), (r, l) in itertools.combinations(flat, 3):
        if i != j and j != l and i != l:
            if orient(p, q, r) * orient(base[i], base[j], base[l]) <= 0:
                return False
    # two points in one cluster against a point of another cluster
    for i, c in enumerate(placed):
        for c1, c2 in itertools.combinations(c, 2):
            if vertical:
                lo, hi = (c1, c2) if c1[1] < c2[1] else (c2, c1)
                if lo[1] == hi[1]:
                    return False
            for j, d in enumerate(placed):
                if j == i:
                    continue
                for q in d:
                    o = orient(c1, c2, q)
                    if o == 0:
                        return False
                    if vertical:
                        # q must lie on the same side of the line lo->hi as of the
                        # upward vertical line through base[i]
                        side = orient(lo, hi, q)
                        want = base[j][0] - base[i][0]
                        if side * want >= 0:
                            return False
                    else:
                        # flattened: q is above the internal line iff it is
                        # higher than base[i]
                        left_to_right = (c1, c2) if c1[0] < c2[0] else (c2, c1)
                        above = orient(left_to_right[0], left_to_right[1], q) > 0
                        if above != (base[j][1] > base[i][1]):
                            return False
    return general_position([p for p, _ in flat])


# ------------------------------------------------------- the point set M

def build_M(m: int) -> tuple[list[Pt], list[int]]:
    """Definition 17: returns the points of M (integer-coordinate clusters
    around the skeleton) and the label ``1`` for left points, ``0`` for right."""
    B = Fraction(4 * m + 4)
    eps = Fraction(1, 3)
    ell = [(Fraction(-m + i - 1), B ** (i - 1) - 1) for i in range(1, m)]
    ar = [(Fraction(m - i + 1), B ** (i - 1) - 1 + eps * (1 + Fraction(i, 100)))
          for i in range(1, m)]
    skeleton = ell + ar
    assert general_position(skeleton)
    # combinatorial conditions of Definition 17
    for i in range(2, m - 1):
        for nxt in (ell[i], ar[i]):
            # above the line through the previous two left points (ordered
            # left to right) and above the line through the previous two
            # right points (r_i is left of r_{i-1})
            assert orient(ell[i - 2], ell[i - 1], nxt) > 0
            assert orient(ar[i - 1], ar[i - 2], nxt) > 0
        assert ell[i][0] > ell[i - 2][0] and ell[i][0] < 0
        assert ar[i][0] < ar[i - 1][0] and ar[i][0] > 0
        assert ar[i][1] > ell[i][1]
    clusters = [list(es_set(m - i + 1, i)) for i in range(1, m)] + \
               [list(es_set(m - i, i + 1)) for i in range(1, m)]
    points = replace_by_clusters(skeleton, clusters, vertical=False)
    labels = []
    for i, c in enumerate(clusters):
        labels.extend([1 if i < m - 1 else 0] * len(c))
    return points, labels


def left_right_gon_sizes(points, labels):
    """s_i: largest convex subset having p_i as rightmost (left points) or
    leftmost (right points) vertex."""
    n = len(points)
    order = sweep_order(points, generic_direction(points))
    pts = [points[i] for i in order]
    lab = [labels[i] for i in order]
    _, longest = chain_tables(pts)
    s = [1] * n
    for i in range(n):
        best = 1
        if lab[i] == 1:
            for l in range(i):
                cup, cap = longest(l, i, True), longest(l, i, False)
                if cup and cap:
                    best = max(best, cup + cap - 2)
                elif cup or cap:
                    best = max(best, 2)
        else:
            for r in range(i + 1, n):
                cup, cap = longest(i, r, True), longest(i, r, False)
                if cup and cap:
                    best = max(best, cup + cap - 2)
                elif cup or cap:
                    best = max(best, 2)
        s[i] = best
    # return in original index order
    inverse = [0] * n
    for position, index in enumerate(order):
        inverse[index] = s[position]
    return inverse


# ------------------------------------------------------------- blow-ups

def blow_up(S: list[Pt], X: list[int], Y: list[int], k: int) -> list[Pt]:
    """Definition 13: (X, Y)-blow-up of S with factor k."""
    n = len(S)
    order = sorted(range(n), key=lambda i: S[i][0])
    S = [S[i] for i in order]
    X = [X[i] for i in order]
    Y = [Y[i] for i in order]
    clusters = []
    for i in range(n):
        if i == 0:
            c = list(es_set3(k, X[0] + 2, k))
        elif i == n - 1:
            c = list(es_set3(Y[-1] + 2, k, k))
        else:
            c = list(es_set(Y[i] + 2, X[i] + 2))
        clusters.append(c)
    return replace_by_clusters(S, clusters, vertical=True)


def expected_blow_up_size(X, Y, k) -> int:
    n = len(X)
    return (sum(math.comb(k - 2, l) for l in range(X[0] + 1))
            + sum(math.comb(X[i] + Y[i], X[i]) for i in range(1, n - 1))
            + sum(math.comb(k - 2, l) for l in range(Y[-1] + 1)))


def x_blow_up_parameters(S, labels, x: int, k: int):
    s = left_right_gon_sizes(S, labels)
    X, Y = [], []
    for i in range(len(S)):
        if labels[i] == 1:
            X.append(x)
            Y.append(k - 1 - x - s[i])
        else:
            X.append(k - 1 - x - s[i])
            Y.append(x)
    if min(X) < 0 or min(Y) < 0:
        raise ValueError("negative blow-up parameter")
    return X, Y, s


def valtr_blow_up(S: list[Pt], k: int) -> list[Pt]:
    """Section 6.1: x_i = i-1, y_i = k-i-1 for S sorted by x, |S| <= k-1."""
    n = len(S)
    order = sorted(range(n), key=lambda i: S[i][0])
    S = [S[i] for i in order]
    X = [i for i in range(n)]
    Y = [k - i - 2 for i in range(n)]
    return blow_up(S, X, Y, k)


# ------------------------------------------------- decomposability

class Coloring:
    """Triple coloring on n ordered vertices with the closure-form
    decomposability test (see census_order_type_decomposability.py)."""

    def __init__(self, n, chi):
        self.n = n
        self.chi = chi
        self.edges_cache = {}

    def closed_sets(self, s: int):
        """Nonempty proper subsets L of s closed under the relation forced
        by the crossing law (L is the lower part)."""
        n = self.n
        succ = [0] * n
        members = [v for v in range(n) if s >> v & 1]
        for i, j, k in itertools.combinations(members, 3):
            if self.chi[(i, j, k)]:
                succ[i] |= 1 << j
                succ[k] |= 1 << j
            else:
                succ[j] |= 1 << i
                succ[j] |= 1 << k
        # transitive closure
        closure = list(succ)
        changed = True
        while changed:
            changed = False
            for v in members:
                acc = closure[v]
                m = acc
                while m:
                    w = (m & -m).bit_length() - 1
                    m &= m - 1
                    acc |= closure[w]
                if acc != closure[v]:
                    closure[v] = acc
                    changed = True
        for v in members:
            closure[v] |= 1 << v
        # enumerate down-sets: unions of closures; generate by recursion over
        # members in an order, choosing to include closure[v] or exclude v
        result = set()
        stack = [(0, 0)]
        while stack:
            index, current = stack.pop()
            if index == len(members):
                if current and current != s:
                    result.add(current)
                continue
            v = members[index]
            if current >> v & 1:
                stack.append((index + 1, current))
            else:
                stack.append((index + 1, current))
                stack.append((index + 1, current | closure[v]))
            if len(result) > 200000:
                raise RuntimeError("too many closed sets")
        return result

    def decomposable(self, s: int, memo: dict) -> bool:
        if s & (s - 1) == 0:
            return True
        if s in memo:
            return memo[s]
        answer = False
        for lower in self.closed_sets(s):
            if self.decomposable(lower, memo) and self.decomposable(s ^ lower, memo):
                answer = True
                break
        memo[s] = answer
        return answer


def _angle_class(d):
    """0 for angles in [0, pi), 1 for [pi, 2pi)."""
    return 0 if (d[1] > 0 or (d[1] == 0 and d[0] > 0)) else 1


def _angle_compare(a, b):
    ca, cb = _angle_class(a), _angle_class(b)
    if ca != cb:
        return ca - cb
    cross = a[0] * b[1] - a[1] * b[0]
    return -1 if cross > 0 else (1 if cross < 0 else 0)


def sort_by_angle(directions):
    """Exact counterclockwise angular sort of integer directions."""
    import functools
    return sorted(directions, key=functools.cmp_to_key(_angle_compare))


def sweep_directions(points):
    critical = set()
    for p, q in itertools.combinations(points, 2):
        v = (q[0] - p[0], q[1] - p[1])
        g = math.gcd(abs(v[0]), abs(v[1]))
        perp = (-v[1] // g, v[0] // g)
        critical.add(perp)
        critical.add((-perp[0], -perp[1]))
    ordered = sort_by_angle(critical)
    directions = []
    for a, b in zip(ordered, ordered[1:] + ordered[:1]):
        d = (a[0] + b[0], a[1] + b[1])
        g = math.gcd(abs(d[0]), abs(d[1]))
        directions.append((d[0] // g, d[1] // g))
    return directions


def coloring_for(points, direction):
    order = sweep_order(points, direction)
    pts = [points[i] for i in order]
    chi = {t: orient(pts[t[0]], pts[t[1]], pts[t[2]]) > 0
           for t in itertools.combinations(range(len(pts)), 3)}
    return Coloring(len(pts), chi)


def decomposability_by_direction(points, limit_directions=None):
    directions = sweep_directions(points)
    if limit_directions:
        directions = directions[:limit_directions]
    count = 0
    undecided = 0
    for d in directions:
        col = coloring_for(points, d)
        try:
            if col.decomposable((1 << len(points)) - 1, {}):
                count += 1
        except RuntimeError:
            undecided += 1
    return {"directions": len(directions), "decomposable": count, "undecided": undecided}


# ------------------------------------------------- half supports

def largest_gon_free_subset(points, g: int, target: int, cadical: Path | None, gons=None,
                            time_limit: int | None = None):
    """Find a subset of size >= target with no convex g-gon, by SAT.
    ``gons`` may carry the convex g-gons enumerated by a previous call on the
    same points (index tuples), so that a search over several targets
    enumerates once.  ``time_limit`` (seconds) bounds the solver; a timeout
    is reported as ``found: None``."""
    n = len(points)
    # The chain enumeration is exact and validated against the four-point
    # test (experiment 0111); the subset scan is kept for small sets.
    if gons is None:
        gons = (convex_polygons_by_chains(points, g) if n > 24
                else convex_sets_of_size(points, g))
    if not gons:
        return {"gon_count": 0, "found": True, "subset": list(range(n))}
    clauses = [[-(p + 1) for p in gon] for gon in gons]
    # at least ``target`` true among x_1..x_n via sequential counter on the
    # negations: at most n - target false.
    variables = n
    bound = n - target
    # sequential counter for at most ``bound`` of the literals ¬x_i
    lits = [-(i + 1) for i in range(n)]
    if bound == 0:
        clauses.extend([[-l] for l in lits])
    else:
        s = [[0] * (bound + 1) for _ in range(n)]
        for i in range(n):
            for j in range(1, bound + 1):
                variables += 1
                s[i][j] = variables
        # standard Sinz encoding
        clauses.append([-lits[0], s[0][1]])
        for j in range(2, bound + 1):
            clauses.append([-s[0][j]])
        for i in range(1, n):
            clauses.append([-lits[i], s[i][1]])
            clauses.append([-s[i - 1][1], s[i][1]])
            for j in range(2, bound + 1):
                clauses.append([-lits[i], -s[i - 1][j - 1], s[i][j]])
                clauses.append([-s[i - 1][j], s[i][j]])
            clauses.append([-lits[i], -s[i - 1][bound]])
    cnf = f"p cnf {variables} {len(clauses)}\n" + "".join(
        " ".join(map(str, c)) + " 0\n" for c in clauses)
    if cadical is None:
        return {"gon_count": len(gons), "found": None, "reason": "no solver"}
    command = [str(cadical), "-q"] + (["-t", str(int(time_limit))] if time_limit else [])
    proc = subprocess.run(command, input=cnf, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out = proc.stdout
    if "s UNSATISFIABLE" in out:
        return {"gon_count": len(gons), "found": False}
    if "s SATISFIABLE" not in out:
        return {"gon_count": len(gons), "found": None, "reason": out[:200]}
    model = set()
    for line in out.splitlines():
        if line.startswith("v "):
            for token in line[2:].split():
                v = int(token)
                if 0 < v <= n:
                    model.add(v - 1)
    subset = sorted(model)
    # independent check
    sub_points = [points[i] for i in subset]
    assert len(subset) >= target
    assert largest_convex_subset(sub_points) < g
    return {"gon_count": len(gons), "found": True, "subset": subset}


# ------------------------------------------------------------- driver

def analyze_set(name, points, k, cadical, do_decomposable=True, do_half=True):
    ints = to_integers(points)
    record = {
        "name": name,
        "k": k,
        "size": len(ints),
        "points": [list(p) for p in ints],
        "general_position": general_position(ints),
        "largest_convex": largest_convex_subset(ints),
    }
    record["k_gon_free"] = record["largest_convex"] < k
    record["extremal"] = record["k_gon_free"] and len(ints) == 2 ** (k - 2)
    if do_decomposable:
        record["decomposability"] = decomposability_by_direction(ints)
    if do_half:
        target = (len(ints) + 1) // 2
        record["half_support"] = largest_gon_free_subset(ints, k - 1, target, cadical)
    print(json.dumps({key: value for key, value in record.items() if key != "points"}),
          file=sys.stderr)
    return record


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cadical", type=Path, default=None)
    parser.add_argument("--base-database", type=Path, default=None,
                        help="order-type database used to enumerate base sets S")
    parser.add_argument("--base-n", type=int, default=0)
    parser.add_argument("--base-limit", type=int, default=40,
                        help="scan only this many database entries for base sets")
    parser.add_argument("--skip-decomposable", action="store_true")
    parser.add_argument("--skip-half", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    k = args.k

    checks = []
    if args.self_test:
        for a in range(2, 7):
            for u in range(2, 7):
                checks.append(verify_es_set(a, u))
        for kk in range(3, 7):
            checks.append(verify_es_set3(kk, kk, kk))
        checks.append(verify_es_set3(4, 5, 5))
        checks.append(verify_es_set3(5, 6, 6))
        bad = [c for c in checks if not c["ok"]]
        print(f"self-test: {len(checks)} checks, {len(bad)} failures", file=sys.stderr)
        for c in bad:
            print(c, file=sys.stderr)

    records = []
    do_dec = not args.skip_decomposable
    do_half = not args.skip_half

    # classical Erdős–Szekeres construction
    records.append(analyze_set(f"ES({k},{k},{k})", list(es_set3(k, k, k)), k,
                               args.cadical, do_dec, do_half))

    # Theorem 19: x-blow-ups of M
    for x in range(1, (k - 3) // 2 + 1):
        m = k - 2 * x
        if m < 3:
            continue
        M, labels = build_M(m)
        L = 2 ** (m - 3)
        X, Y, s = x_blow_up_parameters(M, labels, x, k)
        by_x = sorted(range(len(M)), key=lambda i: M[i][0])
        expected = expected_blow_up_size([X[i] for i in by_x], [Y[i] for i in by_x], k)
        v = {}
        for value in s:
            v[value] = v.get(value, 0) + 1
        points = blow_up(M, X, Y, k)
        rec = analyze_set(f"Theorem19(x={x},m={m})", points, k, args.cadical, do_dec, do_half)
        rec["M"] = {"size": len(M), "largest_convex": largest_convex_subset(to_integers(M)),
                    "v_values": v, "expected_size": expected, "X": X, "Y": Y}
        records.append(rec)

    # Valtr blow-ups over base order types S with |S| = k-1
    if args.base_database and args.base_n:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        from census_order_type_decomposability import read_database
        db = read_database(args.base_database, args.base_n)
        seen = set()
        bases = []
        for pts in db[:args.base_limit]:
            for subset in itertools.combinations(range(args.base_n), k - 1):
                sub = [pts[i] for i in subset]
                key = canonical_order_type(sub)
                if key in seen:
                    continue
                seen.add(key)
                bases.append(sub)
        print(f"{len(bases)} base order types of {k - 1} points", file=sys.stderr)
        for index, S in enumerate(bases):
            S = [(Fraction(p[0]), Fraction(p[1])) for p in S]
            if not distinct_x(S):
                S = [(p[0] + p[1] / 1000, p[1]) for p in S]
            points = valtr_blow_up(S, k)
            rec = analyze_set(f"Valtr(S#{index})", points, k, args.cadical, do_dec, do_half)
            rec["base"] = [list(p) for p in to_integers(S)]
            rec["base_largest_convex"] = largest_convex_subset(to_integers(S))
            records.append(rec)

    output = {
        "schema": "erdos-szekeres-baek-balko-constructions-v1",
        "k": k,
        "self_test": checks,
        "records": records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=1, sort_keys=True) + "\n")
    summary = [{key: value for key, value in r.items() if key not in ("points", "M", "base")}
               for r in records]
    print(json.dumps(summary, indent=1, sort_keys=True))


def canonical_order_type(points) -> str:
    """Chirotope up to relabeling and mirror, by brute force (small sets)."""
    n = len(points)
    best = None
    for perm in itertools.permutations(range(n)):
        pts = [points[i] for i in perm]
        for sign in (1, -1):
            word = "".join("+" if sign * orient(pts[i], pts[j], pts[l]) > 0 else "-"
                           for i, j, l in itertools.combinations(range(n), 3))
            if best is None or word < best:
                best = word
    return best


if __name__ == "__main__":
    main()
