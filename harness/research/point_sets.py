"""Exact primitives for finite planar point sets with integer (or rational) coordinates.

Everything here is exact arithmetic on Python ints/Fractions: orientation tests, general position, convex
position ("no point of the set lies inside a triangle of three others", valid in general position), the
convex k-subsets, the sweep-order chirotope key (compatible with signotope_sat.key_of: triples of the x-sorted
points in itertools.combinations order, '1' = left turn = cup), and the bipartition test behind SPLIT(k):
does a k-gon-free set split into two (k-1)-gon-free sets?  No solver, no floating point, no Lean.

Promoted 2026-10-10 from runs/claude-halving-20261008/verify_points.py (the independent verifier of the
16-point SPLIT(6) counterexample).  Shares no code with the signotope/SAT side on purpose: it is the check
that a claimed realization is what it claims from the coordinates alone.
"""
from __future__ import annotations

import itertools
from fractions import Fraction
from math import lcm
from typing import Iterable, Sequence

Point = tuple[int, int]


def orient(p: Point, q: Point, r: Point) -> int:
    """Twice the signed area of pqr: > 0 for a left turn (counter-clockwise)."""
    return (q[0] - p[0]) * (r[1] - p[1]) - (r[0] - p[0]) * (q[1] - p[1])


def in_triangle(p: Point, a: Point, b: Point, c: Point) -> bool:
    """Strictly inside the triangle abc (general position assumed)."""
    s1, s2, s3 = orient(a, b, p), orient(b, c, p), orient(c, a, p)
    return (s1 > 0 and s2 > 0 and s3 > 0) or (s1 < 0 and s2 < 0 and s3 < 0)


def general_position(points: Sequence[Point]) -> bool:
    """Distinct points, no three collinear."""
    if len(set(points)) != len(points):
        return False
    return all(orient(points[a], points[b], points[c]) != 0 for a, b, c in itertools.combinations(range(len(points)), 3))


def convex_position(points: Sequence[Point]) -> bool:
    """All points are vertices of their convex hull (general position assumed)."""
    m = len(points)
    for i in range(m):
        others = [j for j in range(m) if j != i]
        for a, b, c in itertools.combinations(others, 3):
            if in_triangle(points[i], points[a], points[b], points[c]):
                return False
    return True


def convex_subsets(points: Sequence[Point], k: int) -> list[tuple[int, ...]]:
    """Index tuples of the k-subsets in convex position."""
    return [S for S in itertools.combinations(range(len(points)), k) if convex_position([points[i] for i in S])]


def sweep_order(points: Sequence[Point]) -> list[int]:
    """Indices sorted by x (then y); callers needing a sweep must have distinct x-coordinates."""
    return sorted(range(len(points)), key=lambda i: (points[i][0], points[i][1]))


def sweep_key(points: Sequence[Point]) -> str:
    """Chirotope key of the x-sorted points: one character per triple in itertools.combinations order,
    '1' when the triple turns left (a cup), as in signotope_sat.key_of."""
    P = [points[i] for i in sweep_order(points)]
    return ''.join('1' if orient(P[a], P[b], P[c]) > 0 else '0' for a, b, c in itertools.combinations(range(len(P)), 3))


def gon_free_bipartition(n: int, gons: Iterable[tuple[int, ...]]) -> int | None:
    """Bitmask A (point n-1 always outside A) such that neither A nor its complement contains one of the
    given index sets, or None if every bipartition has a side containing one.  Brute force over 2^(n-1)."""
    masks = [sum(1 << i for i in S) for S in gons]
    full = (1 << n) - 1
    for A in range(1 << (n - 1)):
        B = full & ~A
        if all((m & A) != m and (m & B) != m for m in masks):
            return A
    return None


def check_split_counterexample(points: Sequence[Point], k: int) -> dict:
    """Report whether `points` is a k-gon-free set that is NOT a union of two (k-1)-gon-free sets.
    Returns general_position, counts of convex k- and (k-1)-subsets, the bipartition found (mask) or None,
    and `counterexample` = general position and no k-gon and no bipartition."""
    gp = general_position(points)
    kg = convex_subsets(points, k) if gp else []
    sm = convex_subsets(points, k - 1) if gp else []
    bip = gon_free_bipartition(len(points), sm) if gp and not kg else None
    return {'n': len(points), 'k': k, 'general_position': gp, 'convex_k_sets': len(kg), 'convex_km1_sets': len(sm),
            'bipartition': bip, 'counterexample': gp and not kg and bip is None}


def integer_points(xs: Sequence[float], ys: Sequence[float], scale: int | None = None,
                   key: str | None = None, max_digits: int = 12) -> list[Point] | None:
    """Round float coordinates to integers.  With `scale`, multiply and round.  Otherwise try scales 10^3..10^max_digits
    and return the first whose points are distinct, in general position and (if `key` is given) have that sweep key.
    Exact fallback: `rational_points`."""
    if scale is not None:
        return [(round(x * scale), round(y * scale)) for x, y in zip(xs, ys)]
    for d in range(3, max_digits + 1):
        P = [(round(x * 10 ** d), round(y * 10 ** d)) for x, y in zip(xs, ys)]
        if general_position(P) and (key is None or sweep_key(P) == key):
            return P
    return None


def rational_points(xs: Sequence[float], ys: Sequence[float], max_den: int = 10 ** 12) -> list[Point]:
    """Exact integer points from floats via limit_denominator and a common denominator (large coordinates)."""
    X = [Fraction(float(v)).limit_denominator(max_den) for v in xs]
    Y = [Fraction(float(v)).limit_denominator(max_den) for v in ys]
    L = 1
    for v in X + Y:
        L = lcm(L, v.denominator)
    return [(int(x * L), int(y * L)) for x, y in zip(X, Y)]
