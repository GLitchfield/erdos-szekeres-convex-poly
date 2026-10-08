"""Charts (topes) of a one-change colouring, circuits, hull vertices, chart flips and radial re-sweeps; colouring keys.

Promoted 2026-10-08 from runs/claude-tope-probe-20261007/tope_cover.py, runs/claude-antipodal-flips-20261007/flips.py
and runs/claude-positive-split-20261007/fslib.py.  Diagnostic Python, not Lean.

A one-change colouring chi on [n] (sorted triples -> True cup / False cap) is an acyclic rank-3 chirotope.  For a
4-set a<b<c<d its circuit is C = (chi(bcd), -chi(acd), chi(abd), -chi(abc)) with chi read as +-1.  A chart (tope) is
a sign vector s with sum_{x in Q} C_x s_x != +-4 for every 4-set Q; there are n(n-1)/2 + 1 charts up to global sign
(the cells of the dual arrangement), and the reference chart is s = (+,...,+).  A 4-set is convex in chart s iff
its circuit sum is 0; otherwise the odd sign is its inner point.  A k-set is convex in chart s iff all its 4-subsets are.
p is a hull vertex iff p is the inner point of no 4-set; flipping s_p is then a chart (X^p, p moved across infinity).
Radial re-sweep (brief G, lemma L2): for a hull vertex p, order the other points by x <_p y iff o(p,x,y) = +1; the
listing "p, then the rest in that order" coloured by the alternating orientation o is again one-change, with p first
and every (p,x,y) a cup.  In it, Q+p is convex in X iff Q is a cup, and convex in X^p iff Q is a cap.
"""
from __future__ import annotations

import itertools


# ---- colouring keys -------------------------------------------------------------------------------------------------
def key_of(n: int, chi: dict) -> str:
    """'0'/'1' per sorted triple, '1' = cup."""
    return "".join("1" if chi[t] else "0" for t in itertools.combinations(range(n), 3))


def parse_key(key: str):
    """key -> (n, chi)."""
    n = 3
    while n * (n - 1) * (n - 2) // 6 < len(key):
        n += 1
    if n * (n - 1) * (n - 2) // 6 != len(key):
        raise ValueError("bad key length")
    return n, {t: (c == "1") for t, c in zip(itertools.combinations(range(n), 3), key)}


def mirror(n: int, chi: dict) -> dict:
    """Reverse the sweep order; cups stay cups."""
    return {t: chi[(n - 1 - t[2], n - 1 - t[1], n - 1 - t[0])] for t in chi}


def reflect(chi: dict) -> dict:
    """Reflect in a horizontal line: cups <-> caps, order kept."""
    return {t: not v for t, v in chi.items()}


def enumerate_colourings(nmax: int, ok):
    """All one-change colourings on 3..nmax points whose every prefix satisfies ok(n, chi); yields (n, chi)."""
    from harness.research import signotope_cubes as sc

    level = [{(0, 1, 2): v} for v in (False, True)]
    level = [c for c in level if ok(3, c)]
    n = 3
    while level:
        for c in level:
            yield n, c
        if n == nmax:
            return
        nxt = []
        for c in level:
            for e in sc.extensions(c, range(n), n):
                d = {**c, **e}
                if ok(n + 1, d):
                    nxt.append(d)
        level = nxt
        n += 1


# ---- orientation, circuits, charts ---------------------------------------------------------------------------------
def orient(chi: dict, a: int, b: int, c: int) -> int:
    """+1 / -1 for the ordered triple (a,b,c); sorted cup = +1."""
    s = sorted((a, b, c))
    v = 1 if chi[tuple(s)] else -1
    inv = (a > b) + (a > c) + (b > c)
    return v if inv % 2 == 0 else -v


def circuits(n: int, chi: dict) -> dict:
    """C[(a,b,c,d)] = (chi(bcd), -chi(acd), chi(abd), -chi(abc)) with chi as +-1."""
    C = {}
    for a, b, c, d in itertools.combinations(range(n), 4):
        sg = lambda t: 1 if chi[t] else -1
        C[(a, b, c, d)] = (sg((b, c, d)), -sg((a, c, d)), sg((a, b, d)), -sg((a, b, c)))
    return C


def circuit_sum(C: dict, Q: tuple, s) -> int:
    return sum(cx * s[x] for cx, x in zip(C[Q], Q))


def topes(n: int, C: dict) -> list:
    """All charts s with s[0] = +1 (one of each antipodal pair); n(n-1)/2 + 1 of them."""
    out = []
    for s in itertools.product((1, -1), repeat=n):
        if s[0] != 1:
            continue
        if all(abs(circuit_sum(C, Q, s)) != 4 for Q in C):
            out.append(s)
    return out


def convex4_in_chart(C: dict, s) -> set:
    return {Q for Q in C if circuit_sum(C, Q, s) == 0}


def convex_sets_in_chart(n: int, C: dict, s, k: int) -> list:
    conv4 = convex4_in_chart(C, s)
    return [S for S in itertools.combinations(range(n), k) if all(Q in conv4 for Q in itertools.combinations(S, 4))]


def inner_point(C: dict, Q: tuple, s) -> int | None:
    """The inner point of a 4-set in chart s (None if convex)."""
    v = circuit_sum(C, Q, s)
    if v == 0:
        return None
    sign = 1 if v > 0 else -1
    return [x for cx, x in zip(C[Q], Q) if cx * s[x] != sign][0]


def hull_vertices(n: int, C: dict, s=None) -> list:
    s = s or (1,) * n
    inner = {inner_point(C, Q, s) for Q in C} - {None}
    return [p for p in range(n) if p not in inner]


def flip_chart(s, p: int):
    """Move p across infinity (s_p -> -s_p); a chart iff p is a hull vertex of chart s."""
    t = list(s)
    t[p] = -t[p]
    return tuple(t)


# ---- radial order and re-sweep (brief G, L2) -----------------------------------------------------------------------
def radial_order(n: int, chi: dict, p: int) -> list:
    """The other points sorted by x <_p y iff orient(p,x,y) = +1 (a linear order when p is a hull vertex)."""
    import functools

    others = [x for x in range(n) if x != p]
    return sorted(others, key=functools.cmp_to_key(lambda x, y: -orient(chi, p, x, y)))


def resweep(n: int, chi: dict, p: int):
    """Relist as (p, radial order) and recolour by orientation: returns (listing, chi_prime) with chi_prime
    one-change on [n], p at index 0, every (0,x,y) a cup.  Raises ValueError if the result is not one-change."""
    listing = [p] + radial_order(n, chi, p)
    chi2 = {}
    for u, v, w in itertools.combinations(range(n), 3):
        chi2[(u, v, w)] = orient(chi, listing[u], listing[v], listing[w]) > 0
    for a, b, c, d in itertools.combinations(range(n), 4):
        pat = [chi2[(a, b, c)], chi2[(a, b, d)], chi2[(a, c, d)], chi2[(b, c, d)]]
        if sum(pat[i] != pat[i + 1] for i in range(3)) > 1:
            raise ValueError("re-sweep is not one-change (p is not a hull vertex?)")
    return listing, chi2
