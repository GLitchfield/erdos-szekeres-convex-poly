"""Cup/cap chains and strong sets ("gons") of an ordered triple colouring.

Promoted on 3 Oct 2026 from runs/claude-hypergraph-20261003/q15/lightgon.py (find_gon, cegar). The
chain primitives below were carried as near-identical copies by bl.py (five verbatim copies across the
3 Oct runs), runs/claude-audit-bdl-20261003/dec.py and runs/claude-hypergraph-20261003/sig.py. The run
files stay unchanged as the recorded artifacts.

Conventions (shared by harness.research.decomposable_sets and harness.research.band_partitions):

* Points are integers in sweep (x) order. A colouring ``cup`` maps every sorted triple ``(i, j, k)`` of
  the points in play to a bool: True means CUP (left turn: the middle point lies below the chord; the bit
  is set in the bitmasks of ``decomposable.coloring-enumeration``), False means CAP.
* A chain of colour ``want`` is a sorted tuple of points whose consecutive triples all have colour
  ``want``; its length is its number of points. **Sets of <= 2 points are both cups and caps**: the
  empty set has length 0, a point 1, a pair 2. So a limit "cup <= 1" (or "cap <= 1") admits one point.
* A strong set is Lean's ``IsStrongPolygonSet``: for all i<j<k<l in it, cup(ijk) = cup(ijl) and
  cup(ikl) = cup(jkl). Every set of <= 3 points is strong.
* A colouring is one-change (a rank-3 signotope) when every (ijk, ijl, ikl, jkl) changes value at most
  once. Decomposable colourings are one-change. On a one-change colouring all triples of a chain have
  the chain's colour, deleting interior points of a cup (cap) leaves a cup (cap), a cup and a cap with
  the same two endpoints share no interior point, and a set is strong exactly when it is such a union.
  ``strong_number`` and ``find_gon`` use this and are therefore only valid on one-change colourings;
  ``strong_number_bruteforce`` and ``is_strong`` use the 4-point definition and hold for any colouring.

All results are finite diagnostic computation, not Lean proofs.
"""
from __future__ import annotations

import itertools
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

Triple = Tuple[int, int, int]
Coloring = Mapping[Triple, bool]


def longest_chain(cup: Coloring, points: Iterable[int], want: bool) -> int:
    """Length of a longest colour-``want`` chain inside ``points`` (0, 1, 2 for sets of <= 2 points)."""
    S = sorted(points)
    m = len(S)
    if m <= 2:
        return m
    end: Dict[Tuple[int, int], int] = {}
    best = 2
    for b in range(m):
        for a in range(b):
            v = 2
            for h in range(a):
                if cup[(S[h], S[a], S[b])] == want:
                    w = end[(h, a)] + 1
                    if w > v:
                        v = w
            end[(a, b)] = v
            if v > best:
                best = v
    return best


def cup_number(cup: Coloring, points: Iterable[int]) -> int:
    return longest_chain(cup, points, True)


def cap_number(cup: Coloring, points: Iterable[int]) -> int:
    return longest_chain(cup, points, False)


def chains(cup: Coloring, t: int, want: bool, points: Iterable[int]) -> List[Tuple[int, ...]]:
    """Every colour-``want`` chain of exactly ``t`` points inside ``points``, as sorted tuples.

    ``t == 0`` gives ``[()]``; ``t == 1`` every singleton; ``t == 2`` every pair.
    """
    S = sorted(points)
    if t <= 0:
        return [()]
    if t == 1:
        return [(x,) for x in S]
    out: List[Tuple[int, ...]] = []
    cur: List[int] = []

    def ext(start: int) -> None:
        if len(cur) == t:
            out.append(tuple(cur))
            return
        for yi in range(start, len(S)):
            y = S[yi]
            if len(cur) >= 2 and cup[(cur[-2], cur[-1], y)] != want:
                continue
            cur.append(y)
            ext(yi + 1)
            cur.pop()

    for xi in range(len(S)):
        cur.append(S[xi])
        ext(xi + 1)
        cur.pop()
    return out


def edge_chain_tables(cup: Coloring, n: int, want: bool) -> Tuple[Dict[Tuple[int, int], int], Dict[Tuple[int, int], int]]:
    """For points range(n): ``end[(i, j)]`` / ``start[(i, j)]`` = longest colour-``want`` chain ending /
    starting with the edge i<j (at least 2)."""
    end: Dict[Tuple[int, int], int] = {}
    for j in range(n):
        for i in range(j):
            v = 2
            for h in range(i):
                if cup[(h, i, j)] == want and end[(h, i)] + 1 > v:
                    v = end[(h, i)] + 1
            end[(i, j)] = v
    start: Dict[Tuple[int, int], int] = {}
    for i in range(n - 1, -1, -1):
        for j in range(n - 1, i, -1):
            v = 2
            for l in range(j + 1, n):
                if cup[(i, j, l)] == want and start[(j, l)] + 1 > v:
                    v = start[(j, l)] + 1
            start[(i, j)] = v
    return end, start


def longest_lr(cup: Coloring, points: Iterable[int], want: bool) -> Dict[Tuple[int, int], Tuple[int, Tuple[int, ...]]]:
    """``best[(l, r)] = (length, chain)``: a longest colour-``want`` chain inside ``points`` whose first
    point is l and last point is r, for every pair l < r of points (a pair is a 2-chain). O(|S|^4)."""
    S = sorted(points)
    m = len(S)
    best: Dict[Tuple[int, int], Tuple[int, Tuple[int, ...]]] = {}
    for s in range(m):
        # E[(i, j)] = (length, previous index) of a longest chain from S[s] whose last edge is (S[i], S[j])
        E: Dict[Tuple[int, int], Tuple[int, Optional[int]]] = {}
        for j in range(s + 1, m):
            E[(s, j)] = (2, None)
        for j in range(s + 1, m):
            for q in range(j + 1, m):
                bl, bp = 0, None
                for i in range(s, j):
                    e = E.get((i, j))
                    if e and cup[(S[i], S[j], S[q])] == want and e[0] + 1 > bl:
                        bl, bp = e[0] + 1, i
                if bl and bl > E.get((j, q), (0, None))[0]:
                    E[(j, q)] = (bl, bp)
        for (i, j), (length, _prev) in E.items():
            key = (S[s], S[j])
            if length > best.get(key, (0, ()))[0]:
                chain = [S[j]]
                a, b = i, j
                while True:
                    chain.append(S[a])
                    prev = E[(a, b)][1]
                    if prev is None:
                        break
                    a, b = prev, a
                best[key] = (length, tuple(reversed(chain)))
    return best


def _lr_lengths(cup: Coloring, S: Sequence[int], want: bool) -> Dict[Tuple[int, int], int]:
    """Lengths only: longest colour-``want`` chain from S[l] to S[r] (indices into sorted S)."""
    m = len(S)
    res: Dict[Tuple[int, int], int] = {}
    for l in range(m):
        g: Dict[Tuple[int, int], int] = {}
        for b in range(l + 1, m):
            g[(l, b)] = 2
            for c in range(l + 1, b):
                bestv = None
                for e in range(l, c):
                    v = g.get((e, c))
                    if v is not None and cup[(S[e], S[c], S[b])] == want and (bestv is None or v + 1 > bestv):
                        bestv = v + 1
                if bestv is not None:
                    g[(c, b)] = bestv
        for (_i, j), v in g.items():
            if res.get((l, j), 0) < v:
                res[(l, j)] = v
    return res


def strong_number(cup: Coloring, points: Iterable[int]) -> int:
    """Size of a largest strong set inside ``points``: ``max(min(n, 3), max over l < r of
    cup_lr + cap_lr - 2)``. Valid on one-change colourings only (see module docstring)."""
    S = sorted(points)
    n = len(S)
    if n <= 3:
        return n
    cu, ca = _lr_lengths(cup, S, True), _lr_lengths(cup, S, False)
    st = 3
    for key, v in cu.items():
        w = ca.get(key)
        if w is not None and v + w - 2 > st:
            st = v + w - 2
    return st


def is_strong(cup: Coloring, points: Iterable[int]) -> bool:
    """4-point definition (Lean ``IsStrongPolygonSet``); valid for any colouring."""
    for i, j, k, l in itertools.combinations(sorted(points), 4):
        if cup[(i, j, k)] != cup[(i, j, l)] or cup[(i, k, l)] != cup[(j, k, l)]:
            return False
    return True


def is_one_change(cup: Coloring, points: Iterable[int]) -> bool:
    for i, j, k, l in itertools.combinations(sorted(points), 4):
        seq = (cup[(i, j, k)], cup[(i, j, l)], cup[(i, k, l)], cup[(j, k, l)])
        if (seq[0] != seq[1]) + (seq[1] != seq[2]) + (seq[2] != seq[3]) > 1:
            return False
    return True


def strong_number_bruteforce(cup: Coloring, points: Iterable[int]) -> int:
    """Largest strong set by the 4-point definition (hereditary subset DP, O(2^n n)); any colouring.
    The reference for ``strong_number``; use only for small point sets (n <= ~16)."""
    S = sorted(points)
    n = len(S)
    if n <= 3:
        return n
    good4 = set()
    for q in itertools.combinations(range(n), 4):
        i, j, k, l = (S[x] for x in q)
        if cup[(i, j, k)] == cup[(i, j, l)] and cup[(i, k, l)] == cup[(j, k, l)]:
            good4.add(sum(1 << x for x in q))
    strong = bytearray(1 << n)
    best = 3
    for s in sorted(range(1 << n), key=lambda x: bin(x).count("1")):
        size = bin(s).count("1")
        if size <= 3:
            strong[s] = 1
            continue
        if size == 4:
            ok = s in good4
        else:
            ok = True
            t = s
            while t:
                low = t & -t
                if not strong[s ^ low]:
                    ok = False
                    break
                t ^= low
        strong[s] = ok
        if ok and size > best:
            best = size
    return best


def chain_core(cup: Coloring, points: Iterable[int], want: bool) -> Tuple[int, int, List[Tuple[int, ...]]]:
    """Core of the maximum chains: ``(L*, R*, chains)`` with L* = max first point and R* = min last point
    over all longest colour-``want`` chains inside ``points`` (bl.cap_core / bl.cup_core). The core is
    "interior" when L* < R*. Requires at least one point."""
    S = sorted(points)
    if not S:
        raise ValueError("chain_core needs a nonempty point set")
    top = longest_chain(cup, S, want)
    best = chains(cup, top, want, S)
    return max(c[0] for c in best), min(c[-1] for c in best), best


def find_gon(cup: Coloring, points: Iterable[int], size: int) -> Optional[Tuple[int, ...]]:
    """One strong set of exactly ``size`` points inside ``points`` (sorted tuple), or None if there is none.

    Memory-light: O(|S|^2) witnesses per start point, no enumeration of all gons. Pairs a longest cup and a
    longest cap with the same endpoints and trims interior points to the exact size. Complete (None means
    no strong ``size``-set exists) on one-change colourings only.
    """
    S = sorted(points)
    if size < 0 or len(S) < size:
        return None
    if size <= 3:
        return tuple(S[:size])
    cu, ca = longest_lr(cup, S, True), longest_lr(cup, S, False)
    for key, (a, C) in cu.items():
        if key not in ca:
            continue
        b, D = ca[key]
        if a + b - 2 >= size:
            a2 = min(a, size)
            b2 = size + 2 - a2
            if b2 > b:
                b2 = b
                a2 = size + 2 - b2
            interior = list(C[1:-1])[: a2 - 2] + list(D[1:-1])[: b2 - 2]
            gon = tuple(sorted(set([C[0], C[-1]] + interior)))
            if len(gon) != size:
                raise ValueError("cup and cap share an interior point: the colouring is not one-change")
            return gon
    return None


def cegar_two_colouring(cup: Coloring, points: Sequence[int], hard: List[List[int]], size: int):
    """Two-colour ``points`` so that neither class contains a strong ``size``-set, lazily (CEGAR).

    SAT variable ``p + 1`` is point ``p`` (true = blue), so points must be non-negative integers and
    ``hard`` is a clause list over those variables (plus any auxiliaries above them). Solve ``hard``; while a
    colour class contains a ``size``-gon (``find_gon``), add the two clauses forbidding that gon to be
    monochromatic and re-solve. Returns ``(blue, red)`` point lists, or None when no such colouring exists.
    Memory stays O(n^3 + number of added gons) instead of one clause pair per gon. Requires python-sat
    (Cadical195); valid on one-change colourings (``find_gon`` completeness).
    """
    from pysat.solvers import Cadical195

    solver = Cadical195(bootstrap_with=hard)
    try:
        while True:
            if not solver.solve():
                return None
            model = set(v for v in solver.get_model() if v > 0)
            blue = [p for p in points if (p + 1) in model]
            red = [p for p in points if (p + 1) not in model]
            added = False
            for cls in (blue, red):
                gon = find_gon(cup, cls, size)
                if gon is not None:
                    solver.add_clause([p + 1 for p in gon])
                    solver.add_clause([-(p + 1) for p in gon])
                    added = True
            if not added:
                return blue, red
    finally:
        solver.delete()
