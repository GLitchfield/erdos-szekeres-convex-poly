"""Signotope SAT base: one-change colourings on n points with convex-set, cup, cap and normal-form constraints.

Promoted 2026-10-08 from the SAT bases of runs/claude-cap4-junction-20261006/gon_sat.py (quad encoding),
runs/claude-positive-split-20261007/wsat.py (chain-variable encoding, retained there), runs/claude-antipodal-flips-20261007/flipmod.py
and runs/claude-extremal-20261005/fbdl_all_small.py.  Diagnostic: a python-sat answer, no proof log, no Lean certificate.

Convention: points 0..n-1 in sweep order; triple variable T[(a,b,c)] true = cup.  A 4-set a<b<c<d is in convex
position iff its pattern (abc, abd, acd, bcd) is 0000, 1111, 0011 or 1100 (one-change, no change or the change in
the middle).  A k-set is strong (a convex k-gon) iff all its 4-subsets are convex.  An m-cup (m-cap) is an m-set all of
whose triples are cups (caps).

Lemma used by radial_normal_form (brief G, L2): for a hull vertex p there is a presentation of the same chirotope
with p first and every triple (p,x,y) a cup, so for a question about one hull vertex it is WLOG to fix p = 0 and all
(0,x,y) cups.  Lemma used by hull_vertex (brief G, L1): p is a hull vertex iff all triples (a,p,c), a<p<c, have one
colour.
"""
from __future__ import annotations

import itertools

CONVEX_PATTERNS = ("0000", "1111", "0011", "1100")


class SignotopeSAT:
    """Clause builder for one-change colourings on n points."""

    def __init__(self, n: int):
        if not isinstance(n, int) or isinstance(n, bool) or n < 3:
            raise ValueError("n must be an integer >= 3")
        self.n = n
        self.nv = 0
        self.cl: list[list[int]] = []
        self.T = {t: self.new() for t in itertools.combinations(range(n), 3)}
        self._c4: dict[tuple, int] = {}
        for a, b, c, d in itertools.combinations(range(n), 4):
            v = [self.T[(a, b, c)], self.T[(a, b, d)], self.T[(a, c, d)], self.T[(b, c, d)]]
            for bits in itertools.product((0, 1), repeat=4):
                if sum(bits[i] != bits[i + 1] for i in range(3)) > 1:
                    self.cl.append([-x if bit else x for x, bit in zip(v, bits)])

    def new(self) -> int:
        self.nv += 1
        return self.nv

    def convex4(self, Q: tuple) -> int:
        """Auxiliary variable equivalent to 'the 4-set Q is in convex position'."""
        Q = tuple(sorted(Q))
        if Q not in self._c4:
            a, b, c, d = Q
            v = [self.T[(a, b, c)], self.T[(a, b, d)], self.T[(a, c, d)], self.T[(b, c, d)]]
            x = self.new()
            self._c4[Q] = x
            for pat in itertools.product("01", repeat=4):
                lits = [-y if bit == "1" else y for y, bit in zip(v, pat)]
                if "".join(pat) in CONVEX_PATTERNS:
                    self.cl.append(lits + [x])          # pattern convex -> x
                else:
                    self.cl.append(lits + [-x])         # pattern not convex -> not x
        return self._c4[Q]

    def no_strong_set(self, k: int) -> None:
        """Forbid every convex k-gon (one clause per k-set over its 4-subsets)."""
        for G in itertools.combinations(range(self.n), k):
            self.cl.append([-self.convex4(Q) for Q in itertools.combinations(G, 4)])

    def no_cup(self, m: int) -> None:
        for S in itertools.combinations(range(self.n), m):
            self.cl.append([-self.T[t] for t in itertools.combinations(S, 3)])

    def no_cap(self, m: int) -> None:
        for S in itertools.combinations(range(self.n), m):
            self.cl.append([self.T[t] for t in itertools.combinations(S, 3)])

    def radial_normal_form(self) -> None:
        """Point 0 is a hull vertex seen radially: every (0,x,y) is a cup (WLOG for one-hull-vertex questions)."""
        for x, y in itertools.combinations(range(1, self.n), 2):
            self.cl.append([self.T[(0, x, y)]])

    def hull_vertex(self, p: int) -> None:
        """p is a hull vertex: all triples (a,p,c) with a<p<c have the same colour."""
        trips = [self.T[(a, p, c)] for a in range(p) for c in range(p + 1, self.n)]
        for u, v in zip(trips, trips[1:]):
            self.cl.append([-u, v])
            self.cl.append([u, -v])

    def block(self, chi: dict) -> None:
        """Exclude one colouring (for enumeration with blocking clauses)."""
        self.cl.append([-self.T[t] if chi[t] else self.T[t] for t in self.T])

    def solve(self, assumptions=()):
        """Returns (True, colouring dict) or (False, None) with python-sat CaDiCaL."""
        from pysat.solvers import Cadical195

        with Cadical195(bootstrap_with=self.cl) as s:
            if not s.solve(assumptions=list(assumptions)):
                return False, None
            model = set(v for v in s.get_model() if v > 0)
            return True, {t: (v in model) for t, v in self.T.items()}


def key_of(n: int, chi: dict) -> str:
    return "".join("1" if chi[t] else "0" for t in itertools.combinations(range(n), 3))


def threshold_instance(n: int, k: int | None = None, cup: int | None = None, cap: int | None = None,
                       radial: bool = False) -> SignotopeSAT:
    """n points, no convex k-set, no cup-cup, no cap-cap; the ETV cell (k; cup, cap) instance."""
    inst = SignotopeSAT(n)
    if k is not None:
        inst.no_strong_set(k)
    if cup is not None:
        inst.no_cup(cup)
    if cap is not None:
        inst.no_cap(cap)
    if radial:
        inst.radial_normal_form()
    return inst
