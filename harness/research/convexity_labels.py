"""Convexity labellings and the locality ladder (level-m local realizability), with the 7-point axiom system.

Promoted 2026-10-08 from runs/claude-halving-20261008/{locality.py, locality_dimacs.py, enum7.py, core7.py}.
Diagnostic SAT (python-sat CaDiCaL, or a DIMACS file for a standalone solver), no proof log, not Lean.

A LABELLING on [n] gives every 4-set Q either 'conv' or the name of its inner point.  Convex m-sets are those with all
4-subsets 'conv'.  LEVEL m: for every m-subset F the labels on F are those of some realizable m-point configuration,
encoded by a private acyclic rank-3 chirotope on F (3-term Grassmann-Pluecker on its 5-subsets, no alternating
4-pattern; this is realizability for m <= 8) linked to the labels by the circuit rule (circuit sum 0 = conv, else the
odd sign is the inner point).  Level 4 is no constraint; level n is a real configuration.  Different subsets need
agree only on the labels.  The labels of a colouring chi are labels_of(n, chi).

Results recorded with the fixture examples/convexity-axioms7-v1.json (2026-10-08): the 7-point axiom system
(labellings of 7 points with every 6-subset realizable but not themselves realizable) has exactly 20 patterns up to
relabelling; ES(5) = 9 follows from the 6-point patterns plus one of them (the cone lemma); SPLIT(5) on 8 points is
5-point local; SPLIT(6) on 16 points is not 6-point local.
"""
from __future__ import annotations

import itertools
import json
import os

CONVEX_PATTERNS = ("0000", "1111", "0011", "1100")


def sign_perm(t) -> int:
    inv = sum(1 for i, j in itertools.combinations(range(3), 2) if t[i] > t[j])
    return -1 if inv % 2 else 1


def labels_of(n: int, chi: dict) -> dict:
    """Labels of a one-change colouring in its reference chart: Q -> 'conv' or inner point."""
    lab = {}
    for Q in itertools.combinations(range(n), 4):
        a, b, c, d = Q
        pat = "".join("1" if chi[t] else "0" for t in ((a, b, c), (a, b, d), (a, c, d), (b, c, d)))
        if pat in CONVEX_PATTERNS:
            lab[Q] = "conv"
        else:
            lab[Q] = c if pat in ("0001", "1110") else b
    return lab


def _pattern_table() -> dict:
    """(chi(abc), chi(abd), chi(acd), chi(bcd)) as +-1 -> None (alternating, forbidden), 0 (conv), or 1..4 (inner index+1)."""
    table = {}
    for p in itertools.product((1, -1), repeat=4):
        abc, abd, acd, bcd = p
        C = (bcd, -acd, abd, -abc)
        s = sum(C)
        if abs(s) == 4:
            table[p] = None
        elif s == 0:
            table[p] = 0
        else:
            table[p] = [i for i in range(4) if C[i] != (1 if s > 0 else -1)][0] + 1
    return table


class Enc:
    def __init__(self):
        self.nv = 0
        self.cl: list[list[int]] = []

    def var(self) -> int:
        self.nv += 1
        return self.nv

    def add(self, c) -> None:
        self.cl.append(list(c))


def level_instance(k: int, n: int, m: int, *, gon_free: bool = True, no_halving: bool = True,
                   hull3: bool = False, hull: int | None = None, equal_halves: bool = False):
    """Clauses for: labelling on [n] at level m [, no convex k-set] [, no partition into two (k-1)-gon-free halves].
    hull3: points 0,1,2 never inner (WLOG by relabelling).  hull=h: exactly points 0..h-1 are never inner.
    no_halving: no partition of [n] into two (k-1)-gon-free sets of any sizes.  equal_halves=True restricts to the
    n/2 + n/2 partitions, which is sound only when every (n/2+1)-subset of the labelling has a (k-1)-gon (for k = 6 at
    level >= 7, since ES(5) = 9 is 7-point local; for k = 5 at level >= 5).  Corrected 2026-10-10: the earlier equal-halves
    encoding let a level-5 16-point witness pass that splits into a pentagon-free 7-set and a pentagon-free 9-set.
    Returns (enc, L) with L[Q] = [var_conv, var_inner_Q0, .., var_inner_Q3]."""
    E = Enc()
    four = list(itertools.combinations(range(n), 4))
    L = {Q: [E.var() for _ in range(5)] for Q in four}
    for Q in four:
        E.add(L[Q])
        for i, j in itertools.combinations(range(5), 2):
            E.add([-L[Q][i], -L[Q][j]])
    table = _pattern_table()
    for F in itertools.combinations(range(n), m):
        X = {t: E.var() for t in itertools.combinations(F, 3)}

        def chi(a, b, c):
            t = tuple(sorted((a, b, c)))
            return X[t], sign_perm((a, b, c))

        for a in F:
            rest = [x for x in F if x != a]
            for b, c, d, e in itertools.combinations(rest, 4):
                terms = [((a, b, c), (a, d, e), 1), ((a, b, d), (a, c, e), -1), ((a, b, e), (a, c, d), 1)]
                lits = []
                for t1, t2, sg in terms:
                    v1, s1 = chi(*t1)
                    v2, s2 = chi(*t2)
                    lits.append((v1, s1, v2, s2, sg))
                vs = sorted({v for (v1, s1, v2, s2, sg) in lits for v in (v1, v2)})
                for assign in itertools.product((1, -1), repeat=len(vs)):
                    val = dict(zip(vs, assign))
                    prods = [sg * (s1 * val[v1]) * (s2 * val[v2]) for (v1, s1, v2, s2, sg) in lits]
                    if prods[0] == prods[1] == prods[2]:
                        E.add([-v if val[v] > 0 else v for v in vs])
        for Q in itertools.combinations(F, 4):
            a, b, c, d = Q
            vars4 = [X[(a, b, c)], X[(a, b, d)], X[(a, c, d)], X[(b, c, d)]]
            for p, lab in table.items():
                cl = [-v if s > 0 else v for v, s in zip(vars4, p)]
                E.add(cl if lab is None else cl + [L[Q][lab]])
    if gon_free:
        for G in itertools.combinations(range(n), k):
            E.add([-L[Q][0] for Q in itertools.combinations(G, 4)])
    if no_halving:
        h = k - 1
        half = n // 2
        gon = {}

        def gv(P):
            if P not in gon:
                v = E.var()
                gon[P] = v
                for Q in itertools.combinations(P, 4):
                    E.add([-v, L[Q][0]])
            return gon[P]

        sizes = [half] if equal_halves else range(1, n)
        for a in sizes:
            for A in itertools.combinations(range(n), a):
                if 0 not in A:
                    continue
                B = tuple(x for x in range(n) if x not in A)
                # a part with fewer than h points contributes no literal: it is trivially h-gon-free
                E.add([gv(P) for P in itertools.combinations(A, h)] + [gv(P) for P in itertools.combinations(B, h)])
    if hull is not None:
        for Q in four:
            for j in range(4):
                if Q[j] < hull:
                    E.add([-L[Q][j + 1]])
        for p in range(hull, n):
            E.add([L[Q][Q.index(p) + 1] for Q in four if p in Q])
    if hull3:
        for Q in four:
            for j in range(4):
                if Q[j] in (0, 1, 2):
                    E.add([-L[Q][j + 1]])
    return E, L


def decode(L: dict, model, n: int) -> dict:
    pos = set(v for v in model if v > 0)
    lam = {}
    for Q, vs in L.items():
        j = [i for i, v in enumerate(vs) if v in pos][0]
        lam[Q] = "conv" if j == 0 else Q[j - 1]
    return lam


def label_assumptions(L: dict, lam: dict, F=None) -> list:
    """Unit assumptions fixing the labels lam (keyed by 4-sets of F, or of range(n) when F is None) in instance L."""
    out = []
    for Q, vs in L.items():
        Qg = Q if F is None else tuple(F[x] for x in Q)
        v = lam[Qg]
        out.append(vs[0] if v == "conv" else vs[Qg.index(v) + 1])
    return out


def realizable(m: int, lam: dict) -> bool:
    """Is a labelling of m points (keys = 4-subsets of range(m)) the labelling of an acyclic chirotope (m <= 8: a real set)?"""
    from pysat.solvers import Cadical195

    E, L = level_instance(m + 1, m, m, gon_free=False, no_halving=False)
    with Cadical195(bootstrap_with=E.cl) as s:
        return s.solve(assumptions=label_assumptions(L, lam))


def locality_profile(n: int, lam: dict, levels=(5, 6, 7, 8)) -> dict:
    """For each m, the number of m-subsets of [n] whose labels are not realizable."""
    from pysat.solvers import Cadical195

    out = {}
    for m in levels:
        E, L = level_instance(m + 1, m, m, gon_free=False, no_halving=False)
        with Cadical195(bootstrap_with=E.cl) as s:
            bad = 0
            for F in itertools.combinations(range(n), m):
                sub = {tuple(F.index(x) for x in Q): (lam[Q] if lam[Q] == "conv" else F.index(lam[Q]))
                       for Q in itertools.combinations(F, 4)}
                if not s.solve(assumptions=label_assumptions(L, sub)):
                    bad += 1
            out[m] = bad
    return out


def axioms7(path: str | None = None) -> dict:
    """The frozen 7-point axiom system: 20 canonical patterns (label vectors over the 35 4-subsets of range(7),
    -1 = conv, else inner point) and the cone-lemma core."""
    path = path or os.path.join(os.path.dirname(__file__), "examples", "convexity-axioms7-v1.json")
    return json.load(open(path))


def write_dimacs(k: int, n: int, m: int, out: str, *, hull3: bool = False, gon_free: bool = True,
                 no_halving: bool = True, equal_halves: bool = False) -> tuple[int, int]:
    """Streamed DIMACS for large n (same semantics as level_instance); returns (variables, clauses)."""
    four = list(itertools.combinations(range(n), 4))
    qidx = {Q: i for i, Q in enumerate(four)}

    def L(Q, j):
        return 5 * qidx[Q] + j + 1

    nv = 5 * len(four)
    trip = list(itertools.combinations(range(m), 3))
    X = {t: i + 1 for i, t in enumerate(trip)}
    tmpl = []
    F0 = tuple(range(m))
    for a in F0:
        rest = [x for x in F0 if x != a]
        for b, c, d, e in itertools.combinations(rest, 4):
            terms = [((a, b, c), (a, d, e), 1), ((a, b, d), (a, c, e), -1), ((a, b, e), (a, c, d), 1)]
            lits = []
            for t1, t2, sg in terms:
                v1, s1 = X[tuple(sorted(t1))], sign_perm(t1)
                v2, s2 = X[tuple(sorted(t2))], sign_perm(t2)
                lits.append((v1, s1, v2, s2, sg))
            vs = sorted({v for (v1, s1, v2, s2, sg) in lits for v in (v1, v2)})
            for assign in itertools.product((1, -1), repeat=len(vs)):
                val = dict(zip(vs, assign))
                prods = [sg * (s1 * val[v1]) * (s2 * val[v2]) for (v1, s1, v2, s2, sg) in lits]
                if prods[0] == prods[1] == prods[2]:
                    tmpl.append([-v if val[v] > 0 else v for v in vs])
    table = _pattern_table()
    for Q in itertools.combinations(F0, 4):
        a, b, c, d = Q
        vars4 = [X[(a, b, c)], X[(a, b, d)], X[(a, c, d)], X[(b, c, d)]]
        for p, lab in table.items():
            base = [-v if s > 0 else v for v, s in zip(vars4, p)]
            tmpl.append(base if lab is None else base + [("L", Q, lab)])
    body = out + ".body"
    ncl = 0
    with open(body, "w") as f:
        w = f.write
        for Q in four:
            w(" ".join(str(L(Q, j)) for j in range(5)) + " 0\n")
            ncl += 1
            for i, j in itertools.combinations(range(5), 2):
                w(f"-{L(Q, i)} -{L(Q, j)} 0\n")
                ncl += 1
        if hull3:
            for Q in four:
                for j in range(4):
                    if Q[j] in (0, 1, 2):
                        w(f"-{L(Q, j + 1)} 0\n")
                        ncl += 1
        for F in itertools.combinations(range(n), m):
            off = nv
            nv += len(trip)
            for c in tmpl:
                parts = []
                for lit in c:
                    if isinstance(lit, int):
                        parts.append(str(lit + off if lit > 0 else lit - off))
                    else:
                        _, Ql, j = lit
                        parts.append(str(L(tuple(F[x] for x in Ql), j)))
                w(" ".join(parts) + " 0\n")
                ncl += 1
        if gon_free:
            for G in itertools.combinations(range(n), k):
                w(" ".join(f"-{L(Q, 0)}" for Q in itertools.combinations(G, 4)) + " 0\n")
                ncl += 1
        if no_halving:
            h = k - 1
            half = n // 2
            gon = {}
            sizes = [half] if equal_halves else range(1, n)
            for a in sizes:
                for A in itertools.combinations(range(n), a):
                    if 0 not in A:
                        continue
                    B = tuple(x for x in range(n) if x not in A)
                    lits = []
                    for P in list(itertools.combinations(A, h)) + list(itertools.combinations(B, h)):
                        if P not in gon:
                            nv += 1
                            gon[P] = nv
                            for Q in itertools.combinations(P, 4):
                                w(f"-{nv} {L(Q, 0)} 0\n")
                                ncl += 1
                        lits.append(gon[P])
                    w(" ".join(map(str, lits)) + " 0\n")
                    ncl += 1
    with open(out, "w") as f:
        f.write(f"p cnf {nv} {ncl}\n")
        with open(body) as g:
            for line in g:
                f.write(line)
    os.remove(body)
    return nv, ncl


def decode_dimacs(n: int, solver_output: str) -> dict:
    """Labelling from a standalone solver's 'v' lines (variables as laid out by write_dimacs)."""
    pos = set()
    for line in open(solver_output):
        if line.startswith("v "):
            pos.update(int(x) for x in line.split()[1:] if int(x) > 0)
    lam = {}
    for i, Q in enumerate(itertools.combinations(range(n), 4)):
        js = [j for j in range(5) if 5 * i + j + 1 in pos]
        if len(js) != 1:
            raise ValueError(f"no unique label for {Q}")
        lam[Q] = "conv" if js[0] == 0 else Q[js[0] - 1]
    return lam
