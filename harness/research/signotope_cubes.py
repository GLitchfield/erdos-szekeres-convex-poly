"""Signotope point-set cubes for SAT cube-and-conquer on triple-coloring CNFs.

Promoted from runs/etv-cc-20260930 (acc.py, split_orders.py, sym_filter.py, knuth_walk.py) after the
Workstream C round of 30 Sept 2026.  A *pattern* is a dict mapping sorted triples (i, j, k) of points to
a bool (the triple's color / orientation sign).  A pattern on a point set is *legal* when every 4-subset
obeys the one-change law: the sequence (ijk, ijl, ikl, jkl) changes value at most once (rank-3
signotope axiom).  Only this law is enforced here; cup/cap/convex-gon constraints live in the CNF and
are applied by the caller's solver (e.g. a propagation test).

Triple variables follow scripts/generate_etv_tseitin_sat.py: triple (i, j, k) of an N-point instance is
variable 1 + its index in itertools.combinations(range(N), 3).  Counts of legal patterns on 1..7 points
are 1, 1, 2, 8, 62, 908, 24698 (OEIS A006245), a regression fixture.

The Knuth walk is solver-agnostic: the caller supplies `survives(pattern) -> bool` (e.g. a
conf_budget(1) python-sat call: False when the cube is refuted by propagation) and
`is_leaf(pattern, depth) -> bool` (e.g. a bounded CDCL attempt refutes it).  Pitfalls measured on the
N=27 ETV CNF: python-sat's conf_budget(0) means NO limit, CaDiCaL has no propagate(), and an
incremental solver should stay on one cube point set (mixing sets was ~10x slower).
"""
from __future__ import annotations

import itertools
import math
import random
from math import comb
from typing import Callable, Dict, Iterable, List, Sequence, Tuple

Triple = Tuple[int, int, int]
Pattern = Dict[Triple, bool]


def triple_var(t: Triple, n_points: int) -> int:
    """DIMACS variable of the sorted triple t: 1 + lexicographic index in combinations(range(N), 3)."""
    i, j, k = t
    if not (0 <= i < j < k < n_points):
        raise ValueError(f"triple {t} is not sorted inside range({n_points})")
    idx = sum(comb(n_points - a - 1, 2) for a in range(i))
    idx += sum(comb(n_points - b - 1, 1) for b in range(i + 1, j))
    return idx + (k - j - 1) + 1


def one_change(seq: Sequence[bool]) -> bool:
    return sum(x != y for x, y in zip(seq, seq[1:])) <= 1


def extensions(pattern: Pattern, points: Sequence[int], new: int) -> List[Pattern]:
    """All legal assignments of the triples through `new` that extend the legal `pattern` on `points`.

    Returns the new triples only; merge with {**pattern, **e}.  Quads are checked as soon as their last
    triple is assigned, so the depth-first search prunes early.
    """
    allp = sorted(list(points) + [new])
    new_triples = [t for t in itertools.combinations(allp, 3) if new in t]
    order = {t: n for n, t in enumerate(new_triples)}
    ready: Dict[int, List[List[Triple]]] = {}
    for q in itertools.combinations(allp, 4):
        if new not in q:
            continue
        ts = [(q[0], q[1], q[2]), (q[0], q[1], q[3]), (q[0], q[2], q[3]), (q[1], q[2], q[3])]
        ready.setdefault(max(order[t] for t in ts if t in order), []).append(ts)
    out: List[Pattern] = []
    cur = dict(pattern)

    def rec(n: int) -> None:
        if n == len(new_triples):
            out.append({t: cur[t] for t in new_triples})
            return
        t = new_triples[n]
        for v in (False, True):
            cur[t] = v
            if all(one_change([cur[x] for x in ts]) for ts in ready.get(n, ())):
                rec(n + 1)
        del cur[t]

    rec(0)
    return out


def patterns_on(points: Iterable[int]) -> List[Pattern]:
    """All legal patterns on the point set, built point by point in the given order."""
    pts: List[int] = []
    pats: List[Pattern] = [dict()]
    for new in points:
        pats = [{**p, **e} for p in pats for e in extensions(p, pts, new)]
        pts.append(new)
    return pats


def place(pattern: Pattern, points: Sequence[int]) -> Pattern:
    """Relabel a pattern on ranks 0..k-1 onto the sorted points (legality is preserved)."""
    s = sorted(points)
    return {(s[i], s[j], s[k]): v for (i, j, k), v in pattern.items()}


def lits_of(pattern: Pattern, n_points: int) -> List[int]:
    """Assumption literals of a pattern (positive = True)."""
    return [triple_var(t, n_points) if v else -triple_var(t, n_points) for t, v in sorted(pattern.items())]


def reverse(pattern: Pattern, n_points: int) -> Pattern:
    """Left-right reversal i -> N-1-i: triple (i,j,k) goes to (N-1-k, N-1-j, N-1-i) with the SAME value.

    Maps legal patterns to legal patterns (each quad's one-change sequence is reversed), cups to cups
    and caps to caps, and swaps the two strong-quad conditions.  That it is a symmetry of a particular
    CNF must still be checked for that encoding (done for the ETV CNF: runs/etv-cc-20260930/
    verify_reversal.py).
    """
    return {tuple(sorted(n_points - 1 - x for x in t)): v for t, v in pattern.items()}


def knuth_walk(order: Sequence[int], roots: Sequence[Pattern], start_depth: int,
               survives: Callable[[Pattern], bool], is_leaf: Callable[[Pattern, int], bool],
               rng: random.Random, max_depth: int | None = None) -> List[dict]:
    """One Knuth (1975) random walk down the cube tree over `order`.

    Nodes at depth d are legal patterns on order[:d]; the children of a node are its extensions by
    order[d] that `survives`.  `roots` are the depth-`start_depth` nodes (pass only surviving ones).
    The walk picks a uniformly random surviving child per level and stops at a node for which
    `is_leaf(node, depth)` is true, which has no surviving child, or at max_depth.  Returns one step per
    visited node: depth, log10 of the product of branching factors so far (the unbiased estimate of
    the number of nodes at that depth is 10**log10_prod), and children/survivors counts, with the last
    step marked "leaf" ("test", "no-survivor" or "max-depth").
    """
    max_depth = len(order) if max_depth is None else max_depth
    node, depth, lp = rng.choice(list(roots)), start_depth, math.log10(len(roots))
    steps: List[dict] = []
    while True:
        step = {"depth": depth, "log10_prod": lp}
        if is_leaf(node, depth):
            step["leaf"] = "test"
            steps.append(step)
            return steps
        if depth >= max_depth:
            step["leaf"] = "max-depth"
            steps.append(step)
            return steps
        kids = [{**node, **e} for e in extensions(node, sorted(order[:depth]), order[depth])]
        alive = [kp for kp in kids if survives(kp)]
        step.update(children=len(kids), survivors=len(alive))
        if not alive:
            step["leaf"] = "no-survivor"
            steps.append(step)
            return steps
        steps.append(step)
        node, depth, lp = rng.choice(alive), depth + 1, lp + math.log10(len(alive))


def knuth_estimates(walks: Sequence[Sequence[dict]]) -> dict:
    """Mean-of-walks estimates: leaves (last step of each walk) and internal nodes (sum over non-leaf
    steps).  Heavy-tailed: report the median of the per-walk log10 values too."""
    leaves = [w[-1]["log10_prod"] for w in walks if w and "leaf" in w[-1]]
    internal = [math.log10(sum(10 ** s["log10_prod"] for s in w if "leaf" not in s))
                for w in walks if any("leaf" not in s for s in w)]

    def mean_log(xs: List[float]) -> float | None:
        if not xs:
            return None
        top = max(xs)
        return top + math.log10(sum(10 ** (x - top) for x in xs) / len(xs))

    return {"walks": len(walks), "log10_mean_leaves": mean_log(leaves),
            "log10_median_leaves": sorted(leaves)[len(leaves) // 2] if leaves else None,
            "log10_mean_internal": mean_log(internal)}
