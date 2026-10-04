"""Decomposable point sets as binary label trees, their root splits, and exact decomposability.

Promoted on 3 Oct 2026 from runs/claude-bandrule-20261003/bl.py (copied verbatim into five 3 Oct run
directories and imported by about 200 run scripts) and runs/claude-audit-bdl-20261003/dec.py. The
run files stay unchanged as the recorded artifacts. The exact enumerator is not duplicated:
``decomposable_masks`` wraps ``scripts/enumerate_decomposable_colorings.enumerate_class``
(catalog ``decomposable.coloring-enumeration``), whose class counts on n = 3..9 points are
2, 8, 62, 718, 10596, 186888, 3816380 (n <= 7 regression-tested; n = 8, 9 from
runs/claude-audit-bdl-20261003, which re-derived them independently).

Conventions (see harness.research.chains for chains and strong sets; sets of <= 2 points are both cups
and caps):

* A decomposable set is ``IsDecomposableOn`` in ErdosSzekeres/Decomposable.lean: a singleton, or a split
  into a nonempty lower part A and upper part B, both decomposable, arbitrarily interleaved in x-order,
  such that a triple meeting both parts is a cup iff its middle point lies in A (Lemma M).
* Labels: point p (in x-order) carries a binary string, the root-to-leaf path of p, '0' = lower child,
  '1' = upper child. Labels must be pairwise distinct and prefix-free (a full-depth fixed-length labelling,
  as decoded from SAT models, qualifies). Triple p<q<r is a cup iff at the first position where the three
  labels are not all equal the middle label has '0'. Every prefix-free labelling gives a decomposable
  colouring and every decomposable colouring arises this way (regression-tested on n <= 6).
* Bitmasks follow the enumerator: bit t is the t-th triple of itertools.combinations(range(n), 3);
  set bit = cup.

Diagnostic computation only, not Lean proofs.
"""
from __future__ import annotations

import itertools
import sys
from math import comb
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from .chains import (chain_core, chains as _chains, edge_chain_tables, longest_chain, strong_number)

Triple = Tuple[int, int, int]


# ---------------------------------------------------------------- labels and colourings

def normalize_labels(labels: Iterable) -> List[str]:
    """Labels as '0'/'1' strings; accepts strings or sequences of 0/1 (e.g. SAT-decoded tuples)."""
    return [l if isinstance(l, str) else "".join(str(int(x)) for x in l) for l in labels]


def check_labels(labels: Sequence[str]) -> None:
    """Raise ValueError unless the labels are binary, pairwise distinct and prefix-free."""
    for l in labels:
        if any(ch not in "01" for ch in l):
            raise ValueError(f"label {l!r} is not a binary string")
    srt = sorted(labels)
    for a, b in zip(srt, srt[1:]):
        if b.startswith(a):
            raise ValueError(f"labels {a!r} and {b!r} are equal or one is a prefix of the other")


def coloring_from_labels(labels: Sequence[str]) -> Dict[Triple, bool]:
    """``cup[(p, q, r)]`` for p<q<r: True iff the middle label has '0' where the three labels first differ."""
    n = len(labels)
    cup: Dict[Triple, bool] = {}
    for p, q, r in itertools.combinations(range(n), 3):
        a, b, c = labels[p], labels[q], labels[r]
        i = 0
        while i < len(a) and i < len(b) and i < len(c) and a[i] == b[i] == c[i]:
            i += 1
        cup[(p, q, r)] = b[i] == "0"
    return cup


def coloring_from_mask(mask: int, n: int) -> Dict[Triple, bool]:
    return {t: bool(mask >> i & 1) for i, t in enumerate(itertools.combinations(range(n), 3))}


def mask_from_coloring(cup: Dict[Triple, bool], n: int) -> int:
    return sum(1 << i for i, t in enumerate(itertools.combinations(range(n), 3)) if cup[t])


def decomposable_masks(max_n: int) -> Dict[int, set]:
    """``{m: set of bitmasks}`` of every decomposable colouring on m = 1..max_n points (exact). Wraps the
    catalogued enumerator ``scripts/enumerate_decomposable_colorings.enumerate_class``; n = 7 takes a few
    seconds, n = 8 about a minute, n = 9 needs a guarded job."""
    scripts = str(Path(__file__).resolve().parents[2] / "scripts")
    if scripts not in sys.path:
        sys.path.insert(0, scripts)
    from enumerate_decomposable_colorings import enumerate_class

    classes, _index = enumerate_class(max_n, progress=False)
    return classes


# ---------------------------------------------------------------- the set object

class DecomposableSet:
    """A decomposable point set given by labels, with its colouring and chain data precomputed.

    Attributes match runs/claude-bandrule-20261003/bl.py ``S``: ``labels``, ``n``, ``cup`` (triple -> bool),
    ``end[want][(i, j)]`` / ``st[want][(i, j)]`` (longest chain ending / starting with edge i<j),
    ``alpha`` (cup number), ``beta`` (cap number), ``strong`` (largest strong set).
    """

    def __init__(self, labels: Iterable, validate: bool = True):
        self.labels = normalize_labels(labels)
        if validate:
            check_labels(self.labels)
        self.n = n = len(self.labels)
        self.cup = coloring_from_labels(self.labels)
        self.end = {}
        self.st = {}
        for want in (True, False):
            self.end[want], self.st[want] = edge_chain_tables(self.cup, n, want)
        self.alpha = max([min(n, 1)] + list(self.end[True].values()))
        self.beta = max([min(n, 1)] + list(self.end[False].values()))
        self.strong = strong_number(self.cup, range(n))

    def longest(self, sub: Iterable[int], want: bool) -> int:
        return longest_chain(self.cup, sub, want)

    def chains(self, t: int, want: bool, sub: Optional[Iterable[int]] = None) -> List[Tuple[int, ...]]:
        return _chains(self.cup, t, want, range(self.n) if sub is None else sub)

    def cap_core(self, sub: Optional[Iterable[int]] = None):
        return chain_core(self.cup, range(self.n) if sub is None else sub, False)

    def cup_core(self, sub: Optional[Iterable[int]] = None):
        return chain_core(self.cup, range(self.n) if sub is None else sub, True)

    def root_split(self):
        return root_split(self.labels)


# ---------------------------------------------------------------- generation and composition

def compose(A: Sequence[str], B: Sequence[str], lowerpos: Iterable[int]) -> List[str]:
    """Labels of X = A << B (A lower, B upper); ``lowerpos`` = the x-positions in X of A's points."""
    n = len(A) + len(B)
    ps = set(lowerpos)
    if len(ps) != len(A) or not all(0 <= x < n for x in ps):
        raise ValueError("lowerpos must list len(A) distinct positions in range(len(A) + len(B))")
    out: List[str] = []
    ia = ib = 0
    for x in range(n):
        if x in ps:
            out.append("0" + A[ia])
            ia += 1
        else:
            out.append("1" + B[ib])
            ib += 1
    return out


def root_split(labels: Sequence[str]) -> Tuple[List[int], List[str], List[str]]:
    """``(lower positions, A labels, B labels)`` of the labelled root split (first label character).
    If every label starts with the same character the root is unary and one side is empty."""
    low = [p for p, l in enumerate(labels) if l[0] == "0"]
    A = [l[1:] for l in labels if l[0] == "0"]
    B = [l[1:] for l in labels if l[0] == "1"]
    return low, A, B


def random_labels(n: int, rng) -> List[str]:
    """Random decomposable set on n >= 1 points: uniform split size, uniform interleaving, recursively."""
    if n == 1:
        return [""]
    m = rng.randint(1, n - 1)
    A = random_labels(m, rng)
    B = random_labels(n - m, rng)
    return compose(A, B, sorted(rng.sample(range(n), m)))


def random_nested_labels(n: int, rng, pnest: float = 0.6) -> List[str]:
    """As ``random_labels`` but biased toward nested splits: with probability pnest one part is a contiguous
    x-block strictly inside the other (lower inside upper or upper inside lower, equally likely)."""
    if n == 1:
        return [""]
    m = rng.randint(1, n - 1)
    A = random_nested_labels(m, rng, pnest)
    B = random_nested_labels(n - m, rng, pnest)
    r = rng.random()
    if r < pnest / 2 and n - m >= 2:
        st = rng.randint(1, n - m - 1)
        pos = list(range(st, st + m))
    elif r < pnest and m >= 2:
        st = rng.randint(1, m - 1)
        upper = set(range(st, st + n - m))
        pos = [x for x in range(n) if x not in upper]
    else:
        pos = sorted(rng.sample(range(n), m))
    return compose(A, B, pos)


# ---------------------------------------------------------------- exact decomposability of a colouring

def all_splits(cup: Dict[Triple, bool], pts: Iterable[int]) -> List[Tuple[List[int], List[int]]]:
    """Every ordered split (L, U), both nonempty, of the sorted points with every triple meeting both parts
    a cup iff its middle point is in L. Decomposability of the parts is not checked here."""
    pts = sorted(pts)
    m = len(pts)
    out: List[Tuple[List[int], List[int]]] = []
    side: Dict[int, str] = {}

    def ok_last(i: int) -> bool:
        z = pts[i]
        for a in range(i):
            for b in range(a + 1, i):
                x, y = pts[a], pts[b]
                if side[x] == side[y] == side[z]:
                    continue
                if cup[(x, y, z)] != (side[y] == "L"):
                    return False
        return True

    def rec(i: int) -> None:
        if i == m:
            if "L" in side.values() and "U" in side.values():
                out.append(([p for p in pts if side[p] == "L"], [p for p in pts if side[p] == "U"]))
            return
        for sd in ("L", "U"):
            side[pts[i]] = sd
            if ok_last(i):
                rec(i + 1)
            del side[pts[i]]

    rec(0)
    return out


class Decomposability:
    """Memoised exact decomposability and root-split enumeration for subsets of one colouring (bl.Dec).
    ``dec(pts)`` decides ``IsDecomposableOn`` for the sorted point subset; ``splits(pts)`` lists its root
    splits with both parts decomposable. Exponential in |pts|; fine for a few dozen structured points."""

    def __init__(self, cup: Dict[Triple, bool]):
        self.cup = cup
        self.memo: Dict[Tuple[int, ...], bool] = {}

    def splits(self, pts: Iterable[int]) -> List[Tuple[List[int], List[int]]]:
        return [(L, U) for (L, U) in all_splits(self.cup, pts) if self.dec(L) and self.dec(U)]

    def dec(self, pts: Iterable[int]) -> bool:
        key = tuple(sorted(pts))
        if len(key) <= 2:
            return True
        if key not in self.memo:
            self.memo[key] = any(self.dec(L) and self.dec(U) for (L, U) in all_splits(self.cup, key))
        return self.memo[key]


# ---------------------------------------------------------------- threshold

def _nsub(x: int, y: int) -> int:
    return x - y if x > y else 0


def threshold(a: int, u: int, k: int) -> int:
    """``decomposableThreshold a u k`` (ErdosSzekeres/Decomposable.lean) for natural a, u, k, with Lean's
    truncated subtraction: the largest decomposable set with no a-cap, no u-cup and no strong k-set
    (cap <= a-1, cup <= u-1, strong <= k-1), as checked against exhaustive enumeration for small values."""
    if min(a, u, k) < 0:
        raise ValueError("threshold takes natural numbers")
    if a == 1 or u == 1:
        return 0
    if a + u <= k + 3:
        return comb(_nsub(a + u, 4), _nsub(a, 2))
    return sum(comb(_nsub(k, 2), j) for j in range(_nsub(k, a), _nsub(u, 2) + 1))
