"""Regression fixtures for harness.research.signotope_cubes (promoted from runs/etv-cc-20260930)."""
from __future__ import annotations

import itertools
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))

from harness.research import signotope_cubes as sc  # noqa: E402


def test_legal_pattern_counts_match_a006245():
    # rank-3 signotopes: 1, 1, 2, 8, 62, 908 on 1..6 points (24698 on 7, checked in the run)
    assert [len(sc.patterns_on(range(n))) for n in range(1, 7)] == [1, 1, 2, 8, 62, 908]


def test_every_pattern_obeys_the_one_change_law():
    for p in sc.patterns_on(range(6)):
        for q in itertools.combinations(range(6), 4):
            i, j, k, l = q
            assert sc.one_change([p[(i, j, k)], p[(i, j, l)], p[(i, k, l)], p[(j, k, l)]])


def test_triple_var_is_lexicographic_and_bijective():
    n = 9
    expect = {t: v for v, t in enumerate(itertools.combinations(range(n), 3), start=1)}
    assert all(sc.triple_var(t, n) == v for t, v in expect.items())


def test_triple_var_matches_the_etv_generator():
    sys.path.insert(0, str(ROOT / "scripts"))
    from generate_etv_tseitin_sat import Instance
    inst = Instance(10, 6, 5, 6, False)
    inst.build()
    assert all(sc.triple_var(t, 10) == v for t, v in inst.triple.items())


def test_reversal_is_an_involution_on_legal_patterns_with_ten_palindromes_on_five_points():
    n = 27
    s5 = [0, 26, 13, 6, 20]  # reversal-closed
    pats = [sc.place(p, s5) for p in sc.patterns_on(range(5))]
    keys = {frozenset(p.items()) for p in pats}
    rev = [sc.reverse(p, n) for p in pats]
    assert all(frozenset(r.items()) in keys for r in rev)
    assert all(sc.reverse(r, n) == p for p, r in zip(pats, rev))
    assert sum(r == p for p, r in zip(pats, rev)) == 10  # 26 pairs + 10 palindromes = 62


def test_place_and_lits_round_trip():
    p = sc.patterns_on(range(4))[3]
    q = sc.place(p, [2, 5, 7, 11])
    lits = sc.lits_of(q, 12)
    assert len(lits) == 4 and all(abs(x) == sc.triple_var(t, 12) for x, t in zip(lits, sorted(q)))


def test_knuth_walk_estimates_the_full_tree_when_nothing_is_pruned():
    # no pruning, leaves at depth 5: each walk's product is a positive integer (one walk may overshoot,
    # e.g. 2*4*8 = 64); the mean over walks is an unbiased estimate of the 62 legal 5-point patterns
    order = list(range(5))
    roots = sc.patterns_on(order[:3])
    walks = [sc.knuth_walk(order, roots, 3, survives=lambda p: True, is_leaf=lambda p, d: d == 5,
                           rng=random.Random(s)) for s in range(400)]
    assert all(w[-1]["leaf"] == "test" and w[-1]["depth"] == 5 for w in walks)
    assert all(abs(10 ** w[-1]["log10_prod"] - round(10 ** w[-1]["log10_prod"])) < 1e-6 for w in walks)
    est = sc.knuth_estimates(walks)
    assert abs(10 ** est["log10_mean_leaves"] - 62) < 8
