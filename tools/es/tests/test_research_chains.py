"""Regression fixtures for harness.research.chains (promoted from runs/claude-hypergraph-20261003/q15/lightgon.py
and the chain helpers of bl.py / dec.py / sig.py, 3 Oct 2026)."""
from __future__ import annotations

import random
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))

from harness.research import chains as ch  # noqa: E402
from harness.research import signotope_cubes as sc  # noqa: E402
from harness.research.decomposable_sets import DecomposableSet, random_labels  # noqa: E402


@pytest.fixture(scope="module")
def signotopes6():
    return sc.patterns_on(range(6))


def test_sets_of_at_most_two_points_are_both_cups_and_caps():
    cup = {(0, 1, 2): True}
    for want in (True, False):
        assert [ch.longest_chain(cup, range(m), want) for m in range(3)] == [0, 1, 2]
        assert ch.chains(cup, 0, want, range(3)) == [()]
        assert ch.chains(cup, 2, want, range(3)) == [(0, 1), (0, 2), (1, 2)]
    assert ch.longest_chain(cup, range(3), True) == 3 and ch.longest_chain(cup, range(3), False) == 2
    assert ch.strong_number(cup, range(3)) == 3 and ch.find_gon(cup, range(3), 3) == (0, 1, 2)


def test_strong_number_matches_the_four_point_definition_on_every_six_point_signotope(signotopes6):
    # 908 rank-3 signotopes (A006245), 190 of them not decomposable; largest strong set sizes 4/5/6
    sizes = {}
    for p in signotopes6:
        s = ch.strong_number(p, range(6))
        assert s == ch.strong_number_bruteforce(p, range(6))
        sizes[s] = sizes.get(s, 0) + 1
    assert sizes == {4: 496, 5: 396, 6: 16}


def test_find_gon_is_exact_and_returns_strong_sets(signotopes6):
    for p in signotopes6:
        s = ch.strong_number(p, range(6))
        for size in range(8):
            gon = ch.find_gon(p, range(6), size)
            if size <= s:
                assert gon is not None and len(gon) == size and ch.is_strong(p, gon)
            else:
                assert gon is None


def test_longest_lr_witnesses_are_chains_with_the_stated_endpoints(signotopes6):
    for p in signotopes6[::37]:
        for want in (True, False):
            best = ch.longest_lr(p, range(6), want)
            assert set(best) == {(l, r) for l in range(6) for r in range(l + 1, 6)}
            for (l, r), (length, chain) in best.items():
                assert chain[0] == l and chain[-1] == r and len(chain) == length
                assert all(p[chain[i:i + 3]] == want for i in range(length - 2))
                assert length == max(len(c) for t in range(2, 7) for c in ch.chains(p, t, want, range(l, r + 1))
                                     if c[0] == l and c[-1] == r)


def test_edge_tables_and_chain_core_agree_with_chain_enumeration():
    rng = random.Random(11)
    for _ in range(25):
        s = DecomposableSet(random_labels(rng.randint(3, 9), rng))
        for want in (True, False):
            end, start = ch.edge_chain_tables(s.cup, s.n, want)
            top = max([min(s.n, 1)] + list(end.values()))
            assert top == ch.longest_chain(s.cup, range(s.n), want) == max(start.values(), default=top)
            lo, hi, best = ch.chain_core(s.cup, range(s.n), want)
            assert best and all(len(c) == top for c in best)
            assert lo == max(c[0] for c in best) and hi == min(c[-1] for c in best)


def test_one_change_detects_non_signotopes():
    assert all(ch.is_one_change(p, range(5)) for p in sc.patterns_on(range(5)))
    bad = {(0, 1, 2): True, (0, 1, 3): False, (0, 2, 3): True, (1, 2, 3): False}
    assert not ch.is_one_change(bad, range(4))


def test_cegar_two_colouring_agrees_with_brute_force():
    pytest.importorskip("pysat")
    rng = random.Random(3)
    outcomes = set()
    for _ in range(20):
        n = rng.randint(6, 9)
        s = DecomposableSet(random_labels(n, rng))
        for size in (4, 5):
            got = ch.cegar_two_colouring(s.cup, list(range(n)), [], size)
            brute = any(
                ch.find_gon(s.cup, [p for p in range(n) if m >> p & 1], size) is None
                and ch.find_gon(s.cup, [p for p in range(n) if not m >> p & 1], size) is None
                for m in range(1 << n))
            assert (got is not None) == brute
            if got is not None:
                assert all(ch.strong_number(s.cup, part) < size for part in got)
            outcomes.add(got is not None)
    assert outcomes == {True, False}
