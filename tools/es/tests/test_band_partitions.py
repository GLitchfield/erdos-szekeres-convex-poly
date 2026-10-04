"""Regression fixtures for harness.research.band_partitions (promoted from runs/claude-bandrule-20261003/bl.py and
runs/claude-audit-bdl-20261003/dec.py, 3 Oct 2026)."""
from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))

from harness.research import band_partitions as bp  # noqa: E402
from harness.research.chains import chain_core, longest_chain, strong_number  # noqa: E402
from harness.research.decomposable_sets import DecomposableSet, coloring_from_mask, decomposable_masks  # noqa: E402

FIXTURE = ROOT / "harness/research/examples/band-partitions-v1.json"


def bdl_statistics(classes, n):
    """The per-n counts of runs/claude-audit-bdl-20261003/exh.py, recomputed with the promoted modules."""
    st = Counter()
    for mask in sorted(classes[n]):
        cup = coloring_from_mask(mask, n)
        P = range(n)
        al, be, s = longest_chain(cup, P, True), longest_chain(cup, P, False), strong_number(cup, P)
        st["colourings"] += 1
        for k in range(s + 1, al + be + 1):
            st["pairs"] += 1
            if al + be == k:
                st["one_band"] += 1
                continue
            st["pairs_multi"] += 1
            bands = bp.bdl_range(al, be, k)
            b = bp.find_partition(cup, P, k, bands)
            assert b is not None and bp.check_partition(cup, P, k, b, bands), (n, mask, k)

            def fits(j, forbidden):
                found = bp.find_partition(cup, P, k, bands, allowed=bp.allowed_from_forbid(P, bands, {j: forbidden}))
                assert found is None or bp.check_partition(cup, P, k, found, bands)
                return found is not None

            j0, j1 = k - 1 - be, al - 1
            lo, hi, caps = chain_core(cup, P, False)
            if lo < hi:
                st["cap_core"] += 1
                st["P_both"] += fits(j0, range(lo + 1, n)) and fits(j0, range(0, hi))
            st["PF_first"] += fits(j0, set(P) - {c[0] for c in caps})
            st["PF_last"] += fits(j0, set(P) - {c[-1] for c in caps})
            lo, hi, _cups = chain_core(cup, P, True)
            if lo < hi:
                st["cup_core"] += 1
                st["P'_both"] += fits(j1, range(lo + 1, n)) and fits(j1, range(0, hi))
    return dict(st)


def test_reproduces_the_frozen_exhaustive_bdl_audit_counts():
    fixture = json.loads(FIXTURE.read_text())
    top = fixture["tested_max_n"]
    classes = decomposable_masks(top)
    for n in range(3, top + 1):
        assert len(classes[n]) == fixture["coloring_counts"][str(n)]
        assert bdl_statistics(classes, n) == fixture["per_n"][str(n)], n


def test_bands_zero_and_top_hold_one_point_and_one_band_case_is_the_whole_set():
    s = DecomposableSet(["00", "01", "1"])  # 3 points
    assert s.alpha + s.beta == 5
    assert bp.partitions(s.cup, range(3), 5, [s.alpha - 1]) == [(s.alpha - 1,) * 3]
    # k = 4: bands 0..2; band 0 (cup <= 1) and band 2 (cap <= 1) take at most one point each
    for b in bp.partitions(s.cup, range(3), 4, range(0, 3)):
        assert b.count(0) <= 1 and b.count(2) <= 1 and bp.check_partition(s.cup, range(3), 4, b)
    assert bp.partitions(s.cup, range(3), 4, [-1, 3]) == []
    assert not bp.check_partition(s.cup, range(3), 4, (0, 0, 1))


def test_search_options_limit_first_allowed_and_subsets():
    s = DecomposableSet(["000", "10", "001", "01", "11"])
    k = 5
    allp = bp.partitions(s.cup, range(5), k, range(k - 1))
    assert allp and len(set(allp)) == len(allp)
    assert all(bp.check_partition(s.cup, range(5), k, b) for b in allp)
    assert bp.partitions(s.cup, range(5), k, range(k - 1), limit=2) == allp[:2]
    assert bp.find_partition(s.cup, range(5), k, range(k - 1)) == allp[0]
    allowed = {p: {1, 2} for p in range(5)}
    restricted = bp.partitions(s.cup, range(5), k, range(k - 1), allowed=allowed)
    assert restricted == [b for b in allp if set(b) <= {1, 2}]
    sub = [0, 2, 4]
    for b in bp.partitions(s.cup, sub, k, range(k - 1)):
        assert len(b) == 3 and bp.check_partition(s.cup, sub, k, b)


def test_sat_cross_check_agrees_with_backtracking():
    pytest.importorskip("pysat")
    classes = decomposable_masks(6)
    seen = Counter()
    for n in (5, 6):
        for mask in sorted(classes[n])[::3]:
            cup = coloring_from_mask(mask, n)
            al, be = longest_chain(cup, range(n), True), longest_chain(cup, range(n), False)
            for k in range(3, al + be + 1):
                bands = bp.bdl_range(al, be, k)
                bt = bp.find_partition(cup, range(n), k, bands)
                sat = bp.partition_sat(cup, range(n), k, bands)
                assert (bt is None) == (sat is None)
                assert sat is None or bp.check_partition(cup, range(n), k, sat, bands)
                seen[sat is None] += 1
    assert seen[True] and seen[False]
