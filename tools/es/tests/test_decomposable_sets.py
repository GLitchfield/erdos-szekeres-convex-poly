"""Regression fixtures for harness.research.decomposable_sets (promoted from runs/claude-bandrule-20261003/bl.py and
runs/claude-audit-bdl-20261003/dec.py, 3 Oct 2026)."""
from __future__ import annotations

import random
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))

from harness.research import decomposable_sets as ds  # noqa: E402
from harness.research import signotope_cubes as sc  # noqa: E402
from harness.research.chains import longest_chain, strong_number, strong_number_bruteforce  # noqa: E402


@pytest.fixture(scope="module")
def classes():
    return ds.decomposable_masks(7)


def test_exact_class_counts(classes):
    # runs/claude-audit-bdl-20261003 re-derived these independently (and 186888, 3816380 for n = 8, 9)
    assert [len(classes[n]) for n in range(3, 8)] == [2, 8, 62, 718, 10596]


def test_label_trees_generate_exactly_the_enumerated_class(classes):
    reps = {1: [[""]]}
    for m in range(2, 7):
        seen = {}
        for low in range(1, (1 << m) - 1):
            pos = [x for x in range(m) if low >> x & 1]
            for A in reps[len(pos)]:
                for B in reps[m - len(pos)]:
                    labels = ds.compose(A, B, pos)
                    seen.setdefault(ds.mask_from_coloring(ds.coloring_from_labels(labels), m), labels)
        reps[m] = list(seen.values())
        assert set(seen) == (classes[m] if m >= 3 else {0})


def test_exact_decomposability_separates_the_six_point_signotopes(classes):
    accepted = {ds.mask_from_coloring(p, 6) for p in sc.patterns_on(range(6))
                if ds.Decomposability(p).dec(range(6))}
    assert accepted == classes[6]  # 718 of the 908 signotopes


def test_mask_conversion_matches_the_enumerator_convention(classes):
    sys.path.insert(0, str(ROOT / "scripts"))
    from enumerate_decomposable_colorings import coloring_dict, triple_index
    for mask in sorted(classes[6])[::50]:
        cup = ds.coloring_from_mask(mask, 6)
        assert cup == coloring_dict(mask, 6, triple_index(6))
        assert ds.mask_from_coloring(cup, 6) == mask


def test_threshold_matches_lean_and_the_exact_maximum_for_small_values(classes):
    sys.path.insert(0, str(ROOT / "scripts"))
    from enumerate_decomposable_colorings import threshold as legacy
    for k in range(3, 12):
        for a in range(2, k + 1):
            for u in range(2, k + 1):
                assert ds.threshold(a, u, k) == legacy(a, u, k)
    assert ds.threshold(4, 4, 6) == 6 and ds.threshold(6, 6, 6) == 16 and ds.threshold(1, 5, 5) == 0
    nmax = 7
    realised = {1: {(1, 1, 1)}, 2: {(2, 2, 2)}}
    for n in range(3, nmax + 1):
        realised[n] = set()
        for mask in classes[n]:
            cup = ds.coloring_from_mask(mask, n)
            realised[n].add((longest_chain(cup, range(n), True), longest_chain(cup, range(n), False),
                             strong_number(cup, range(n))))
    exact = 0
    for k in range(3, 11):
        for a in range(2, k + 1):
            for u in range(2, k + 1):
                best = max([n for n in realised
                            if any(al <= u - 1 and be <= a - 1 and s <= k - 1 for al, be, s in realised[n])])
                if best < nmax:
                    exact += 1
                    assert best == ds.threshold(a, u, k), (a, u, k)
                else:
                    assert ds.threshold(a, u, k) >= nmax, (a, u, k)
    assert exact == 139


def test_decomposable_set_object_and_splits():
    rng = random.Random(5)
    for trial in range(30):
        labels = (ds.random_labels if trial % 2 else ds.random_nested_labels)(rng.randint(2, 9), rng)
        s = ds.DecomposableSet(labels)
        assert s.alpha == longest_chain(s.cup, range(s.n), True)
        assert s.beta == longest_chain(s.cup, range(s.n), False)
        assert s.strong == strong_number_bruteforce(s.cup, range(s.n))
        low, A, B = s.root_split()
        assert ds.compose(A, B, low) == s.labels
        dec = ds.Decomposability(s.cup)
        upper = [p for p in range(s.n) if p not in low]
        if low and upper:
            assert (low, upper) in dec.splits(range(s.n))
        assert dec.dec(range(s.n))


def test_labels_are_validated_and_normalised():
    assert ds.DecomposableSet([(0, 0), (1,), (0, 1)]).labels == ["00", "1", "01"]
    for bad in (["0", "01"], ["0", "0"], ["0", "2"]):
        with pytest.raises(ValueError):
            ds.DecomposableSet(bad)
    with pytest.raises(ValueError):
        ds.compose(["", ""], [""], [0])
