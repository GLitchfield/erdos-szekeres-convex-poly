"""Independent complete-triple/quad definitions and retained R25 fixtures."""
from itertools import combinations
import json
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from harness.research.triple_metrics import FiniteTripleColoring
from harness.research.binary_labels import binary_label_coloring


def direct(colors, n, ground):
    points = tuple(x for x in range(n) if ground >> x & 1)
    chains = {True: [], False: []}
    sigma = 0
    for size in range(len(points) + 1):
        for S in combinations(points, size):
            for want in (True, False):
                if all(colors[T] == want for T in combinations(S, 3)):
                    chains[want].append(S)
            # Independent compiled characterization: a strong set's triple
            # color depends only on its middle point, including tiny sets.
            if all(len({colors[a, b, c] for a in S if a < b
                        for c in S if c > b}) <= 1 for b in S):
                sigma = max(sigma, size)
    metrics = tuple(max(map(len, chains[want])) for want in (True, False))
    extrema = {}
    for want, size in zip((True, False), metrics):
        maximal = [S for S in chains[want] if len(S) == size]
        extrema[want] = (frozenset(S[0] for S in maximal if S),
                         frozenset(S[-1] for S in maximal if S))
    return metrics, sigma, extrema


def test_every_arbitrary_coloring_and_subset_through_five():
    for n in range(6):
        triples = tuple(combinations(range(n), 3))
        for bits in range(1 << len(triples)):
            colors = {T: bool(bits >> i & 1) for i, T in enumerate(triples)}
            value = FiniteTripleColoring(colors, n)
            for ground in range(1 << n):
                metrics, sigma, extrema = direct(colors, n, ground)
                assert value.metrics(ground) == metrics, (n, bits, ground)
                assert value.strong_number(ground) == sigma, (n, bits, ground)
                for want in (True, False):
                    assert value.extrema(ground, want) == extrema[want]


def fixture_colors(case):
    triples = tuple(combinations(range(case['n']), 3))
    if 'mask' in case:
        return {T: bool(case['mask'] >> i & 1) for i, T in enumerate(triples)}
    return binary_label_coloring(case['labels'])


def test_retained_research_fixtures():
    fixture = json.loads((ROOT / 'harness/research/examples/triple-metrics-v1.json').read_text())
    for case in fixture['cases']:
        colors = fixture_colors(case)
        value = FiniteTripleColoring(colors, case['n'])
        assert value.metrics() == tuple(case['metrics']), case['name']
        assert value.strong_number() == case['strong'], case['name']
        for want, key in [(True, 'cores'), (False, 'cap_core')]:
            if key == 'cores' and key in case:
                for index, color in enumerate((True, False)):
                    F, L = value.extrema(None, color)
                    assert [max(F), min(L)] == case[key][index]
            elif key in case:
                F, L = value.extrema(None, want)
                assert [max(F), min(L)] == case[key]
        for query in case.get('queries', []):
            assert value.metrics(query['mask']) == tuple(query['metrics'])
            assert value.strong_number(query['mask']) == query['strong']


def test_duality_snapshot_and_immutable_results():
    colors = {(0, 1, 2): True}
    value = FiniteTripleColoring(colors, 3)
    colors[0, 1, 2] = False
    assert value.metrics() == (3, 2)
    dual = FiniteTripleColoring(colors, 3)
    assert dual.metrics() == (2, 3)
    assert value.monochromatic_masks(True) == dual.monochromatic_masks(False)
    assert value.strong_masks() == dual.strong_masks()
    assert isinstance(value.monochromatic_masks(True), tuple)
    assert value.extrema(0, True) == (frozenset(), frozenset())
    with pytest.raises(TypeError):
        value.colors[0, 1, 2] = False


@pytest.mark.parametrize('n', [-1, True, 3.0, '3'])
def test_invalid_size(n):
    with pytest.raises(ValueError):
        FiniteTripleColoring({}, n)


@pytest.mark.parametrize('colors,n', [({}, 3), ({(0, 2, 1): True}, 3),
    ({(0, 1, 2): 1}, 3), ({(False, 1, 2): True}, 3)])
def test_invalid_complete_coloring(colors, n):
    with pytest.raises(ValueError):
        FiniteTripleColoring(colors, n)


@pytest.mark.parametrize('mask', [-1, 8, True, 1.0, '1'])
def test_invalid_subset(mask):
    value = FiniteTripleColoring({}, 2)
    with pytest.raises(ValueError):
        value.metrics(mask)
    with pytest.raises(ValueError):
        value.strong_number(mask)


def test_invalid_chain_color_and_nonmapping():
    value = FiniteTripleColoring({}, 0)
    with pytest.raises(ValueError):
        value.extrema(None, 1)
    with pytest.raises(TypeError):
        FiniteTripleColoring([], 0)
