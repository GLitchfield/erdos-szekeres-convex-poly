"""All-triple profiles, immutable retained labels and strict input semantics."""
from itertools import combinations
import json
from math import comb
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from harness.research.binary_labels import classical_pascal_labels, binary_label_coloring
from harness.research.triple_metrics import FiniteTripleColoring


def test_classical_profiles_counts_and_duality_through_ten_points():
    for cup in range(1, 7):
        for cap in range(1, 7):
            if cup + cap > 7:
                continue
            labels = classical_pascal_labels(cup, cap)
            assert isinstance(labels, tuple)
            assert len(labels) == comb(cup + cap - 2, cup - 1)
            assert len(labels) == len(set(labels))
            assert not any(y.startswith(x) for i, x in enumerate(labels)
                           for j, y in enumerate(labels) if i != j)
            value = FiniteTripleColoring(binary_label_coloring(labels), len(labels))
            expected = (1, 1) if min(cup, cap) == 1 else (cup, cap)
            assert value.metrics() == expected, (cup, cap)
            assert value.strong_number() == (1 if min(cup, cap) == 1 else cup + cap - 2)
            dual = tuple(''.join('1' if bit == '0' else '0' for bit in x)
                         for x in reversed(labels))
            assert dual == classical_pascal_labels(cap, cup)


def test_retained_fixture_exact_words_and_profiles():
    fixture = json.loads((ROOT / 'harness/research/examples/binary-labels-v1.json').read_text())
    for case in fixture['cases']:
        labels = classical_pascal_labels(case['cup'], case['cap'])
        assert list(labels) == case['labels']
        value = FiniteTripleColoring(binary_label_coloring(labels), len(labels))
        assert value.metrics() == tuple(case['metrics'])
        assert value.strong_number() == case['strong']


def test_decoder_preserves_spatial_order_and_snapshots_iterables():
    assert binary_label_coloring([]) == {}
    assert binary_label_coloring(['']) == {}
    assert binary_label_coloring(['1', '00', '01']) == {(0, 1, 2): True}
    source = ['0', '10', '11']
    colors = binary_label_coloring(iter(source))
    source[:] = ['00', '01', '1']
    assert colors == {(0, 1, 2): False}
    assert binary_label_coloring(source) == {(0, 1, 2): True}
    assert set(colors) == set(combinations(range(3), 3))
    assert all(type(value) is bool for value in colors.values())
    assert classical_pascal_labels(1, 1_000_000) == ('',)
    assert classical_pascal_labels(1_000_000, 1) == ('',)


@pytest.mark.parametrize('bad', [True, False, 0, -1, 2.0, '2', None])
def test_invalid_classical_bound(bad):
    with pytest.raises(ValueError):
        classical_pascal_labels(bad, 3)
    with pytest.raises(ValueError):
        classical_pascal_labels(3, bad)


@pytest.mark.parametrize('labels', ['01', b'01', ['0', '0'], ['0', '01'],
                                    ['', '0'], ['2'], [0], [True], ['a']])
def test_invalid_binary_labels(labels):
    with pytest.raises(ValueError):
        binary_label_coloring(labels)
