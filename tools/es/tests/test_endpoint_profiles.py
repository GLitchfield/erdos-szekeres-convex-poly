"""Independent legacy-signature fixtures and public-input regression checks."""
from copy import deepcopy
import json
from pathlib import Path

import pytest

from harness.research.endpoint_profiles import (
    child_slot_barriers, expand_run_profile, refine_slot_profile,
)


ROOT = Path(__file__).resolve().parents[3]
FIXTURE = ROOT / 'harness/research/examples/endpoint-profiles-v1.json'


def state(saved):
    return tuple(tuple(tuple(row) for row in saved[key]) for key in ('caps', 'cups')) + (
        tuple(saved['barriers']),)


def test_independent_original_signature_fixtures():
    fixture = json.loads(FIXTURE.read_text())
    assert fixture['diagnostic'] and len(fixture['rows']) == 4
    for row in fixture['rows']:
        parent = row['parent']
        before = deepcopy(parent)
        assert expand_run_profile(row['word'], parent['run_caps'], parent['run_cups']) == state(parent)
        for child in row['children']:
            args = (parent['caps'], parent['cups'], child['keep'], child['side'],
                    child['opposite_max'], row['case'][2] - 1)
            actual = (*refine_slot_profile(*args), child_slot_barriers(
                parent['barriers'], child['keep']))
            assert actual == state(child['expected'])
            assert refine_slot_profile(*args) == refine_slot_profile(
                args[0], args[1], reversed(args[2]), *args[3:])
        assert parent == before


@pytest.mark.parametrize('keep', [[], [0, 0], [0, 1], [2], [True]])
def test_rejects_ambiguous_or_invalid_retained_indices(keep):
    matrix = [[2, 3], [0, 2]]
    with pytest.raises(ValueError):
        refine_slot_profile(matrix, matrix, keep, 'lower', 1, 3)


@pytest.mark.parametrize('matrix', [
    [[2], [0, 2]], [[2, 3], [1, 2]], [[-1, 3], [0, 2]], [[2.0, 3], [0, 2]],
])
def test_rejects_malformed_endpoint_matrices(matrix):
    with pytest.raises(ValueError):
        refine_slot_profile(matrix, [[2, 3], [0, 2]], [0], 'lower', 1, 3)


@pytest.mark.parametrize('side,opposite,strong', [
    ('unknown', 1, 3), ('lower', 0, 3), ('upper', 3, 3), ('lower', True, 3),
])
def test_rejects_invalid_child_capacity_contract(side, opposite, strong):
    matrix = [[2, 3], [0, 2]]
    with pytest.raises(ValueError):
        refine_slot_profile(matrix, matrix, [0], side, opposite, strong)


def test_empty_expansion_and_marker_barrier_contract():
    assert expand_run_profile([], [], []) == ((), (), ())
    assert child_slot_barriers([], [0]) == ()
    with pytest.raises(ValueError):
        expand_run_profile(['S'], [], [])
    with pytest.raises(ValueError):
        child_slot_barriers([0], [0])
    with pytest.raises(ValueError):
        refine_slot_profile([[2, 3], [0, 2]], [[2]], [0], 'lower', 1, 3)
