"""Regression fixture for harness.research.cegar_obstructions (promoted 2026-10-10 from
runs/claude-fbdl-20261010/fbdl_obstructions.py)."""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))

FIXTURE = ROOT / 'harness/research/examples/cegar-obstructions-v1.json'


@pytest.mark.parametrize('case', json.loads(FIXTURE.read_text())['cases'], ids=lambda c: f"n{c['n']}k{c['k']}{'free' if c['kfree'] else ''}")
def test_band_stack_obstructions(case):
    pytest.importorskip('pysat')
    from harness.research.cegar_obstructions import band_stack_obstructions
    from harness.research.band_partitions import find_partition
    import itertools
    r = band_stack_obstructions(case['n'], case['k'], kfree=case['kfree'])
    assert r.status == case['status']
    found = sorted((o['cup'], o['cap']) for o in r.obstructions)
    assert found == sorted((o['cup'], o['cap']) for o in case['obstructions'])
    if case.get('all_minimal'):
        assert all(o['minimal'] for o in r.obstructions)
    for o in r.obstructions:   # every recorded obstruction really has no stack (independent backtracking search)
        n = o['n']; cup = {t: o['key'][i] == '1' for i, t in enumerate(itertools.combinations(range(n), 3))}
        assert find_partition(cup, range(n), case['k'], range(case['k'] - 1)) is None
