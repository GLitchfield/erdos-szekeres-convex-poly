"""Regression fixtures for harness.research.point_sets and harness.research.realizability (promoted 2026-10-10 from
runs/claude-halving-20261008/verify_points.py and cell_descent.py)."""
from __future__ import annotations

import itertools
import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))

from harness.research import point_sets as ps  # noqa: E402

FIXTURE = ROOT / 'harness/research/examples/split6-counterexample-v1.json'


def load():
    return json.loads(FIXTURE.read_text())


def test_split6_counterexample_exact():
    fx = load(); P = [tuple(p) for p in fx['points']]
    out = ps.check_split_counterexample(P, 6)
    assert out['general_position'] and out['convex_k_sets'] == 0
    assert out['convex_km1_sets'] == fx['expected']['convex_pentagons'] == 292
    assert out['bipartition'] is None and out['counterexample']
    assert ps.sweep_key(P) == fx['sweep_key']


def test_convex_position_against_hull_definition():
    # convex position <=> every point is a hull vertex; compare with a gift-wrapping hull on small random sets
    import random
    rng = random.Random(3)
    for _ in range(30):
        P = [(rng.randrange(-50, 50), rng.randrange(-50, 50)) for _ in range(6)]
        if not ps.general_position(P):
            continue
        # hull vertices: points not inside any triangle of others (the definition used) must agree with
        # the extreme-point test: p is extreme iff some line through p has all others strictly on one side
        for i, p in enumerate(P):
            others = [q for j, q in enumerate(P) if j != i]
            inside = any(ps.in_triangle(p, a, b, c) for a, b, c in itertools.combinations(others, 3))
            extreme = any(all(ps.orient(p, q, r) > 0 for r in others if r != q) or all(ps.orient(p, q, r) < 0 for r in others if r != q) for q in others)
            assert inside == (not extreme)


def test_bipartition_finder_small():
    # four points in convex position: the unique 4-gon cannot be split, two triangles can
    P = [(0, 0), (10, 1), (11, 10), (1, 9)]
    assert ps.gon_free_bipartition(4, ps.convex_subsets(P, 4)) is not None       # mask splitting the single 4-set
    assert ps.gon_free_bipartition(4, ps.convex_subsets(P, 3)) is not None       # 2 + 2 splits every triangle
    P5 = [(0, 0), (10, 1), (12, 8), (5, 12), (-2, 7)]
    assert ps.gon_free_bipartition(5, ps.convex_subsets(P5, 3)) is None           # a side has >= 3 points, hence a triangle


def test_realizer_controls_and_witness():
    pytest.importorskip('scipy')
    from harness.research import realizability as rz
    fx = load(); ctrl = fx['realizable_control_10pt']
    Q, b = rz.realize(10, ctrl['key'], restarts=3, kicks=10, seed=1)
    assert Q is not None and ps.sweep_key(Q) == ctrl['key']
    Q8, _ = rz.realize(8, fx['pentagon_free_8pt_key'], restarts=5, kicks=10, seed=0)
    assert Q8 is not None and not ps.convex_subsets(Q8, 5)
