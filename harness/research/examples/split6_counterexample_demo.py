"""Exact check of the 16-point SPLIT(6) counterexample in examples/split6-counterexample-v1.json, then a
realization of the 8-point pentagon-free key of charts-v1.json by harness.research.realizability (needs scipy)."""
import json, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..'))
from harness.research import point_sets as ps
fx = json.load(open(os.path.join(os.path.dirname(__file__), 'split6-counterexample-v1.json')))
P = [tuple(p) for p in fx['points']]
out = ps.check_split_counterexample(P, fx['k'])
print('16 points:', out)
assert out['counterexample'] and out['convex_k_sets'] == 0 and out['convex_km1_sets'] == fx['expected']['convex_pentagons']
assert ps.sweep_key(P) == fx['sweep_key']
try:
    from harness.research import realizability as rz
    key = fx['pentagon_free_8pt_key']; Q, b = rz.realize(8, key, restarts=5, kicks=10, seed=0)
    print('8-point pentagon-free key realized:', Q is not None, '; key check:', Q is not None and ps.sweep_key(Q) == key)
    assert Q is not None and not ps.convex_subsets(Q, 5)
except ImportError as e:
    print('realizability demo skipped (scipy missing):', e)
