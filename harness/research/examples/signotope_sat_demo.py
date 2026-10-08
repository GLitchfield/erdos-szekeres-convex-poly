"""Recompute the fast threshold cases of examples/signotope-sat-thresholds-v1.json with the signotope SAT base.
Run from the repository root: python3 harness/research/examples/signotope_sat_demo.py  (needs python-sat)."""
import json, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..'))
from harness.research import signotope_sat as ss
fx = json.load(open(os.path.join(os.path.dirname(__file__), 'signotope-sat-thresholds-v1.json')))
for c in fx['cases']:
    inst = ss.threshold_instance(c['n'], c.get('k'), c.get('cup'), c.get('cap'), c.get('radial', False))
    sat, chi = inst.solve()
    got = 'SAT' if sat else 'UNSAT'
    print(f"{c['name']:40s} n={c['n']}: {got} (fixture {c['expect']})")
    assert got == c['expect']
