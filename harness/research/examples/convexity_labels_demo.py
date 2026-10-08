"""Locality ladder at k = 5: level 4 SAT, level 5 UNSAT on 8 points (the halving is 5-point local), and the cone lemma
pattern of examples/convexity-axioms7-v1.json is level-6 realizable but not realizable.  Needs python-sat; ~5 s."""
import itertools, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..'))
from pysat.solvers import Cadical195
from harness.research import convexity_labels as cl
for m, expect in ((4, True), (5, False)):
    E, L = cl.level_instance(5, 8, m, hull3=True)
    with Cadical195(bootstrap_with=E.cl) as s:
        sat = s.solve()
    print(f'k=5 n=8 level {m}: {"SAT" if sat else "UNSAT"}'); assert sat == expect
ax = cl.axioms7(); t = ax['patterns'][ax['cone_lemma_index']]
lam = {Q: ('conv' if v == -1 else v) for Q, v in zip(itertools.combinations(range(7), 4), t)}
print('cone lemma pattern: realizable', cl.realizable(7, lam), ' bad 6-subsets', cl.locality_profile(7, lam, levels=(6,))[6])
assert not cl.realizable(7, lam)
