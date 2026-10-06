"""Enumerate all signotopes on n = C(a+u-4, a-2) points with no a-cap and no u-cup (classical extremal cups-caps
sets), modulo reversal; report count and decomposability. Diagnostic. usage: classical_enum.py a u"""
import itertools, sys, math, time
from collections import Counter
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly')
from pysat.solvers import Cadical195
from harness.research.decomposable_sets import Decomposability
a, u = int(sys.argv[1]), int(sys.argv[2]); n = math.comb(a + u - 4, a - 2)
T = list(itertools.combinations(range(n), 3)); V = {t: i + 1 for i, t in enumerate(T)}
cl = [[v, -v] for v in range(1, len(T) + 1)]
for i, j, x, y in itertools.combinations(range(n), 4):
    q = [V[(i, j, x)], V[(i, j, y)], V[(i, x, y)], V[(j, x, y)]]
    for bits in itertools.product((0, 1), repeat=4):
        if sum(bits[z] != bits[z + 1] for z in range(3)) >= 2:
            cl.append([-q[z] if bits[z] else q[z] for z in range(4)])
# no a-cap / no u-cup via consecutive-triple chains: forbid all-cap a-subsets and all-cup u-subsets (signotope: chain = all triples)
for S in itertools.combinations(range(n), a):
    cl.append([V[t] for t in itertools.combinations(S, 3)])
for S in itertools.combinations(range(n), u):
    cl.append([-V[t] for t in itertools.combinations(S, 3)])
s = Cadical195(bootstrap_with=cl); seen = set(); st = Counter(); t0 = time.time()
while s.solve():
    m = s.get_model()[:len(T)]
    key = ''.join('1' if x > 0 else '0' for x in m)
    col = {t: key[i] == '1' for i, t in enumerate(T)}
    rev = ''.join('1' if col[(n - 1 - t[2], n - 1 - t[1], n - 1 - t[0])] else '0' for t in T)
    st['labelled'] += 1
    if min(key, rev) not in seen:
        seen.add(min(key, rev)); st[('dec', Decomposability(col).dec(list(range(n))))] += 1
    s.add_clause([-x for x in m])
print(f'classical ({a},{u}) n={n}:', dict(st), f'orbits mod reversal {len(seen)}  {time.time()-t0:.1f}s')
