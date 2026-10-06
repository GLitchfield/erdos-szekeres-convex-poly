"""Knuth estimate of the number of n-point signotopes with no strong k-set: fix triple variables in a given order,
at each step test both values by SAT under assumptions, choose a feasible one uniformly, multiply the branching.
The product is an unbiased estimate of the solution count; report log10 of each walk, mean and median.
usage: knuth16.py n k WALKS SEED"""
import itertools, sys, time, random, math
from pysat.solvers import Cadical195
n, k, W, seed = map(int, sys.argv[1:5])
T = list(itertools.combinations(range(n), 3)); V = {t: i + 1 for i, t in enumerate(T)}
cl = []
for i, j, a, b in itertools.combinations(range(n), 4):
    q = [V[(i, j, a)], V[(i, j, b)], V[(i, a, b)], V[(j, a, b)]]
    for bits in itertools.product((0, 1), repeat=4):
        if sum(bits[x] != bits[x + 1] for x in range(3)) >= 2:
            cl.append([-q[x] if bits[x] else q[x] for x in range(4)])
for S in itertools.combinations(range(n), k):
    inner = S[1:-1]
    for down in itertools.product((0, 1), repeat=k - 2):
        dd = dict(zip(inner, down))
        cl.append([-V[t] if dd[t[1]] else V[t] for t in itertools.combinations(S, 3)])
s = Cadical195(bootstrap_with=cl)
# order: by largest point, then lexicographic (point-by-point insertion)
order = sorted(T, key=lambda t: (t[2], t[1], t[0]))
rng = random.Random(seed); logs = []
t0 = time.time()
for w in range(W):
    assum = []; lg = 0.0
    for t in order:
        v = V[t]
        ok = [lit for lit in (v, -v) if s.solve(assumptions=assum + [lit])]
        if not ok:
            lg = None; break
        lg += math.log10(len(ok))
        assum.append(rng.choice(ok))
    logs.append(lg)
    print(f'walk {w}: log10 = {lg:.2f}  ({time.time()-t0:.0f}s)', flush=True)
vals = sorted(x for x in logs if x is not None)
mx = max(vals); mean = mx + math.log10(sum(10 ** (x - mx) for x in vals) / len(vals))
print(f'n={n} k={k}: walks {len(vals)}, median log10 {vals[len(vals)//2]:.2f}, log10 mean {mean:.2f}')
