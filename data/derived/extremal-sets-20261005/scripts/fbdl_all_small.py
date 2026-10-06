"""FBDL exhaustively for small k: every n-point signotope with no strong k-set (all n up to 2^(k-2)) has a
full-range band partition (bands 0..k-2, cup <= j+1, cap <= k-1-j). Enumerates by SAT with blocking.
Diagnostic. usage: fbdl_all_small.py k"""
import itertools, sys, time
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly')
from pysat.solvers import Cadical195
from harness.research.band_partitions import find_partition

k = int(sys.argv[1])
for n in range(3, 2 ** (k - 2) + 1):
    T = list(itertools.combinations(range(n), 3)); V = {t: i + 1 for i, t in enumerate(T)}
    cl = [[v, -v] for v in range(1, len(T) + 1)]
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
    s = Cadical195(bootstrap_with=cl); c = 0; bad = 0; t0 = time.time()
    while s.solve():
        m = s.get_model()[:len(T)]; c += 1
        cup = {t: m[V[t] - 1] > 0 for t in T}
        if find_partition(cup, range(n), k, list(range(k - 1))) is None:
            bad += 1; print('FBDL FAIL', n, ''.join('1' if cup[t] else '0' for t in T), flush=True)
        s.add_clause([-v for v in m])
    print(f'k={k} n={n}: {c} signotopes with no strong {k}-set, FBDL failures {bad}, {time.time()-t0:.1f}s', flush=True)
