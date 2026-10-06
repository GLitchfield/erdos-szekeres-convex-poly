"""Pilot: rate of enumerating 16-point hexagon-free signotopes (first N solutions with blocking), to decide whether
full enumeration is feasible. usage: pilot16.py N"""
import itertools, sys, time
from pysat.solvers import Cadical195
n, k, N = 16, 6, int(sys.argv[1])
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
t0 = time.time(); s = Cadical195(bootstrap_with=cl); print('clauses', len(cl), 'build %.1fs' % (time.time() - t0), flush=True)
c = 0
while c < N and s.solve():
    m = s.get_model(); c += 1
    s.add_clause([-v for v in m[:len(T)]])
    if c in (1, 10, 100, 1000, 5000):
        print(c, 'solutions %.1fs' % (time.time() - t0), flush=True)
