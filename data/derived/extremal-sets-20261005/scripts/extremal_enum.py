"""Enumerate ALL rank-3 signotopes on n points with no strong k-set (n = 2^(k-2) is the extremal case).

Encoding (diagnostic, independent of the project's CNF generators):
- var(t) for each sorted triple t, True = cup;
- one-change law: for i<j<k<l the sequence (ijk, ijl, ikl, jkl) changes value at most once (8 forbidden patterns);
- no strong k-set: a k-subset is strong iff every triple's colour is determined by its middle point (cup iff the
  middle point is on the lower chain), so for each k-subset and each of the 2^(k-2) up/down assignments of its interior
  points, forbid that full colour pattern.
Solutions are enumerated with blocking clauses and reduced modulo the symmetry group {id, reverse, mirror,
reverse+mirror} (reverse keeps colours, mirror swaps cup/cap). Writes keys ('1' = cup, combinations order) as JSON.
usage: extremal_enum.py n k OUT.json"""
import itertools, json, sys, time
from pysat.solvers import Cadical195

n, k, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
T = list(itertools.combinations(range(n), 3))
V = {t: i + 1 for i, t in enumerate(T)}
cl = []
for i, j, a, b in itertools.combinations(range(n), 4):
    q = [V[(i, j, a)], V[(i, j, b)], V[(i, a, b)], V[(j, a, b)]]
    for bits in itertools.product((0, 1), repeat=4):
        if sum(bits[x] != bits[x + 1] for x in range(3)) >= 2:
            cl.append([-q[x] if bits[x] else q[x] for x in range(4)])
for S in itertools.combinations(range(n), k):
    inner = S[1:-1]
    for down in itertools.product((0, 1), repeat=k - 2):
        d = dict(zip(inner, down))
        cl.append([-V[t] if d[t[1]] else V[t] for t in itertools.combinations(S, 3)])


def key_of(model_set):
    return ''.join('1' if V[t] in model_set else '0' for t in T)


def sym(key):
    col = {t: key[i] == '1' for i, t in enumerate(T)}
    rev = ''.join('1' if col[(n - 1 - t[2], n - 1 - t[1], n - 1 - t[0])] else '0' for t in T)
    mir = ''.join('0' if c == '1' else '1' for c in key)
    revmir = ''.join('0' if c == '1' else '1' for c in rev)
    return [key, rev, mir, revmir]


t0 = time.time()
s = Cadical195(bootstrap_with=cl)
allk = set(); reps = []
while s.solve():
    m = set(v for v in s.get_model() if v > 0)
    key = key_of(m)
    orb = sym(key)
    reps.append(min(orb))
    for kk in orb:
        if kk not in allk:
            allk.add(kk)
            s.add_clause([-V[t] if kk[i] == '1' else V[t] for i, t in enumerate(T)])
    if len(reps) % 1000 == 0:
        print(f'{len(reps)} orbits {len(allk)} signotopes {time.time()-t0:.0f}s', flush=True)
reps = sorted(set(reps))
print(f'n={n} k={k}: {len(allk)} signotopes, {len(reps)} symmetry orbits, {time.time()-t0:.1f}s', flush=True)
json.dump({'n': n, 'k': k, 'signotopes': len(allk), 'orbits': reps}, open(out, 'w'))
