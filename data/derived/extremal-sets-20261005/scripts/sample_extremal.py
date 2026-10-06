"""Diverse samples of n-point signotopes with no strong k-set (SAT with random phases and random assumption cubes),
and a structural scan of each: cup/cap numbers, decomposability, BDL band partition with full bands, overfull
points, canonical cupEnd layering. Diagnostic. usage: sample_extremal.py n k COUNT SEED OUT.jsonl"""
import itertools, json, sys, time, random
from collections import Counter
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly')
from pysat.solvers import Cadical195
from harness.research.chains import edge_chain_tables, longest_chain, strong_number
from harness.research.band_partitions import bdl_range, find_partition, check_partition
from harness.research.decomposable_sets import Decomposability

n, k, N, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
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
rng = random.Random(seed); st = Counter(); t0 = time.time(); f = open(out, 'w')
got = 0
while got < N:
    s.set_phases([v if rng.random() < 0.5 else -v for v in range(1, len(T) + 1)])
    na = rng.randint(0, 3 * n)
    assum = [v if rng.random() < 0.5 else -v for v in rng.sample(range(1, len(T) + 1), na)]
    if not s.solve(assumptions=assum):
        st['unsat cube'] += 1; continue
    m = set(v for v in s.get_model() if v > 0)
    cup = {t: V[t] in m for t in T}
    key = ''.join('1' if cup[t] else '0' for t in T)
    got += 1
    al, be = longest_chain(cup, range(n), True), longest_chain(cup, range(n), False)
    sg = strong_number(cup, range(n))
    assert sg <= k - 1
    end, _ = edge_chain_tables(cup, n, True); cE = [1] * n
    for (i, j), v in end.items(): cE[j] = max(cE[j], v)
    end2, _ = edge_chain_tables(cup, n, False); kE = [1] * n
    for (i, j), v in end2.items(): kE[j] = max(kE[j], v)
    over = sum(cE[v] + kE[v] >= k + 2 for v in range(n))
    bands = bdl_range(al, be, k)
    b = find_partition(cup, range(n), k, bands)
    dec = Decomposability(cup).dec(list(range(n)))
    rec = {'key': key, 'cup': al, 'cap': be, 'strong': sg, 'overfull': over, 'decomposable': dec,
           'bdl': None if b is None else list(b), 'na': na}
    f.write(json.dumps(rec) + '\n'); f.flush()
    st[('cup,cap', al, be)] += 1; st[('BDL', b is not None)] += 1; st[('dec', dec)] += 1
    st[('overfull>0', over > 0)] += 1
    if b is not None:
        st[('bandsizes', tuple(sorted(Counter(b).items())))] += 1
    if got % 20 == 0:
        print(f'{got}/{N} {time.time()-t0:.0f}s', dict(st), flush=True)
print('FINAL', f'{got} samples {time.time()-t0:.0f}s', {str(a): c for a, c in st.items()}, flush=True)
