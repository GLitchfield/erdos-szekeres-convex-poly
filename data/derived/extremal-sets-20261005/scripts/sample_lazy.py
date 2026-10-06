"""Diverse n-point signotopes with no strong k-set by lazy gon clauses (for k=7, n=32 where the full gon CNF is
too large). Each sample: random phases + random assumption cube; solve; while a strong k-set exists, add the clause
forbidding that set's exact colour pattern (permanent: it is a valid constraint), resolve. Then the same structural
scan as sample_extremal.py. Diagnostic. usage: sample_lazy.py n k COUNT SEED OUT.jsonl"""
import itertools, json, sys, time, random
from collections import Counter
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly')
from pysat.solvers import Cadical195
from harness.research.chains import edge_chain_tables, longest_chain, strong_number, longest_lr
from harness.research.band_partitions import bdl_range, find_partition
from harness.research.decomposable_sets import Decomposability

n, k, N, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
T = list(itertools.combinations(range(n), 3)); V = {t: i + 1 for i, t in enumerate(T)}
s = Cadical195()
for i, j, a, b in itertools.combinations(range(n), 4):
    q = [V[(i, j, a)], V[(i, j, b)], V[(i, a, b)], V[(j, a, b)]]
    for bits in itertools.product((0, 1), repeat=4):
        if sum(bits[x] != bits[x + 1] for x in range(3)) >= 2:
            s.add_clause([-q[x] if bits[x] else q[x] for x in range(4)])


def strong_set(cup):
    """Return one strong set of size >= k (as a sorted tuple) or None, from longest cup/cap with given endpoints."""
    cu = longest_lr(cup, range(n), True); ca = longest_lr(cup, range(n), False)
    for (l, r), (lc, ch) in cu.items():
        lk, chk = ca[(l, r)]
        if lc + lk - 2 >= k:
            pts = sorted(set(ch) | set(chk))
            return tuple(pts[:1] + [p for p in pts[1:-1]][: k - 2] + pts[-1:]) if len(pts) > k else tuple(pts)
    return None


rng = random.Random(seed); st = Counter(); t0 = time.time(); f = open(out, 'w'); got = 0; nclauses = 0
while got < N:
    s.set_phases([v if rng.random() < 0.5 else -v for v in range(1, len(T) + 1)])
    na = rng.randint(0, 2 * n)
    assum = [v if rng.random() < 0.5 else -v for v in rng.sample(range(1, len(T) + 1), na)]
    ok = False
    while s.solve(assumptions=assum):
        m = set(v for v in s.get_model() if v > 0)
        cup = {t: V[t] in m for t in T}
        S = strong_set(cup)
        if S is None:
            ok = True; break
        # any k-subset of a strong set is strong: forbid the pattern of a k-subset (first, interior..., last)
        S = S[:k - 1] + S[-1:] if len(S) > k else S
        s.add_clause([-V[t] if cup[t] else V[t] for t in itertools.combinations(S, 3)]); nclauses += 1
    if not ok:
        st['unsat cube'] += 1; continue
    got += 1
    key = ''.join('1' if cup[t] else '0' for t in T)
    al, be = longest_chain(cup, range(n), True), longest_chain(cup, range(n), False)
    sg = strong_number(cup, range(n)); assert sg <= k - 1
    end, _ = edge_chain_tables(cup, n, True); cE = [1] * n
    for (i, j), v in end.items(): cE[j] = max(cE[j], v)
    end2, _ = edge_chain_tables(cup, n, False); kE = [1] * n
    for (i, j), v in end2.items(): kE[j] = max(kE[j], v)
    over = sum(cE[v] + kE[v] >= k + 2 for v in range(n))
    b = find_partition(cup, range(n), k, bdl_range(al, be, k))
    dec = Decomposability(cup).dec(list(range(n))) if n <= 20 else None
    rec = {'key': key, 'cup': al, 'cap': be, 'strong': sg, 'overfull': over, 'decomposable': dec,
           'bdl': None if b is None else list(b)}
    f.write(json.dumps(rec) + '\n'); f.flush()
    st[('cup,cap', al, be)] += 1; st[('BDL', b is not None)] += 1; st[('overfull>0', over > 0)] += 1
    if b is not None: st[('bandsizes', tuple(sorted(Counter(b).items())))] += 1
    print(f'{got}/{N} {time.time()-t0:.0f}s gon-clauses {nclauses}', dict(st), flush=True)
print('FINAL', got, {str(a): c for a, c in st.items()}, flush=True)
