"""For extremal sets: J(v) = set of bands j such that some full-range band partition puts v in band j. Is J(v) an
interval? Is it a function of v's local chain data (cupEnd, capEnd, cupStart, capStart)? Diagnostic.
usage: feasible_bands.py (k5.json | samples.jsonl) [max]"""
import itertools, json, sys
from collections import Counter, defaultdict
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly')
from harness.research.band_partitions import find_partition, partition_sat
from harness.research.chains import edge_chain_tables

src = sys.argv[1]; mx = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
if src.endswith('.json'):
    d = json.load(open(src)); n, k = d['n'], d['k']; keys = d['orbits'][:mx]
else:
    recs = [json.loads(l) for l in open(src)][:mx]; keys = [r['key'] for r in recs]
    n = int(round((6 * len(keys[0])) ** (1 / 3))) + 1
    while n * (n - 1) * (n - 2) // 6 != len(keys[0]): n -= 1
    k = {16: 6, 32: 7, 8: 5}[n]
T = list(itertools.combinations(range(n), 3)); bands = list(range(k - 1))
fn = find_partition if n <= 16 else partition_sat
st = Counter(); func = defaultdict(set)
for key in keys:
    cup = {t: key[i] == '1' for i, t in enumerate(T)}
    loc = []
    for want in (True, False):
        end, start = edge_chain_tables(cup, n, want)
        e = [1] * n; s_ = [1] * n
        for (i, j), v in end.items(): e[j] = max(e[j], v)
        for (i, j), v in start.items(): s_[i] = max(s_[i], v)
        loc += [e, s_]
    for v in range(n):
        J = tuple(j for j in bands if fn(cup, range(n), k, bands, allowed={p: ([j] if p == v else bands) for p in range(n)}) is not None)
        st[('interval', J == tuple(range(J[0], J[-1] + 1)))] += 1
        st[('|J|', len(J))] += 1
        sig = tuple(L[v] for L in loc)
        func[sig].add(J)
print(f'k={k} n={n} sets={len(keys)}', dict(st))
amb = {s: J for s, J in func.items() if len(J) > 1}
print('local signatures (cupEnd,cupStart,capEnd,capStart):', len(func), ' with non-unique J:', len(amb))
for s, J in list(func.items())[:12]:
    print('  ', s, sorted(J))
