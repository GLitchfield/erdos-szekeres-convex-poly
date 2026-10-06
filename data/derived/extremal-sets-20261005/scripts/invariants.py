"""Invariant scan over a list of extremal signotopes (keys from extremal_enum.py). For each orbit representative compute
candidate structural quantities and report which are constant across ALL extremal sets, and the distribution of
the others. Diagnostic. usage: invariants.py IN.json [maxsets]"""
import itertools, json, sys
from collections import Counter
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly')
from harness.research.chains import edge_chain_tables, longest_chain, strong_number, chains, is_strong
from harness.research.band_partitions import bdl_range, find_partition
from harness.research.decomposable_sets import Decomposability

d = json.load(open(sys.argv[1])); n, k = d['n'], d['k']
reps = d['orbits'][: int(sys.argv[2])] if len(sys.argv) > 2 else d['orbits']
T = list(itertools.combinations(range(n), 3))


def col(key):
    return {t: key[i] == '1' for i, t in enumerate(T)}


def ends(cup, want):
    end, start = edge_chain_tables(cup, n, want)
    e = [1] * n; s = [1] * n
    for (i, j), v in end.items():
        e[j] = max(e[j], v)
    for (i, j), v in start.items():
        s[i] = max(s[i], v)
    return e, s


inv = {}
def rec(name, val):
    inv.setdefault(name, Counter())[val] += 1

for key in reps:
    cup = col(key)
    al, be = longest_chain(cup, range(n), True), longest_chain(cup, range(n), False)
    rec('cup,cap', (al, be))
    cE, cS = ends(cup, True); kE, kS = ends(cup, False)
    rec('cupEnd hist', tuple(sorted(Counter(cE).items())))
    rec('capEnd hist', tuple(sorted(Counter(kE).items())))
    rec('(cupEnd,capEnd) hist', tuple(sorted(Counter(zip(cE, kE)).items())))
    rec('(cupEnd,cupStart) hist', tuple(sorted(Counter(zip(cE, cS)).items())))
    rec('overfull count', sum(cE[v] + kE[v] >= k + 2 for v in range(n)))
    rec('#strong (k-1)-sets', sum(is_strong(cup, S) for S in itertools.combinations(range(n), k - 1)))
    for t in range(3, k):
        rec(f'#{t}-cups', len(chains(cup, t, True, range(n))))
        rec(f'#{t}-caps', len(chains(cup, t, False, range(n))))
    rec('#cup triples', sum(cup.values()))
    dec = Decomposability(cup)
    rec('decomposable', dec.dec(list(range(n))))
    rec('#root splits', len(dec.splits(list(range(n)))))
    b = find_partition(cup, range(n), k, bdl_range(al, be, k))
    rec('BDL partition exists', b is not None)
    if b is not None:
        rec('BDL band sizes', tuple(sorted(Counter(b).items())))
print(f'n={n} k={k} sets scanned: {len(reps)}')
for name, c in inv.items():
    tag = 'CONSTANT' if len(c) == 1 else f'{len(c)} values'
    top = c.most_common(6)
    print(f'{name:28s} {tag:12s} {top}')
