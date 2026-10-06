"""FLAG-BDL: bands b(v) in 0..k-2 such that every prefix P_j = {b <= j} has no (j+2)-cup and every suffix
S_j = {b >= j} has no (k-j)-cap (implies BDL; the ES construction satisfies it). Order-encoded SAT:
y[v][j] = [b(v) <= j], y[v][k-2] = true, y[v][j] -> y[v][j+1]; cup C of length j+2: OR_v not y[v][j];
cap D of length k-j: OR_v y[v][j-1]. Inputs: k5.json (orbits), samples .jsonl, or 'constructions K'. Diagnostic.
usage: flag_bdl.py SRC [max]"""
import itertools, json, sys
from fractions import Fraction
from collections import Counter
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly')
from pysat.solvers import Cadical195
from harness.research.chains import chains, longest_chain


def load(src, mx):
    if src == 'constructions':
        k = int(sys.argv[2]); d = json.load(open(f'/home/gavin/git/erdos-szekeres-convex-poly/data/derived/baek-balko-constructions-k{k}.json'))
        out = []
        for r in d['records']:
            P = sorted((Fraction(x), Fraction(y)) for x, y in r['points']); n = len(P)
            cup = {(i, j, l): ((P[j][0] - P[i][0]) * (P[l][1] - P[i][1]) - (P[j][1] - P[i][1]) * (P[l][0] - P[i][0])) > 0
                   for i, j, l in itertools.combinations(range(n), 3)}
            out.append((r['name'], n, k, cup))
        return out
    if src.endswith('.json'):
        d = json.load(open(src)); n, k = d['n'], d['k']; keys = d['orbits'][:mx]
    else:
        keys = [json.loads(l)['key'] for l in open(src)][:mx]
        n = 3
        while n * (n - 1) * (n - 2) // 6 < len(keys[0]): n += 1
        k = {8: 5, 16: 6, 32: 7, 64: 8}[n]
    T = list(itertools.combinations(range(n), 3))
    return [(f'#{i}', n, k, {t: key[a] == '1' for a, t in enumerate(T)}) for i, key in enumerate(keys)]


def flag(cup, n, k):
    y = {(v, j): 1 + v * (k - 1) + j for v in range(n) for j in range(k - 1)}
    cl = [[y[(v, k - 2)]] for v in range(n)] + [[-y[(v, j)], y[(v, j + 1)]] for v in range(n) for j in range(k - 2)]
    for j in range(k - 2):  # prefix P_j has no (j+2)-cup
        for C in chains(cup, j + 2, True, range(n)):
            cl.append([-y[(v, j)] for v in C])
    for j in range(1, k - 1):  # suffix S_j = {b >= j} = {not y[v][j-1]} has no (k-j)-cap
        for D in chains(cup, k - j, False, range(n)):
            cl.append([y[(v, j - 1)] for v in D])
    s = Cadical195(bootstrap_with=cl); ok = s.solve()
    b = None
    if ok:
        m = set(x for x in s.get_model() if x > 0)
        b = [min(j for j in range(k - 1) if y[(v, j)] in m) for v in range(n)]
    s.delete(); return b


src = sys.argv[1]; mx = int(sys.argv[3] if src == 'constructions' and len(sys.argv) > 3 else (sys.argv[2] if len(sys.argv) > 2 and src != 'constructions' else 10 ** 9))
st = Counter()
for name, n, k, cup in load(src, mx):
    b = flag(cup, n, k)
    st[('FLAG', b is not None)] += 1
    if b is not None: st[('sizes', tuple(sorted(Counter(b).items())))] += 1
    if src == 'constructions': print(name, 'FLAG', b is not None, flush=True)
    elif b is None and st[('FLAG', False)] <= 3: print('FLAG FAIL', name, flush=True)
print(dict(st))
