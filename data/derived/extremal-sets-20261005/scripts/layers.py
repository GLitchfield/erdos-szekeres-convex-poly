"""Convex-layer (onion) profiles of extremal signotopes. orient(i,j,l) for any order = chi(sorted) * sign of the
sorting permutation (chi = +1 for a cup = left turn in sweep order). v is interior to S iff some triangle abc in S has
v strictly inside (orient(a,b,v), orient(b,c,v), orient(c,a,v) all equal to orient(a,b,c)). Peel extreme points
repeatedly. Diagnostic. usage: layers.py SRC MAX  (SRC = k5.json | samples.jsonl | constructions:K)"""
import itertools, json, sys
from fractions import Fraction
from collections import Counter
src, mx = sys.argv[1], int(sys.argv[2])


def load():
    if src.startswith('constructions:'):
        k = int(src.split(':')[1]); d = json.load(open(f'/home/gavin/git/erdos-szekeres-convex-poly/data/derived/baek-balko-constructions-k{k}.json'))
        for r in d['records'][:mx]:
            P = sorted((Fraction(x), Fraction(y)) for x, y in r['points']); n = len(P)
            yield r['name'], n, {(i, j, l): ((P[j][0] - P[i][0]) * (P[l][1] - P[i][1]) - (P[j][1] - P[i][1]) * (P[l][0] - P[i][0])) > 0
                                  for i, j, l in itertools.combinations(range(n), 3)}
        return
    if src.endswith('.json'):
        d = json.load(open(src)); n = d['n']; keys = d['orbits'][:mx]
    else:
        keys = [json.loads(l)['key'] for l in open(src)][:mx]; n = 3
        while n * (n - 1) * (n - 2) // 6 < len(keys[0]): n += 1
    T = list(itertools.combinations(range(n), 3))
    for i, key in enumerate(keys):
        yield f'#{i}', n, {t: key[a] == '1' for a, t in enumerate(T)}


def orient(cup, i, j, l):
    s = sorted((i, j, l)); val = 1 if cup[tuple(s)] else -1
    perm = [s.index(i), s.index(j), s.index(l)]
    inv = sum(perm[a] > perm[b] for a in range(3) for b in range(a + 1, 3))
    return val if inv % 2 == 0 else -val


st = Counter()
for name, n, cup in load():
    rest = set(range(n)); prof = []
    while rest:
        R = sorted(rest)
        interior = set()
        for a, b, c in itertools.combinations(R, 3):
            o = orient(cup, a, b, c)
            for v in R:
                if v in (a, b, c) or v in interior: continue
                if orient(cup, a, b, v) == o and orient(cup, b, c, v) == o and orient(cup, c, a, v) == o:
                    interior.add(v)
        ext = rest - interior
        prof.append(len(ext)); rest = interior
    st['-'.join(map(str, prof))] += 1
    if src.startswith('constructions'): print(name, '-'.join(map(str, prof)))
print(sorted(st.items(), key=lambda x: -x[1])[:25], 'distinct', len(st))
