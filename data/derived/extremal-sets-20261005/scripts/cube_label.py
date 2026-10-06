"""Cube labelling of an extremal set (2^(k-2) points, no strong k-set): a bijection phi: X -> {0,1}^(k-2) such that for
every prefix w (length m = 0..k-2) and every j, the class S(w,j) = {v : phi(v) = w u, weight(u) = j} has
cup <= j+1 and cap <= (k-m)-1-j. Level m = 0 is a full band stack; each level refines it by band-compatible Pascal
halvings; the ES construction has one. Option GON: also require every prefix class X_w to have no strong
(k-m)-set (halves extremal). SAT with one-hot x[v][word]. Diagnostic.
usage: cube_label.py SRC MAX [gon]   SRC = k5.json | samples.jsonl | constructions:K"""
import itertools, json, sys
from fractions import Fraction
from collections import Counter
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly')
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from harness.research.chains import chains

src, mx = sys.argv[1], int(sys.argv[2]); gon = len(sys.argv) > 3 and sys.argv[3] == 'gon'


def load():
    if src.startswith('constructions:'):
        k = int(src.split(':')[1]); d = json.load(open(f'/home/gavin/git/erdos-szekeres-convex-poly/data/derived/baek-balko-constructions-k{k}.json'))
        for r in d['records'][:mx]:
            P = sorted((Fraction(x), Fraction(y)) for x, y in r['points']); n = len(P)
            yield r['name'], n, k, {(i, j, l): ((P[j][0] - P[i][0]) * (P[l][1] - P[i][1]) - (P[j][1] - P[i][1]) * (P[l][0] - P[i][0])) > 0
                                     for i, j, l in itertools.combinations(range(n), 3)}
        return
    if src.endswith('.json'):
        d = json.load(open(src)); n, k = d['n'], d['k']; keys = d['orbits'][:mx]
    else:
        keys = [json.loads(l)['key'] for l in open(src)][:mx]
        n = 3
        while n * (n - 1) * (n - 2) // 6 < len(keys[0]): n += 1
        k = {8: 5, 16: 6, 32: 7, 64: 8}[n]
    T = list(itertools.combinations(range(n), 3))
    for i, key in enumerate(keys):
        yield f'#{i}', n, k, {t: key[a] == '1' for a, t in enumerate(T)}


def strong_sets(cup, n, size):
    out = set(); cups = {}; caps = {}
    for t in range(2, size + 1):
        for c in chains(cup, t, True, range(n)): cups.setdefault((c[0], c[-1]), []).append(c)
        for c in chains(cup, t, False, range(n)): caps.setdefault((c[0], c[-1]), []).append(c)
    for e, cl in cups.items():
        for c in cl:
            for d in caps.get(e, []):
                if len(c) + len(d) - 2 == size and not (set(c[1:-1]) & set(d[1:-1])):
                    out.add(tuple(sorted(set(c) | set(d))))
    return out


st = Counter()
for name, n, k, cup in load():
    D = k - 2; words = list(itertools.product((0, 1), repeat=D))
    pool = IDPool(); x = {(v, w): pool.id(('x', v, w)) for v in range(n) for w in words}
    cl = []
    for v in range(n):
        cl += CardEnc.equals(lits=[x[(v, w)] for w in words], bound=1, vpool=pool, encoding=EncType.seqcounter).clauses
    for w in words:
        cl += CardEnc.equals(lits=[x[(v, w)] for v in range(n)], bound=1, vpool=pool, encoding=EncType.seqcounter).clauses
    cupch = {t: chains(cup, t, True, range(n)) for t in range(2, k + 1)}
    capch = {t: chains(cup, t, False, range(n)) for t in range(2, k + 1)}
    for m in range(D + 1):
        for w in itertools.product((0, 1), repeat=m):
            for j in range(D - m + 1):
                cls = [w + u for u in itertools.product((0, 1), repeat=D - m) if sum(u) == j]
                s = {v: pool.id(('s', v, w, j)) for v in range(n)}
                for v in range(n):  # s[v] <-> OR x[v][word] over the class
                    cl.append([-s[v]] + [x[(v, ww)] for ww in cls])
                    for ww in cls: cl.append([s[v], -x[(v, ww)]])
                kk = k - m
                if j + 2 <= k:
                    for C in cupch.get(j + 2, []): cl.append([-s[v] for v in C])
                if kk - j <= k and kk - j >= 2:
                    for C in capch.get(kk - j, []): cl.append([-s[v] for v in C])
            if gon and 3 <= k - m < k:
                pw = {v: pool.id(('p', v, w)) for v in range(n)}
                cls = [w + u for u in itertools.product((0, 1), repeat=D - m)]
                for v in range(n):
                    cl.append([-pw[v]] + [x[(v, ww)] for ww in cls])
                    for ww in cls: cl.append([pw[v], -x[(v, ww)]])
                for G in strong_sets(cup, n, k - m): cl.append([-pw[v] for v in G])
    sol = Cadical195(bootstrap_with=cl); ok = sol.solve(); sol.delete()
    st[('cube labelling' + (' +gon' if gon else ''), ok)] += 1
    if src.startswith('constructions'): print(name, ok, flush=True)
print(dict(st))
