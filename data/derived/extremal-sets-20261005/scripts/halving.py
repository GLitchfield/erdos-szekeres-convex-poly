"""Halving of extremal sets: X (2^(k-2) points, no strong k-set) = Y + Z with |Y| = |Z| = 2^(k-3) and neither containing
a strong (k-1)-set (so both are extremal for k-1). SAT: y_v; every strong (k-1)-set S of X is split (not all in Y,
not all in Z); sum y_v = n/2 (cardinality encoding). Counts halvings up to CAP (blocking, symmetric Y<->Z counted once).
Diagnostic. usage: halving.py samples.jsonl MAX CAP"""
import itertools, json, sys
from collections import Counter
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly')
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from harness.research.chains import longest_lr

src, mx, cap = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
keys = [json.loads(l)['key'] for l in open(src)][:mx]
n = 3
while n * (n - 1) * (n - 2) // 6 < len(keys[0]): n += 1
k = {8: 5, 16: 6, 32: 7, 64: 8}[n]
T = list(itertools.combinations(range(n), 3))


def strong_sets(cup, size):
    """All strong sets of exactly `size` points (strong = cup C and cap D sharing endpoints l, r, |C u D| = size)."""
    out = set()
    from harness.research.chains import chains
    cups = {}
    for t in range(2, size + 1):
        for c in chains(cup, t, True, range(n)):
            cups.setdefault((c[0], c[-1]), []).append(c)
    caps = {}
    for t in range(2, size + 1):
        for c in chains(cup, t, False, range(n)):
            caps.setdefault((c[0], c[-1]), []).append(c)
    for e, cl in cups.items():
        for c in cl:
            for d in caps.get(e, []):
                if len(c) + len(d) - 2 == size and not (set(c[1:-1]) & set(d[1:-1])):
                    out.add(tuple(sorted(set(c) | set(d))))
    return out


st = Counter()
for key in keys:
    cup = {t: key[i] == '1' for i, t in enumerate(T)}
    G = strong_sets(cup, k - 1)
    pool = IDPool(); y = [pool.id(('y', v)) for v in range(n)]
    cl = [[y[0]]]  # symmetry: point 0 in Y
    for S in G:
        cl.append([-y[v] for v in S]); cl.append([y[v] for v in S])
    cl += CardEnc.equals(lits=y, bound=n // 2, vpool=pool, encoding=EncType.seqcounter).clauses
    s = Cadical195(bootstrap_with=cl); c = 0
    while c < cap and s.solve():
        m = set(x for x in s.get_model() if x > 0); c += 1
        s.add_clause([-y[v] if y[v] in m else y[v] for v in range(n)])
    s.delete()
    st[('#strong (k-1)-sets', len(G) // 100 * 100)] += 0
    st[('halvings', c if c < cap else f'>={cap}')] += 1
print(f'k={k} n={n} sets={len(keys)}', dict((str(a), b) for a, b in st.items() if b))
