"""k=5 complete family: crosstab FLAG-BDL vs decomposability, and prefix-only / suffix-only flag variants."""
import itertools, json, sys
from collections import Counter
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly'); sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-extremal-20261005')
from pysat.solvers import Cadical195
from harness.research.chains import chains
from harness.research.decomposable_sets import Decomposability
d = json.load(open('/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-extremal-20261005/k5.json')); n, k = d['n'], d['k']
T = list(itertools.combinations(range(n), 3))


def solve(cup, pre, suf, band):
    y = {(v, j): 1 + v * (k - 1) + j for v in range(n) for j in range(k - 1)}
    cl = [[y[(v, k - 2)]] for v in range(n)] + [[-y[(v, j)], y[(v, j + 1)]] for v in range(n) for j in range(k - 2)]
    for j in range(k - 1):
        for C in chains(cup, j + 2, True, range(n)):
            if pre and j < k - 2: cl.append([-y[(v, j)] for v in C])
            if band:  # band j = y[j] and not y[j-1] has no (j+2)-cup
                for _ in [0]:
                    pass
    if band:
        for j in range(k - 1):
            for C in chains(cup, j + 2, True, range(n)):
                cl.append([-y[(v, j)] for v in C] + ([y[(v, j - 1)] for v in C] if j > 0 else []))
            for D in chains(cup, k - j, False, range(n)):
                cl.append([-y[(v, j)] for v in D] + ([y[(v, j - 1)] for v in D] if j > 0 else []))
    for j in range(1, k - 1):
        for D in chains(cup, k - j, False, range(n)):
            if suf: cl.append([y[(v, j - 1)] for v in D])
    s = Cadical195(bootstrap_with=cl); r = s.solve(); s.delete(); return r


st = Counter()
for key in d['orbits']:
    cup = {t: key[i] == '1' for i, t in enumerate(T)}
    dec = Decomposability(cup).dec(list(range(n)))
    full = solve(cup, True, True, False)
    pre = solve(cup, True, False, True)
    suf = solve(cup, False, True, True)
    st[('dec', dec, 'FLAG', full, 'prefix+bands', pre, 'suffix+bands', suf)] += 1
for kk, v in sorted(st.items(), key=str): print(kk, v)
