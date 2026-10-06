"""Gluing structure of halvings X = Y + Z (both extremal for k-1) on the complete k=5 family. Per halving: is it
x-separated (Y = first half in sweep order)? Is it a deep-below split (every cross triple is a cup iff its middle
point is in the lower part, for one of the two orientations)? Fraction of cross triples obeying the better
deep-below orientation. Per set: does some halving have each property? Diagnostic."""
import itertools, json, sys
from collections import Counter
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly')
from harness.research.chains import is_strong

d = json.load(open('/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-extremal-20261005/k5.json')); n, k = d['n'], d['k']
T = list(itertools.combinations(range(n), 3))
st = Counter(); fr = Counter()
for key in d['orbits']:
    cup = {t: key[i] == '1' for i, t in enumerate(T)}
    hv = []
    for Yr in itertools.combinations(range(1, n), n // 2 - 1):
        Y = set((0,) + Yr); Z = set(range(n)) - Y
        if not is_strong(cup, sorted(Y)) and not is_strong(cup, sorted(Z)):
            hv.append((Y, Z))
    props = Counter()
    best = 0
    for Y, Z in hv:
        cross = [t for t in T if not (set(t) <= Y or set(t) <= Z)]
        for low, up in ((Y, Z), (Z, Y)):
            ok = sum(cup[t] == (t[1] in low) for t in cross)
            best = max(best, ok / len(cross))
            if ok == len(cross): props['deep-below'] += 1
        if Y == set(range(n // 2)) or Z == set(range(n // 2)): props['x-separated'] += 1
    for p in ('deep-below', 'x-separated'):
        st[(p, props[p] > 0)] += 1
    fr[round(best, 1)] += 1
print(dict(st)); print('best deep-below agreement over halvings (fraction of cross triples):', sorted(fr.items()))
