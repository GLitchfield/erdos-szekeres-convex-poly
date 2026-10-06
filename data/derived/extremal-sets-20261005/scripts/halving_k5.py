"""k=5 complete family: per extremal set, the number of full-band BDL partitions and of halvings (X = Y + Z,
|Y| = |Z| = 4, neither containing a strong 4-set). Also records whether some halving is 'band-compatible'. Diagnostic.
usage: halving_k5.py k5.json"""
import itertools, json, sys
from collections import Counter
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly')
from harness.research.chains import is_strong, longest_chain
from harness.research.band_partitions import bdl_range, partitions

d = json.load(open(sys.argv[1])); n, k = d['n'], d['k']
T = list(itertools.combinations(range(n), 3))
st = Counter()
for key in d['orbits']:
    cup = {t: key[i] == '1' for i, t in enumerate(T)}
    nb = len(partitions(cup, range(n), k, bdl_range(4, 4, k)))
    st[('#BDL partitions', min(nb, 50) if nb < 50 else '50+')] += 1
    hv = 0
    for Y in itertools.combinations(range(1, n), 3):
        Y = (0,) + Y
        Z = tuple(p for p in range(n) if p not in Y)
        if not is_strong(cup, Y) and not is_strong(cup, Z):
            hv += 1
    st[('#halvings', hv)] += 1
for kk, v in sorted(st.items(), key=str):
    print(kk, v)
