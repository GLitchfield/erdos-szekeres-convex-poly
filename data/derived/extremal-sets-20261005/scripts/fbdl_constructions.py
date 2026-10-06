"""FBDL on stored point-set constructions (data/derived/baek-balko-constructions-k*.json): convert coordinates to the
x-sweep signotope (cup = left turn), check cup/cap/strong and a full-range band partition by SAT. Diagnostic.
usage: fbdl_constructions.py k"""
import json, sys, itertools
from fractions import Fraction
from collections import Counter
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly')
from harness.research.band_partitions import partition_sat, check_partition
from harness.research.chains import longest_chain, strong_number
from harness.research.decomposable_sets import Decomposability

k = int(sys.argv[1])
d = json.load(open(f'/home/gavin/git/erdos-szekeres-convex-poly/data/derived/baek-balko-constructions-k{k}.json'))
for r in d['records']:
    P = sorted((Fraction(x), Fraction(y)) for x, y in r['points'])
    n = len(P)
    cup = {}
    for i, j, l in itertools.combinations(range(n), 3):
        (xi, yi), (xj, yj), (xl, yl) = P[i], P[j], P[l]
        cr = (xj - xi) * (yl - yi) - (yj - yi) * (xl - xi)
        assert cr != 0
        cup[(i, j, l)] = cr > 0
    al, be, sg = longest_chain(cup, range(n), True), longest_chain(cup, range(n), False), strong_number(cup, range(n))
    b = partition_sat(cup, range(n), k, list(range(k - 1)))
    ok = b is not None and check_partition(cup, range(n), k, b, list(range(k - 1)))
    print(f"{r['name']:24s} n={n} cup={al} cap={be} strong={sg} FBDL={ok}", '' if b is None else dict(sorted(Counter(b).items())), flush=True)
