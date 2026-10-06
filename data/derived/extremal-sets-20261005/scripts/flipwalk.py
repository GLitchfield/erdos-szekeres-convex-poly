"""Random triangle-flip walks inside the space of n-point signotopes with no strong k-set, started from stored
constructions (data/derived/baek-balko-constructions-k{k}.json). A flip toggles one triple; it is accepted iff every
4-subset containing the triple still satisfies the one-change law and the strong number stays <= k-1. After L
accepted flips per walk, test a full-range band partition (SAT) and decomposability. Prints progress per walk.
Diagnostic. usage: flipwalk.py k WALKS_PER_BASE L SEED OUT.jsonl"""
import itertools, json, sys, random, time
from fractions import Fraction
from collections import Counter
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly')
from harness.research.band_partitions import partition_sat, check_partition
from harness.research.chains import strong_number, longest_chain

k, W, L, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
d = json.load(open(f'/home/gavin/git/erdos-szekeres-convex-poly/data/derived/baek-balko-constructions-k{k}.json'))
rng = random.Random(seed); f = open(out, 'w'); st = Counter(); t0 = time.time()


def onechange_ok(cup, n, t):
    i, j, l = t
    for x in range(n):
        if x in t: continue
        q = tuple(sorted((i, j, l, x)))
        a, b, c, e = q
        seq = [cup[(a, b, c)], cup[(a, b, e)], cup[(a, c, e)], cup[(b, c, e)]]
        if sum(seq[z] != seq[z + 1] for z in range(3)) >= 2: return False
    return True


for r in d['records']:
    P = sorted((Fraction(x), Fraction(y)) for x, y in r['points']); n = len(P)
    base = {(i, j, l): ((P[j][0] - P[i][0]) * (P[l][1] - P[i][1]) - (P[j][1] - P[i][1]) * (P[l][0] - P[i][0])) > 0
            for i, j, l in itertools.combinations(range(n), 3)}
    T = list(base)
    for w in range(W):
        cup = dict(base); acc = tries = 0
        while acc < L:
            t = rng.choice(T); tries += 1
            cup[t] = not cup[t]
            if onechange_ok(cup, n, t) and strong_number(cup, range(n)) <= k - 1:
                acc += 1
            else:
                cup[t] = not cup[t]
        al, be = longest_chain(cup, range(n), True), longest_chain(cup, range(n), False)
        b = partition_sat(cup, range(n), k, list(range(k - 1)))
        ok = b is not None and check_partition(cup, range(n), k, b, list(range(k - 1)))
        diff = sum(cup[t] != base[t] for t in T)
        rec = {'base': r['name'], 'walk': w, 'accepted': acc, 'tries': tries, 'hamming_from_base': diff,
               'cup': al, 'cap': be, 'fbdl': ok, 'key': ''.join('1' if cup[t] else '0' for t in T)}
        f.write(json.dumps(rec) + '\n'); f.flush()
        st[('FBDL', ok)] += 1; st[('cup,cap', al, be)] += 1
        print(f"{r['name']} walk {w}: hamming {diff}, cup {al} cap {be}, FBDL {ok}  [{time.time()-t0:.0f}s] {dict(st)}", flush=True)
print('FINAL', {str(a): c for a, c in st.items()})
