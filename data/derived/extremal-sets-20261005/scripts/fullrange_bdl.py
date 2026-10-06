"""Full-range diagonal BDL on the known BDL obstructions: bands j = 0..k-2 (cup <= j+1, cap <= k-1-j), NOT restricted
to [k-1-cap, cup-1]. Tests X14 and the k=7 tight failures in o_q1_k7.json. Diagnostic."""
import sys, json, itertools
sys.path.insert(0, '/home/gavin/git/erdos-szekeres-convex-poly')
from harness.research.band_partitions import partition_sat as find_partition, bdl_range
from harness.research.chains import longest_chain, strong_number
H = '/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-hypergraph-20261003/'


def test(n, key, k, tag):
    sys.stdout.flush()
    T = list(itertools.combinations(range(n), 3))
    cup = {t: key[i] == '1' for i, t in enumerate(T)}
    al, be, sg = longest_chain(cup, range(n), True), longest_chain(cup, range(n), False), strong_number(cup, range(n))
    own = find_partition(cup, range(n), k, bdl_range(al, be, k))
    full = find_partition(cup, range(n), k, list(range(0, k - 1)))
    print(tag, f'n={n} k={k} cup={al} cap={be} strong={sg}', 'own-range BDL:', own is not None, ' full-range BDL:', full is not None,
          '' if full is None else f'bands used {sorted(set(full))}')


d = json.load(open(H + 'minimal_14_6.json')); test(int(d['n']), d['key'], int(d['k']), 'X14')
q = json.load(open(H + 'o_q1_k7.json'))
for i, f in enumerate(q['fails'][:10]):
    if isinstance(f, dict):
        test(int(f.get('n')), f['key'], int(f.get('k', 7)), f'k7fail{i}')
    else:
        print('fail record format', type(f), str(f)[:200])
