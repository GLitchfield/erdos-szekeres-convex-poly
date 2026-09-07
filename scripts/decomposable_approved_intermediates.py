"""Bounded falsification for the three approved context lemmas."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import sys
import time
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import decomposable_recursive_formula as drf
from decomposable_additivity_test import child, contexts

def key(x):
    return hashlib.sha256(repr(x).encode()).hexdigest()

def uniform_cases(k):
    templates = [((), ()), (((2, 'lower'),), ()), ((), ((2, 'upper'),)),
                 (((2, 'lower'),), ((3, 'upper'),)),
                 (((3, 'upper'),), ((2, 'lower'),)),
                 (((2, 'upper'), (3, 'lower')), ())]
    candidates = []
    for left, right in templates:
        depth = max((x[0] for x in left + right), default=1)
        for maxima in itertools.product(range(1, k - 1), repeat=depth):
            for r, t, m in ((1, 2, 1), (2, 1, 2), (2, 2, 1)):
                for side in ('lower', 'upper'):
                    candidates.append((left, right, maxima, r, t, m, side))
    mandatory = [x for x in candidates if all(v == 1 for v in x[2])]
    return list(dict.fromkeys(mandatory + sorted(candidates, key=key)[:48]))

def run(mode):
    drf.CACHE_SIZE = 40000
    start = time.monotonic()
    out = {'mode': mode, 'recursion': 'literal Lean', 'unused_levels': True,
           'exhaustive': False, 'cases': [], 'counterexample': None}
    for a, u, k in ((5, 5, 6), (4, 5, 6), (4, 4, 5)):
        F = drf.make_F2(a, u, k, include_zero_children=True)
        stats = {'parameters': [a, u, k], 'checks': 0}
        out['cases'].append(stats)
        if mode == 'external':
            selected = sorted(((w, ms) for w, ms in contexts(3, 2, 2, k,
                include_unused_levels=True) if any(x != 'S' for x in w)), key=key)[:80]
            trials = []
            for word, maxima in selected:
                for p, letter in enumerate(word):
                    if letter != 'S':
                        large = word[:p] + (letter,) + word[p:]
                        trials.append((F(large, maxima), F(word, maxima),
                            {'word': large, 'maxima': maxima, 'contracted': word, 'position': p}))
        else:
            trials = []
            for left, right, maxima, r, t, m, side in uniform_cases(k):
                word = left + ('S',) * r + ((1, side),) * m + ('S',) * t + right
                witness = {'word': word, 'maxima': maxima, 'r': r, 't': t, 'm': m, 'side': side}
                if mode == 'uniform':
                    small = left + ('S',) + ((1, side),) * m + ('S',) + right
                    x, y = F(word, maxima), F(small, maxima)
                    witness['contracted'] = small
                else:
                    parent = tuple((l - 1, s) for l, s in left) + ('S',) * (r + m + t) + tuple((l - 1, s) for l, s in right)
                    keep = frozenset(range(len(left) + r, len(left) + r + m))
                    middle = child(parent, maxima[1:], keep,
                        'upper' if side == 'lower' else 'lower', k - 1 - maxima[0])
                    x, y = F(word, maxima) + F(*middle), F(parent, maxima[1:])
                    witness['parent'] = parent
                trials.append((x, y, witness))
        for x, y, witness in trials:
            stats['checks'] += 1
            if (x > y if mode == 'sandwich' else x != y):
                out['counterexample'] = witness | {'case': [a, u, k], 'values': [x, y]}
                break
        if out['counterexample']:
            break
    out['seconds'] = time.monotonic() - start
    return out

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--mode', required=True, choices=['external', 'uniform', 'sandwich'])
    p.add_argument('--output', required=True, type=Path)
    args = p.parse_args()
    out = run(args.mode)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(out), flush=True)
    return 2 if out['counterexample'] else 0
if __name__ == '__main__':
    raise SystemExit(main())
