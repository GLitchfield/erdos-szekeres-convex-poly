#!/usr/bin/env python3
"""Bounded falsifier for adjacent identical-letter contraction of context bounds.

Samples contexts deterministically within each (children, externals, depth)
bucket. This is finite evidence, not an exhaustive check of the conjecture.
The evaluator is the literal Lean recurrence, including zero-valued children
and unused external levels.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import time

import decomposable_recursive_formula as drf
from decomposable_additivity_test import contexts


def sampled_contexts(k, per_bucket=16):
    buckets = defaultdict(list)
    for word, maxima in contexts(4, 2, 2, k, include_unused_levels=True):
        if not any(x == y for x, y in zip(word, word[1:])):
            continue
        key = (word.count('S'), len(word) - word.count('S'), len(maxima))
        score = hashlib.sha256(repr((word, maxima)).encode()).hexdigest()
        buckets[key].append((score, word, maxima))
    for key in sorted(buckets):
        for _, word, maxima in sorted(buckets[key])[:per_bucket]:
            yield word, maxima


def run():
    drf.CACHE_SIZE = 60000
    started = time.monotonic()
    result = {
        'scope': 'Deterministic samples with 2..4 children, <=2 externals, <=2 levels',
        'recursion': 'lean',
        'include_unused_levels': True,
        'exhaustive': False,
        'cases': [],
        'counterexample': None,
    }
    for a, u, k in [(4, 4, 5), (4, 5, 6), (5, 5, 6)]:
        bound = drf.make_F2(a, u, k, include_zero_children=True)
        stats = Counter()
        for word, maxima in sampled_contexts(k):
            original = bound(word, maxima)
            stats['contexts'] += 1
            stats['nonzero'] += original > 0
            for p in range(len(word) - 1):
                if word[p] != word[p + 1]:
                    continue
                contracted = word[:p + 1] + word[p + 2:]
                value = bound(contracted, maxima)
                kind = 'child' if word[p] == 'S' else 'external'
                stats[kind + '_comparisons'] += 1
                if original != value:
                    result['counterexample'] = {
                        'case': [a, u, k], 'word': word, 'maxima': maxima,
                        'position': p, 'kind': kind, 'original': original,
                        'contracted': contracted, 'contracted_bound': value,
                    }
                    break
            if result['counterexample'] is not None:
                break
        result['cases'].append({'parameters': [a, u, k], 'stats': dict(stats)})
        print(json.dumps(result['cases'][-1]), flush=True)
        if result['counterexample'] is not None:
            break
    result['seconds'] = time.monotonic() - started
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    return 2 if result['counterexample'] is not None else 0


if __name__ == '__main__':
    raise SystemExit(main())
