"""Registered bounded probes; abstract witnesses remain explicitly unrealized."""
from __future__ import annotations

import random
import time
from .primitives import P, clip

SEMANTICS = 'abstract-rank-strip-v1'


def witness(rows, keep):
    keep = set(keep)
    other = set(range(len(rows))) - keep
    alpha, beta = clip(rows, keep, 0), clip(rows, other, 1)
    return {'rows': rows, 'keep': sorted(keep), 'alpha': alpha, 'beta': beta,
            'P': P(rows), 'Pa': P(alpha), 'Pb': P(beta)}


def replay(record):
    rows = record['rows']
    keep = record['keep']
    if not rows or any(len(r) != 4 or not all(type(x) is int for x in r) or r[0] > r[1] or r[2] > r[3] for r in rows):
        raise ValueError('invalid rectangle witness')
    if not keep or len(set(keep)) == len(rows) or not set(keep) <= set(range(len(rows))):
        raise ValueError('witness requires a proper nonempty part')
    actual = witness(rows, keep)
    return {'replayed': actual['Pa'] + actual['Pb'] > actual['P'], 'witness': actual,
            'realization_status': 'abstract_interval_family_unrealized', 'lean_refutation': False}


def evaluate(spec):
    if spec.get('semantics') != SEMANTICS or spec.get('domain') != 'abstract_interval_family':
        raise ValueError('explicit abstract-rank-strip-v1 semantics and abstract_interval_family domain required')
    generator = spec['generator']
    if generator.get('name') != 'sorted_intervals' or spec.get('candidate', {}).get('name') != 'clipped_potential':
        raise ValueError('unregistered generator/candidate')
    rng = random.Random(generator['seed'])
    bounds = generator.get('bounds', {})
    width = int(bounds.get('width', 11))
    size_max = int(bounds.get('size', 9))
    if not 1 <= width <= 10000 or not 2 <= size_max <= 1000:
        raise ValueError('invalid generator bounds')
    budget = spec['budget']
    start = time.monotonic()
    cases = generated = 0
    found = None
    for _ in range(budget['cases']):
        if time.monotonic()-start >= budget['seconds']: break
        generated += 1
        w, size = rng.randrange(1,width+1), rng.randrange(2,size_max+1)
        chosen = sorted((a,a+rng.randrange(2)) for a in [rng.randrange(1,4) for _ in range(size)])
        chosen = [(a,min(4,b)) for a,b in chosen]
        lows, highs = sorted(rng.randrange(1,w+1) for _ in range(size)), sorted(rng.randrange(1,w+1) for _ in range(size))
        rows = [list(a)+[min(b,c),max(b,c)] for a,b,c in zip(chosen,lows,highs)]
        if any(rows[i][1] > rows[i+1][1] for i in range(size-1)): continue
        a = rng.randrange(size); b = rng.randrange(a+1,size+1)
        keep = list(range(a,b))
        if len(keep) == size: continue
        record = witness(rows, keep)
        cases += 1
        if record['Pa']+record['Pb'] > record['P']:
            found = record; break
    return {'outcome':'witness_found' if found else 'no_witness_within_budget', 'witness':found,
            'coverage':{'generated':generated,'tested':cases,'seed':generator['seed'],'exhaustive':False},
            'seconds':time.monotonic()-start,'realization_status':'abstract_interval_family_unrealized','lean_refutation':False}
