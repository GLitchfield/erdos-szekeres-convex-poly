#!/usr/bin/env python3
"""Runnable example for harness.research.decomposable_sets and harness.research.band_partitions
(catalog ids decomposable.label-sets and decomposable.band-partitions).

Builds a seeded random nested decomposable set from binary labels, prints its cup/cap/strong numbers and
root split, finds and independently verifies one BDL band partition for every multi-band k, and recomputes
the exhaustive per-n BDL pair counts for n <= 6 against the frozen fixture band-partitions-v1.json.
Runs in under a second. Usage: python3 harness/research/examples/band_partitions_demo.py
"""
import json
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from harness.research import band_partitions as bp  # noqa: E402
from harness.research import decomposable_sets as ds  # noqa: E402
from harness.research.chains import longest_chain, strong_number  # noqa: E402

s = ds.DecomposableSet(ds.random_nested_labels(14, random.Random(2026)))
low, _A, _B = s.root_split()
print(f"n={s.n} cup={s.alpha} cap={s.beta} strong={s.strong}; root split lower part at x = {low}")
for k in range(s.strong + 1, s.alpha + s.beta):
    bands = bp.bdl_range(s.alpha, s.beta, k)
    b = bp.find_partition(s.cup, range(s.n), k, bands)
    ok = b is not None and bp.check_partition(s.cup, range(s.n), k, b, bands)
    print(f"  k={k}: bands {bands[0]}..{bands[-1]}, partition {b}, verified={ok}")

fixture = json.loads((Path(__file__).with_name("band-partitions-v1.json")).read_text())
classes = ds.decomposable_masks(6)
for n in range(3, 7):
    pairs = multi = 0
    for mask in classes[n]:
        cup = ds.coloring_from_mask(mask, n)
        al, be, st = longest_chain(cup, range(n), True), longest_chain(cup, range(n), False), strong_number(cup, range(n))
        for k in range(st + 1, al + be + 1):
            pairs += 1
            if al + be > k:
                multi += 1
                assert bp.find_partition(cup, range(n), k, bp.bdl_range(al, be, k)) is not None
    want = fixture["per_n"][str(n)]
    print(f"n={n}: {len(classes[n])} colourings, {pairs} (X,k) pairs, {multi} multi-band, all partitioned;"
          f" fixture {want['pairs']}/{want['pairs_multi']}")
