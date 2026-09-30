#!/usr/bin/env python3
"""Runnable example for harness.research.signotope_cubes (catalog id research.signotope-cubes).

Prints the legal-pattern counts on 1..6 points (A006245), the reversal orbit structure of the 5-point
patterns on the reversal-closed set {0,26,13,6,20} of a 27-point instance (26 pairs + 10 palindromes),
the first cube's literals on the center-outward 6-point set, and a Knuth estimate of the (unpruned)
5-point pattern tree, whose exact size is 62.  Solver-free; runs in well under a second.
Usage: python3 harness/research/examples/signotope_cubes_demo.py
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from harness.research import signotope_cubes as sc  # noqa: E402

print("legal patterns on 1..6 points:", [len(sc.patterns_on(range(n))) for n in range(1, 7)])
s5 = [0, 26, 13, 6, 20]
pats = [sc.place(p, s5) for p in sc.patterns_on(range(5))]
pal = sum(sc.reverse(p, 27) == p for p in pats)
print(f"reversal on {sorted(s5)}: {len(pats)} patterns = {(len(pats) - pal) // 2} pairs + {pal} palindromes")
cube = sc.patterns_on([13, 12, 14, 11, 15, 10])[0]
print("first center-outward level-6 cube, literals:", sc.lits_of(cube, 27)[:6], "...")
walks = [sc.knuth_walk(list(range(5)), sc.patterns_on(range(3)), 3, lambda p: True, lambda p, d: d == 5,
                       random.Random(s)) for s in range(400)]
est = sc.knuth_estimates(walks)
print(f"Knuth estimate of the 5-point tree (exact 62): {10 ** est['log10_mean_leaves']:.1f} from {est['walks']} walks")
