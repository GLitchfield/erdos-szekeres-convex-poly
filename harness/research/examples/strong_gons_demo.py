#!/usr/bin/env python3
"""Runnable example for harness.research.chains (catalog ids research.cup-cap-chains and research.lazy-strong-gons).

Checks the cup+cap strong-set formula against the 4-point definition on all 908 six-point signotopes, finds
a largest strong set (gon) in a seeded 24-point decomposable set without enumerating gons, and, when
python-sat is installed, two-colours that set so that neither class has a strong (strong-1)-set by CEGAR.
Runs in about a second. Usage: python3 harness/research/examples/strong_gons_demo.py
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from harness.research import chains as ch  # noqa: E402
from harness.research import signotope_cubes as sc  # noqa: E402
from harness.research.decomposable_sets import DecomposableSet, random_labels  # noqa: E402

pats = sc.patterns_on(range(6))
same = sum(ch.strong_number(p, range(6)) == ch.strong_number_bruteforce(p, range(6)) for p in pats)
print(f"strong number formula = 4-point definition on {same}/{len(pats)} six-point signotopes")

s = DecomposableSet(random_labels(24, random.Random(7)))
gon = ch.find_gon(s.cup, range(s.n), s.strong)
print(f"n={s.n} cup={s.alpha} cap={s.beta} strong={s.strong}; a largest gon {gon} strong={ch.is_strong(s.cup, gon)};"
      f" gon of size {s.strong + 1}: {ch.find_gon(s.cup, range(s.n), s.strong + 1)}")
try:
    import pysat  # noqa: F401
except ImportError:
    print("python-sat not installed: skipping cegar_two_colouring")
else:
    size = s.strong - 1
    res = ch.cegar_two_colouring(s.cup, list(range(s.n)), [], size)
    if res is None:
        print(f"no two-colouring avoids a monochromatic strong {size}-set")
    else:
        blue, red = res
        print(f"two-colouring without monochromatic strong {size}-sets: blue {blue} (strong"
              f" {ch.strong_number(s.cup, blue)}), red strong {ch.strong_number(s.cup, red)}")
