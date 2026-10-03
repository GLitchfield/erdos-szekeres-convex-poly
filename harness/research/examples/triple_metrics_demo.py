#!/usr/bin/env python3
"""Guarded example: python3 harness/research/examples/triple_metrics_demo.py."""
from itertools import combinations
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from harness.research.triple_metrics import FiniteTripleColoring

colors = {T: bool(9 >> i & 1) for i, T in enumerate(combinations(range(4), 3))}
value = FiniteTripleColoring(colors, 4)
print(json.dumps({"diagnostic": True, "cup_cap": value.metrics(),
                  "strong": value.strong_number(),
                  "maximum_cup_masks": value.maximal_chain_masks(None, True),
                  "cup_endpoints": [sorted(S) for S in value.extrema(None, True)]},
                 sort_keys=True))
