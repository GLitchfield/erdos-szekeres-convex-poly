#!/usr/bin/env python3
"""Guarded runnable example: python3 harness/research/examples/root_cuts_demo.py.

Diagnostic root cuts of an ordered cup triple; no Lean or ES theorem credit.
"""
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from harness.research.root_cuts import graph_profile, root_masks

colors = {(0, 1, 2): True}
_, reachability, components = graph_profile(colors, 3)
print(json.dumps({"reachability_masks": reachability,
                  "component_masks": components,
                  "lower_root_masks": root_masks(colors, 3),
                  "diagnostic": True}, sort_keys=True))
