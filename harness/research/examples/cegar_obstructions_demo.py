#!/usr/bin/env python3
"""Runnable example for research.cegar-obstructions: FBDL(5) fails only for the 8-cup and the 8-cap, and every
pentagon-free colouring on 8 points has a band stack.  Needs python-sat (runs/etv-cc-20260930/.venv)."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from harness.research.cegar_obstructions import band_stack_obstructions  # noqa: E402

r = band_stack_obstructions(8, 5)
print(r.status, r.iterations, 'iterations;', [(o['cup'], o['cap'], o['minimal']) for o in r.obstructions])
r = band_stack_obstructions(8, 5, kfree=True)
print('pentagon-free:', r.status, r.iterations, 'iterations;', len(r.obstructions), 'obstructions')
