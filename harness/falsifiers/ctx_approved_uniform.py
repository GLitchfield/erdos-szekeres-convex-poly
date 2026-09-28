"""Harness adapter for the approved uniform lemma."""
import argparse
from pathlib import Path
import subprocess
import sys
ROOT = Path(__file__).resolve().parents[2]
p = argparse.ArgumentParser()
for name in ("dataset", "node", "statement"):
    p.add_argument("--" + name)
p.add_argument("--out", required=True)
a = p.parse_args()
raise SystemExit(subprocess.call([sys.executable, str(ROOT / "scripts/decomposable_approved_intermediates.py"), "--mode", "uniform", "--output", a.out], cwd=ROOT))
