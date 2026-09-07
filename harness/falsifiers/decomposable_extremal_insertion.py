#!/usr/bin/env python3
"""Bounded exact-coordinate insertion search; exit 2 reports a candidate refutation."""
import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser()
    for name in ("dataset", "node", "statement"):
        parser.add_argument("--" + name)
    parser.add_argument("--out", required=True)
    args = parser.parse_args()
    return subprocess.call([sys.executable, str(ROOT / "scripts/decomposable_extremal_insertion.py"),
                            "--output", args.out], cwd=ROOT)


if __name__ == "__main__":
    raise SystemExit(main())
