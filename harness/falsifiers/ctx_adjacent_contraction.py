#!/usr/bin/env python3
"""Harness adapter for the bounded adjacent-letter contraction falsifier."""
import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser()
    for name in ('dataset', 'node', 'statement'):
        parser.add_argument('--' + name)
    parser.add_argument('--out', required=True)
    args = parser.parse_args()
    return subprocess.call([
        sys.executable, str(ROOT / 'scripts/decomposable_adjacent_contraction.py'),
        '--output', args.out,
    ], cwd=ROOT)


if __name__ == '__main__':
    raise SystemExit(main())
