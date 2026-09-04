#!/usr/bin/env python3
"""Falsifier contract fixture: always reports a counterexample (exit 2) and writes the witness."""
import argparse, json, sys
ap = argparse.ArgumentParser()
ap.add_argument("--dataset"); ap.add_argument("--out"); ap.add_argument("--node"); ap.add_argument("--statement")
a = ap.parse_args()
if a.out:
    json.dump({"node": a.node, "witness": {"points": [[0, 0], [1, 0], [0, 1]], "note": "contract fixture"}}, open(a.out, "w"))
print("contract fixture: counterexample", file=sys.stderr)
sys.exit(2)
