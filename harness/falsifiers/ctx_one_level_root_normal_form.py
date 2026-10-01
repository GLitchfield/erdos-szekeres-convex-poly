#!/usr/bin/env python3
"""Finite diagnostic falsifier for one-level ROOT-NF.

Retain the presence of each end marker; replace every run by one child and
clamp the run count at three when a=2 or u=2, and two otherwise. Adjacent
external multiplicities and run lengths are varied. No C-to-Lean equivalence
or theorem credit is asserted. Zero-child words have bound zero by definition
and are excluded because the compiled evaluator requires a child.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness.research.context_bound import compiled_evaluator


def normal_form(word, a, u, side):
    marker = (1, side)
    runs = sum(token == "S" and (i == 0 or word[i - 1] != "S")
               for i, token in enumerate(word))
    count = min(runs, 3 if a == 2 or u == 2 else 2)
    body = []
    for i in range(count):
        if i:
            body.append(marker)
        body.append("S")
    return ((marker,) if word and word[0] == marker else ()) + tuple(body) + (
        (marker,) if word and word[-1] == marker else ())


def words(side, children):
    marker = (1, side)
    for runs in range(1, children + 1):
        for lengths in itertools.product(range(1, children + 1), repeat=runs):
            if sum(lengths) != children:
                continue
            for separators in itertools.product((1, 2), repeat=runs - 1):
                for left, right in itertools.product((0, 1, 2), repeat=2):
                    word = [marker] * left
                    for i, length in enumerate(lengths):
                        word.extend(["S"] * length)
                        if i < runs - 1:
                            word.extend([marker] * separators[i])
                    yield tuple(word)


def main():
    ap = argparse.ArgumentParser()
    for name in ("dataset", "out", "node", "statement"):
        ap.add_argument("--" + name)
    ap.add_argument("--ks", default="3,4")
    ap.add_argument("--max-children", type=int, default=4)
    ap.add_argument("--timing", action="store_true")
    args = ap.parse_args()
    result = {"semantics": "context-bound-zero-children-c-v1", "node": args.node,
              "run_clamp": "3 if a=2 or u=2, else 2", "end_markers": "presence",
              "cases": [], "checked": 0, "violations": []}
    ks = tuple(map(int, args.ks.split(",")))
    if not args.timing:
        result["total"] = 2 * 9 * ((3 ** args.max_children - 1) // 2) * sum(
            k * k * (k - 2) for k in ks)
        result["scope"] = {"ks": ks, "max_children": args.max_children,
                           "end_multiplicities": [0, 1, 2], "separator_multiplicities": [1, 2]}
    start = time.monotonic()
    if args.timing:
        cases = [(4, 4, 4, 1, "lower", (2, 1, 1)),
                 (5, 5, 5, 1, "lower", (1, 1, 1, 1)),
                 (5, 2, 5, 1, "lower", (1, 1, 1, 1)),
                 (6, 6, 6, 1, "lower", (2, 1, 1, 1))]
        for k, a, u, m, side, lengths in cases:
            marker = (1, side)
            word = [marker]
            for i, length in enumerate(lengths):
                if i:
                    word.append(marker)
                word.extend(["S"] * length)
            word.append(marker)
            f = compiled_evaluator(a, u, k, cache_size=500000, persistent=True)
            began = time.monotonic()
            try:
                nf = normal_form(word, a, u, side)
                value, normal = f(word, (m,)), f(nf, (m,))
            finally:
                f.close()
            row = {"k": k, "a": a, "u": u, "m": m, "word": word, "normal_form": nf,
                   "bound": value, "normal_bound": normal,
                   "seconds": time.monotonic() - began}
            result["cases"].append(row)
            result["checked"] += 1
            if value != normal:
                result["violations"].append(row)
            print(json.dumps(row), flush=True)
    else:
        for k in ks:
            for a in range(1, k + 1):
                for u in range(1, k + 1):
                    f = compiled_evaluator(a, u, k, cache_size=500000, persistent=True)
                    try:
                        for side in ("lower", "upper"):
                            for m in range(1, k - 1):
                                for children in range(1, args.max_children + 1):
                                    for word in words(side, children):
                                        nf = normal_form(word, a, u, side)
                                        value, normal = f(word, (m,)), f(nf, (m,))
                                        result["checked"] += 1
                                        if value != normal:
                                            result["violations"].append({
                                                "k": k, "a": a, "u": u, "m": m,
                                                "word": word, "normal_form": nf,
                                                "bound": value, "normal_bound": normal})
                                            break
                                    if result["violations"]:
                                        break
                                if result["violations"]:
                                    break
                            if result["violations"]:
                                break
                    finally:
                        f.close()
                    elapsed = time.monotonic() - start
                    print(json.dumps({"k": k, "a": a, "u": u,
                                      "checked": result["checked"],
                                      "total": result["total"], "seconds": elapsed,
                                      "rate_per_second": result["checked"] / max(elapsed, 1e-9),
                                      "violations": len(result["violations"])}), flush=True)
                    if result["violations"]:
                        break
                if result["violations"]:
                    break
            if result["violations"]:
                break
    result["seconds"] = time.monotonic() - start
    if args.out:
        Path(args.out).write_text(json.dumps(result, indent=2) + "\n")
    return 2 if result["violations"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
