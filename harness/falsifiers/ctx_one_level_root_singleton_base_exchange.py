#!/usr/bin/env python3
"""Finite diagnostic for the one-level-root singleton-base exchange.

For every adjacent SS pair and every singleton child p, explicitly evaluate
T(cap+1,cup+1,k) plus the complement part. Compare with all couplings and
both sides at the mapped singleton in the shortened word. The compiled
singleton value is independently audited against each explicit T.

Default domain: k5 all a,u=1..5; k6 (5,5) and (6,6); every m=1..k-2;
two or three child runs, lengths1..2, <=4 children; one marker per gap,
0/1 end markers, both old sides. This is exhaustive in the declared
family, not in the universal Lean statement. No C1r or singleton-normal-
form claim follows from a pass. Shared APIs implement parts and limits.
"""
from __future__ import annotations

import argparse
from collections import Counter
import itertools
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))
from harness.research.context_bound import compiled_evaluator
from decomposable_additivity_test import child
from decomposable_depth2_tables import limits_from_signature
from enumerate_decomposable_colorings import threshold


def roots(max_children):
    for old_side in ("lower", "upper"):
        marker = (1, old_side)
        for runs in (2, 3):
            for lengths in itertools.product((1, 2), repeat=runs):
                if sum(lengths) > max_children or max(lengths) < 2:
                    continue
                for left, right in itertools.product((0, 1), repeat=2):
                    word = [marker] * left
                    for i, length in enumerate(lengths):
                        if i:
                            word.append(marker)
                        word.extend(["S"] * length)
                    yield tuple(word + [marker] * right)


def singleton_values(bound, a, u, k, word, m, counts):
    children = frozenset(i for i, x in enumerate(word) if x == "S")
    values = {}
    for p in sorted(children):
        for side in ("lower", "upper"):
            other = "upper" if side == "lower" else "lower"
            for c in range(1, k - 1):
                leaf_word, leaf_maxima = child(word, (m,), {p}, side, c)
                runs, cups, caps = limits_from_signature(
                    leaf_word, leaf_maxima, a, u, k, lean=True)
                assert runs == 1
                cup, cap = int(cups[0, 0]), int(caps[0, 0])
                leaf = threshold(cap + 1, cup + 1, k)
                counts["leaf_audits"] += 1
                if leaf != bound(leaf_word, leaf_maxima):
                    raise ValueError("explicit T disagrees with compiled singleton")
                rest = bound(*child(word, (m,), children - {p}, other, k - 1 - c))
                values[p, side, c] = leaf + rest
    return values


def main():
    parser = argparse.ArgumentParser()
    for flag in ("dataset", "out", "node", "statement"):
        parser.add_argument("--" + flag)
    parser.add_argument("--ks", default="5,6")
    parser.add_argument("--max-children", type=int, default=4)
    args = parser.parse_args()
    words = tuple(roots(args.max_children))
    counts = Counter()
    violations = []
    start = time.monotonic()
    scope = []
    for k in map(int, args.ks.split(",")):
        parameters = list(itertools.product(range(1, k + 1), repeat=2)) if k <= 5 else [(5, 5), (k, k)]
        scope.append({"k": k, "parameters": parameters, "words": len(words),
                      "maxima": list(range(1, k - 1))})
        for a, u in parameters:
            bound = compiled_evaluator(a, u, k, cache_size=2000000, persistent=True)
            try:
                for m in range(1, k - 1):
                    for word in words:
                        original = singleton_values(bound, a, u, k, word, m, counts)
                        counts["roots"] += 1
                        for y in range(len(word) - 1):
                            if word[y:y + 2] != ("S", "S"):
                                continue
                            short = word[:y + 1] + word[y + 2:]
                            shortened = singleton_values(bound, a, u, k, short, m, counts)
                            counts["pairs"] += 1
                            for (p, side, coupling), value in original.items():
                                q = p if p <= y else p - 1
                                best = max(v for (r, _, _), v in shortened.items() if r == q)
                                counts["cuts"] += 1
                                if value > best:
                                    counts["violations"] += 1
                                    if len(violations) < 20:
                                        violations.append({"a": a, "u": u, "k": k, "m": m,
                                            "word": word, "pair_start": y, "p": p, "q": q,
                                            "side": side, "coupling": coupling, "value": value,
                                            "best_shortened": best})
                    elapsed = time.monotonic() - start
                    print(json.dumps({"k": k, "a": a, "u": u, "m": m,
                        "elapsed": elapsed, "counts": dict(counts)}), flush=True)
            finally:
                bound.close()
    result = {"node": args.node, "statement": args.statement,
        "semantics": "context-bound-zero-children-c-v1", "scope": scope,
        "max_children": args.max_children, "counts": dict(counts),
        "seconds": time.monotonic() - start, "violations": violations}
    if args.out:
        Path(args.out).write_text(json.dumps(result, indent=2) + "\n")
    return 2 if violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
