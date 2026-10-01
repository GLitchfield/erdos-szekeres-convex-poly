#!/usr/bin/env python3
"""Finite N_root diagnostic, adapted from R13's probe_singleton_normal.py.

The default family has two to four runs of lengths one/two, at most four
children, one marker per gap, optional single end markers and both sides.
Includes roots without adjacent children. Test k=5 at every a,u=1..5 and
k=6 at (5,5),(6,6), every m=1..k-2. Singleton arithmetic uses the retained
shared primitive and each leaf is audited against its explicit threshold.
These finite compiled-evaluator results give no Lean theorem credit.
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
from harness.research.primitives import part
from harness.research.singleton_cuts import singleton_cut_values
from decomposable_depth2_tables import limits_from_signature
from enumerate_decomposable_colorings import threshold


def root_words(max_runs, max_len, max_children):
    """R13's declared family, including all-singleton runs."""
    for side in ("lower", "upper"):
        marker = (1, side)
        for runs in range(2, max_runs + 1):
            for lengths in itertools.product(range(1, max_len + 1), repeat=runs):
                if sum(lengths) > max_children:
                    continue
                for left, right in itertools.product((0, 1), repeat=2):
                    word = [marker] * left
                    for i, length in enumerate(lengths):
                        if i:
                            word.append(marker)
                        word.extend(["S"] * length)
                    yield tuple(word + [marker] * right)


def check_row(evaluate, row, counts):
    value = evaluate(row["word"], row["maxima"])
    choices = singleton_cut_values(evaluate, row)
    for _, p, side, maximum in choices:
        leaf = part(row, {p}, side, maximum)
        runs, cups, caps = limits_from_signature(
            leaf["word"], leaf["maxima"], row["a"], row["u"], row["k"], lean=True)
        if runs != 1:
            raise ValueError("singleton part did not have exactly one run")
        explicit = threshold(int(caps[0, 0]) + 1, int(cups[0, 0]) + 1, row["k"])
        if explicit != evaluate(leaf["word"], leaf["maxima"]):
            raise ValueError("explicit T disagrees with compiled singleton")
        counts["leaf_audits"] += 1
    counts["roots"] += 1
    counts["cuts"] += len(choices)
    best = max(choices)
    return None if value <= best[0] else {**row, "bound": value, "best_singleton": best}


def main():
    parser = argparse.ArgumentParser()
    for flag in ("dataset", "out", "node", "statement"):
        parser.add_argument("--" + flag)
    parser.add_argument("--ks", default="5,6")
    parser.add_argument("--max-runs", type=int, default=4)
    parser.add_argument("--max-len", type=int, default=2)
    parser.add_argument("--max-children", type=int, default=4)
    parser.add_argument("--timing-only", action="store_true")
    args = parser.parse_args()
    start = time.monotonic()
    counts = Counter()
    violations = []
    scope = []
    words = tuple(root_words(args.max_runs, args.max_len, args.max_children))
    for k in map(int, args.ks.split(",")):
        parameters = ([(k, k)] if args.timing_only else
            list(itertools.product(range(1, k + 1), repeat=2)) if k <= 5 else [(5, 5), (k, k)])
        selected_words = (max(words, key=len),) if args.timing_only else words
        maxima = [1] if args.timing_only else list(range(1, k - 1))
        total = len(parameters) * len(selected_words) * len(maxima)
        scope.append({"k": k, "parameters": parameters, "words": len(selected_words),
                      "maxima": maxima, "total": total})
        for a, u in parameters:
            evaluate = compiled_evaluator(a, u, k, cache_size=2_000_000, persistent=True)
            try:
                for m in maxima:
                    for word in selected_words:
                        row = {"word": word, "maxima": (m,), "a": a, "u": u, "k": k,
                               "chosen": "lower"}
                        witness = check_row(evaluate, row, counts)
                        if witness is not None:
                            counts["violations"] += 1
                            if len(violations) < 20:
                                violations.append(witness)
                    elapsed = time.monotonic() - start
                    print(json.dumps({"k": k, "a": a, "u": u, "m": m,
                        "elapsed": elapsed, "rate": counts["roots"] / elapsed,
                        "counts": dict(counts), "scope_total": total}), flush=True)
            finally:
                evaluate.close()
    result = {"node": args.node, "statement": args.statement,
        "semantics": "context-bound-zero-children-c-v1", "args": vars(args),
        "scope": scope, "counts": dict(counts), "seconds": time.monotonic() - start,
        "violations": violations, "complete": True}
    if args.out:
        Path(args.out).write_text(json.dumps(result, indent=2) + "\n")
    return 2 if violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
