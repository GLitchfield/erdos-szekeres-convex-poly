#!/usr/bin/env python3
"""Falsifier for ctx_bound_child_run_contraction_one_level_root (C1r, Workstream B): for a root
context with one external level, <a, u, k, word over {S, ext 1 s}, maxima [m]> with
1 <= a, u <= k, 3 <= k and 1 <= m <= k-2, deleting one of two adjacent child letters leaves the bound
unchanged.

This is the normalized form of run contraction (C1) as the single-run chain uses it: every part of
a single-run context has the bound of such a context (ctx_single_run_descendant_bound_normalize),
with (a, u) = (capLimit + 1, cupLimit + 1) of the run.  Contexts: 1-3 runs of lengths <= 3 with at
least one run of length >= 2 and at most 5 child letters (one 4-run, 6-child context alone takes
minutes: the recursion adds a level per cut), 1-2 separator letters, 0-2 letters at each end, both
sides, every m, all a, u in [1, k]; one progress line per (k, a, u) on stderr.  Uses the compiled evaluator (context-bound-zero-children-c-v1, a
persistent memo per (a, u, k)).  Evidence at research scale: runs/claude-comb-closedform-20260930/c1r
(root-level cross-cut domination, k = 5..7) and p10.
Exit 0: no violation; exit 2: a context whose bound changes (witness in --out).
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness.research.context_bound import compiled_evaluator  # noqa: E402


def words(rng, side, per_shape):
    x = (1, side)
    for j in (1, 2, 3):
        shapes = [lens for lens in itertools.product(range(1, 4), repeat=j) if max(lens) >= 2 and sum(lens) <= 5]
        for lens in rng.sample(shapes, min(per_shape, len(shapes))):
            seps = [rng.choice((1, 2)) for _ in range(j - 1)]
            eL, eR = rng.choice((0, 1, 2)), rng.choice((0, 1, 2))
            w = [x] * eL
            for i, r in enumerate(lens):
                w += ['S'] * r
                if i < j - 1:
                    w += [x] * seps[i]
            yield tuple(w + [x] * eR)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset"); ap.add_argument("--out"); ap.add_argument("--node"); ap.add_argument("--statement")
    ap.add_argument("--ks", default="5,6")
    ap.add_argument("--per-shape", type=int, default=3)
    ap.add_argument("--seed", type=int, default=20260930)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    summary = {"node": a.node, "semantics": "context-bound-zero-children-c-v1", "cases": {}}
    violations = []
    for K in map(int, a.ks.split(",")):
        checked = 0
        for A in range(1, K + 1):
            for U in range(1, K + 1):
                F = compiled_evaluator(A, U, K, cache_size=500000, persistent=True)
                for side in ("lower", "upper"):
                    for m in range(1, K - 1):
                        for w in words(rng, side, a.per_shape):
                            i = next(p for p in range(len(w) - 1) if w[p] == 'S' and w[p + 1] == 'S')
                            short = w[:i] + w[i + 1:]
                            x, y = F(w, (m,)), F(short, (m,))
                            checked += 1
                            if x != y:
                                violations.append({"a": A, "u": U, "k": K, "m": m, "word": w, "bound": x,
                                                   "contracted_bound": y})
                F.close()
                print(json.dumps({"k": K, "a": A, "u": U, "checked": checked, "violations": len(violations)}),
                      file=sys.stderr, flush=True)
        summary["cases"][str(K)] = {"checked": checked}
        print(json.dumps({"k": K, "checked": checked, "violations": len(violations)}), file=sys.stderr, flush=True)
        if violations:
            break
    summary["violations"] = violations[:20]
    if a.out:
        Path(a.out).write_text(json.dumps(summary, indent=1) + "\n")
    return 2 if violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
