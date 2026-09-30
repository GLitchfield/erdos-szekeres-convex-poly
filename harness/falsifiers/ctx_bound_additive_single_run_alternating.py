#!/usr/bin/env python3
"""Falsifier for ctx_bound_additive_single_run_alternating (Workstream B): single-run additivity
restricted to alternating singleton partitions.  For a well-formed single-run context sigma
(outside letters of levels 1-2 on either side), the kept set is every second child position
starting at the first (r = 0) or the second (r = 1); for every coupling d in [1, k-2] and both
orientations, the two part bounds sum to at most bound(sigma).

Together with run contraction under level-one spans (ctx_bound_child_run_contraction_of_level_one_span)
and ctx_bound_external_letter_contraction this gives ctx_bound_additive_single_run
(ctx_bound_additive_single_run_of_run_contraction_and_alternating).  Research evidence with a compiled
evaluator: 0 violations up to run length 10 in ten triples (runs/claude-comb-reduction-20260929/p6/).
Uses the registered Python evaluator (harness.research.recursive, context-bound-zero-children-v1).
Exit 0: no violation; exit 2: a violating context (witness in --out).
"""
from __future__ import annotations

import argparse
import json
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))
from harness.research.recursive import evaluator  # noqa: E402
from decomposable_additivity_test import child  # noqa: E402

OUTSIDE = [((), ()), (((1, 'lower'),), ()), ((), ((1, 'upper'),)), (((1, 'upper'),), ()),
           (((1, 'lower'),), ((1, 'lower'),)), (((1, 'lower'),), ((2, 'upper'),)),
           (((2, 'upper'),), ((1, 'lower'),)), (((1, 'upper'), (2, 'lower')), ()),
           ((), ((1, 'lower'), (2, 'upper')))]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset"); ap.add_argument("--out"); ap.add_argument("--node"); ap.add_argument("--statement")
    ap.add_argument("--cases", default="4,4,5;3,4,5;5,5,5;4,5,6;5,5,6")
    ap.add_argument("--n-max", type=int, default=6)
    ap.add_argument("--seed", type=int, default=20260929)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    summary = {"node": a.node, "semantics": "context-bound-zero-children-v1", "cases": {}}
    violations = []
    for case in a.cases.split(";"):
        A, U, K = map(int, case.split(","))
        F = evaluator(A, U, K, semantics="context-bound-zero-children-v1", cache_size=300000)
        checked = 0
        for n in range(2, a.n_max + 1):
            for left, right in OUTSIDE:
                depth = max([l for l, _ in left + right], default=0)
                for maxima in {(1,) * depth, (K - 2,) * depth, tuple(rng.randint(1, K - 2) for _ in range(depth))}:
                    word = tuple(left) + ('S',) * n + tuple(right)
                    base = F(word, maxima)
                    first = len(left)
                    for r in (0, 1):
                        keep = frozenset(first + i for i in range(n) if i % 2 == r)
                        rest = frozenset(first + i for i in range(n) if i % 2 != r)
                        for d in range(1, K - 1):
                            c = K - 1 - d
                            v1 = F(*child(word, maxima, keep, 'lower', d)) + F(*child(word, maxima, rest, 'upper', c))
                            v2 = F(*child(word, maxima, keep, 'upper', c)) + F(*child(word, maxima, rest, 'lower', d))
                            checked += 1
                            if max(v1, v2) > base:
                                violations.append({"case": case, "word": word, "maxima": maxima, "r": r, "d": d,
                                                   "values": [v1, v2], "bound": base})
                                break
        summary["cases"][case] = {"checked": checked}
        print(json.dumps({"case": case, "checked": checked}), file=sys.stderr, flush=True)
        if violations:
            break
    summary["violations"] = violations
    if a.out:
        Path(a.out).write_text(json.dumps(summary, indent=1) + "\n")
    return 2 if violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
