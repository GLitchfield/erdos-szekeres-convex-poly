#!/usr/bin/env python3
"""Falsifier for ctx_bound_child_run_contraction_of_level_one_span (Workstream B): if every
letter strictly inside the child span of a well-formed context is a child letter or a level-one
external letter of one fixed side, deleting one of two adjacent child letters leaves the bound
unchanged.  Repeated, it shortens every child run to one letter (multi-run uniform-separator
contraction; the two-run case is ctx_bound_uniform_separator_contraction).

Contexts: OLDER_L + (1,s)^e1 + S^r1 (1,s)^m1 S^r2 ... S^rj + (1,s)^e2 + OLDER_R with j = 2 or 3
runs, one run of length 2 or 3, separators of 1 or 2 letters, optional level-one letters outside
the span, and older letters (levels >= 2) only outside the span; maxima all 1, all k-2, or
seeded random.  Uses the registered Python evaluator (harness.research.recursive,
context-bound-zero-children-v1).  The unrestricted law is false
(ctx_bound_adjacent_letter_contraction_counterexample); its witness [S,1L,2U,S,S] has a
level-two letter inside the span and is checked to lie outside this hypothesis.
Research evidence with a compiled evaluator (exhaustive over this family at nine parameter
triples): runs/claude-comb-reduction-20260929/p1c.json.
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
from harness.research.recursive import evaluator  # noqa: E402

OLDER = [((), ()), (((2, 'lower'),), ()), ((), ((2, 'upper'),)), (((2, 'lower'),), ((2, 'lower'),)),
         (((2, 'lower'),), ((3, 'upper'),)), (((2, 'upper'), (3, 'lower')), ())]
RUNS = [(2, 1), (1, 2), (3, 1), (2, 2), (2, 1, 1), (1, 2, 1), (1, 1, 2)]


def build(left, e1, runs, seps, e2, right, side):
    w = list(left) + [(1, side)] * e1
    for i, r in enumerate(runs):
        w += ['S'] * r
        if i < len(seps):
            w += [(1, side)] * seps[i]
    return tuple(w + [(1, side)] * e2 + list(right))


def in_class(word):
    kids = [i for i, x in enumerate(word) if x == 'S']
    inner = [word[i] for i in range(kids[0] + 1, kids[-1]) if word[i] != 'S']
    return all(x[0] == 1 for x in inner) and len({x for x in inner}) <= 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset"); ap.add_argument("--out"); ap.add_argument("--node"); ap.add_argument("--statement")
    ap.add_argument("--cases", default="4,4,5;3,4,5;4,5,5;5,5,6")
    ap.add_argument("--per-case", type=int, default=120)
    ap.add_argument("--seed", type=int, default=20260929)
    a = ap.parse_args()
    assert not in_class(('S', (1, 'lower'), (2, 'upper'), 'S', 'S')), "control: refuted witness must be excluded"
    rng = random.Random(a.seed)
    summary = {"node": a.node, "semantics": "context-bound-zero-children-v1", "cases": {}}
    violations = []
    for case in a.cases.split(";"):
        A, U, K = map(int, case.split(","))
        F = evaluator(A, U, K, semantics="context-bound-zero-children-v1", cache_size=200000)
        cands = []
        for left, right in OLDER:
            depth = max([l for l, _ in left + right], default=1)
            for side in ("lower", "upper"):
                for e1, e2 in ((0, 0), (1, 0), (0, 1)):
                    for runs in RUNS:
                        for seps in itertools.product((1, 2), repeat=len(runs) - 1):
                            for maxima in {(1,) * depth, (K - 2,) * depth,
                                           tuple(rng.randint(1, K - 2) for _ in range(depth))}:
                                cands.append((left, right, side, e1, e2, runs, seps, maxima))
        rng.shuffle(cands)
        checked = 0
        for left, right, side, e1, e2, runs, seps, maxima in cands[:a.per_case]:
            long_ = build(left, e1, runs, seps, e2, right, side)
            assert in_class(long_)
            # delete one letter of the first run of length >= 2
            i = next(k for k, r in enumerate(runs) if r >= 2)
            short = build(left, e1, runs[:i] + (runs[i] - 1,) + runs[i + 1:], seps, e2, right, side)
            x, y = F(long_, maxima), F(short, maxima)
            checked += 1
            if x != y:
                violations.append({"case": case, "word": long_, "contracted": short, "maxima": maxima,
                                   "bound": x, "contracted_bound": y})
                break
        summary["cases"][case] = {"checked": checked, "available": len(cands)}
        print(json.dumps({"case": case, **summary["cases"][case]}), file=sys.stderr, flush=True)
    summary["violations"] = violations
    if a.out:
        Path(a.out).write_text(json.dumps(summary, indent=1) + "\n")
    return 2 if violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
