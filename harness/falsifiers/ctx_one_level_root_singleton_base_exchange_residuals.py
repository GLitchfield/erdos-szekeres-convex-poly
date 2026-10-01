#!/usr/bin/env python3
"""Actual-domain finite checks of the five R17 restrictions of X.

The --node selects one registered mathematical domain. Every retained source
cut is compared with every legal side/coupling at its mapped target singleton.
Root enumeration, explicit singleton T audits, part construction, and the
compiled zero-child interval-cut recurrence reuse existing implementations.
Passes are bounded arithmetic evidence, never kernel proof credit.

Default family: k3..5, all legal global axes and m, 2/3 child runs of lengths
1/2 with an adjacent pair, at most five children, one marker per gap,
0/1 endpoint markers, both old sides. Residuals require a,u>=2. Unit-axis
cuts require a<=1 or u<=1. Inside and multirun-complement residuals also
require the old chosen axis >=3; the chosen-axis-two subcase requires <=2.
The complement run predicate counts runs in the
actual complement part, rather than in the parent root.
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
from harness.falsifiers.ctx_one_level_root_singleton_base_exchange import (
    roots, singleton_values,
)
from harness.research.context_bound import SEMANTICS, compiled_evaluator
from harness.research.primitives import part
from decomposable_recursive_formula import run_index

DOMAINS = {
    "ErdosSzekeres.ctx_one_level_root_singleton_base_exchange_unit_axis": "unit",
    "ErdosSzekeres.ctx_one_level_root_singleton_base_exchange_chosen_axis_two": "chosen_axis_two",
    "ErdosSzekeres.ctx_one_level_root_singleton_base_exchange_inside_pair": "inside",
    "ErdosSzekeres.ctx_one_level_root_singleton_base_exchange_outside_single_run": "outside_single_run",
    "ErdosSzekeres.ctx_one_level_root_singleton_base_exchange_outside_multirun": "outside_multirun",
}


def selected(domain, a, u, old_side, p, pair_start, complement_runs):
    """Exact extra predicates of the corresponding registered X restriction."""
    if domain == "unit":
        return a <= 1 or u <= 1
    chosen = u if old_side == "lower" else a
    if domain == "chosen_axis_two":
        return chosen <= 2
    if a < 2 or u < 2:
        return False
    if domain in ("inside", "outside_multirun") and chosen < 3:
        return False
    inside = p in (pair_start, pair_start + 1)
    if domain == "inside":
        return inside
    if domain == "outside_single_run":
        return not inside and complement_runs <= 1
    if domain == "outside_multirun":
        return not inside and complement_runs >= 2
    raise ValueError("unknown exchange restriction")


def main():
    parser = argparse.ArgumentParser()
    for flag in ("dataset", "out", "node", "statement"):
        parser.add_argument("--" + flag)
    parser.add_argument("--ks", default="3,4,5")
    parser.add_argument("--max-children", type=int, default=5)
    args = parser.parse_args()
    if args.node not in DOMAINS:
        parser.error("--node must name a registered R17 exchange restriction")
    domain = DOMAINS[args.node]
    words = tuple(roots(args.max_children))
    counts = Counter()
    violations = []
    scope = []
    started = time.monotonic()
    for k in map(int, args.ks.split(",")):
        if k < 3:
            parser.error("k must be at least three")
        parameters = list(itertools.product(range(1, k + 1), repeat=2))
        if domain == "unit":
            parameters = [(a, u) for a, u in parameters if a <= 1 or u <= 1]
        elif domain == "chosen_axis_two":
            parameters = [(a, u) for a, u in parameters if a <= 2 or u <= 2]
        else:
            parameters = [(a, u) for a, u in parameters if a >= 2 and u >= 2]
        scope.append(dict(k=k, parameters=parameters, words=len(words),
                          maxima=list(range(1, k - 1))))
        for a, u in parameters:
            evaluate = compiled_evaluator(a, u, k, cache_size=2_000_000, persistent=True)
            try:
                for m in range(1, k - 1):
                    for word in words:
                        row = dict(word=word, maxima=(m,), a=a, u=u, k=k, chosen="lower")
                        old_side = next(token[1] for token in word if token != "S")
                        children = frozenset(i for i, token in enumerate(word) if token == "S")
                        original = singleton_values(evaluate, a, u, k, word, m, counts)
                        counts["roots"] += 1
                        complement_runs = {}
                        for p in children:
                            rest = part(row, children - {p}, "lower", 1)
                            complement_runs[p] = len({r for r in run_index(rest["word"])
                                                      if r is not None})
                        for y in range(len(word) - 1):
                            if word[y:y + 2] != ("S", "S"):
                                continue
                            short = word[:y + 1] + word[y + 2:]
                            shortened = singleton_values(evaluate, a, u, k, short, m, counts)
                            counts["pairs"] += 1
                            for (p, side, c), value in original.items():
                                if not selected(domain, a, u, old_side, p, y, complement_runs[p]):
                                    counts["excluded_cuts"] += 1
                                    continue
                                q = p if p <= y else p - 1
                                candidates = [(t, d, v) for (r, t, d), v in shortened.items()
                                              if r == q]
                                best = max(v for _, _, v in candidates)
                                counts["selected_cuts"] += 1
                                if value > best:
                                    counts["violations"] += 1
                                    violations.append(dict(a=a, u=u, k=k, m=m, word=word,
                                        pair_start=y, p=p, q=q, side=side, coupling=c,
                                        complement_runs=complement_runs[p], value=value,
                                        best_shortened=best, candidates=candidates))
                    print(json.dumps(dict(k=k, a=a, u=u, m=m,
                        elapsed=time.monotonic() - started, counts=dict(counts))), flush=True)
            finally:
                evaluate.close()
    result = dict(node=args.node, statement=args.statement, domain=domain,
                  semantics=SEMANTICS, scope=scope, max_children=args.max_children,
                  counts=dict(counts), seconds=time.monotonic() - started,
                  violations=violations)
    if args.out:
        Path(args.out).write_text(json.dumps(result, indent=2) + "\n")
    return 2 if violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
