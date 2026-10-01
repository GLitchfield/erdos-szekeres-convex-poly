"""Finite actual-domain checks of the two strict source-opposite-three residuals.

Reuse the baseline restricted root family and singleton_values, including its
independent explicit-T audit for every singleton. Compare each selected source
cut with every legal target side/coupling; the target domain is never filtered.
Compiled arithmetic is diagnostic evidence, not a Lean proof or selector.
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
sys.path.insert(0, str(ROOT / "tools/es"))
from es.artifact_cache import sha256_file
from harness.falsifiers.ctx_one_level_root_singleton_base_exchange import roots, singleton_values
from harness.research.context_bound import SEMANTICS, compiled_evaluator
from harness.research.primitives import part
from decomposable_recursive_formula import run_index

DOMAINS = {
    "ErdosSzekeres.ctx_one_level_root_singleton_base_exchange_inside_pair_source_opposite_three": "inside",
    "ErdosSzekeres.ctx_one_level_root_singleton_base_exchange_outside_multirun_source_opposite_three": "outside_multirun",
}
DEADLINE = 1790906271.164032


def selected(domain, a, u, old_side, p, pair_start, complement_runs, source_side):
    """Exactly the new registered predicates; the two sides are independent."""
    if a < 2 or u < 2:
        return False
    if (u if old_side == "lower" else a) < 3:
        return False
    if (a if source_side == "lower" else u) < 3:
        return False
    inside = p in (pair_start, pair_start + 1)
    if domain == "inside":
        return inside
    if domain == "outside_multirun":
        return not inside and complement_runs >= 2
    raise ValueError("unknown strict residual domain")


def main():
    parser = argparse.ArgumentParser()
    for flag in ("dataset", "out", "node", "statement"):
        parser.add_argument("--" + flag)
    parser.add_argument("--ks", default="3,4,5")
    parser.add_argument("--max-children", type=int, default=5)
    args = parser.parse_args()
    if args.node not in DOMAINS:
        parser.error("--node must name one of the two source-opposite-three residuals")
    domain = DOMAINS[args.node]
    # Semantic fixtures distinguish the old-marker and source-cut axes.
    assert selected("inside", 2, 4, "lower", 1, 0, 1, "upper")
    assert not selected("inside", 2, 4, "lower", 1, 0, 1, "lower")
    assert not selected("inside", 4, 2, "lower", 1, 0, 1, "lower")
    assert selected("outside_multirun", 2, 4, "lower", 4, 0, 2, "upper")
    assert not selected("outside_multirun", 2, 4, "lower", 4, 0, 1, "upper")
    words = tuple(roots(args.max_children))
    counts, violations, scope = Counter(), [], []
    started = time.monotonic()
    for k in map(int, args.ks.split(",")):
        if k < 3:
            parser.error("k must be at least three")
        parameters = list(itertools.product(range(2, k + 1), repeat=2))
        scope.append(dict(k=k, parameters=parameters, words=len(words),
                          maxima=list(range(1, k - 1))))
        for a, u in parameters:
            if time.time() >= DEADLINE:
                raise RuntimeError("Exact user research deadline reached; no new axis")
            evaluate = compiled_evaluator(a, u, k, cache_size=2_000_000, persistent=True)
            try:
                for m in range(1, k - 1):
                    for word in words:
                        if time.time() >= DEADLINE:
                            raise RuntimeError("Exact user research deadline reached; no new root")
                        row = dict(word=word, maxima=(m,), a=a, u=u, k=k, chosen="lower")
                        old_side = next(token[1] for token in word if token != "S")
                        children = frozenset(i for i, token in enumerate(word) if token == "S")
                        original = singleton_values(evaluate, a, u, k, word, m, counts)
                        counts["roots"] += 1
                        complement_runs = {}
                        for p in children:
                            rest = part(row, children - {p}, "lower", 1)
                            complement_runs[p] = len({r for r in run_index(rest["word"]) if r is not None})
                        for y in range(len(word) - 1):
                            if word[y:y + 2] != ("S", "S"):
                                continue
                            short = word[:y + 1] + word[y + 2:]
                            shortened = singleton_values(evaluate, a, u, k, short, m, counts)
                            counts["pairs"] += 1
                            for (p, side, c), value in original.items():
                                if not selected(domain, a, u, old_side, p, y, complement_runs[p], side):
                                    counts["excluded_cuts"] += 1
                                    continue
                                q = p if p <= y else p - 1
                                candidates = [(t, d, v) for (r, t, d), v in shortened.items() if r == q]
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
                  violations=violations, terminal=True,
                  source_sha256={str(p.relative_to(ROOT)): sha256_file(p) for p in (
                      Path(__file__), ROOT / "harness/falsifiers/ctx_one_level_root_singleton_base_exchange.py",
                      ROOT / "harness/research/context_bound.py", ROOT / "harness/research/primitives.py",
                  )})
    if args.out:
        Path(args.out).write_text(json.dumps(result, indent=2) + "\n")
    return 2 if violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
