#!/usr/bin/env python3
"""Finite direct PEEL diagnostic for legal contexts, including absent levels.

Each word has a fixed number of children and at most one marker of each actual
level. Any subset of the declared levels may be present, at arbitrary positions,
with every side assignment and every legal maximum. This is explicitly a finite
family, not coverage of arbitrary depth, multiplicity, or child count. Compare
the full interval-cut bound with every singleton cut, retaining zero-valued
parts and filtering exactly the conjecture's bound >= 2 domain.
An explicit JSON dataset file instead supplies a list of rows (or {"rows": [...]}),
each checked against the statement's WellFormed/global/two-run hypotheses.
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
from harness.research.context_bound import compiled_evaluator
from harness.research.singleton_cuts import singleton_cut_values


def num_runs(word):
    return sum(x == "S" and (i == 0 or word[i - 1] != "S")
               for i, x in enumerate(word))


def templates(depth, children):
    """Distinct marker levels, all actual subsets, all sides and placements."""
    for actual in range(1, depth + 1):
        size = children + actual
        for levels in itertools.permutations(range(1, depth + 1), actual):
            for positions in itertools.combinations(range(size), actual):
                raw = ["S"] * size
                for p, level in zip(positions, levels):
                    raw[p] = level
                if num_runs(raw) < 2:
                    continue
                for sides in itertools.product(("lower", "upper"), repeat=actual):
                    word = list(raw)
                    for p, level, side in zip(positions, levels, sides):
                        word[p] = (level, side)
                    yield tuple(word)


def validated_row(raw):
    row = {key: raw[key] for key in ("a", "u", "k", "word", "maxima")}
    a, u, k = row["a"], row["u"], row["k"]
    if any(type(x) is not int for x in (a, u, k)) or not (4 <= a <= k and 4 <= u <= k):
        raise ValueError("dataset row requires integer 4 <= a,u <= k")
    maxima = tuple(row["maxima"])
    if any(type(x) is not int or not 1 <= x <= k - 2 for x in maxima):
        raise ValueError("dataset maxima must satisfy 1 <= m <= k-2")
    word = []
    sides = {}
    for token in row["word"]:
        if token == "S":
            word.append("S")
            continue
        if not isinstance(token, (tuple, list)) or len(token) != 2:
            raise ValueError(f"invalid dataset marker {token!r}")
        level, side = token
        if type(level) is not int or not 1 <= level <= len(maxima) or side not in ("lower", "upper"):
            raise ValueError(f"invalid dataset level/side {token!r}")
        if level in sides and sides[level] != side:
            raise ValueError("one actual level has conflicting sides")
        sides[level] = side
        word.append((level, side))
    if num_runs(word) < 2:
        raise ValueError("dataset row requires at least two child runs")
    return {**row, "word": tuple(word), "maxima": maxima, "chosen": "lower"}


def inspect_row(evaluate, row, counts):
    value = evaluate(row["word"], row["maxima"])
    counts["rows"] += 1
    if value < 2:
        counts["outside_bound_domain"] += 1
        return None
    counts["eligible"] += 1
    choices = singleton_cut_values(evaluate, row)
    counts["singleton_cuts"] += len(choices)
    best = max(x[0] for x in choices)
    if best > value:
        raise ValueError(f"singleton exceeds interval recurrence: {row!r}, {value}, {best}")
    if any(x[0] == value for x in choices):
        return None
    counts["violations"] += 1
    witness = {**row, "bound": value, "best_singleton": best,
               "maximizers": [x for x in choices if x[0] == best]}
    print(json.dumps({"counterexample": witness}), flush=True)
    return witness


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ("dataset", "out", "node", "statement"):
        parser.add_argument("--" + flag)
    parser.add_argument("--ks", default="5,6")
    parser.add_argument("--depths", default="1,2,3")
    parser.add_argument("--children", type=int, default=4)
    parser.add_argument("--timing-only", action="store_true")
    parser.add_argument("--timing-samples", type=int, default=256)
    args = parser.parse_args()
    ks = tuple(map(int, args.ks.split(",")))
    depths = tuple(map(int, args.depths.split(",")))
    if args.children < 2 or min(ks) < 4 or min(depths) < 1 or args.timing_samples < 1:
        parser.error("need children >= 2, k >= 4, depth >= 1 and positive sample count")
    start = time.monotonic()
    counts = Counter()
    scope = []
    violations = []
    if args.dataset and Path(args.dataset).is_file():
        dataset = json.loads(Path(args.dataset).read_text())
        raw_rows = dataset if isinstance(dataset, list) else dataset["rows"]
        if not isinstance(raw_rows, list) or not raw_rows:
            raise ValueError("explicit dataset must contain a nonempty row list")
        for done, raw in enumerate(raw_rows, 1):
            row = validated_row(raw)
            evaluate = compiled_evaluator(row["a"], row["u"], row["k"], persistent=True)
            try:
                witness = inspect_row(evaluate, row, counts)
                if witness is not None and len(violations) < 20:
                    violations.append(witness)
            finally:
                evaluate.close()
            print(json.dumps({"done": done, "total": len(raw_rows),
                              "counts": dict(counts)}), flush=True)
        result = {"node": args.node, "statement": args.statement,
                  "semantics": "context-bound-zero-children-c-v1", "args": vars(args),
                  "family": "explicit-wellformed-context-rows-v1", "counts": dict(counts),
                  "seconds": time.monotonic() - start, "violations": violations,
                  "complete": True, "diagnostic_only": True}
        if args.out:
            Path(args.out).parent.mkdir(parents=True, exist_ok=True)
            Path(args.out).write_text(json.dumps(result, indent=2) + "\n")
        return 2 if violations else 0
    if args.dataset and not Path(args.dataset).is_dir():
        raise ValueError("dataset must be an existing JSON file or a directory for generated coverage")
    words = {d: tuple(templates(d, args.children)) for d in depths}
    for k in ks:
        axes = [(k, k)] if args.timing_only else list(itertools.product(range(4, k + 1), repeat=2))
        for a, u in axes:
            evaluate = compiled_evaluator(a, u, k, cache_size=2_000_000, persistent=True)
            try:
                for depth in depths:
                    maxima = tuple(itertools.product(range(1, k - 1), repeat=depth))
                    total = len(words[depth]) * len(maxima)
                    indices = range(total)
                    if args.timing_only:
                        stride = max(1, (total + args.timing_samples - 1) // args.timing_samples)
                        indices = range(0, total, stride)
                    selected = len(indices)
                    family_start = time.monotonic()
                    family_counts = Counter()
                    scope.append({"a": a, "u": u, "k": k, "depth": depth,
                                  "children": args.children, "templates": len(words[depth]),
                                  "full_rows": total, "selected_rows": selected})
                    for done, index in enumerate(indices, 1):
                        word = words[depth][index // len(maxima)]
                        mx = maxima[index % len(maxima)]
                        row = {"word": word, "maxima": mx, "a": a, "u": u, "k": k,
                               "chosen": "lower"}
                        witness = inspect_row(evaluate, row, family_counts)
                        if witness is not None and len(violations) < 20:
                            violations.append(witness)
                        if done % 1000 == 0 or done == selected:
                            elapsed = time.monotonic() - family_start
                            rate = done / max(elapsed, 1e-9)
                            print(json.dumps({"a": a, "u": u, "k": k, "depth": depth,
                                              "done": done, "total": selected,
                                              "seconds": elapsed, "rate": rate,
                                              "eta_seconds": (selected - done) / rate,
                                              "counts": dict(family_counts)}), flush=True)
                    counts.update(family_counts)
            finally:
                evaluate.close()
    result = {"node": args.node, "statement": args.statement,
              "semantics": "context-bound-zero-children-c-v1", "args": vars(args),
              "family": "distinct-actual-markers-all-subsets-v1", "scope": scope,
              "counts": dict(counts), "seconds": time.monotonic() - start,
              "violations": violations, "complete": True,
              "diagnostic_only": True}
    if args.out:
        Path(args.out).parent.mkdir(parents=True, exist_ok=True)
        Path(args.out).write_text(json.dumps(result, indent=2) + "\n")
    return 2 if violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
