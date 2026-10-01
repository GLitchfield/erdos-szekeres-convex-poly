#!/usr/bin/env python3
"""R15 singleton-segment exchange; diagnostic arithmetic, never Lean proof credit.

The original value is tested at every coupling/orientation by taking its maximum.
The right side may use any coupling/orientation. A candidate child must have every
existing immediate child-order neighbour on the opposite side. Both original sides
must be nonempty, proper and noninterval. Complements are identified only because
both orientations are evaluated. The broad domain is an explicitly retained sample,
not an exhaustive assertion about all generated contexts.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))
from harness.research.context_bound import SEMANTICS, compiled_evaluator
from decomposable_additivity_test import child, contexts


def interval(kids, keep):
    indices = [i for i, p in enumerate(kids) if p in keep]
    return bool(indices) and indices == list(range(indices[0], indices[-1] + 1))


def singleton_indices(kids, keep):
    return [i for i, p in enumerate(kids)
            if all((kids[j] in keep) != (p in keep)
                   for j in (i - 1, i + 1) if 0 <= j < len(kids))]


def profile(evaluate, k, word, maxima, keep):
    rest = frozenset(i for i, token in enumerate(word) if token == "S") - keep
    best = None
    for d in range(1, k - 1):
        c = k - 1 - d
        for side, other, m, m2 in (("lower", "upper", d, c), ("upper", "lower", c, d)):
            parts = [evaluate(*child(word, maxima, keep, side, m)),
                     evaluate(*child(word, maxima, rest, other, m2))]
            item = {"value": sum(parts), "d": d, "orientation": side, "parts": parts}
            if best is None or item["value"] > best["value"]:
                best = item
    return best


def test_context(row, evaluate):
    word = tuple("S" if token == "S" else tuple(token) for token in row["word"])
    maxima = tuple(row["maxima"])
    kids = [i for i, token in enumerate(word) if token == "S"]
    profiles = {}
    counts, choices, failures = Counter(), Counter(), []

    def value(keep):
        key = tuple(sorted(keep))
        if key not in profiles:
            profiles[key] = profile(evaluate, row["k"], word, maxima, keep)
        return profiles[key]

    masks = ([sum(1 << i for i, p in enumerate(kids) if p in row["keep"])]
             if "keep" in row else range(1, 1 << len(kids)))
    for mask in masks:
        if ("keep" not in row and not mask & 1) or mask == (1 << len(kids)) - 1:
            continue
        keep = frozenset(p for i, p in enumerate(kids) if mask >> i & 1)
        rest = frozenset(kids) - keep
        if interval(kids, keep) or interval(kids, rest):
            continue
        if len(kids) >= 6:
            print(json.dumps({"starting_partition": sorted(keep), "mask": mask,
                              "mask_space": 1 << len(kids),
                              "completed_interleaved": counts["interleaved_partitions"]}), flush=True)
        counts["interleaved_partitions"] += 1
        eligible = singleton_indices(kids, keep)
        if not eligible:
            counts["no_singleton_failures"] += 1
            failures.append({"row": row, "keep": sorted(keep), "eligible_indices": [],
                             "d": 1, "orientation": "lower",
                             "reason": "No singleton segment exists; values are irrelevant."})
            continue
        old = value(keep)
        working = []
        for i in eligible:
            flipped = keep ^ {kids[i]}
            new = value(flipped)
            if old["value"] <= new["value"]:
                working.append(i)
                choices["end" if i in (0, len(kids) - 1) else "interior"] += 1
                choices["next_to_external" if any(
                    0 <= q < len(word) and word[q] != "S" for q in (kids[i]-1, kids[i]+1)
                ) else "no_adjacent_external"] += 1
        if not working:
            counts["value_failures"] += 1
            failures.append({"row": row, "keep": sorted(keep), "eligible_indices": eligible,
                             "old": old, "flips": [value(keep ^ {kids[i]}) for i in eligible]})
        else:
            counts["passed_partitions"] += 1
    return {"counts": dict(counts), "working_choices": dict(choices), "failures": failures[:30]}


def broad_rows():
    """Retain 24 reproducible rows per case from each of the two declared domains."""
    rows = []
    for a, u, k in ((3, 4, 5), (4, 4, 5), (5, 5, 6)):
        for depth in (2, 3):
            selected = []
            seen = 0
            for word, maxima in contexts(5, depth, depth, k, include_unused_levels=True):
                if word.count("S") < 4 or len(maxima) != depth or len(set(maxima)) < 2:
                    continue
                if {token[1] for token in word if token != "S"} != {"lower", "upper"}:
                    continue
                if sum(token == "S" and (i == 0 or word[i-1] != "S")
                       for i, token in enumerate(word)) < 2:
                    continue
                seen += 1
                row = {"a": a, "u": u, "k": k, "word": word, "maxima": maxima}
                rank = hashlib.sha256(json.dumps(row, sort_keys=True).encode()).hexdigest()
                selected.append((rank, row))
                selected.sort(key=lambda item: item[0])
                del selected[24:]
            rows.extend(row for _, row in selected)
            print(json.dumps({"selection_case": [a, u, k], "depth": depth,
                              "eligible_rows": seen, "retained": len(selected)}), flush=True)
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dataset")
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--node")
    parser.add_argument("--statement")
    parser.add_argument("--mode", choices=("timing", "broad", "obstruction"), default="broad")
    args = parser.parse_args()
    heavy = {"a": 5, "u": 5, "k": 6,
             "word": ["S", [1, "lower"], "S", [2, "upper"], "S", [3, "lower"],
                      "S", "S", "S"], "maxima": [1, 2, 4]}
    obstruction = {"a": 3, "u": 3, "k": 4,
                   "word": ["S", "S", [1, "lower"], "S", "S", "S", "S", "S", "S"],
                   "maxima": [1], "keep": [3, 4, 7, 8]}
    rows = [heavy] if args.mode == "timing" else ([obstruction] if args.mode == "obstruction"
                                                else broad_rows() + [heavy, obstruction])
    started = time.monotonic()
    result = {"semantics": SEMANTICS, "certification": "diagnostic", "mode": args.mode,
              "selection": ("24 lowest SHA256 rows per case and depth (2,3), mixed maxima, "
                            "both sides, 4-5 children; plus explicit six-child timing "
                            "and exact eight-child obstruction" if args.mode == "broad"
                            else "single explicit fixture"),
              "rows_total": len(rows), "rows_done": 0,
              "counts": {}, "working_choices": {}, "failures": [], "row_timings": []}
    counts, choices = Counter(), Counter()
    evaluators = {}
    try:
        for index, row in enumerate(rows):
            print(json.dumps({"starting_row": index, "total": len(rows), "row": row}), flush=True)
            key = row["a"], row["u"], row["k"]
            if key not in evaluators:
                evaluators[key] = compiled_evaluator(*key, cache_size=2_000_000, persistent=True)
            before = time.monotonic()
            tested = test_context(row, evaluators[key])
            counts.update(tested["counts"])
            choices.update(tested["working_choices"])
            result["failures"].extend(tested["failures"][:max(0, 30-len(result["failures"]))])
            result.update(rows_done=index+1, counts=dict(counts), working_choices=dict(choices),
                          seconds=time.monotonic()-started)
            result["row_timings"].append({"row": row, "seconds": time.monotonic()-before})
            args.out.parent.mkdir(parents=True, exist_ok=True)
            args.out.write_text(json.dumps(result, indent=2) + "\n")
            print(json.dumps({"done": index+1, "total": len(rows), "seconds": result["seconds"],
                              "rate_rows_per_second": (index+1)/result["seconds"],
                              "counts": dict(counts)}), flush=True)
    finally:
        for evaluate in evaluators.values():
            evaluate.close()
    return 2 if result["failures"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
