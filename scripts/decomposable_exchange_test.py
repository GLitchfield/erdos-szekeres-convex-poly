#!/usr/bin/env python3
"""Test concrete exchange rules for interleaved context partitions.

For a split ``keep | rest``, compare its literal Lean-recursion value with
contiguous blocks of the parent child-position list.  The candidate names make
the allowed exchange precise:

* ``same_size_same_parameters`` preserves cardinality, orientation, and coupling;
* ``any_block_same_parameters`` may change cardinality and location only;
* ``any_block_fixed_coupling`` may also reverse orientation;
* ``any_block_same_orientation`` may instead change the coupling; and
* ``any_interval_cut`` may change all three.

With ``--true-crossing-only``, neither side may itself be an interval block.
Failure records include the best candidate and a fully flexible rescue witness.

This is finite evidence for choosing a Lean exchange statement.  It does not
prove the generic exchange argument.
"""
from __future__ import annotations

import argparse
import itertools
import json
import os
import sys
from pathlib import Path

_LOCAL_SCRIPTS = str(Path(__file__).resolve().parent)
sys.path.insert(0, _LOCAL_SCRIPTS)
if semantic_scripts := os.environ.get("ES_CONTEXT_SCRIPT_DIR"):
    sys.path.insert(0, semantic_scripts)
from decomposable_additivity_test import child, contexts  # noqa: E402
import decomposable_recursive_formula as drf  # noqa: E402
from decomposable_recursive_formula import run_index  # noqa: E402


def split_value(F, word, maxima, keep, orientation, d, k):
    """Value of one oriented split at coupling ``d``."""
    rest = frozenset(i for i, w in enumerate(word) if w == "S") - keep
    c = k - 1 - d
    if orientation == "lower":
        w1, m1 = child(word, maxima, keep, "lower", d)
        w2, m2 = child(word, maxima, rest, "upper", c)
    else:
        w1, m1 = child(word, maxima, keep, "upper", c)
        w2, m2 = child(word, maxima, rest, "lower", d)
    return F(w1, m1) + F(w2, m2)


def contiguous_blocks(positions):
    return [frozenset(positions[i:j])
            for i in range(len(positions))
            for j in range(i + 1, len(positions) + 1)
            if j - i < len(positions)]


def shown_word(word):
    return ["S" if w == "S" else f"{w[0]}{'L' if w[1] == 'lower' else 'U'}"
            for w in word]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", required=True)
    parser.add_argument("--s-max", type=int, default=5)
    parser.add_argument("--e-max", type=int, default=2)
    parser.add_argument("--levels", type=int, default=2)
    parser.add_argument("--max-contexts", type=int, default=0)
    parser.add_argument("--runs", default="2", help="child runs of the contexts to test: 1, 2, 3, ... or 'any' (default 2)")
    parser.add_argument("--true-crossing-only", action="store_true",
                        help="require that neither side of the partition is an interval block")
    parser.add_argument("--all-partitions", action="store_true",
                        help="also test partitions whose kept part or rest is an interior block (sandwiches); "
                             "only partitions that are themselves a prefix/suffix cut are skipped")
    parser.add_argument("--include-unused-levels", action="store_true",
                        help="enumerate maxima levels that have no external letter (literal Lean domain)")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cache-size", type=int, default=100_000)
    args = parser.parse_args()
    a, u, k = map(int, args.case.split(","))
    drf.CACHE_SIZE = args.cache_size
    F = drf.make_F2(a, u, k, include_zero_children=True)

    names = (
        "same_size_same_parameters",
        "any_block_same_parameters",
        "any_block_fixed_coupling",
        "any_block_same_orientation",
        "any_interval_cut",
        # deterministic candidates (a Lean proof needs a specific cut): the hull of the kept
        # part, or of the rest, as the block; same orientation; same or any coupling
        "hull_keep_same_coupling",
        "hull_keep_any_coupling",
        "hull_rest_any_coupling",
        "hulls_any_coupling",
        # boundary cuts: the block is a prefix or a suffix of the child positions (any length);
        # the k=5 runs showed the rescuing cut is usually a short prefix or suffix
        "prefix_suffix_same_parameters",
        "prefix_suffix_same_coupling",
        "prefix_suffix_same_orientation",
        "prefix_suffix_any",
        "end_singleton_same_coupling",
    )
    stats = {"contexts": 0, "splits": 0, "failures": {name: 0 for name in names}}
    examples = {name: [] for name in names}
    context_args = (args.s_max, args.e_max, args.levels, k)
    context_kwargs = {"include_unused_levels": True} if args.include_unused_levels else {}
    try:
        context_iter = contexts(*context_args, **context_kwargs)
    except TypeError as exc:
        parser.error(f"selected context generator does not support --include-unused-levels: {exc}")
    for word, maxima in context_iter:
        child_positions = [i for i, w in enumerate(word) if w == "S"]
        ridx = run_index(word)
        nruns = len({ridx[p] for p in child_positions})
        if args.runs != "any" and nruns != int(args.runs):
            continue
        if args.max_contexts and stats["contexts"] >= args.max_contexts:
            break
        stats["contexts"] += 1
        blocks = contiguous_blocks(child_positions)
        cut_table = {
            (block, orientation, d): split_value(F, word, maxima, block, orientation, d, k)
            for block in blocks for orientation in ("lower", "upper")
            for d in range(1, k - 1)
        }
        cut_table_blocks = set(blocks)
        n_pos = len(child_positions)
        boundary_blocks = [frozenset(child_positions[:j]) for j in range(1, n_pos)] + [frozenset(child_positions[j:]) for j in range(1, n_pos)]
        end_blocks = [frozenset(child_positions[:1]), frozenset(child_positions[-1:])]
        boundary_set = set(boundary_blocks)
        for mask in range(1, (1 << len(child_positions)) - 1):
            keep = frozenset(p for j, p in enumerate(child_positions) if mask >> j & 1)
            rest = frozenset(child_positions) - keep
            if args.all_partitions:
                if keep in boundary_set or rest in boundary_set:
                    continue  # the partition is a prefix/suffix cut itself
            else:
                if keep in blocks:
                    continue
                if args.true_crossing_only and rest in blocks:
                    continue
            for orientation, d in itertools.product(("lower", "upper"), range(1, k - 1)):
                stats["splits"] += 1
                target = split_value(F, word, maxima, keep, orientation, d, k)
                candidates = {}
                candidates["same_size_same_parameters"] = [
                    (cut_table[block, orientation, d], block,
                     orientation, d)
                    for block in blocks if len(block) == len(keep)]
                candidates["any_block_same_parameters"] = [
                    (cut_table[block, orientation, d], block,
                     orientation, d)
                    for block in blocks]
                candidates["any_block_fixed_coupling"] = [
                    (cut_table[block, orientation2, d], block,
                     orientation2, d)
                    for block in blocks for orientation2 in ("lower", "upper")]
                candidates["any_block_same_orientation"] = [
                    (cut_table[block, orientation, d2], block,
                     orientation, d2)
                    for block in blocks for d2 in range(1, k - 1)]
                candidates["any_interval_cut"] = [
                    (cut_table[block, orientation2, d2], block,
                     orientation2, d2)
                    for block in blocks for orientation2 in ("lower", "upper")
                    for d2 in range(1, k - 1)]
                hull_keep = frozenset(p for p in child_positions if min(keep) <= p <= max(keep))
                hull_rest = frozenset(p for p in child_positions if min(rest) <= p <= max(rest))
                hulls = [h for h in (hull_keep, hull_rest) if h in cut_table_blocks]
                candidates["hull_keep_same_coupling"] = [
                    (cut_table[hull_keep, orientation, d], hull_keep, orientation, d)] if hull_keep in cut_table_blocks else [(-1, hull_keep, orientation, d)]
                candidates["hull_keep_any_coupling"] = [
                    (cut_table[hull_keep, orientation, d2], hull_keep, orientation, d2)
                    for d2 in range(1, k - 1)] if hull_keep in cut_table_blocks else [(-1, hull_keep, orientation, d)]
                candidates["hull_rest_any_coupling"] = [
                    (cut_table[hull_rest, orientation, d2], hull_rest, orientation, d2)
                    for d2 in range(1, k - 1)] if hull_rest in cut_table_blocks else [(-1, hull_rest, orientation, d)]
                candidates["prefix_suffix_same_parameters"] = [
                    (cut_table[b, orientation, d], b, orientation, d) for b in boundary_blocks]
                candidates["prefix_suffix_same_coupling"] = [
                    (cut_table[b, o2, d], b, o2, d) for b in boundary_blocks for o2 in ("lower", "upper")]
                candidates["prefix_suffix_same_orientation"] = [
                    (cut_table[b, orientation, d2], b, orientation, d2) for b in boundary_blocks for d2 in range(1, k - 1)]
                candidates["prefix_suffix_any"] = [
                    (cut_table[b, o2, d2], b, o2, d2) for b in boundary_blocks for o2 in ("lower", "upper") for d2 in range(1, k - 1)]
                candidates["end_singleton_same_coupling"] = [
                    (cut_table[b, o2, d], b, o2, d) for b in end_blocks for o2 in ("lower", "upper")]
                candidates["hulls_any_coupling"] = [
                    (cut_table[h, o2, d2], h, o2, d2)
                    for h in hulls for o2 in ("lower", "upper") for d2 in range(1, k - 1)] or [(-1, hull_keep, orientation, d)]
                for name, values in candidates.items():
                    best = max(values, key=lambda x: x[0])
                    if best[0] < target:
                        stats["failures"][name] += 1
                        if len(examples[name]) < 12:
                            rescue = max(candidates["any_interval_cut"], key=lambda x: x[0])
                            examples[name].append({
                                "word": shown_word(word), "maxima": list(maxima),
                                "parent_bound": F(word, maxima), "keep": sorted(keep),
                                "orientation": orientation, "d": d, "target": target,
                                "best": best[0], "best_block": sorted(best[1]),
                                "best_orientation": best[2], "best_d": best[3],
                                "rescue": rescue[0], "rescue_block": sorted(rescue[1]),
                                "rescue_orientation": rescue[2], "rescue_d": rescue[3],
                            })
    result = {"case": args.case, "parameters": vars(args) | {"output": str(args.output)},
              "stats": stats, "examples": examples,
              "scope": (f"{args.runs} child run(s) with literal unused-level semantics"
                        if args.include_unused_levels else f"{args.runs} child run(s) with occupied levels"),
              "interpretation": "finite evidence only; splits count oriented coupling cases"}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(stats), file=sys.stderr)


if __name__ == "__main__":
    main()
