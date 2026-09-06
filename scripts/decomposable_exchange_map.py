#!/usr/bin/env python3
"""The exchange map behind the additivity lemma (experiment 0120): for every
interleaved partition (L, U) of an abstract context, which stacked cut of the
recursion dominates its value, and does a fixed rule always pick a dominating cut?

Rules tested (a cut is a run boundary t with the prefix runs 0..t-1 as one part):
  A  cut before the first run holding a U-letter, prefix lower
  A' same cut, prefix upper
  B  cut after the last run holding an L-letter, prefix lower
  B' same cut, prefix upper
  C  cut before the first run holding an L-letter, prefix upper (mirror of A)
  D  cut after the last run holding a U-letter, prefix upper (mirror of B)
For each partition the best interleaved value V (both orientations, all
couplings) is compared with each rule's cut value W (all couplings).  Output:
coverage of each rule (fraction of partitions with W >= V), coverage of their
union, and the partitions no rule covers.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decomposable_recursive_formula import make_F, run_index, child_signature  # noqa: E402
from decomposable_additivity_test import contexts, child  # noqa: E402


def cut_value(F, word, maxima, t, p, k, prefix_lower):
    prefix = frozenset(range(t)); suffix = frozenset(range(t, p))
    best = 0
    for dp in range(1, k - 1):
        c = k - 1 - dp
        if prefix_lower:
            w1, m1 = child_signature(word, maxima, prefix, "lower", dp); w2, m2 = child_signature(word, maxima, suffix, "upper", c)
        else:
            w1, m1 = child_signature(word, maxima, prefix, "upper", c); w2, m2 = child_signature(word, maxima, suffix, "lower", dp)
        v1 = F(w1, m1)
        if v1:
            v2 = F(w2, m2)
            if v2:
                best = max(best, v1 + v2)
    return best


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", required=True)
    parser.add_argument("--s-max", type=int, default=5)
    parser.add_argument("--e-max", type=int, default=2)
    parser.add_argument("--levels", type=int, default=2)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--recursion", choices=("F", "F2"), default="F",
                        help="F2: interval cuts; adds the rules 'block = span of L' and 'block = span of U'")
    parser.add_argument("--cache-size", type=int, default=None)
    args = parser.parse_args()
    a, u, k = (int(x) for x in args.case.split(","))
    import decomposable_recursive_formula as drf
    if args.cache_size:
        drf.CACHE_SIZE = args.cache_size
    F = drf.make_F2(a, u, k) if args.recursion == "F2" else make_F(a, u, k)
    started = time.time()
    rules = ["before first U-run", "after last L-run", "before first L-run", "after last U-run"]
    if args.recursion == "F2":
        rules += ["block = span of L", "block = span of U"]
    sanity_fail = 0
    covered = Counter(); partitions = 0; uncovered = []
    base_contexts = 0
    union_covered = 0
    by_alternations = Counter(); by_alternations_uncovered = Counter()
    for word, maxima in contexts(args.s_max, args.e_max, args.levels, k):
        value = F(word, maxima)
        if value == 0:
            continue
        s_pos = [i for i, w in enumerate(word) if w == "S"]
        runs = run_index(word)
        p = max(r for r in runs if r is not None) + 1
        if p == 1:
            base_contexts += 1          # a single run: dominance is the base threshold, no cut exists
            continue
        for r in range(1, (1 << len(s_pos)) - 1):
            L = frozenset(s_pos[i] for i in range(len(s_pos)) if r >> i & 1)
            U = frozenset(s_pos) - L
            lr = {runs[i] for i in L}; ur = {runs[i] for i in U}
            if not (lr & ur) and (max(lr) < min(ur) or max(ur) < min(lr)):
                continue
            partitions += 1
            # interleaved value
            V = 0
            for dp in range(1, k - 1):
                c = k - 1 - dp
                w1, m1 = child(word, maxima, L, "lower", dp); w2, m2 = child(word, maxima, U, "upper", c)
                v1 = F(w1, m1); v2 = F(w2, m2) if v1 else 0
                if v1 and v2: V = max(V, v1 + v2)
                w1, m1 = child(word, maxima, L, "upper", c); w2, m2 = child(word, maxima, U, "lower", dp)
                v1 = F(w1, m1); v2 = F(w2, m2) if v1 else 0
                if v1 and v2: V = max(V, v1 + v2)
            # alternations of the partition along the S-letters
            seq = ["L" if i in L else "U" for i in s_pos]
            alt = sum(1 for x, y in zip(seq, seq[1:]) if x != y)
            by_alternations[alt] += 1
            # rules
            first_U = min(ur); last_L = max(lr); first_L = min(lr); last_U = max(ur)
            # rule positions; each takes the better of the two orientations
            cuts = {"before first U-run": first_U, "after last L-run": last_L + 1,
                    "before first L-run": first_L, "after last U-run": last_U + 1}
            any_cover = False
            best_any = max((cut_value(F, word, maxima, t, p, k, pl) for t in range(1, p) for pl in (True, False)), default=0)
            if best_any < V:
                sanity_fail += 1
            for name, t in cuts.items():
                t = min(max(t, 1), p - 1)      # clamp into the valid cut range
                if max(cut_value(F, word, maxima, t, p, k, True), cut_value(F, word, maxima, t, p, k, False)) >= V:
                    covered[name] += 1; any_cover = True
            if args.recursion == "F2":
                # interval rules: the block is the span (letters between first and last) of one part
                for name, part in (("block = span of L", L), ("block = span of U", U)):
                    lo, hi = min(part), max(part)
                    block = frozenset(i for i in s_pos if lo <= i <= hi); rest = frozenset(s_pos) - block
                    if not rest:
                        continue
                    W = 0
                    for dp in range(1, k - 1):
                        c = k - 1 - dp
                        for (sb, sr) in (("lower", "upper"), ("upper", "lower")):
                            wb, mb = child(word, maxima, block, sb, dp if sb == "lower" else c); wr, mr = child(word, maxima, rest, sr, c if sr == "upper" else dp)
                            vb = F(wb, mb); vr = F(wr, mr) if vb else 0
                            if vb and vr: W = max(W, vb + vr)
                    if W >= V:
                        covered[name] += 1; any_cover = True
            if any_cover:
                union_covered += 1
            else:
                by_alternations_uncovered[alt] += 1
                if len(uncovered) < 40:
                    uncovered.append({"word": ["S" if w == "S" else f"{w[0]}{'L' if w[1]=='lower' else 'U'}" for w in word],
                                      "maxima": list(maxima), "L": sorted(L), "U": sorted(U), "V": V, "F": value,
                                      "cuts": {f"t={t}{'L' if pl else 'U'}": cut_value(F, word, maxima, t, p, k, pl) for t in range(1, p) for pl in (True, False)}})
    out = {"case": args.case, "recursion": args.recursion, "single_run_contexts_skipped": base_contexts, "partitions": partitions, "additivity_failures": sanity_fail, "coverage": {r: covered[r] for r in rules}, "union_coverage": union_covered,
           "by_alternations": dict(sorted(by_alternations.items())), "uncovered_by_alternations": dict(sorted(by_alternations_uncovered.items())),
           "uncovered_examples": uncovered, "seconds": round(time.time() - started, 1)}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps({k2: v for k2, v in out.items() if k2 != "uncovered_examples"}), file=sys.stderr)


if __name__ == "__main__":
    main()
