#!/usr/bin/env python3
"""Workstream B, step 2, second level: what a subtree at any depth sees of the
rest of the coloring.

For every decomposable coloring T on n <= --max-n vertices, every subtree S of
every decomposition tree of T (S reached from [n] by repeated deep-below
splits with both parts decomposable), and every cup, cap or strong set Q of S
with at least three vertices, the exact external extension numbers are
computed by brute force over the subsets of T:

  ext_cup(Q)    = max |X|, X in T \\ S, Q ∪ X a cup of T        (Q a cup)
  ext_cap(Q)    = max |X|, X in T \\ S, Q ∪ X a cap of T        (Q a cap)
  ext_strong(Q) = max |X|, X in T \\ S, Q ∪ X a strong set of T

The constraints that T's avoidance of an a-cap, a u-cup and a strong k-set
imposes on S are exactly |Q| + ext(Q) <= a-1, u-1, k-1.  The script tests,
for each (T, S), the structural claims behind a positional induction state:

  H1  ext_cup(Q) and ext_strong(Q) of a cup Q depend only on (first(Q), last(Q))
      (and symmetrically for caps);
  H2  ext_cup(Q) = [an above-vertex lies left of first(Q)] + [one lies right of
      last(Q)]  (above-vertices: external x with S in the lower part of their
      separating split; read off the coloring), i.e. one gap pair suffices;
  H3  ext_strong(Q) = D + [first(Q) >= g1] + [last(Q) < g2] for a single triple
      (D, g1, g2): the one-level positional form found at the top level
      (experiment 0116).  Where H3 fails, the table is recorded: that is the
      shape of the "stacking across levels" the induction state must carry;
  H4  a strong set of S that is neither a cup nor a cap of S has
      ext_strong = 0 (strong sets cannot chain across a level except through
      cups and caps).
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from enumerate_decomposable_colorings import enumerate_class, coloring_dict  # noqa: E402


def classify_subsets(chi, n):
    """For every subset (bitmask) of [n]: is it a cup, a cap, a strong set."""
    cup = {}
    cap = {}
    strong = {}
    for mask in range(1, 1 << n):
        vs = [v for v in range(n) if mask >> v & 1]
        is_cup = is_cap = is_strong = True
        if len(vs) >= 3:
            for t in itertools.combinations(vs, 3):
                if chi[t]:
                    is_cap = False
                else:
                    is_cup = False
                if not is_cup and not is_cap:
                    break
        if len(vs) >= 4:
            for i, j, k, l in itertools.combinations(vs, 4):
                if chi[(i, j, k)] != chi[(i, j, l)] or chi[(i, k, l)] != chi[(j, k, l)]:
                    is_strong = False
                    break
        cup[mask] = is_cup
        cap[mask] = is_cap
        strong[mask] = is_strong
    return cup, cap, strong


def restrict_mask(chi, vertices, class_masks, tindex):
    """Mask of chi restricted to ``vertices`` (in the class's indexing) and membership."""
    m = len(vertices)
    idx = tindex[m]
    mask = 0
    for (a, b, c), pos in idx.items():
        if chi[(vertices[a], vertices[b], vertices[c])]:
            mask |= 1 << pos
    return mask, (m <= 2 or mask in class_masks[m])


def deep_below_split_ok(chi, vertices, lower_set):
    for i, j, k in itertools.combinations(vertices, 3):
        inl = (i in lower_set) + (j in lower_set) + (k in lower_set)
        if 0 < inl < 3 and chi[(i, j, k)] != (j in lower_set):
            return False
    return True


def subtrees(chi, n, class_masks, tindex):
    """All vertex sets that are nodes of some decomposition tree of chi, with the
    set of splits seen (parent -> (lower, upper))."""
    seen = {}
    stack = [tuple(range(n))]
    seen[tuple(range(n))] = None
    while stack:
        vs = stack.pop()
        if len(vs) == 1:
            continue
        for lower_bits in range(1, (1 << len(vs)) - 1):
            lower = tuple(v for i, v in enumerate(vs) if lower_bits >> i & 1)
            upper = tuple(v for i, v in enumerate(vs) if not lower_bits >> i & 1)
            if not deep_below_split_ok(chi, vs, set(lower)):
                continue
            _, okl = restrict_mask(chi, lower, class_masks, tindex)
            _, oku = restrict_mask(chi, upper, class_masks, tindex)
            if not (okl and oku):
                continue
            for part, side in ((lower, "lower"), (upper, "upper")):
                if part not in seen:
                    seen[part] = (vs, side)
                    stack.append(part)
    return seen


def path_levels(seen, S):
    """Ancestor levels of S along one decomposition path: (side of the child, sibling
    vertices) from S's parent up to the root."""
    levels = []
    node = S
    while seen[node] is not None:
        parent, side = seen[node]
        sibling = tuple(v for v in parent if v not in node)
        levels.append((side, sibling))
        node = parent
    return levels


def chain_max(chi, vertices, left):
    """Longest chain of consecutive turns of color ``left`` inside ``vertices`` (1 or 2 for tiny sets)."""
    vs = list(vertices)
    if len(vs) <= 2:
        return len(vs)
    best = 2
    end = {}
    for j in range(len(vs)):
        for i in range(j):
            b = 2
            for h in range(i):
                if chi[(vs[h], vs[i], vs[j])] == left:
                    b = max(b, end[(h, i)] + 1)
            end[(i, j)] = b
            best = max(best, b)
    return best


def predicted_extensions(chi, levels, first, last, cup: bool):
    """Level-wise rule.  For a cup Q with global first/last vertices: at every ancestor
    level where the child is the lower part, one vertex of the upper sibling may be
    added on each side, strictly beyond the current end; the chain extension is the
    largest number of levels usable on the left (a longest chain of levels with
    decreasing positions, so a level may be skipped) plus the same on the right; the
    strong extension is the best of "extend through the levels below N, then join the
    longest cap of the upper sibling at N" over levels N where the child is lower, or
    the pure chain extension.  Caps: mirror image."""
    grow_side = "lower" if cup else "upper"
    # dynamic programme over levels: best count for each possible current end position
    left_states = {first: 0}
    right_states = {last: 0}
    best_strong = 0
    for side, sibling in levels:
        if side != grow_side:
            continue
        below_count = max(left_states.values()) + max(right_states.values())
        best_strong = max(best_strong, below_count + chain_max(chi, sibling, left=not cup))
        new_left = dict(left_states)
        for end, count in left_states.items():
            for x in sibling:
                if x < end and count + 1 > new_left.get(x, -1):
                    new_left[x] = count + 1
        new_right = dict(right_states)
        for end, count in right_states.items():
            for y in sibling:
                if y > end and count + 1 > new_right.get(y, -1):
                    new_right[y] = count + 1
        left_states, right_states = new_left, new_right
    count = max(left_states.values()) + max(right_states.values())
    return count, max(best_strong, count)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=7)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--limit-per-n", type=int, default=0, help="sample this many colorings per n (0 = all)")
    args = parser.parse_args()
    started = time.time()
    class_masks, tindex = enumerate_class(args.max_n, progress=False)
    stats = {"colorings": 0, "subtrees": 0, "queries": 0,
             "H1_cup_position_fail": 0, "H1_cap_position_fail": 0,
             "H2_cup_gap_fail": 0, "H2_cap_gap_fail": 0,
             "H3_cup_single_level_fail": 0, "H3_cap_single_level_fail": 0,
             "H4_mixed_strong_ext_nonzero": 0,
             "ext_cup_values": Counter(), "ext_strong_cup_values": Counter()}
    failures = {"H1": [], "H2": [], "H3": [], "H4": []}
    h3_tables = Counter()   # shapes of ext_strong tables that are not single-level
    for n in range(3, args.max_n + 1):
        idx = tindex[n]
        masks = sorted(class_masks[n])
        if args.limit_per_n:
            masks = masks[:: max(1, len(masks) // args.limit_per_n)][: args.limit_per_n]
        for mask in masks:
            chi = coloring_dict(mask, n, idx)
            cup, cap, strong = classify_subsets(chi, n)
            full = (1 << n) - 1
            stats["colorings"] += 1
            seen = subtrees(chi, n, class_masks, tindex)
            for S in seen:
                if len(S) < 3 or len(S) == n:
                    continue
                levels = path_levels(seen, S)
                stats["subtrees"] += 1
                Smask = sum(1 << v for v in S)
                ext_mask = full & ~Smask
                ext_subsets = [x for x in range(1 << n) if x & ~ext_mask == 0]
                pos = {v: i for i, v in enumerate(S)}          # S's own sweep order
                cup_ext = {}
                cup_strong = {}
                cap_ext = {}
                cap_strong = {}
                for Q in range(1, 1 << n):
                    if Q & ~Smask or bin(Q).count("1") < 3:
                        continue
                    vs = [v for v in range(n) if Q >> v & 1]
                    key = (pos[vs[0]], pos[vs[-1]])
                    stats["queries"] += 1
                    if cup[Q] or cap[Q]:
                        is_cup = bool(cup[Q])
                        chain = cup if is_cup else cap
                        e = max((bin(X).count("1") for X in ext_subsets if chain[Q | X]), default=0)
                        es = max((bin(X).count("1") for X in ext_subsets if strong[Q | X]), default=0)
                        (cup_ext if is_cup else cap_ext).setdefault(key, set()).add(e)
                        (cup_strong if is_cup else cap_strong).setdefault(key, set()).add(es)
                        if is_cup:
                            stats["ext_cup_values"][e] += 1
                            stats["ext_strong_cup_values"][es] += 1
                        pe, ps = predicted_extensions(chi, levels, vs[0], vs[-1], is_cup)
                        kind = "cup" if is_cup else "cap"
                        if pe != e:
                            stats[f"H2_{kind}_gap_fail"] += 1
                            if len(failures["H2"]) < 20:
                                failures["H2"].append({"n": n, "mask": mask, "S": S, "kind": kind, "Q": vs, "ext": e, "predicted": pe, "levels": levels})
                        if ps != es:
                            stats[f"H3_{kind}_single_level_fail"] += 1
                            if len(failures["H3"]) < 30:
                                failures["H3"].append({"n": n, "mask": mask, "S": S, "kind": kind, "Q": vs, "ext_strong": es, "predicted": ps, "levels": levels})
                    elif strong[Q]:
                        es = max((bin(X).count("1") for X in ext_subsets if strong[Q | X]), default=0)
                        if es:
                            stats["H4_mixed_strong_ext_nonzero"] += 1
                            if len(failures["H4"]) < 20:
                                failures["H4"].append({"n": n, "mask": mask, "S": S, "Q": vs, "ext_strong": es})
                # H1: position-determined
                for name, table in (("cup", cup_ext), ("cup", cup_strong), ("cap", cap_ext), ("cap", cap_strong)):
                    if any(len(v) > 1 for v in table.values()):
                        stats[f"H1_{name}_position_fail"] += 1
                        if len(failures["H1"]) < 20:
                            failures["H1"].append({"n": n, "mask": mask, "S": S, "kind": name,
                                                   "table": {str(k): sorted(v) for k, v in table.items() if len(v) > 1}})
        print(json.dumps({"n": n, "colorings": stats["colorings"], "subtrees": stats["subtrees"],
                          **{k: v for k, v in stats.items() if k.startswith("H")},
                          "seconds": round(time.time() - started, 1)}), file=sys.stderr, flush=True)
    stats["ext_cup_values"] = dict(stats["ext_cup_values"])
    stats["ext_strong_cup_values"] = dict(stats["ext_strong_cup_values"])
    out = {"max_n": args.max_n, "stats": stats, "failures": failures,
           "H3_table_shapes": [{"size": s, "table": [[list(k), v] for k, v in shape], "count": c}
                               for (s, shape), c in h3_tables.most_common(40)],
           "seconds": round(time.time() - started, 1)}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main()
