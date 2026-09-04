#!/usr/bin/env python3
"""Enumerate the abstract decomposable class (`IsDecomposableOn` in
Decomposable.lean) on n ordered vertices, exactly.

A coloring on an index set S is decomposable if S is a singleton or S is the
disjoint union of a lower and an upper part, both decomposable, such that every
triple meeting both parts is a left turn exactly when its middle vertex is in
the lower part (`HasDeepBelowSplit`).  Parts may interleave in sweep order.

Colorings are bitmasks over the increasing triples of range(n) in
lexicographic order (bit set = left turn).  The class on n vertices is built
recursively from the classes on the parts, transported through the order
isomorphisms, and deduplicated.  Per coloring the script records the longest
cap and cup, the strong sets present, and per-vertex attachment profiles
(longest cap/cup ending at or starting from each vertex), which Workstream B's
plan uses to search for a profile-carrying induction hypothesis.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))


def triple_index(n):
    return {t: i for i, t in enumerate(itertools.combinations(range(n), 3))}


def enumerate_class(max_n, progress=True):
    """Return {m: set of bitmasks} for 1 <= m <= max_n."""
    classes = {1: {0}, 2: {0}}
    tindex = {m: triple_index(m) for m in range(1, max_n + 1)}
    for m in range(3, max_n + 1):
        started = time.time()
        found = set()
        idx = tindex[m]
        vertices = list(range(m))
        # ordered bipartitions (lower, upper), both nonempty
        for lower_bits in range(1, (1 << m) - 1):
            lower = [v for v in vertices if lower_bits >> v & 1]
            upper = [v for v in vertices if not lower_bits >> v & 1]
            # crossing triples: colored by the side of the middle vertex
            cross_left = 0
            for (i, j, k), pos in idx.items():
                inl = (lower_bits >> i & 1) + (lower_bits >> j & 1) + (lower_bits >> k & 1)
                if inl in (1, 2) and lower_bits >> j & 1:
                    cross_left |= 1 << pos
            # transport tables for the two parts
            def transport(part):
                table = []
                for (a, b, c) in itertools.combinations(range(len(part)), 3):
                    table.append(idx[(part[a], part[b], part[c])])
                return table
            tl, tu = transport(lower), transport(upper)
            def lift(mask, table):
                out = 0
                p = 0
                while mask:
                    if mask & 1:
                        out |= 1 << table[p]
                    mask >>= 1
                    p += 1
                return out
            lower_lifted = [lift(x, tl) for x in classes[len(lower)]]
            upper_lifted = [lift(x, tu) for x in classes[len(upper)]]
            for xl in lower_lifted:
                base = cross_left | xl
                for xu in upper_lifted:
                    found.add(base | xu)
        classes[m] = found
        if progress:
            print(f"n={m}: {len(found)} decomposable colorings ({time.time()-started:.1f}s)", file=sys.stderr, flush=True)
    return classes, tindex


def coloring_dict(mask, n, idx):
    return {t: bool(mask >> p & 1) for t, p in idx.items()}


def one_change(chi, n):
    for i, j, k, l in itertools.combinations(range(n), 4):
        v = [chi[(i, j, k)], chi[(i, j, l)], chi[(i, k, l)], chi[(j, k, l)]]
        if sum(a != b for a, b in zip(v, v[1:])) > 1:
            return False
    return True


def chain_profiles(chi, n, left):
    """Longest chain (all consecutive triples with color ``left``) ending at
    each vertex and starting at each vertex; chains of one or two vertices
    count as length 1 or 2."""
    # end[(i, j)] = longest chain ending with edge i<j ; start[(i, j)] = starting with edge
    end = {}
    for j in range(n):
        for i in range(j):
            best = 2
            for h in range(i):
                if chi[(h, i, j)] == left:
                    best = max(best, end[(h, i)] + 1)
            end[(i, j)] = best
    start = {}
    for i in range(n - 1, -1, -1):
        for j in range(i + 1, n):
            best = 2
            for k in range(j + 1, n):
                if chi[(i, j, k)] == left:
                    best = max(best, start[(j, k)] + 1)
            start[(i, j)] = best
    ending = [max([1] + [end[(i, v)] for i in range(v)]) for v in range(n)]
    starting = [max([1] + [start[(v, k)] for k in range(v + 1, n)]) for v in range(n)]
    return ending, starting, max(ending)


def strong_sizes(chi, n):
    """Sizes k for which a strong k-set exists (all quads strong)."""
    def strong(vs):
        for i, j, k, l in itertools.combinations(vs, 4):
            if chi[(i, j, k)] != chi[(i, j, l)] or chi[(i, k, l)] != chi[(j, k, l)]:
                return False
        return True
    largest = 3 if n >= 3 else n
    for k in range(4, n + 1):
        if any(strong(vs) for vs in itertools.combinations(range(n), k)):
            largest = k
        else:
            break
    return largest


def threshold(a, u, k):
    """decomposableThreshold a u k from Decomposable.lean."""
    from math import comb
    if a == 1 or u == 1:
        return 0
    if a + u <= k + 3:
        return comb(a + u - 4, a - 2)
    return sum(comb(k - 2, j) for j in range(k - a, u - 1))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=8)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--validate", action="store_true", help="cross-check with the census checker for n <= 6")
    parser.add_argument("--max-k", type=int, default=7)
    args = parser.parse_args()
    classes, tindex = enumerate_class(args.max_n)
    summary = {"counts": {m: len(c) for m, c in classes.items()}, "validation": {}, "per_n": {}}
    if args.validate:
        import census_order_type_decomposability as census
        for m in range(3, min(6, args.max_n) + 1):
            idx = tindex[m]
            # every enumerated coloring is accepted by the checker
            accepted = 0
            for mask in classes[m]:
                col = census.Coloring(m, coloring_dict(mask, m, idx))
                if col.decomposable((1 << m) - 1, {}):
                    accepted += 1
            # completeness against all one-change colorings (the class lies inside them)
            complete = None
            if m <= 6:
                total = 1 << len(idx)
                checker_yes = set()
                onechange = 0
                for mask in range(total):
                    chi = coloring_dict(mask, m, idx)
                    if not one_change(chi, m):
                        continue
                    onechange += 1
                    if census.Coloring(m, chi).decomposable((1 << m) - 1, {}):
                        checker_yes.add(mask)
                complete = {"one_change_colorings": onechange, "checker_decomposable": len(checker_yes),
                            "sets_equal": checker_yes == classes[m]}
            summary["validation"][m] = {"enumerated": len(classes[m]), "accepted_by_checker": accepted, "completeness": complete}
            print(f"validate n={m}: {summary['validation'][m]}", file=sys.stderr, flush=True)
    # per-coloring statistics, streamed; full records kept only for extremal
    # colorings (those avoiding an a-cap, u-cup and strong k-set at the
    # largest n where that happens is decided after the pass, so witnesses are
    # kept per (a,u,k) up to a cap)
    keys = [(a, u, k) for a in range(3, args.max_k + 1) for u in range(3, args.max_k + 1)
            for k in range(max(a, u, 4), args.max_k + 1)]
    witness_cap = 3000
    for m in range(3, args.max_n + 1):
        idx = tindex[m]
        avoid = {key: 0 for key in keys}
        witnesses = {key: [] for key in keys}
        profile_hist = {}
        count = 0
        for mask in classes[m]:
            chi = coloring_dict(mask, m, idx)
            cup_end, cup_start, max_cup = chain_profiles(chi, m, True)
            cap_end, cap_start, max_cap = chain_profiles(chi, m, False)
            largest = strong_sizes(chi, m)
            count += 1
            profile = [[cap_end[v], cap_start[v], cup_end[v], cup_start[v]] for v in range(m)]
            for key in keys:
                a, u, k = key
                if max_cap < a and max_cup < u and largest < k:
                    avoid[key] += 1
                    if len(witnesses[key]) < witness_cap:
                        witnesses[key].append({"mask": mask, "profile": profile})
            sig = (max_cap, max_cup, largest)
            profile_hist[sig] = profile_hist.get(sig, 0) + 1
        avoid_named = {f"{a},{u},{k}": c for (a, u, k), c in avoid.items() if c}
        summary["per_n"][m] = {"colorings": count, "avoiding_counts": avoid_named,
                               "cap_cup_strong_histogram": {f"{a},{u},{k}": c for (a, u, k), c in sorted(profile_hist.items())}}
        out = args.output.with_name(args.output.stem + f"-witnesses-n{m}.json")
        out.write_text(json.dumps({f"{a},{u},{k}": w for (a, u, k), w in witnesses.items() if w}, separators=(",", ":")) + "\n")
        summary["per_n"][m]["witness_file"] = str(out)
        print(f"stats n={m}: {count} colorings; avoiding table entries {len(avoid_named)}", file=sys.stderr, flush=True)
    # threshold check: largest n with an (a,u,k)-avoiding decomposable coloring vs decomposableThreshold
    table = {}
    for a in range(3, args.max_k + 1):
        for u in range(3, args.max_k + 1):
            for k in range(max(a, u, 4), args.max_k + 1):
                key = f"{a},{u},{k}"
                largest_n = max((m for m in range(3, args.max_n + 1) if key in summary["per_n"][m]["avoiding_counts"]), default=None)
                table[key] = {"largest_avoiding_n_enumerated": largest_n, "decomposableThreshold": threshold(a, u, k),
                              "extremal_count": summary["per_n"][largest_n]["avoiding_counts"][key] if largest_n else 0,
                              "bound_holds_within_enumeration": largest_n is None or largest_n <= threshold(a, u, k)}
    summary["threshold_table"] = table
    args.output.write_text(json.dumps(summary, indent=1) + "\n")
    print(f"wrote {args.output}", file=sys.stderr)


if __name__ == "__main__":
    main()
