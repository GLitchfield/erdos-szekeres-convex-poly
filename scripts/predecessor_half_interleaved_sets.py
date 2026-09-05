#!/usr/bin/env python3
"""Workstream E falsifier, second form: Horton-type (interleaved deep-below)
heptagon-free sets, tested abstractly in the decomposable class.

A Horton-type set is a lower part A and an upper part B whose x-orders
interleave, with B so far above A that every line through two points of one
part misses the other.  Its sweep coloring is then determined by the colorings
of A and B and the interleaving pattern: a mixed triple turns left exactly
when its middle vertex lies in A.  That is `HasDeepBelowSplit`, so the union
of two decomposable colorings is a decomposable coloring, and every
decomposable coloring is sweep-realizable (`IsDecomposable.isSweepRealizable`,
DecomposableRealization.lean).  The test therefore runs on colorings, with no
coordinates: parts are the Erdős–Szekeres sets P(a,u) (no a-cap, no u-cup; a
deep-below stack, hence decomposable), patterns are the canonical ones and
random ones, and a union is kept when it has no strong 7-set (or is pruned by
SAT to a strong-7-free subset of at least --min-size vertices).  For each kept
coloring the half search asks CaDiCaL for a ceil(n/2)-subset meeting no strong
6-set; a coloring without one is a realizable counterexample to the
predecessor-half conjecture at k = 7 and is written out at once.
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import baek_balko_constructions as bb  # noqa: E402
from predecessor_half_k7_cegar import free_subsets, max_free_size, sinz_at_least, make_solver  # noqa: E402


def es_coloring(a: int, u: int):
    """Triple coloring (True = left) of P(a,u) in x-order."""
    pts = sorted(bb.es_set(a, u), key=lambda p: p[0])
    n = len(pts)
    color = {}
    for i, j, k in itertools.combinations(range(n), 3):
        color[(i, j, k)] = bb.orient(pts[i], pts[j], pts[k]) > 0
    return n, color


def union(parts, pattern):
    """Deep-below union of colorings ``parts`` = [(n_A, color_A), (n_B, color_B), ...]
    ordered from lowest to highest; ``pattern`` lists the part index of each
    vertex in sweep order.  Mixed triples: left iff the middle vertex's part is
    lower than the part of ... (two-part rule generalized: the middle vertex is
    in the lower of the parts present)."""
    n = len(pattern)
    local = {}
    counters = [0] * len(parts)
    for v, part in enumerate(pattern):
        local[v] = (part, counters[part])
        counters[part] += 1
    assert counters == [p[0] for p in parts]
    color = {}
    for i, j, k in itertools.combinations(range(n), 3):
        pi, pj, pk = local[i][0], local[j][0], local[k][0]
        if pi == pj == pk:
            color[(i, j, k)] = parts[pi][1][(local[i][1], local[j][1], local[k][1])]
        elif pi == pk != pj:
            # endpoints in one part, middle in another: left iff middle is lower
            color[(i, j, k)] = pj < pi
        elif pi == pj != pk:
            # (a, a', b): b far above -> left turn; b far below -> right turn
            color[(i, j, k)] = pk > pi
        elif pj == pk != pi:
            # (b, a, a') with b far above -> left; far below -> right
            color[(i, j, k)] = pi > pj
        else:
            # three different parts: the middle vertex decides against the highest endpoint
            # (lower middle -> left); consistent with nested two-part unions
            color[(i, j, k)] = pj < max(pi, pk)
    return n, color


def one_change_ok(n, color):
    for i, j, k, l in itertools.combinations(range(n), 4):
        v = [color[(i, j, k)], color[(i, j, l)], color[(i, k, l)], color[(j, k, l)]]
        if sum(x != y for x, y in zip(v, v[1:])) > 1:
            return False
    return True


def strong_sets_by_size(n, color, max_size):
    """Strong sets of each size 4..max_size, built level by level (every subset
    of a strong set is strong)."""
    def quad_ok(i, j, k, l):
        return color[(i, j, k)] == color[(i, j, l)] and color[(i, k, l)] == color[(j, k, l)]
    levels = {4: [q for q in itertools.combinations(range(n), 4) if quad_ok(*q)]}
    quads = set(levels[4])
    for size in range(5, max_size + 1):
        new = []
        for s in levels[size - 1]:
            for v in range(s[-1] + 1, n):
                if all(tuple(sorted(c + (v,))) in quads for c in itertools.combinations(s, 3)):
                    new.append(s + (v,))
        levels[size] = new
        if not new:
            break
    return levels


def max_strong_free_subset(n, strong_sets, lo, hi, backend, cadical, time_limit):
    """Largest subset meeting no strong set of the given size, size in [lo, hi]."""
    for target in range(hi, lo - 1, -1):
        card, next_var = sinz_at_least(n, target, n + 1)
        solver = make_solver(backend, cadical, next_var - 1)
        for s in strong_sets:
            solver.add_clause([-(v + 1) for v in s])
        for c in card:
            solver.add_clause(c)
        sat, model = solver.solve()
        if sat:
            return sorted(v - 1 for v in model if 0 < v <= n)
    return None


def restrict(n, color, subset):
    index = {v: i for i, v in enumerate(subset)}
    return len(subset), {(index[i], index[j], index[k]): color[(i, j, k)]
                         for i, j, k in itertools.combinations(subset, 3)}


def patterns_for(sizes, rng, random_count):
    total = sum(sizes)
    yield "stacked", [p for p, m in enumerate(sizes) for _ in range(m)]
    yield "stacked-reversed", [p for p, m in reversed(list(enumerate(sizes))) for _ in range(m)]
    alt = []
    remaining = list(sizes)
    while sum(remaining):
        for p in range(len(sizes)):
            if remaining[p]:
                alt.append(p); remaining[p] -= 1
    yield "alternating", alt
    for index in range(random_count):
        pat = [p for p, m in enumerate(sizes) for _ in range(m)]
        rng.shuffle(pat)
        yield f"random#{index}", pat


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=7)
    parser.add_argument("--pairs", default="6,4|4,6;5,5|4,5;5,5|5,4;7,4|4,5;4,7|5,4;7,4|3,6;5,5|3,6;6,4|4,7;5,5|5,5;6,4|5,4|4,5",
                        help="';'-separated unions, each '|'-separated list of a,u parameters from lowest to highest part")
    parser.add_argument("--random-patterns", type=int, default=30)
    parser.add_argument("--min-size", type=int, default=25)
    parser.add_argument("--seed", type=int, default=20260905)
    parser.add_argument("--backend", choices=("auto", "pysat", "cadical"), default="auto")
    parser.add_argument("--cadical", type=Path, default=None)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--counterexample-dir", type=Path, required=True)
    args = parser.parse_args()
    k = args.k
    rng = random.Random(args.seed)
    records = []
    counterexamples = 0
    tested = 0
    started = time.time()
    for spec in args.pairs.split(";"):
        parts = []
        for au in spec.split("|"):
            a, u = (int(x) for x in au.split(","))
            parts.append((a, u, es_coloring(a, u)))
        sizes = [p[2][0] for p in parts]
        name = "U(" + ",".join(f"P({a},{u})" for a, u, _ in parts) + ")"
        for pattern_name, pattern in patterns_for(sizes, rng, args.random_patterns):
            t0 = time.time()
            n, color = union([p[2] for p in parts], pattern)
            rec = {"union": name, "pattern": pattern_name, "size": n, "one_change": one_change_ok(n, color)}
            levels = strong_sets_by_size(n, color, k)
            rec["strong_counts"] = {str(s): len(v) for s, v in levels.items()}
            if levels.get(k):
                subset = max_strong_free_subset(n, levels[k], args.min_size, min(n, 2 ** (k - 2)) if n > 2 ** (k - 2) else n - 1,
                                                args.backend, args.cadical, None)
                if subset is None:
                    rec["pruned"] = None
                    rec["seconds"] = round(time.time() - t0, 1)
                    records.append(rec)
                    print(json.dumps(rec), file=sys.stderr, flush=True)
                    continue
                n, color = restrict(n, color, subset)
                levels = strong_sets_by_size(n, color, k)
                assert not levels.get(k)
                rec["pruned"] = n
            strong6 = levels.get(6, [])
            target = (n + 1) // 2
            halves = free_subsets(n, strong6, target, 1, args.backend, args.cadical)
            tested += 1
            rec["tested_size"] = n
            rec["strong_six_sets"] = len(strong6)
            if halves:
                rec["half"] = {"found": True, "size": len(halves[0]),
                               "max_strong_six_free": max_free_size(n, strong6, target, args.backend, args.cadical)}
            else:
                counterexamples += 1
                args.counterexample_dir.mkdir(parents=True, exist_ok=True)
                path = args.counterexample_dir / f"k{k}-interleaved-{counterexamples}.json"
                path.write_text(json.dumps({"union": name, "pattern": pattern, "size": n,
                                            "left_turn_triples": sorted(t for t, v in color.items() if v),
                                            "strong_six_sets": len(strong6),
                                            "realizability": "decomposable, hence realizable (IsDecomposable.isSweepRealizable)"}, indent=1))
                rec["half"] = {"found": False, "path": str(path)}
                print(f"ALERT: no strong-6-free half in {name} pattern {pattern_name}: {path}", file=sys.stderr, flush=True)
            rec["seconds"] = round(time.time() - t0, 1)
            records.append(rec)
            print(json.dumps(rec), file=sys.stderr, flush=True)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps({"k": k, "seed": args.seed, "min_size": args.min_size, "tested": tested,
                                               "counterexamples": counterexamples, "records": records}, indent=1) + "\n")
    print(json.dumps({"unions": len(records), "tested": tested, "counterexamples": counterexamples,
                      "seconds": round(time.time() - started, 1)}), file=sys.stderr)
    return 2 if counterexamples else 0


if __name__ == "__main__":
    sys.exit(main())
