#!/usr/bin/env python3
"""Workstream E falsifier, second and fourth forms: structured k-gon-free sets
that are not blow-ups, and flip walks seeded from them.

Seeds are Horton sets (several vertical scales, hence several order types),
double chains, and random integer sets.  None of these is k-gon-free as built
(the 32-point Horton set contains a convex 14-gon, a 2x16 double chain a convex
16-gon), so each seed is pruned to a maximum k-gon-free subset by SAT
(polygons enumerated once by the chain enumerator of experiment 0111, then a
descending search on the subset size).  Every pruned set with at least
--min-size points is a valid test of the predecessor-half conjecture at k
regardless of how it was built: the half search of experiment 0108 asks
CaDiCaL for a (k-1)-gon-free subset of at least half its points, and each
witness is re-verified by the independent cup/cap dynamic programme.  A set
with no such half is a counterexample and is written to --counterexample-dir
at once.  Finally a flip walk (experiment 0113) starts from each pruned set
and tests every new k-gon-free order type it reaches.
"""
from __future__ import annotations

import argparse
import json
import random
import sys
import time
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import baek_balko_constructions as bb  # noqa: E402
from predecessor_half_perturbation_search import flip_walk, orientation_signature  # noqa: E402


# ------------------------------------------------------------------ seeds

def horton(m: int, factor: Fraction) -> list[tuple[Fraction, Fraction]]:
    """Horton's set of 2^m points: the even-indexed half and the odd-indexed
    half, the latter shifted up by ``factor`` times the smallest shift that
    separates every line of one half from the other half (``factor`` >= 1
    gives Horton's order type; smaller factors give Horton-type sets)."""
    if m == 0:
        return [(Fraction(0), Fraction(0))]
    prev = horton(m - 1, factor)
    n = len(prev)
    maxy = max(abs(p[1]) for p in prev)
    shift = (maxy + 1) * (2 * n) ** 2 * factor
    pts = []
    for x, y in prev:
        pts.append((2 * x, y))
        pts.append((2 * x + 1, y + shift))
    return pts


def double_chain(m: int) -> list[tuple[Fraction, Fraction]]:
    up = [(Fraction(i), Fraction(1000) + Fraction((2 * i - (m - 1)) ** 2, 4)) for i in range(m)]
    lo = [(Fraction(i) + Fraction(1, 2), -Fraction(1000) - Fraction((2 * i - (m - 1)) ** 2, 4)) for i in range(m)]
    return up + lo


def random_set(n: int, rng: random.Random, box: int = 10 ** 6) -> list[tuple[Fraction, Fraction]]:
    while True:
        pts = [(Fraction(rng.randrange(box)), Fraction(rng.randrange(box))) for _ in range(n)]
        if bb.general_position(pts) and bb.distinct_x(pts):
            return pts


def seeds(families: list[str], rng: random.Random):
    if "horton" in families:
        for m, factors in ((5, (Fraction(4), Fraction(1), Fraction(1, 4), Fraction(1, 64), Fraction(1, 4096))),
                           (6, (Fraction(1),))):
            for factor in factors:
                pts = horton(m, factor)
                if bb.general_position(pts):
                    yield f"Horton(m={m},factor={factor})", pts
    if "double_chain" in families:
        for m in (13, 16):
            yield f"DoubleChain(2x{m})", double_chain(m)
    if "random" in families:
        for index in range(3):
            yield f"Random(36,#{index})", random_set(36, rng)


# ------------------------------------------------------------- pruning

def max_gon_free_subset(points, g: int, lo: int, hi: int, cadical: Path, time_limit: int = 300):
    """Largest subset with no convex g-gon and size in [lo, hi]: one polygon
    enumeration, then an ascending search over the target size (a subset of
    size ``lo`` is found quickly when one exists; each solver call is bounded
    by ``time_limit`` seconds and a timeout ends the search with the best
    subset so far)."""
    gons = (bb.convex_polygons_by_chains(points, g) if len(points) > 24
            else bb.convex_sets_of_size(points, g))
    best = {"gon_count": len(gons), "size": 0}
    for target in range(lo, hi + 1):
        result = bb.largest_gon_free_subset(points, g, target, cadical, gons=gons, time_limit=time_limit)
        if result.get("found"):
            best = {"gon_count": len(gons), "size": len(result["subset"]), "subset": result["subset"]}
            continue
        if result.get("found") is None:
            best["reason"] = f"timeout at target {target}: " + str(result.get("reason"))[:80]
        else:
            best["unsat_at"] = target
        break
    return best


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=7)
    parser.add_argument("--cadical", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--counterexample-dir", type=Path, required=True)
    parser.add_argument("--min-size", type=int, default=25)
    parser.add_argument("--families", default="horton,double_chain,random")
    parser.add_argument("--walk-keep", type=int, default=20, help="new order types tested per pruned seed")
    parser.add_argument("--walk-nearest", type=int, default=6)
    parser.add_argument("--seed", type=int, default=20260905)
    args = parser.parse_args()
    k = args.k
    rng = random.Random(args.seed)
    records = []
    counterexamples = 0

    def half_search(name, points):
        nonlocal counterexamples
        n = len(points)
        target = (n + 1) // 2
        result = bb.largest_gon_free_subset(points, k - 1, target, args.cadical)
        if result.get("found"):
            half = [points[i] for i in result["subset"]]
            assert bb.largest_convex_subset(half) < k - 1, "witness failed re-verification"
            return {"found": True, "gon_count": result["gon_count"], "subset": result["subset"]}
        if result.get("found") is None:
            return {"found": None, "reason": result.get("reason")}
        counterexamples += 1
        args.counterexample_dir.mkdir(parents=True, exist_ok=True)
        path = args.counterexample_dir / f"k{k}-structured-{counterexamples}.json"
        path.write_text(json.dumps({"name": name, "points": [[str(x), str(y)] for x, y in points],
                                    "gon_count": result.get("gon_count"),
                                    "largest_convex": bb.largest_convex_subset(points)}, indent=1))
        print(f"ALERT: no {k-1}-gon-free half in {name}: {path}", file=sys.stderr, flush=True)
        return {"found": False, "gon_count": result.get("gon_count"), "path": str(path)}

    for name, pts in seeds(args.families.split(","), rng):
        started = time.time()
        ints = bb.to_integers(pts)
        rec = {"name": name, "size": len(ints), "general_position": bb.general_position(ints),
               "largest_convex": bb.largest_convex_subset(ints)}
        hi = min(len(ints), 2 ** (k - 2))
        if rec["largest_convex"] < k:
            pruned = {"gon_count": 0, "size": len(ints), "subset": list(range(len(ints)))}
        else:
            pruned = max_gon_free_subset(ints, k, args.min_size, hi, args.cadical)
        rec["prune"] = {key: value for key, value in pruned.items() if key != "subset"}
        rec["prune_seconds"] = round(time.time() - started, 1)
        if pruned["size"] >= args.min_size:
            sub = [ints[i] for i in pruned["subset"]]
            assert bb.largest_convex_subset(sub) < k
            rec["pruned_points"] = [list(p) for p in sub]
            rec["pruned_largest_convex"] = bb.largest_convex_subset(sub)
            rec["half"] = half_search(name, sub)
            walk_stats = {"half_found": 0, "half_missing": 0}
            seen_types = {orientation_signature([tuple(Fraction(c) for c in p) for p in sub])}

            def on_state(points, v, pair, name=name, walk_stats=walk_stats):
                result = half_search(f"{name} after flips", [tuple(p) for p in bb.to_integers(points)])
                walk_stats["half_found" if result.get("found") else "half_missing"] += 1

            walk = flip_walk([tuple(p) for p in sub], k, rng, args.walk_keep, args.cadical,
                             (len(sub) + 1) // 2, args.walk_nearest, on_state)
            rec["walk"] = {**walk, **walk_stats}
        rec["seconds"] = round(time.time() - started, 1)
        print(json.dumps({key: value for key, value in rec.items() if key != "pruned_points"}), file=sys.stderr, flush=True)
        records.append(rec)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({"k": k, "seed": args.seed, "min_size": args.min_size,
                                           "counterexamples": counterexamples, "records": records}, indent=1) + "\n")
    print(json.dumps({"seeds": len(records), "tested": sum(1 for r in records if "half" in r),
                      "counterexamples": counterexamples}), file=sys.stderr)


if __name__ == "__main__":
    main()
