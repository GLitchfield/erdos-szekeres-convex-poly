#!/usr/bin/env python3
"""Workstream E falsifier: search perturbations of the known k-gon-free
extremal sets for one with no (k-1)-gon-free half.

Order-type-preserving moves cannot change anything (convexity is a function of
the orientations), so the perturbations are multi-scale integer jitters that
flip some orientations.  A candidate is kept when it is in general position,
still k-gon-free (checked by enumerating its convex k-gons), and has an order
type not seen before.  For each kept candidate the SAT half search of
experiment 0108 runs; an UNSAT answer is a counterexample to the
predecessor-half conjecture at k and is written out immediately."""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import baek_balko_constructions as bb  # noqa: E402


def nearest_distances(points):
    out = []
    for i, (x, y) in enumerate(points):
        best = None
        for j, (u, v) in enumerate(points):
            if i == j:
                continue
            d = ((x - u) ** 2 + (y - v) ** 2) ** 0.5
            best = d if best is None or d < best else best
        out.append(best)
    return out


def orientation_signature(points):
    """Labeled chirotope: enough to detect a changed order type under jitter,
    which keeps labels (the brute-force canonical form is for small sets)."""
    return tuple(bb.orient(points[i], points[j], points[l]) > 0
                 for i, j, l in itertools.combinations(range(len(points)), 3))


def jitter(points, fraction, rng, scale):
    scaled = [(x * scale, y * scale) for x, y in points]
    dists = nearest_distances(scaled)
    out = []
    for (x, y), d in zip(scaled, dists):
        r = max(1, int(round(fraction * d)))
        out.append((x + rng.randint(-r, r), y + rng.randint(-r, r)))
    return out


def simplest_between(lo, hi):
    """A rational strictly inside (lo, hi) with a small denominator, so that
    coordinates do not compound denominators along a walk."""
    mid = (lo + hi) / 2
    limit = 1
    while True:
        cand = Fraction(mid).limit_denominator(limit)
        if lo < cand < hi:
            return cand
        limit *= 4


def flip_point_across(points, v, pair):
    """Move point ``v`` across the line through ``pair`` by the smallest
    exact displacement along that line's normal that flips only that
    orientation; returns the new point or None if another line is crossed
    first (ties included)."""
    p = points[v]
    i, j = pair
    a, b = points[i], points[j]
    nx, ny = -(b[1] - a[1]), (b[0] - a[0])
    others = [x for x in range(len(points)) if x != v]
    t_target = None
    same_side = []
    for c, d in itertools.combinations(others, 2):
        pc, pd = points[c], points[d]
        base = bb.orient(pc, pd, p)
        slope = (pd[0] - pc[0]) * ny - (pd[1] - pc[1]) * nx
        if slope == 0:
            continue
        t = Fraction(-base, slope)
        if (c, d) == pair:
            t_target = t
        elif t != 0:
            same_side.append(t)
    if t_target is None or t_target == 0:
        return None
    sign = 1 if t_target > 0 else -1
    nearer = [abs(t) for t in same_side if (t > 0) == (t_target > 0) and abs(t) <= abs(t_target)]
    if nearer:
        return None
    beyond = [abs(t) for t in same_side if (t > 0) == (t_target > 0) and abs(t) > abs(t_target)]
    hi = min(beyond) if beyond else 2 * abs(t_target)
    t = sign * simplest_between(abs(t_target), hi)
    return (p[0] + t * nx, p[1] + t * ny)


def nearest_lines(points, v, count):
    """The ``count`` pairs whose line is closest to point ``v``."""
    p = points[v]
    others = [x for x in range(len(points)) if x != v]
    scored = []
    for i, j in itertools.combinations(others, 2):
        a, b = points[i], points[j]
        num = abs(bb.orient(a, b, p))
        den2 = (b[0] - a[0]) ** 2 + (b[1] - a[1]) ** 2
        scored.append((Fraction(num * num, den2), (i, j)))
    scored.sort()
    return [pair for _, pair in scored[:count]]


def flip_walk(base, k, rng, steps, cadical, target, nearest, on_state):
    """Random walk on single-orientation flips that keep the set k-gon-free.
    ``on_state`` is called with each new accepted set; returns statistics."""
    points = [tuple(Fraction(x) for x in p) for p in base]
    stats = {"flips_tried": 0, "flips_free": 0, "accepted": 0}
    seen = {orientation_signature(points)}
    tries = 0
    while stats["accepted"] < steps and tries < 20 * steps:
        tries += 1
        v = rng.randrange(len(points))
        pair = rng.choice(nearest_lines(points, v, nearest))
        new_point = flip_point_across(points, v, pair)
        if new_point is None:
            continue
        cand = list(points); cand[v] = new_point
        stats["flips_tried"] += 1
        if bb.convex_polygons_by_chains(cand, k):
            continue
        stats["flips_free"] += 1
        key = orientation_signature(cand)
        if key in seen:
            continue
        seen.add(key)
        # rescale to integers so that denominators do not grow along the walk
        points = [tuple(Fraction(c) for c in q) for q in bb.to_integers(cand)]
        stats["accepted"] += 1
        on_state(points, v, pair)
    return stats


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--k", type=int, required=True)
    parser.add_argument("--cadical", type=Path, required=True)
    parser.add_argument("--tries", type=int, default=150, help="jitters attempted per base set")
    parser.add_argument("--keep", type=int, default=60, help="new order types tested per base set")
    parser.add_argument("--seed", type=int, default=20260904)
    parser.add_argument("--scale", type=int, default=64)
    parser.add_argument("--mode", choices=("flip", "jitter"), default="flip")
    parser.add_argument("--nearest", type=int, default=6, help="flip mode: choose among this many nearest flips")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--counterexample-dir", type=Path, required=True)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    data = json.load(open(args.input))
    k = args.k
    summary = []
    seen = set()
    for record in data["records"]:
        base = [tuple(p) for p in record["points"]]
        n = len(base)
        target = (n + 1) // 2
        seen.add(orientation_signature(base))
        stats = {"base": record["name"], "tries": 0, "general_position": 0, "k_gon_free": 0,
                 "new_order_types": 0, "half_found": 0, "half_missing": 0, "seconds": 0.0}
        started = time.time()
        if args.mode == "flip":
            def on_state(points, v, pair, record=record, stats=stats, target=target):
                result = bb.largest_gon_free_subset(points, k - 1, target, args.cadical)
                if result.get("found"):
                    half = [points[i] for i in result["subset"]]
                    assert bb.largest_convex_subset(half) < k - 1, "witness failed re-verification"
                    stats["half_found"] += 1
                else:
                    stats["half_missing"] += 1
                    args.counterexample_dir.mkdir(parents=True, exist_ok=True)
                    path = args.counterexample_dir / f"k{k}-{record['name'].replace('(', '_').replace(')', '').replace(',', '-')}-flip{stats['half_missing']}.json"
                    path.write_text(json.dumps({"base": record["name"], "points": [[str(x), str(y)] for x, y in points],
                                                "gon_count": result.get("gon_count"), "largest_convex": bb.largest_convex_subset(points)}, indent=1))
                    print(f"ALERT: no {k-1}-gon-free half after flips of {record['name']}: {path}", file=sys.stderr, flush=True)
            walk = flip_walk(base, k, rng, args.keep, args.cadical, target, args.nearest, on_state)
            stats.update({"tries": walk["flips_tried"], "k_gon_free": walk["flips_free"], "new_order_types": walk["accepted"],
                          "general_position": walk["flips_tried"]})
            stats["seconds"] = round(time.time() - started, 1)
            print(json.dumps(stats), file=sys.stderr, flush=True)
            summary.append(stats)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps({"k": k, "seed": args.seed, "mode": "flip", "partial": True,
                                               "per_base": summary}, indent=1) + "\n")
            continue
        for attempt in range(args.tries):
            if stats["new_order_types"] >= args.keep:
                break
            stats["tries"] += 1
            fraction = rng.choice((0.25, 0.5, 1.0))
            cand = jitter(base, fraction, rng, args.scale)
            if len(set(cand)) < n or not bb.general_position(cand):
                continue
            stats["general_position"] += 1
            if bb.convex_polygons_by_chains(cand, k):
                continue
            stats["k_gon_free"] += 1
            key = orientation_signature(cand)
            if key in seen:
                continue
            seen.add(key)
            stats["new_order_types"] += 1
            result = bb.largest_gon_free_subset(cand, k - 1, target, args.cadical)
            if result.get("found"):
                half = [cand[i] for i in result["subset"]]
                assert bb.largest_convex_subset(half) < k - 1, "witness failed re-verification"
                stats["half_found"] += 1
            else:
                stats["half_missing"] += 1
                args.counterexample_dir.mkdir(parents=True, exist_ok=True)
                path = args.counterexample_dir / f"k{k}-{record['name'].replace('(', '_').replace(')', '').replace(',', '-')}-{attempt}.json"
                path.write_text(json.dumps({"base": record["name"], "attempt": attempt, "fraction": fraction,
                                            "points": cand, "gon_count": result.get("gon_count"),
                                            "largest_convex": bb.largest_convex_subset(cand)}, indent=1))
                print(f"ALERT: no {k-1}-gon-free half for a perturbation of {record['name']}: {path}",
                      file=sys.stderr, flush=True)
        stats["seconds"] = round(time.time() - started, 1)
        print(json.dumps(stats), file=sys.stderr, flush=True)
        summary.append(stats)
    totals = {key: sum(s[key] for s in summary) for key in ("tries", "general_position", "k_gon_free", "new_order_types", "half_found", "half_missing")}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"k": k, "seed": args.seed, "scale": args.scale, "tries_per_base": args.tries,
                                       "keep_per_base": args.keep, "per_base": summary, "totals": totals}, indent=1) + "\n")
    print(json.dumps(totals), file=sys.stderr)


if __name__ == "__main__":
    main()
