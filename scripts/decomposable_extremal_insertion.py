#!/usr/bin/env python3
"""Exact-coordinate, bounded falsifier for extremal decomposable insertion.

Checks selected vertical fibers of the canonical ES(k,k,k) realization.
These fibers and realizations do not exhaust the conjecture's domain.
Every positive result includes an independently checked convex polygon.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import itertools
import json
from pathlib import Path
import time

import baek_balko_constructions as bb


def hull_indices(points, subset):
    """Independent monotone-chain hull; indices refer to the input points."""
    ordered = sorted(subset, key=lambda i: points[i])
    def half(indices):
        result = []
        for i in indices:
            while len(result) >= 2 and bb.orient(
                    points[result[-2]], points[result[-1]], points[i]) <= 0:
                result.pop()
            result.append(i)
        return result
    return half(ordered)[:-1] + half(reversed(ordered))[:-1]


def convex_witness(points, target):
    """Cup/cap dynamic program with paths, independently verified by a hull."""
    order = sorted(range(len(points)), key=lambda i: points[i][0])
    pts = [points[i] for i in order]
    signs = {t: bb.orient(*(pts[i] for i in t)) > 0
             for t in itertools.combinations(range(len(pts)), 3)}
    for left in range(len(pts)):
        tables = []
        for turn in (False, True):
            best = {(left, j): (left, j) for j in range(left + 1, len(pts))}
            ends = {j: (left, j) for j in range(left + 1, len(pts))}
            for j in range(left + 1, len(pts)):
                for right in range(j + 1, len(pts)):
                    path = max((best[h, j] + (right,) for h in range(left, j)
                                if (h, j) in best and signs[h, j, right] == turn),
                               key=len, default=())
                    if path:
                        best[j, right] = path
                        if len(path) > len(ends[right]):
                            ends[right] = path
            tables.append(ends)
        for right in range(left + 1, len(pts)):
            lower, upper = tables[0][right], tables[1][right]
            candidate = [order[i] for i in lower + upper[-2:0:-1]]
            if len(candidate) >= target:
                candidate = candidate[:target]
                if len(set(candidate)) != target or len(hull_indices(points, candidate)) != target:
                    raise AssertionError("chain witness failed independent hull verification")
                return candidate
    return None


def decomposition_tree(points):
    """Find a tree, checking its crossing law independently at every split."""
    col = bb.coloring_for(points, (1, 0))
    def visit(mask):
        vertices = [i for i in range(len(points)) if mask >> i & 1]
        if len(vertices) == 1:
            return vertices[0]
        for lower in sorted(col.closed_sets(mask)):
            upper = mask ^ lower
            if not col.decomposable(lower, {}) or not col.decomposable(upper, {}):
                continue
            for i, j, k in itertools.combinations(vertices, 3):
                sides = [bool(lower >> x & 1) for x in (i, j, k)]
                if len(set(sides)) > 1 and col.chi[i, j, k] != sides[1]:
                    raise AssertionError("decomposition crossing law failed")
            return [visit(lower), visit(upper)]
        raise AssertionError("seed is not decomposable in the x sweep")
    return visit((1 << len(points)) - 1)


def insertion_candidates(points, cells_per_gap):
    xs = [p[0] for p in points]
    fibers = [xs[0] - 1] + [(a + b) / 2 for a, b in zip(xs, xs[1:])] + [xs[-1] + 1]
    for gap, x in enumerate(fibers):
        heights = sorted({a[1] + (b[1] - a[1]) * (x - a[0]) / (b[0] - a[0])
                          for a, b in itertools.combinations(points, 2)})
        candidates = [heights[0] - 1] + [(a + b) / 2 for a, b in zip(heights, heights[1:])]
        candidates += [heights[-1] + 1]
        count = len(candidates)
        selected = (range(count) if cells_per_gap == 0 or count <= cells_per_gap else
                    sorted({i * (count - 1) // (cells_per_gap - 1) for i in range(cells_per_gap)}))
        for cell in selected:
            yield gap, cell, count, (x, candidates[cell])


def run(cases, cells_per_gap):
    started = time.monotonic()
    rows, violations = [], []
    for k in cases:
        points = sorted(bb.es_set3(k, k, k))
        if len(points) != 2 ** (k - 2) or not bb.general_position(points) or not bb.distinct_x(points):
            raise AssertionError("seed hypotheses failed")
        tree = decomposition_tree(points)
        if convex_witness(points, k) is not None or bb.largest_convex_subset(points) >= k:
            raise AssertionError("seed is not target-free")
        row = {"k": k, "points": [[str(x), str(y)] for x, y in points],
               "decomposition_tree": tree, "insertions": [], "violations": 0}
        for gap, cell, total, q in insertion_candidates(points, cells_per_gap):
            extended = points + [q]
            if not bb.general_position(extended) or not bb.distinct_x(extended):
                raise AssertionError("fiber candidate violated general position or sweep order")
            witness = convex_witness(extended, k)
            entry = {"gap": gap, "cell": cell, "fiber_cells": total,
                     "point": [str(c) for c in q], "polygon": witness}
            if witness is None:
                maximum = bb.largest_convex_subset(extended)
                if maximum >= k:
                    raise AssertionError("witness search disagreed with reference maximum")
                entry["largest_convex"] = maximum
                violations.append({"k": k, "seed": row["points"], **entry})
                row["violations"] += 1
            elif len(points) not in witness:
                raise AssertionError("polygon unexpectedly avoids the inserted vertex")
            row["insertions"].append(entry)
        rows.append(row)
        print(json.dumps({"k": k, "insertions": len(row["insertions"]),
                          "violations": row["violations"]}), flush=True)
    return {"scope": "selected vertical fibers of canonical ES(k,k,k) realizations only",
            "exhaustive_over_realizations": False, "cells_per_gap": cells_per_gap,
            "cases": rows, "violations": violations, "seconds": time.monotonic() - started}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cases", default="4,5,6,7")
    parser.add_argument("--cells-per-gap", type=int, default=7)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    cases = [int(k) for k in args.cases.split(",")]
    if not cases or any(k < 4 or k > 7 for k in cases):
        parser.error("bounded probe supports 4 <= k <= 7")
    if args.cells_per_gap == 1 or args.cells_per_gap < 0:
        parser.error("cells-per-gap must be zero (all) or at least two")
    result = run(cases, args.cells_per_gap)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    return 2 if result["violations"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
