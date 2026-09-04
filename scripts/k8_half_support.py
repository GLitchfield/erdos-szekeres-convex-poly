#!/usr/bin/env python3
"""Experiment 0111: (k-1)-gon-free halves of the 64-point k = 8 extremal sets.

Loads the k = 8 records produced by ``baek_balko_constructions.py`` (which
skipped the half search), enumerates the convex 7-gons of each 64-point set by
the cap/cup chain enumeration, asks CaDiCaL for a 32-point subset meeting no
7-gon, and re-verifies any witness with the independent cup/cap dynamic
programme (``largest_convex_subset``)."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import baek_balko_constructions as bb  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cadical", type=Path, required=True)
    args = parser.parse_args()
    data = json.load(open(args.input))
    k = data["k"]
    for record in data["records"]:
        points = [tuple(p) for p in record["points"]]
        n = len(points)
        target = (n + 1) // 2
        started = time.time()
        gons = bb.convex_polygons_by_chains(points, k - 1)
        enumeration_seconds = time.time() - started
        print(f"{record['name']}: n={n}, convex {k-1}-gons={len(gons)}, "
              f"enumerated in {enumeration_seconds:.1f}s", file=sys.stderr, flush=True)
        started = time.time()
        result = bb.largest_gon_free_subset(points, k - 1, target, args.cadical)
        result["solver_seconds"] = round(time.time() - started, 1)
        result["enumeration_seconds"] = round(enumeration_seconds, 1)
        result["target"] = target
        if result.get("found") and result.get("subset") is not None:
            subset = sorted(result["subset"])
            half = [points[i] for i in subset]
            largest = bb.largest_convex_subset(half)
            result["verified"] = (len(subset) >= target and len(set(subset)) == len(subset)
                                  and all(0 <= i < n for i in subset) and largest < k - 1)
            result["half_largest_convex"] = largest
            result["subset"] = subset
        record["half_support"] = result
        print(json.dumps({key: value for key, value in result.items() if key != "subset"}),
              file=sys.stderr, flush=True)
    data["schema"] = data.get("schema", 1)
    data["half_support_method"] = ("convex_polygons_by_chains + CaDiCaL sequential counter; "
                                   "witness re-verified by largest_convex_subset")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=1) + "\n")
    print(f"wrote {args.output}", file=sys.stderr)


if __name__ == "__main__":
    main()
