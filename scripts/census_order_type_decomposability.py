#!/usr/bin/env python3
"""Census of deep-below decomposability over k-gon-free order types.

Input: one of Aichholzer's realizable order-type databases (``otypes08.b08``
with 3,315 eight-point types, ``otypes09.b16`` with 158,817 nine-point
types; every entry is an integer-coordinate realization in general
position).  For every type with no convex ``k``-gon the script enumerates all
combinatorially distinct sweep directions and, for each direction, forms the
sweep coloring exactly as ``ErdosSzekeres/Sweep.lean`` does (vertices ordered
by projection on the direction; a triple is a left turn iff the orientation
of its three points in that order is positive) and tests

* ``IsDecomposable`` in the sense of ``ErdosSzekeres/Decomposable.lean``: the
  full index set is a singleton or splits as ``lower ⊔ upper`` (parts may
  interleave in sweep order) with both parts recursively decomposable and
  every crossing triple colored left exactly when its middle vertex lies in
  ``lower``;
* whether any top-level deep-below split exists at all, ignoring recursion;
* the longest cap and the longest cup.

Direction-independent data recorded per type: convex-hull layer sizes and
the number of distinct sweep directions.  The "database direction" is the
sweep by ``x`` with ties broken by ``y``.

The crossing law is implemented through its closure form: for a split
``(L, U)`` of ``S`` the law holds iff for every left triple ``(i, j, k)`` in
``S`` with ``j ∈ U`` both ``i, k ∈ U``, and for every right triple with
``j ∈ L`` both ``i, k ∈ L``.  A brute-force check of the literal definition
is kept as a self-test on random splits.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import random
import sys
from collections import Counter
from functools import lru_cache
from pathlib import Path

ORDER_TYPE_COUNTS = {8: 3315, 9: 158817}

Point = tuple[int, int]


def read_database(path: Path, n: int) -> list[tuple[Point, ...]]:
    width = 1 if path.suffix == ".b08" else 2
    raw = path.read_bytes()
    record = 2 * n * width
    if len(raw) % record:
        raise ValueError("database size is not a multiple of the record size")
    if n in ORDER_TYPE_COUNTS and len(raw) != ORDER_TYPE_COUNTS[n] * record:
        raise ValueError("unexpected order-type database size")
    result = []
    for start in range(0, len(raw), record):
        row = raw[start:start + record]
        if width == 1:
            values = list(row)
        else:
            values = [int.from_bytes(row[i:i + 2], "little")
                      for i in range(0, len(row), 2)]
        result.append(tuple(zip(values[::2], values[1::2])))
    return result


def orient(a: Point, b: Point, c: Point) -> int:
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def in_general_position(points) -> bool:
    return all(orient(a, b, c) != 0
               for a, b, c in itertools.combinations(points, 3))


def inside_triangle(p: Point, a: Point, b: Point, c: Point) -> bool:
    s1, s2, s3 = orient(a, b, p), orient(b, c, p), orient(c, a, p)
    return (s1 > 0 and s2 > 0 and s3 > 0) or (s1 < 0 and s2 < 0 and s3 < 0)


def convex_four(points, quad) -> bool:
    for x in quad:
        others = [points[y] for y in quad if y != x]
        if inside_triangle(points[x], *others):
            return False
    return True


def contains_convex_kgon(points, k: int) -> bool:
    n = len(points)
    conv4 = {q: convex_four(points, q) for q in itertools.combinations(range(n), 4)}
    for subset in itertools.combinations(range(n), k):
        if all(conv4[q] for q in itertools.combinations(subset, 4)):
            return True
    return False


def hull_layers(points) -> list[int]:
    remaining = list(range(len(points)))
    layers = []
    while remaining:
        if len(remaining) <= 3:
            layers.append(len(remaining))
            break
        hull = []
        for x in remaining:
            others = [y for y in remaining if y != x]
            interior = any(inside_triangle(points[x], points[a], points[b], points[c])
                           for a, b, c in itertools.combinations(others, 3))
            if not interior:
                hull.append(x)
        layers.append(len(hull))
        remaining = [x for x in remaining if x not in hull]
    return layers


def primitive(v: tuple[int, int]) -> tuple[int, int]:
    g = math.gcd(abs(v[0]), abs(v[1]))
    return (v[0] // g, v[1] // g)


def _angle_class(d):
    """0 for angles in [0, pi), 1 for [pi, 2pi)."""
    return 0 if (d[1] > 0 or (d[1] == 0 and d[0] > 0)) else 1


def _angle_compare(a, b):
    ca, cb = _angle_class(a), _angle_class(b)
    if ca != cb:
        return ca - cb
    cross = a[0] * b[1] - a[1] * b[0]
    return -1 if cross > 0 else (1 if cross < 0 else 0)


def sort_by_angle(directions):
    """Exact counterclockwise angular sort of integer directions."""
    import functools
    return sorted(directions, key=functools.cmp_to_key(_angle_compare))


def sweep_directions(points) -> list[tuple[int, int]]:
    """One generic integer direction per open arc between critical directions."""
    critical = set()
    for p, q in itertools.combinations(points, 2):
        v = (q[0] - p[0], q[1] - p[1])
        perp = primitive((-v[1], v[0]))
        critical.add(perp)
        critical.add((-perp[0], -perp[1]))
    ordered = sort_by_angle(critical)
    directions = []
    for a, b in zip(ordered, ordered[1:] + ordered[:1]):
        d = (a[0] + b[0], a[1] + b[1])
        if d == (0, 0):
            raise ValueError("antipodal consecutive critical directions")
        directions.append(primitive(d))
    return directions


def sweep_coloring(points, direction):
    """Return (order, chi) where chi maps increasing position triples to
    True for a left turn."""
    keys = [direction[0] * p[0] + direction[1] * p[1] for p in points]
    if len(set(keys)) != len(keys):
        raise ValueError("direction is not generic")
    order = sorted(range(len(points)), key=lambda i: keys[i])
    pts = [points[i] for i in order]
    chi = {}
    for a, b, c in itertools.combinations(range(len(points)), 3):
        chi[(a, b, c)] = orient(pts[a], pts[b], pts[c]) > 0
    return order, chi


class Coloring:
    """A triple coloring on n ordered vertices with decomposability tests."""

    def __init__(self, n: int, chi: dict[tuple[int, int, int], bool]):
        self.n = n
        self.chi = chi
        self.left_triples = [t for t, v in chi.items() if v]
        self.right_triples = [t for t, v in chi.items() if not v]
        self._closure_cache: dict[int, tuple[list[int], list[int]]] = {}

    def closure(self, s: int) -> tuple[list[int], list[int]]:
        cached = self._closure_cache.get(s)
        if cached is not None:
            return cached
        need_u = [0] * self.n
        need_l = [0] * self.n
        for i, j, k in self.left_triples:
            m = (1 << i) | (1 << j) | (1 << k)
            if m & s == m:
                need_u[j] |= (1 << i) | (1 << k)
        for i, j, k in self.right_triples:
            m = (1 << i) | (1 << j) | (1 << k)
            if m & s == m:
                need_l[j] |= (1 << i) | (1 << k)
        self._closure_cache[s] = (need_u, need_l)
        return need_u, need_l

    def valid_split(self, s: int, lower: int) -> bool:
        upper = s ^ lower
        need_u, need_l = self.closure(s)
        for j in range(self.n):
            bit = 1 << j
            if upper & bit and need_u[j] & ~upper:
                return False
            if lower & bit and need_l[j] & ~lower:
                return False
        return True

    def valid_split_literal(self, s: int, lower: int) -> bool:
        upper = s ^ lower
        for (i, j, k), left in self.chi.items():
            m = (1 << i) | (1 << j) | (1 << k)
            if m & s != m:
                continue
            if m & lower == m or m & upper == m:
                continue
            if left != bool(lower & (1 << j)):
                return False
        return True

    def proper_subsets(self, s: int):
        sub = (s - 1) & s
        while sub:
            yield sub
            sub = (sub - 1) & s

    def decomposable(self, s: int, memo: dict[int, bool]) -> bool:
        if s & (s - 1) == 0:
            return True
        cached = memo.get(s)
        if cached is not None:
            return cached
        answer = False
        for lower in self.proper_subsets(s):
            if not self.valid_split(s, lower):
                continue
            if self.decomposable(lower, memo) and self.decomposable(s ^ lower, memo):
                answer = True
                break
        memo[s] = answer
        return answer

    def top_split_count(self) -> int:
        full = (1 << self.n) - 1
        return sum(1 for lower in self.proper_subsets(full)
                   if self.valid_split(full, lower))

    def longest_chain(self, left: bool) -> int:
        """Longest cup (left=True) or cap (left=False) by consecutive triples,
        valid for sweep-realizable colorings by ``Chains.lean``."""
        n = self.n
        best = min(n, 2)
        length = {}
        for j in range(n - 1, -1, -1):
            for i in range(j - 1, -1, -1):
                value = 2
                for k in range(j + 1, n):
                    if self.chi[(i, j, k)] == left:
                        value = max(value, 1 + length[(j, k)])
                length[(i, j)] = value
                best = max(best, value)
        return best

    def bits(self) -> int:
        value = 0
        for position, triple in enumerate(itertools.combinations(range(self.n), 3)):
            if self.chi[triple]:
                value |= 1 << position
        return value


def analyze(points, k: int, self_test: random.Random | None):
    n = len(points)
    directions = sweep_directions(points)
    per_direction = []
    colorings = set()
    for direction in directions:
        order, chi = sweep_coloring(points, direction)
        col = Coloring(n, chi)
        full = (1 << n) - 1
        if self_test is not None:
            for _ in range(8):
                lower = self_test.randrange(1, full)
                if col.valid_split(full, lower) != col.valid_split_literal(full, lower):
                    raise AssertionError("closure form disagrees with literal crossing law")
        memo: dict[int, bool] = {}
        per_direction.append({
            "direction": list(direction),
            "order": order,
            "decomposable": col.decomposable(full, memo),
            "top_splits": col.top_split_count(),
            "max_cup": col.longest_chain(True),
            "max_cap": col.longest_chain(False),
        })
        colorings.add(col.bits())
    # database direction: x with ties broken by y
    span = max(abs(p[1] - q[1]) for p, q in itertools.combinations(points, 2)) + 1
    order, chi = sweep_coloring(points, (span, 1))
    col = Coloring(n, chi)
    db = {
        "decomposable": col.decomposable((1 << n) - 1, {}),
        "top_splits": col.top_split_count(),
    }
    return {
        "points": [list(p) for p in points],
        "hull_layers": hull_layers(points),
        "direction_count": len(directions),
        "distinct_colorings": len(colorings),
        "database_direction": db,
        "directions_decomposable": sum(d["decomposable"] for d in per_direction),
        "directions_with_top_split": sum(d["top_splits"] > 0 for d in per_direction),
        "max_cup_over_directions": max(d["max_cup"] for d in per_direction),
        "max_cap_over_directions": max(d["max_cap"] for d in per_direction),
        "min_max_cup_over_directions": min(d["max_cup"] for d in per_direction),
        "min_max_cap_over_directions": min(d["max_cap"] for d in per_direction),
        "per_direction": per_direction,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("database", type=Path)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--k", type=int, required=True,
                        help="forbidden convex polygon size")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--sample", type=int, default=0,
                        help="analyze only this many k-gon-free types (0 = all)")
    parser.add_argument("--seed", type=int, default=20260903)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--compact", action="store_true",
                        help="drop per-direction lists from records (summary is unaffected)")
    args = parser.parse_args()

    raw = args.database.read_bytes()
    database = read_database(args.database, args.n)
    free_indices = []
    for index, points in enumerate(database):
        if not in_general_position(points):
            raise ValueError(f"type {index} is not in general position")
        if not contains_convex_kgon(points, args.k):
            free_indices.append(index)
    print(f"{len(database)} types, {len(free_indices)} with no convex {args.k}-gon",
          file=sys.stderr)

    rng = random.Random(args.seed)
    selected = free_indices
    if args.sample and args.sample < len(free_indices):
        selected = sorted(rng.sample(free_indices, args.sample))
    tester = random.Random(args.seed + 1) if args.self_test else None

    records = []
    for count, index in enumerate(selected, 1):
        record = analyze(database[index], args.k, tester)
        record["type_index"] = index
        if args.compact:
            for key in [k for k in record if k.startswith("per_direction")]:
                del record[key]
        records.append(record)
        if count % 100 == 0:
            print(f"  {count}/{len(selected)}", file=sys.stderr)

    summary = {
        "types_total": len(database),
        "types_free": len(free_indices),
        "types_analyzed": len(records),
        "decomposable_in_database_direction":
            sum(r["database_direction"]["decomposable"] for r in records),
        "top_split_in_database_direction":
            sum(r["database_direction"]["top_splits"] > 0 for r in records),
        "decomposable_in_some_direction":
            sum(r["directions_decomposable"] > 0 for r in records),
        "decomposable_in_every_direction":
            sum(r["directions_decomposable"] == r["direction_count"] for r in records),
        "top_split_in_some_direction":
            sum(r["directions_with_top_split"] > 0 for r in records),
        "top_split_in_every_direction":
            sum(r["directions_with_top_split"] == r["direction_count"] for r in records),
        "hull_layer_profiles": dict(Counter(
            "-".join(map(str, r["hull_layers"])) for r in records)),
        "direction_counts": dict(Counter(r["direction_count"] for r in records)),
        "decomposable_direction_fraction_histogram": dict(Counter(
            f"{r['directions_decomposable']}/{r['direction_count']}" for r in records)),
    }
    output = {
        "schema": "erdos-szekeres-order-type-decomposability-census-v1",
        "database": str(args.database),
        "database_sha256": hashlib.sha256(raw).hexdigest(),
        "n": args.n,
        "k": args.k,
        "sample": args.sample,
        "seed": args.seed,
        "conventions": {
            "coloring": "vertices sorted by projection on the sweep direction; "
                        "triple is left iff orientation of the three points in "
                        "that order is positive",
            "decomposable": "ErdosSzekeres.IsDecomposable: recursive deep-below "
                            "split with interleaving allowed; crossing triple "
                            "is left iff its middle vertex is in the lower part",
            "database_direction": "x-coordinate with ties broken by y",
            "chains": "cup = consecutive left triples, cap = consecutive right",
        },
        "summary": summary,
        "records": records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=1, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=1, sort_keys=True))


if __name__ == "__main__":
    main()
