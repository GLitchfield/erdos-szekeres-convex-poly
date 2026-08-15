#!/usr/bin/env python3
"""Generate decomposition and exact-coordinate coverage at five and six.

Every catalog state declared recursively decomposable receives an explicit
decomposition tree.  Exact integer coordinates are searched only for the 190
six-point states outside that class, as required by Wayfinder ticket 0014.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import random


RANDOM_SEED = 20260814
DRAW_LIMIT = 1_000_000
GAP_MAXIMUM = 100
ORDINATE_RADIUS = 3000


def triples(n: int) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(range(n), 3))


def mask_width(n: int) -> int:
    return max(1, (len(triples(n)) + 3) // 4)


def show(mask: int, n: int) -> str:
    return format(mask, f"0{mask_width(n)}x")


def color(mask: int, positions: dict[tuple[int, int, int], int],
          triple: tuple[int, int, int]) -> bool:
    return bool(mask & (1 << positions[triple]))


def decomposition_tree(mask: int, n: int) -> dict[str, object] | None:
    triple_list = triples(n)
    positions = {triple: index for index, triple in enumerate(triple_list)}

    @lru_cache(maxsize=None)
    def build(support: int) -> dict[str, object] | None:
        if support.bit_count() == 1:
            vertex = (support & -support).bit_length() - 1
            return {"leaf": vertex, "support_hex": format(support, "x")}
        lower = (support - 1) & support
        while lower:
            upper = support ^ lower
            compatible = True
            for triple in triple_list:
                triple_support = sum(1 << vertex for vertex in triple)
                if triple_support & support != triple_support:
                    continue
                if triple_support & lower == triple_support:
                    continue
                if triple_support & upper == triple_support:
                    continue
                required = bool(lower & (1 << triple[1]))
                if color(mask, positions, triple) != required:
                    compatible = False
                    break
            if compatible:
                lower_tree = build(lower)
                upper_tree = build(upper)
                if lower_tree is not None and upper_tree is not None:
                    return {
                        "lower": lower_tree,
                        "lower_support_hex": format(lower, "x"),
                        "support_hex": format(support, "x"),
                        "upper": upper_tree,
                        "upper_support_hex": format(upper, "x"),
                    }
            lower = (lower - 1) & support
        return None

    return build((1 << n) - 1)


def determinant(points: tuple[tuple[int, int], ...],
                triple: tuple[int, int, int]) -> int:
    i, j, k = triple
    xi, yi = points[i]
    xj, yj = points[j]
    xk, yk = points[k]
    return (xj - xi) * (yk - yi) - (yj - yi) * (xk - xi)


def point_mask(points: tuple[tuple[int, int], ...]) -> tuple[int, tuple[int, ...]] | None:
    determinants = tuple(determinant(points, triple)
                         for triple in triples(len(points)))
    if any(value == 0 for value in determinants):
        return None
    mask = sum(int(value > 0) << index
               for index, value in enumerate(determinants))
    return mask, determinants


def search_fin_six(targets: set[int]) -> tuple[dict[int, dict[str, object]], int]:
    generator = random.Random(RANDOM_SEED)
    found: dict[int, dict[str, object]] = {}
    for draw in range(1, DRAW_LIMIT + 1):
        xs = [0]
        for _ in range(5):
            xs.append(xs[-1] + generator.randint(1, GAP_MAXIMUM))
        raw_y = [generator.randint(-ORDINATE_RADIUS, ORDINATE_RADIUS)
                 for _ in range(6)]
        ys = [value - raw_y[0] for value in raw_y]
        points = tuple(zip(xs, ys))
        result = point_mask(points)
        if result is None:
            continue
        mask, determinants = result
        if mask not in targets or mask in found:
            continue
        found[mask] = {
            "determinants": list(determinants),
            "discovery_draw": draw,
            "mask_hex": show(mask, 6),
            "points": [list(point) for point in points],
        }
        if len(found) == len(targets):
            return found, draw
    missing = ",".join(show(mask, 6) for mask in sorted(targets - set(found)))
    raise RuntimeError(f"coordinate coverage incomplete after {DRAW_LIMIT} draws: {missing}")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def catalog_rows(catalog: dict[str, object], n: int) -> list[tuple[int, bool]]:
    level = catalog["levels"][str(n)]  # type: ignore[index]
    annotations = level["annotations"]  # type: ignore[index]
    states = level["states_hex"]  # type: ignore[index]
    return [(int(mask_hex, 16), bool(annotations[mask_hex]["decomposable"]))
            for mask_hex in states]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    catalog = json.loads(args.catalog.read_text())
    trees: dict[str, list[dict[str, object]]] = {}
    nondecomposable_six: set[int] = set()
    for n in (5, 6):
        level_trees = []
        for mask, declared_decomposable in catalog_rows(catalog, n):
            tree = decomposition_tree(mask, n)
            if (tree is not None) != declared_decomposable:
                raise RuntimeError(f"decomposition annotation mismatch at {n}/{show(mask, n)}")
            if tree is not None:
                level_trees.append({"mask_hex": show(mask, n), "tree": tree})
            elif n == 6:
                nondecomposable_six.add(mask)
            else:
                raise RuntimeError(f"Fin5 state lacks decomposition: {show(mask, n)}")
        trees[str(n)] = level_trees

    if len(trees["5"]) != 62 or len(trees["6"]) != 718:
        raise RuntimeError("unexpected decomposition coverage counts")
    if len(nondecomposable_six) != 190:
        raise RuntimeError("unexpected nondecomposable Fin6 count")
    coordinates, draws = search_fin_six(nondecomposable_six)
    document = {
        "catalog_sha256": sha256_file(args.catalog),
        "coordinate_search": {
            "draw_limit": DRAW_LIMIT,
            "draws_used": draws,
            "gap_maximum": GAP_MAXIMUM,
            "ordinate_radius": ORDINATE_RADIUS,
            "prng": "python-random-mt19937",
            "seed": RANDOM_SEED,
        },
        "decomposition_certificates": trees,
        "model": "complete labeled OneChangeOn catalogs at Fin5 and Fin6",
        "nondecomposable_fin_six_realizations": [
            coordinates[mask] for mask in sorted(nondecomposable_six)
        ],
        "summary": {
            "fin5_decomposition": len(trees["5"]),
            "fin5_total": 62,
            "fin6_coordinates": len(coordinates),
            "fin6_decomposition": len(trees["6"]),
            "fin6_total": 908,
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")
    print(f"Fin5 62/62 decomposable; Fin6 718 trees + {len(coordinates)} coordinates")
    print(f"coordinate search completed at deterministic draw {draws}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
