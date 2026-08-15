#!/usr/bin/env python3
"""Generate exact four-point sweep realizations for the frozen catalog.

This producer searches a fixed integer ordinate box in lexicographic order.
Bit 1 denotes a positive determinant (`Turn.left`), and bit positions are the
lexicographically ordered increasing triples.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


def triples(n: int) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(range(n), 3))


def determinant(points: tuple[tuple[int, int], ...],
                triple: tuple[int, int, int]) -> int:
    i, j, k = triple
    xi, yi = points[i]
    xj, yj = points[j]
    xk, yk = points[k]
    return (xj - xi) * (yk - yi) - (yj - yi) * (xk - xi)


def point_mask(points: tuple[tuple[int, int], ...]) -> tuple[int, tuple[int, ...]] | None:
    values = tuple(determinant(points, triple) for triple in triples(len(points)))
    if any(value == 0 for value in values):
        return None
    mask = sum(int(value > 0) << index for index, value in enumerate(values))
    return mask, values


def frozen_fin_four_states(catalog: dict[str, object]) -> tuple[int, ...]:
    levels = catalog.get("levels")
    if not isinstance(levels, dict):
        raise ValueError("catalog has no levels object")
    level = levels.get("4")
    if not isinstance(level, dict):
        raise ValueError("catalog has no Fin4 level")
    states = level.get("states_hex")
    if not isinstance(states, list) or not all(isinstance(value, str) for value in states):
        raise ValueError("catalog Fin4 states are malformed")
    return tuple(int(value, 16) for value in states)


def search_fin_four(targets: tuple[int, ...], radius: int = 3) -> dict[int, dict[str, object]]:
    remaining = set(targets)
    found: dict[int, dict[str, object]] = {}
    alphabet = range(-radius, radius + 1)
    for heights in itertools.product(alphabet, repeat=4):
        if heights[0] != 0:
            continue
        points = tuple((index, height) for index, height in enumerate(heights))
        result = point_mask(points)
        if result is None:
            continue
        mask, determinants = result
        if mask not in remaining:
            continue
        found[mask] = {
            "determinants": list(determinants),
            "mask_hex": format(mask, "x"),
            "points": [list(point) for point in points],
        }
        remaining.remove(mask)
        if not remaining:
            return found
    missing = ",".join(format(mask, "x") for mask in sorted(remaining))
    raise RuntimeError(f"integer search did not realize masks: {missing}")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--radius", type=int, default=3)
    args = parser.parse_args()

    catalog = json.loads(args.catalog.read_text())
    targets = frozen_fin_four_states(catalog)
    if targets != (0, 1, 3, 7, 8, 12, 14, 15):
        raise ValueError(f"unexpected Fin4 catalog: {targets}")
    found = search_fin_four(targets, args.radius)
    document = {
        "catalog_sha256": sha256_file(args.catalog),
        "coordinate_domain": {
            "abscissae": [0, 1, 2, 3],
            "ordinate_radius": args.radius,
            "ordinate_zero_normalization": True,
            "search_order": "lexicographic heights",
        },
        "mask_convention": "lex triples; bit 1 iff determinant is positive",
        "n": 4,
        "realizations": [found[mask] for mask in targets],
        "triples": [list(triple) for triple in triples(4)],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")
    print(f"realized {len(found)} Fin4 masks in integer radius {args.radius}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
