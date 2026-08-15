#!/usr/bin/env python3
"""Compare rightmost extension cells of two realizations of each Fin5 type."""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import random


RANDOM_SEED = 314159
RANDOM_DRAW_LIMIT = 100_000


def triples(n: int) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(range(n), 3))


def pairs(n: int) -> tuple[tuple[int, int], ...]:
    return tuple(itertools.combinations(range(n), 2))


def determinant(points: tuple[tuple[int, int], ...], i: int, j: int, k: int) -> int:
    xi, yi = points[i]
    xj, yj = points[j]
    xk, yk = points[k]
    return (xj - xi) * (yk - yi) - (yj - yi) * (xk - xi)


def point_mask(points: tuple[tuple[int, int], ...]) -> int | None:
    values = [determinant(points, *triple) for triple in triples(len(points))]
    if any(value == 0 for value in values):
        return None
    return sum(int(value > 0) << index for index, value in enumerate(values))


def strict_one_variable_solution(inequalities: list[tuple[Fraction, Fraction]]) -> Fraction | None:
    lower: Fraction | None = None
    upper: Fraction | None = None
    for coefficient, constant in inequalities:
        if coefficient > 0:
            bound = -constant / coefficient
            lower = bound if lower is None or lower < bound else lower
        elif coefficient < 0:
            bound = -constant / coefficient
            upper = bound if upper is None or bound < upper else upper
        elif constant <= 0:
            return None
    if lower is not None and upper is not None:
        return (lower + upper) / 2 if lower < upper else None
    if lower is not None:
        return lower + 1
    if upper is not None:
        return upper - 1
    return Fraction(0)


def extension_witness(points: tuple[tuple[int, int], ...],
                      pair_mask: int) -> tuple[Fraction, Fraction] | None:
    lower: list[tuple[Fraction, Fraction]] = []
    upper: list[tuple[Fraction, Fraction]] = []
    x_constraints = [(Fraction(1), Fraction(-max(x for x, _ in points)))]
    for position, (i, j) in enumerate(pairs(len(points))):
        xi, yi = points[i]
        xj, yj = points[j]
        coefficient_x = -(yj - yi)
        coefficient_y = xj - xi
        constant = (yj - yi) * xi - (xj - xi) * yi
        if not pair_mask & (1 << position):
            coefficient_x = -coefficient_x
            coefficient_y = -coefficient_y
            constant = -constant
        if coefficient_y > 0:
            lower.append((Fraction(-coefficient_x, coefficient_y),
                          Fraction(-constant, coefficient_y)))
        elif coefficient_y < 0:
            upper.append((Fraction(-coefficient_x, coefficient_y),
                          Fraction(-constant, coefficient_y)))
        else:
            x_constraints.append((Fraction(coefficient_x), Fraction(constant)))
    for lower_slope, lower_offset in lower:
        for upper_slope, upper_offset in upper:
            x_constraints.append((upper_slope - lower_slope,
                                  upper_offset - lower_offset))
    x = strict_one_variable_solution(x_constraints)
    if x is None:
        return None
    lower_values = [slope * x + offset for slope, offset in lower]
    upper_values = [slope * x + offset for slope, offset in upper]
    lower_bound = max(lower_values) if lower_values else None
    upper_bound = min(upper_values) if upper_values else None
    if lower_bound is not None and upper_bound is not None:
        if not lower_bound < upper_bound:
            return None
        y = (lower_bound + upper_bound) / 2
    elif lower_bound is not None:
        y = lower_bound + 1
    elif upper_bound is not None:
        y = upper_bound - 1
    else:
        y = Fraction(0)
    return x, y


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def extension_rows(points: tuple[tuple[int, int], ...]) -> list[dict[str, object]]:
    result = []
    for pair_mask in range(1 << len(pairs(len(points)))):
        witness = extension_witness(points, pair_mask)
        if witness is None:
            continue
        result.append({
            "pair_mask_hex": format(pair_mask, "03x"),
            "witness": [fraction_text(witness[0]), fraction_text(witness[1])],
        })
    return result


def first_equal_x_realizations(targets: set[int]) -> dict[int, tuple[tuple[int, int], ...]]:
    found = {}
    for tail in itertools.product(range(-5, 6), repeat=4):
        points = tuple((index, height) for index, height in enumerate((0,) + tail))
        mask = point_mask(points)
        if mask in targets and mask not in found:
            found[mask] = points
        if len(found) == len(targets):
            return found
    raise RuntimeError("equal-x search did not cover every Fin5 parent")


def first_varied_realizations(targets: set[int]) -> tuple[
        dict[int, tuple[tuple[int, int], ...]], dict[int, int]]:
    generator = random.Random(RANDOM_SEED)
    found = {}
    draws = {}
    for draw in range(1, RANDOM_DRAW_LIMIT + 1):
        xs = [0]
        for _ in range(4):
            xs.append(xs[-1] + generator.randint(1, 30))
        raw_y = [generator.randint(-300, 300) for _ in range(5)]
        ys = [value - raw_y[0] for value in raw_y]
        points = tuple(zip(xs, ys))
        mask = point_mask(points)
        if mask in targets and mask not in found:
            found[mask] = points
            draws[mask] = draw
        if len(found) == len(targets):
            return found, draws
    raise RuntimeError("varied-x search did not cover every Fin5 parent")


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
    args = parser.parse_args()

    catalog = json.loads(args.catalog.read_text())
    fin_five = tuple(int(value, 16)
                     for value in catalog["levels"]["5"]["states_hex"])
    if len(fin_five) != 62:
        raise RuntimeError("unexpected Fin5 catalog")
    targets = set(fin_five)
    equal_x = first_equal_x_realizations(targets)
    varied, discovery_draws = first_varied_realizations(targets)
    rows = []
    sensitive = 0
    for mask in fin_five:
        first_extensions = extension_rows(equal_x[mask])
        second_extensions = extension_rows(varied[mask])
        first_masks = {row["pair_mask_hex"] for row in first_extensions}
        second_masks = {row["pair_mask_hex"] for row in second_extensions}
        differs = first_masks != second_masks
        sensitive += int(differs)
        rows.append({
            "equal_x": {
                "extensions": first_extensions,
                "points": [list(point) for point in equal_x[mask]],
            },
            "extension_sets_differ": differs,
            "mask_hex": format(mask, "03x"),
            "symmetric_difference": sorted(first_masks ^ second_masks),
            "varied_x": {
                "discovery_draw": discovery_draws[mask],
                "extensions": second_extensions,
                "points": [list(point) for point in varied[mask]],
            },
        })
    document = {
        "catalog_sha256": sha256_file(args.catalog),
        "cell_semantics": (
            "all strict sign vectors of the old pair lines in x > max parent x"
        ),
        "comparison": {
            "equal_x_domain": "x=0..4, y0=0, remaining y in [-5,5] lexicographic",
            "varied_x_draw_limit": RANDOM_DRAW_LIMIT,
            "varied_x_prng": "python-random-mt19937",
            "varied_x_seed": RANDOM_SEED,
        },
        "parents": rows,
        "summary": {
            "parents_checked": len(rows),
            "sensitive_parent_count": sensitive,
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")
    print(f"fixed-realization extension sets differ for {sensitive}/62 Fin5 parents")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
