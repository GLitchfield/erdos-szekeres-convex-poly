#!/usr/bin/env python3
"""Search for rational planar coordinates realizing a 12-point SAT model.

For fixed increasing x-coordinates, all requested orientation signs are strict
linear inequalities in the y-coordinates.  Deterministic projection searches
many integer x-gap patterns.  A result is evidence only after the separate
exact-rational checker accepts it; failure to find coordinates proves nothing.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from fractions import Fraction
from pathlib import Path

import numpy as np

from generate_signotope_state_sat import write_atomic


def parse_model(path: Path, variable_count: int) -> set[int]:
    assignment = {}
    for line in path.read_text().splitlines():
        if not line.startswith("v "):
            continue
        for token in line.split()[1:]:
            value = int(token)
            if value:
                assignment[abs(value)] = value > 0
    missing = [index for index in range(1, variable_count + 1)
               if index not in assignment]
    if missing:
        raise ValueError(f"model omits {len(missing)} triple variables")
    return {index for index, value in assignment.items() if value}


def inequality_matrix(xs, triples, left_turns, n):
    matrix = np.zeros((len(triples), n - 2), dtype=np.float64)
    for row_index, (i, j, k) in enumerate(triples):
        sign = 1.0 if row_index + 1 in left_turns else -1.0
        coefficients = {
            i: xs[k] - xs[j],
            j: -(xs[k] - xs[i]),
            k: xs[j] - xs[i],
        }
        for vertex, coefficient in coefficients.items():
            if 0 < vertex < n - 1:
                matrix[row_index, vertex - 1] += sign * coefficient
    norms = np.sum(matrix * matrix, axis=1)
    if np.any(norms == 0):
        raise ValueError("degenerate orientation inequality")
    return matrix, norms


def project(matrix, norms, iterations, rng):
    y = rng.normal(0.0, 0.01, matrix.shape[1])
    best = float("-inf")
    for iteration in range(iterations):
        margins = matrix @ y
        index = int(np.argmin(margins))
        minimum = float(margins[index])
        best = max(best, minimum)
        if minimum > 1e-5:
            return y, minimum, iteration + 1
        target = 1.0
        y += ((target - minimum) / norms[index]) * matrix[index]
        if (iteration + 1) % 2000 == 0:
            scale = max(1.0, float(np.max(np.abs(y))) / 1e6)
            y /= scale
    return None, best, iterations


def exact_witness(xs, interior_y, triples, left_turns, denominator):
    xq = [Fraction(int(value), 1) for value in xs]
    yq = [Fraction(0)] + [
        Fraction(int(round(float(value) * denominator)), denominator)
        for value in interior_y
    ] + [Fraction(0)]
    margins = []
    for index, (i, j, k) in enumerate(triples, start=1):
        orientation = ((xq[j] - xq[i]) * (yq[k] - yq[i]) -
                       (yq[j] - yq[i]) * (xq[k] - xq[i]))
        signed = orientation if index in left_turns else -orientation
        if signed <= 0:
            return None
        margins.append(signed)
    return xq, yq, min(margins)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("model", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--trials", type=int, default=500)
    parser.add_argument("--iterations", type=int, default=20000)
    parser.add_argument("--max-gap", type=int, default=1000)
    parser.add_argument("--denominator", type=int, default=10**9)
    args = parser.parse_args()
    n = 12
    all_triples = tuple(itertools.combinations(range(n), 3))
    left_turns = parse_model(args.model, len(all_triples))
    rng = np.random.default_rng(0)
    best = float("-inf")
    record = None
    for trial in range(args.trials):
        if trial == 0:
            gaps = np.ones(n - 1, dtype=np.int64)
        else:
            gaps = rng.integers(1, args.max_gap + 1, size=n - 1)
        xs = np.concatenate(([0], np.cumsum(gaps))).astype(np.int64)
        matrix, norms = inequality_matrix(xs, all_triples, left_turns, n)
        candidate, score, used = project(matrix, norms, args.iterations, rng)
        best = max(best, score)
        if candidate is None:
            continue
        exact = exact_witness(
            xs, candidate, all_triples, left_turns, args.denominator
        )
        if exact is None:
            continue
        xq, yq, margin = exact
        record = {
            "trial": trial,
            "iterations": used,
            "minimum_exact_signed_orientation": {
                "numerator": margin.numerator,
                "denominator": margin.denominator,
            },
            "points": [
                {
                    "x": {"numerator": x.numerator, "denominator": x.denominator},
                    "y": {"numerator": y.numerator, "denominator": y.denominator},
                }
                for x, y in zip(xq, yq)
            ],
        }
        break
    result = {
        "schema_version": 1,
        "search": "scripts/search_middle_bridge_realization.py",
        "model": str(args.model),
        "model_sha256": hashlib.sha256(args.model.read_bytes()).hexdigest(),
        "parameters": {
            "trials": args.trials,
            "iterations": args.iterations,
            "max_gap": args.max_gap,
            "denominator": args.denominator,
            "seed": 0,
        },
        "result": "FOUND" if record else "NOT_FOUND",
        "witness": record,
        "best_projection_score": best,
        "evidence_ceiling": (
            "exact rational witness after independent checking"
            if record else "heuristic search failure; no mathematical conclusion"
        ),
    }
    write_atomic(args.output, json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "result": result["result"],
        "trial": record["trial"] if record else None,
        "best_projection_score": best,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
