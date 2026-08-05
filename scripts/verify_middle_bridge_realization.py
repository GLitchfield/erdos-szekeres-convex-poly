#!/usr/bin/env python3
"""Check a proposed middle-bridge realization with exact rational arithmetic."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from fractions import Fraction
from pathlib import Path


def parse_model(path: Path, variable_count: int) -> set[int]:
    assignment = {}
    for line in path.read_text().splitlines():
        if line.startswith("v "):
            for token in line.split()[1:]:
                value = int(token)
                if value:
                    assignment[abs(value)] = value > 0
    if any(index not in assignment for index in range(1, variable_count + 1)):
        raise SystemExit("incomplete SAT model")
    return {index for index, value in assignment.items() if value}


def rational(raw):
    return Fraction(int(raw["numerator"]), int(raw["denominator"]))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("result", type=Path)
    args = parser.parse_args()
    data = json.loads(args.result.read_text())
    if data["result"] != "FOUND" or not data["witness"]:
        raise SystemExit("result contains no realization witness")
    model_path = Path(data["model"])
    if hashlib.sha256(model_path.read_bytes()).hexdigest() != data["model_sha256"]:
        raise SystemExit("SAT model hash mismatch")
    triples = tuple(itertools.combinations(range(12), 3))
    left_turns = parse_model(model_path, len(triples))
    points = [
        (rational(point["x"]), rational(point["y"]))
        for point in data["witness"]["points"]
    ]
    if len(points) != 12:
        raise SystemExit("expected twelve points")
    if not all(points[index][0] < points[index + 1][0] for index in range(11)):
        raise SystemExit("x-coordinates are not strictly increasing")
    minimum = None
    for index, (i, j, k) in enumerate(triples, start=1):
        xi, yi = points[i]
        xj, yj = points[j]
        xk, yk = points[k]
        orientation = (xj - xi) * (yk - yi) - (yj - yi) * (xk - xi)
        signed = orientation if index in left_turns else -orientation
        if signed <= 0:
            raise SystemExit(f"orientation mismatch on {(i, j, k)}")
        minimum = signed if minimum is None else min(minimum, signed)
    print(json.dumps({
        "valid": True,
        "triples_checked": len(triples),
        "minimum_signed_orientation": {
            "numerator": minimum.numerator,
            "denominator": minimum.denominator,
        },
    }, sort_keys=True))


if __name__ == "__main__":
    main()
