#!/usr/bin/env python3
"""Independently replay fixed-realization rightmost extension cells."""

from __future__ import annotations

import argparse
from copy import deepcopy
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path


class VerificationError(Exception):
    pass


def triples(n: int) -> tuple[tuple[int, int, int], ...]:
    return tuple((i, j, k) for i in range(n)
                 for j in range(i + 1, n) for k in range(j + 1, n))


def pairs(n: int) -> tuple[tuple[int, int], ...]:
    return tuple((i, j) for i in range(n) for j in range(i + 1, n))


def area(points: list[list[int]], i: int, j: int, k: int) -> int:
    return ((points[j][0] - points[i][0]) * (points[k][1] - points[i][1]) -
            (points[j][1] - points[i][1]) * (points[k][0] - points[i][0]))


def coloring(points: list[list[int]]) -> int:
    values = [area(points, *triple) for triple in triples(len(points))]
    if any(value == 0 for value in values):
        raise VerificationError("parent realization is degenerate")
    return sum(int(value > 0) << position
               for position, value in enumerate(values))


def parse_fraction(text: object) -> Fraction:
    if not isinstance(text, str):
        raise VerificationError("malformed rational witness")
    try:
        return Fraction(text)
    except (ValueError, ZeroDivisionError) as error:
        raise VerificationError("malformed rational witness") from error


def signed_inequalities(points: list[list[int]], pair_mask: int) -> list[
        tuple[Fraction, Fraction, Fraction]]:
    inequalities = [(Fraction(1), Fraction(0), Fraction(-max(p[0] for p in points)))]
    for position, (i, j) in enumerate(pairs(len(points))):
        xi, yi = points[i]
        xj, yj = points[j]
        row = [Fraction(-(yj - yi)), Fraction(xj - xi),
               Fraction((yj - yi) * xi - (xj - xi) * yi)]
        if not pair_mask & (1 << position):
            row = [-value for value in row]
        inequalities.append(tuple(row))
    return inequalities


def witness_satisfies(points: list[list[int]], pair_mask: int,
                      witness: list[object]) -> bool:
    if len(witness) != 2:
        return False
    x, y = (parse_fraction(value) for value in witness)
    return all(a * x + b * y + c > 0
               for a, b, c in signed_inequalities(points, pair_mask))


def feasible(points: list[list[int]], pair_mask: int) -> bool:
    inequalities = signed_inequalities(points, pair_mask)
    lower_y: list[tuple[Fraction, Fraction]] = []
    upper_y: list[tuple[Fraction, Fraction]] = []
    x_rows: list[tuple[Fraction, Fraction]] = []
    for a, b, c in inequalities:
        if b > 0:
            lower_y.append((-a / b, -c / b))
        elif b < 0:
            upper_y.append((-a / b, -c / b))
        else:
            x_rows.append((a, c))
    for lower_slope, lower_constant in lower_y:
        for upper_slope, upper_constant in upper_y:
            x_rows.append((upper_slope - lower_slope,
                           upper_constant - lower_constant))
    lower_x: Fraction | None = None
    upper_x: Fraction | None = None
    for coefficient, constant in x_rows:
        if coefficient == 0:
            if constant <= 0:
                return False
        elif coefficient > 0:
            boundary = -constant / coefficient
            lower_x = boundary if lower_x is None or lower_x < boundary else lower_x
        else:
            boundary = -constant / coefficient
            upper_x = boundary if upper_x is None or boundary < upper_x else upper_x
    return not (lower_x is not None and upper_x is not None and lower_x >= upper_x)


def complete_extension_set(points: list[list[int]]) -> set[int]:
    return {mask for mask in range(1 << len(pairs(len(points))))
            if feasible(points, mask)}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while chunk := source.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def verify(document: dict[str, object], catalog: dict[str, object],
           catalog_hash: str) -> dict[str, object]:
    if document.get("catalog_sha256") != catalog_hash:
        raise VerificationError("catalog hash mismatch")
    expected_parents = tuple(int(value, 16)
                             for value in catalog["levels"]["5"]["states_hex"])
    fin_six = {int(value, 16)
               for value in catalog["levels"]["6"]["states_hex"]}
    rows = document.get("parents")
    if not isinstance(rows, list) or len(rows) != len(expected_parents):
        raise VerificationError("parent rows missing")
    seen = []
    sensitive = 0
    extension_cells = 0
    for row, expected_mask in zip(rows, expected_parents):
        if not isinstance(row, dict) or row.get("mask_hex") != format(expected_mask, "03x"):
            raise VerificationError("parent order mismatch")
        extension_sets = []
        for key in ("equal_x", "varied_x"):
            realization = row.get(key)
            if not isinstance(realization, dict):
                raise VerificationError("realization missing")
            points = realization.get("points")
            extension_rows = realization.get("extensions")
            if not isinstance(points, list) or not isinstance(extension_rows, list):
                raise VerificationError("malformed realization")
            if len(points) != 5 or any(len(point) != 2 for point in points):
                raise VerificationError("malformed parent points")
            if any(left[0] >= right[0] for left, right in zip(points, points[1:])):
                raise VerificationError("parent sweep order is not strict")
            if coloring(points) != expected_mask:
                raise VerificationError("two realizations do not share the parent mask")
            complete = complete_extension_set(points)
            claimed = []
            for extension in extension_rows:
                if not isinstance(extension, dict):
                    raise VerificationError("malformed extension row")
                pair_mask = int(extension["pair_mask_hex"], 16)
                if not witness_satisfies(points, pair_mask, extension["witness"]):
                    raise VerificationError("extension witness fails")
                claimed.append(pair_mask)
                child_points = points + [[parse_fraction(extension["witness"][0]),
                                          parse_fraction(extension["witness"][1])]]
                child_mask = coloring(child_points)  # type: ignore[arg-type]
                if child_mask not in fin_six:
                    raise VerificationError("extension does not enter the Fin6 catalog")
            if len(claimed) != len(set(claimed)) or set(claimed) != complete:
                raise VerificationError("extension-cell set is incomplete")
            extension_sets.append(complete)
            extension_cells += len(complete)
        differs = extension_sets[0] != extension_sets[1]
        symmetric_difference = sorted(extension_sets[0] ^ extension_sets[1])
        if row.get("extension_sets_differ") != differs:
            raise VerificationError("sensitivity verdict mismatch")
        if row.get("symmetric_difference") != [format(mask, "03x")
                                                for mask in symmetric_difference]:
            raise VerificationError("symmetric difference mismatch")
        sensitive += int(differs)
        seen.append(expected_mask)
    if tuple(seen) != expected_parents:
        raise VerificationError("parent coverage mismatch")
    summary = document.get("summary")
    if not isinstance(summary, dict) or summary.get("sensitive_parent_count") != sensitive:
        raise VerificationError("summary mismatch")
    if sensitive == 0:
        raise VerificationError("no fixed-realization sensitivity witness")
    return {
        "extension_cells_checked": extension_cells,
        "parents_checked": len(seen),
        "sensitive_parent_count": sensitive,
    }


def rejects(document: dict[str, object], catalog: dict[str, object],
            catalog_hash: str) -> bool:
    try:
        verify(document, catalog, catalog_hash)
    except (VerificationError, KeyError, TypeError, ValueError):
        return True
    return False


def corruption_controls(document: dict[str, object], catalog: dict[str, object],
                        catalog_hash: str) -> dict[str, bool]:
    coordinate = deepcopy(document)
    coordinate["parents"][0]["equal_x"]["points"][1] = [0, 0]  # type: ignore[index]
    extension = deepcopy(document)
    extension["parents"][0]["equal_x"]["extensions"][0][  # type: ignore[index]
        "pair_mask_hex"] = "3ff"
    witness = deepcopy(document)
    witness["parents"][0]["equal_x"]["extensions"][0][  # type: ignore[index]
        "witness"][0] = "0/1"
    omitted = deepcopy(document)
    omitted["parents"][0]["equal_x"]["extensions"].pop()  # type: ignore[index]
    verdict = deepcopy(document)
    verdict["parents"][0]["extension_sets_differ"] = not (  # type: ignore[index]
        verdict["parents"][0]["extension_sets_differ"])  # type: ignore[index]
    return {
        "coordinate_change_rejected": rejects(coordinate, catalog, catalog_hash),
        "extension_mask_rejected": rejects(extension, catalog, catalog_hash),
        "omitted_cell_rejected": rejects(omitted, catalog, catalog_hash),
        "verdict_flip_rejected": rejects(verdict, catalog, catalog_hash),
        "witness_change_rejected": rejects(witness, catalog, catalog_hash),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()

    catalog = json.loads(args.catalog.read_text())
    document = json.loads(args.certificate.read_text())
    catalog_hash = sha256_file(args.catalog)
    positive = verify(document, catalog, catalog_hash)
    controls = corruption_controls(document, catalog, catalog_hash)
    if not all(controls.values()):
        raise VerificationError(f"corruption control escaped: {controls}")
    report = {
        "certificate_sha256": sha256_file(args.certificate),
        "controls": controls,
        "ok": True,
        "positive": positive,
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print("fixed-realization extension sensitivity verified independently")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
