#!/usr/bin/env python3
"""Independently verify exact finite sweep-realizability certificates."""

from __future__ import annotations

import argparse
from copy import deepcopy
import hashlib
import itertools
import json
from pathlib import Path


EXPECTED_COORDINATES = {
    "0": [[0, 0], [1, 0], [2, -1], [3, -3]],
    "1": [[0, 0], [1, 0], [2, 1], [3, -3]],
    "3": [[0, 0], [1, -3], [2, -1], [3, -3]],
    "7": [[0, 0], [1, -3], [2, -2], [3, -2]],
    "8": [[0, 0], [1, 1], [2, -1], [3, -2]],
    "c": [[0, 0], [1, 0], [2, -3], [3, -3]],
    "e": [[0, 0], [1, -1], [2, -3], [3, -2]],
    "f": [[0, 0], [1, -3], [2, -3], [3, -2]],
}


class VerificationError(Exception):
    pass


def all_triples(n: int) -> tuple[tuple[int, int, int], ...]:
    result: list[tuple[int, int, int]] = []
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                result.append((i, j, k))
    return tuple(result)


def at_most_one_change(word: tuple[bool, ...]) -> bool:
    changes = 0
    for left, right in zip(word, word[1:]):
        if left != right:
            changes += 1
    return changes <= 1


def exhaustive_fin_four() -> tuple[int, ...]:
    accepted = []
    for mask in range(16):
        word = tuple(bool(mask & (1 << index)) for index in range(4))
        if at_most_one_change(word):
            accepted.append(mask)
    return tuple(accepted)


def determinant(points: list[list[int]], triple: tuple[int, int, int]) -> int:
    i, j, k = triple
    xi, yi = points[i]
    xj, yj = points[j]
    xk, yk = points[k]
    return (xj - xi) * (yk - yi) - (yj - yi) * (xk - xi)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while True:
            chunk = source.read(1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
    return digest.hexdigest()


def catalog_states(catalog: dict[str, object]) -> tuple[int, ...]:
    try:
        raw = catalog["levels"]["4"]["states_hex"]  # type: ignore[index]
        return tuple(int(value, 16) for value in raw)  # type: ignore[arg-type]
    except (KeyError, TypeError, ValueError) as error:
        raise VerificationError("malformed catalog") from error


def verify(document: dict[str, object], catalog: dict[str, object],
           catalog_hash: str) -> dict[str, object]:
    if document.get("n") != 4:
        raise VerificationError("certificate is not Fin4")
    if document.get("catalog_sha256") != catalog_hash:
        raise VerificationError("catalog hash mismatch")
    expected_masks = exhaustive_fin_four()
    if catalog_states(catalog) != expected_masks:
        raise VerificationError("frozen catalog differs from exhaustive reconstruction")
    if document.get("triples") != [list(triple) for triple in all_triples(4)]:
        raise VerificationError("triple order mismatch")
    rows = document.get("realizations")
    if not isinstance(rows, list):
        raise VerificationError("realizations are missing")
    masks: list[int] = []
    for row in rows:
        if not isinstance(row, dict):
            raise VerificationError("malformed realization row")
        mask_hex = row.get("mask_hex")
        points = row.get("points")
        claimed_determinants = row.get("determinants")
        if not isinstance(mask_hex, str) or not isinstance(points, list):
            raise VerificationError("malformed mask or points")
        if points != EXPECTED_COORDINATES.get(mask_hex):
            raise VerificationError("coordinate certificate differs from Lean witness")
        if len(points) != 4 or any(not isinstance(point, list) or len(point) != 2
                                   for point in points):
            raise VerificationError("malformed point list")
        xs = [point[0] for point in points]
        if any(not isinstance(value, int) for value in xs):
            raise VerificationError("nonintegral abscissa")
        if any(xs[index] >= xs[index + 1] for index in range(3)):
            raise VerificationError("broken strict sweep order")
        determinants = [determinant(points, triple) for triple in all_triples(4)]
        if any(value == 0 for value in determinants):
            raise VerificationError("degenerate triple")
        if claimed_determinants != determinants:
            raise VerificationError("determinant ledger mismatch")
        mask = sum(int(value > 0) << index
                   for index, value in enumerate(determinants))
        if mask_hex != format(mask, "x"):
            raise VerificationError("color mask mismatch")
        masks.append(mask)
    if len(masks) != len(set(masks)):
        raise VerificationError("duplicate mask")
    if tuple(masks) != expected_masks:
        raise VerificationError("omitted, inserted, or reordered mask")
    return {
        "determinants_checked": len(rows) * 4,
        "mask_count": len(masks),
        "masks_hex": [format(mask, "x") for mask in masks],
    }


def expect_rejected(document: dict[str, object], catalog: dict[str, object],
                    catalog_hash: str) -> bool:
    try:
        verify(document, catalog, catalog_hash)
    except VerificationError:
        return True
    return False


def corruption_controls(document: dict[str, object], catalog: dict[str, object],
                        catalog_hash: str) -> dict[str, bool]:
    coordinate = deepcopy(document)
    coordinate["realizations"][0]["points"][0][1] += 1  # type: ignore[index]
    color = deepcopy(document)
    color["realizations"][0]["mask_hex"] = "1"  # type: ignore[index]
    omitted = deepcopy(document)
    omitted["realizations"].pop()  # type: ignore[union-attr]
    duplicated = deepcopy(document)
    duplicated["realizations"].append(  # type: ignore[union-attr]
        deepcopy(duplicated["realizations"][0]))  # type: ignore[index]
    sweep = deepcopy(document)
    sweep["realizations"][0]["points"][1][0] = 0  # type: ignore[index]
    return {
        "color_change_rejected": expect_rejected(color, catalog, catalog_hash),
        "coordinate_change_rejected": expect_rejected(
            coordinate, catalog, catalog_hash),
        "duplicated_mask_rejected": expect_rejected(duplicated, catalog, catalog_hash),
        "omitted_mask_rejected": expect_rejected(omitted, catalog, catalog_hash),
        "sweep_order_rejected": expect_rejected(sweep, catalog, catalog_hash),
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
    print("Fin4 exact realizability certificate verified; all corruptions rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
