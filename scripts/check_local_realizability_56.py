#!/usr/bin/env python3
"""Independently check five/six finite sweep-realizability coverage."""

from __future__ import annotations

import argparse
from copy import deepcopy
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path


class VerificationError(Exception):
    pass


def triples(n: int) -> tuple[tuple[int, int, int], ...]:
    result = []
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                result.append((i, j, k))
    return tuple(result)


def width(n: int) -> int:
    return max(1, (len(triples(n)) + 3) // 4)


def show(mask: int, n: int) -> str:
    return format(mask, f"0{width(n)}x")


def at_most_one_change(word: tuple[bool, ...]) -> bool:
    return sum(left != right for left, right in zip(word, word[1:])) <= 1


def is_one_change(mask: int, n: int) -> bool:
    positions = {triple: index for index, triple in enumerate(triples(n))}
    for a, b, c, d in itertools.combinations(range(n), 4):
        word = tuple(bool(mask & (1 << positions[triple])) for triple in (
            (a, b, c), (a, b, d), (a, c, d), (b, c, d)))
        if not at_most_one_change(word):
            return False
    return True


def exhaustive_catalog(n: int) -> tuple[int, ...]:
    return tuple(mask for mask in range(1 << len(triples(n)))
                 if is_one_change(mask, n))


def independently_decomposable(mask: int, n: int) -> bool:
    triple_list = triples(n)
    positions = {triple: index for index, triple in enumerate(triple_list)}

    @lru_cache(maxsize=None)
    def visit(support: int) -> bool:
        if support.bit_count() == 1:
            return True
        submasks = [submask for submask in range(1, support)
                    if submask & support == submask and submask != support]
        for lower in submasks:
            upper = support ^ lower
            if upper == 0:
                continue
            compatible = True
            for i, j, k in triple_list:
                triple_support = (1 << i) | (1 << j) | (1 << k)
                if triple_support & support != triple_support:
                    continue
                if triple_support & lower == triple_support:
                    continue
                if triple_support & upper == triple_support:
                    continue
                actual = bool(mask & (1 << positions[i, j, k]))
                if actual != bool(lower & (1 << j)):
                    compatible = False
                    break
            if compatible and visit(lower) and visit(upper):
                return True
        return False

    return visit((1 << n) - 1)


def validate_tree(mask: int, n: int, node: object) -> int:
    if not isinstance(node, dict):
        raise VerificationError("malformed decomposition node")
    if "leaf" in node:
        leaf = node["leaf"]
        if not isinstance(leaf, int) or not 0 <= leaf < n:
            raise VerificationError("invalid leaf")
        support = 1 << leaf
        if node.get("support_hex") != format(support, "x"):
            raise VerificationError("leaf support mismatch")
        return support
    lower = validate_tree(mask, n, node.get("lower"))
    upper = validate_tree(mask, n, node.get("upper"))
    support = lower | upper
    if lower & upper:
        raise VerificationError("tree children overlap")
    if node.get("lower_support_hex") != format(lower, "x"):
        raise VerificationError("lower support mismatch")
    if node.get("upper_support_hex") != format(upper, "x"):
        raise VerificationError("upper support mismatch")
    if node.get("support_hex") != format(support, "x"):
        raise VerificationError("node support mismatch")
    positions = {triple: index for index, triple in enumerate(triples(n))}
    for i, j, k in triples(n):
        triple_support = (1 << i) | (1 << j) | (1 << k)
        if triple_support & support != triple_support:
            continue
        if triple_support & lower == triple_support:
            continue
        if triple_support & upper == triple_support:
            continue
        actual = bool(mask & (1 << positions[i, j, k]))
        if actual != bool(lower & (1 << j)):
            raise VerificationError("deep-below crossing mismatch")
    return support


def determinant(points: list[list[int]], triple: tuple[int, int, int]) -> int:
    i, j, k = triple
    xi, yi = points[i]
    xj, yj = points[j]
    xk, yk = points[k]
    return (xj - xi) * (yk - yi) - (yj - yi) * (xk - xi)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while chunk := source.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def catalog_level(catalog: dict[str, object], n: int) -> tuple[tuple[int, ...], dict[str, object]]:
    try:
        level = catalog["levels"][str(n)]  # type: ignore[index]
        states = tuple(int(value, 16) for value in level["states_hex"])
        annotations = level["annotations"]
    except (KeyError, TypeError, ValueError) as error:
        raise VerificationError(f"malformed Fin{n} catalog") from error
    if not isinstance(annotations, dict):
        raise VerificationError("malformed annotations")
    return states, annotations


def verify(document: dict[str, object], catalog: dict[str, object],
           catalog_hash: str) -> dict[str, object]:
    if document.get("catalog_sha256") != catalog_hash:
        raise VerificationError("catalog hash mismatch")
    certificates = document.get("decomposition_certificates")
    coordinates = document.get("nondecomposable_fin_six_realizations")
    if not isinstance(certificates, dict) or not isinstance(coordinates, list):
        raise VerificationError("missing coverage sections")
    decomposable_masks: dict[int, set[int]] = {}
    catalog_masks: dict[int, set[int]] = {}
    for n, expected_count in ((5, 62), (6, 908)):
        exhaustive = exhaustive_catalog(n)
        states, annotations = catalog_level(catalog, n)
        if states != exhaustive or len(states) != expected_count:
            raise VerificationError(f"Fin{n} catalog reconstruction mismatch")
        catalog_masks[n] = set(states)
        independently_true = {
            mask for mask in states if independently_decomposable(mask, n)
        }
        declared_true = {
            mask for mask in states
            if annotations[show(mask, n)]["decomposable"]  # type: ignore[index]
        }
        if independently_true != declared_true:
            raise VerificationError(f"Fin{n} decomposition annotations mismatch")
        rows = certificates.get(str(n))
        if not isinstance(rows, list):
            raise VerificationError(f"Fin{n} tree rows missing")
        seen = set()
        for row in rows:
            if not isinstance(row, dict) or not isinstance(row.get("mask_hex"), str):
                raise VerificationError("malformed tree row")
            mask = int(row["mask_hex"], 16)
            if mask in seen:
                raise VerificationError("duplicate tree mask")
            if validate_tree(mask, n, row.get("tree")) != (1 << n) - 1:
                raise VerificationError("tree does not cover the full support")
            seen.add(mask)
        if seen != independently_true:
            raise VerificationError(f"Fin{n} tree coverage mismatch")
        decomposable_masks[n] = seen

    coordinate_masks = []
    determinants_checked = 0
    for row in coordinates:
        if not isinstance(row, dict) or not isinstance(row.get("mask_hex"), str):
            raise VerificationError("malformed coordinate row")
        points = row.get("points")
        if not isinstance(points, list) or len(points) != 6:
            raise VerificationError("malformed Fin6 points")
        if any(not isinstance(point, list) or len(point) != 2 for point in points):
            raise VerificationError("malformed coordinate pair")
        xs = [point[0] for point in points]
        if any(not isinstance(value, int) for value in xs):
            raise VerificationError("nonintegral coordinate")
        if any(left >= right for left, right in zip(xs, xs[1:])):
            raise VerificationError("sweep order is not strict")
        determinants = [determinant(points, triple) for triple in triples(6)]
        if any(value == 0 for value in determinants):
            raise VerificationError("coordinate certificate is degenerate")
        if row.get("determinants") != determinants:
            raise VerificationError("determinant ledger mismatch")
        mask = sum(int(value > 0) << index
                   for index, value in enumerate(determinants))
        if row["mask_hex"] != show(mask, 6):
            raise VerificationError("coordinate color mismatch")
        coordinate_masks.append(mask)
        determinants_checked += len(determinants)
    if len(coordinate_masks) != len(set(coordinate_masks)):
        raise VerificationError("duplicate coordinate mask")
    coordinate_set = set(coordinate_masks)
    if coordinate_set & decomposable_masks[6]:
        raise VerificationError("coordinates improperly duplicate decomposable coverage")
    if coordinate_set | decomposable_masks[6] != catalog_masks[6]:
        raise VerificationError("Fin6 union coverage mismatch")
    if len(decomposable_masks[5]) != 62 or len(decomposable_masks[6]) != 718:
        raise VerificationError("unexpected decomposition counts")
    if len(coordinate_set) != 190:
        raise VerificationError("unexpected coordinate count")
    return {
        "decomposition_trees_checked": 62 + 718,
        "determinants_checked": determinants_checked,
        "fin5_coverage": len(decomposable_masks[5]),
        "fin6_coverage": len(coordinate_set | decomposable_masks[6]),
    }


def rejects(document: dict[str, object], catalog: dict[str, object],
            catalog_hash: str) -> bool:
    try:
        verify(document, catalog, catalog_hash)
    except VerificationError:
        return True
    return False


def corruption_controls(document: dict[str, object], catalog: dict[str, object],
                        catalog_hash: str) -> dict[str, bool]:
    tree = deepcopy(document)
    tree["decomposition_certificates"]["5"][0]["tree"][  # type: ignore[index]
        "lower_support_hex"] = "0"
    coordinate = deepcopy(document)
    coordinate["nondecomposable_fin_six_realizations"][0][  # type: ignore[index]
        "points"][0] = coordinate["nondecomposable_fin_six_realizations"][0][  # type: ignore[index]
            "points"][1]
    color = deepcopy(document)
    color["nondecomposable_fin_six_realizations"][0][  # type: ignore[index]
        "mask_hex"] = "00000"
    omitted = deepcopy(document)
    omitted["nondecomposable_fin_six_realizations"].pop()  # type: ignore[union-attr]
    duplicated = deepcopy(document)
    duplicated["nondecomposable_fin_six_realizations"].append(  # type: ignore[union-attr]
        deepcopy(duplicated["nondecomposable_fin_six_realizations"][0]))  # type: ignore[index]
    sweep = deepcopy(document)
    sweep["nondecomposable_fin_six_realizations"][0]["points"][1][0] = (  # type: ignore[index]
        sweep["nondecomposable_fin_six_realizations"][0]["points"][0][0])  # type: ignore[index]
    return {
        "color_change_rejected": rejects(color, catalog, catalog_hash),
        "coordinate_change_rejected": rejects(coordinate, catalog, catalog_hash),
        "duplicated_mask_rejected": rejects(duplicated, catalog, catalog_hash),
        "omitted_mask_rejected": rejects(omitted, catalog, catalog_hash),
        "sweep_order_rejected": rejects(sweep, catalog, catalog_hash),
        "tree_change_rejected": rejects(tree, catalog, catalog_hash),
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
    print("Fin5/Fin6 coverage verified independently; all corruptions rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
