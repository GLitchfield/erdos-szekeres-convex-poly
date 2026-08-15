#!/usr/bin/env python3
"""Analyze the frozen two-step decorated extension summary through six points."""

from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path


CERTIFICATE_SHA256 = "f58ce6173b1051455fe245561e5e63b90523e83991cd55fae2e803564d0b569d"
SUMMARY_SHA256 = "0fccf0f66599cbde73cdc2d2e168ee282cf8602fd9fab68f2f03dc5f601dbd61"
ALLOWED_WORDS = {
    (0, 0, 0, 0),
    (0, 0, 0, 1),
    (0, 0, 1, 1),
    (0, 1, 1, 1),
    (1, 0, 0, 0),
    (1, 1, 0, 0),
    (1, 1, 1, 0),
    (1, 1, 1, 1),
}


class AnalysisError(Exception):
    """The frozen data or a claimed transition is inconsistent."""


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while chunk := source.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_sha256(value: object) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def parse_point(row: list[str]) -> tuple[Fraction, Fraction]:
    if len(row) != 2:
        raise AnalysisError("point does not have two coordinates")
    return Fraction(row[0]), Fraction(row[1])


def orientation(points: tuple[tuple[Fraction, Fraction], ...],
                i: int, j: int, k: int) -> int:
    xi, yi = points[i]
    xj, yj = points[j]
    xk, yk = points[k]
    determinant = (xj - xi) * (yk - yi) - (yj - yi) * (xk - xi)
    if determinant == 0:
        raise AnalysisError(f"degenerate triple {(i, j, k)}")
    return int(determinant > 0)


def pairs(n: int) -> tuple[tuple[int, int], ...]:
    return tuple(itertools.combinations(range(n), 2))


def triples(n: int) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(range(n), 3))


def inversion_mask(permutation: tuple[int, ...]) -> int:
    return sum(
        int(permutation[i] > permutation[j]) << bit
        for bit, (i, j) in enumerate(pairs(len(permutation)))
    )


def mask_to_permutation(n: int, mask: int) -> tuple[int, ...]:
    matches = [
        permutation
        for permutation in itertools.permutations(range(n))
        if inversion_mask(permutation) == mask
    ]
    if len(matches) != 1:
        raise AnalysisError(
            f"mask {mask} on {n} vertices has {len(matches)} permutation witnesses"
        )
    return matches[0]


def link_mask(points: tuple[tuple[Fraction, Fraction], ...],
              old_n: int, endpoint: int) -> int:
    return sum(
        orientation(points, i, j, endpoint) << bit
        for bit, (i, j) in enumerate(pairs(old_n))
    )


def old_mask(points: tuple[tuple[Fraction, Fraction], ...], old_n: int) -> int:
    return sum(
        orientation(points, i, j, k) << bit
        for bit, (i, j, k) in enumerate(triples(old_n))
    )


def vertex_order(permutation: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(sorted(range(len(permutation)), key=permutation.__getitem__))


def interval_encoding(permutation: tuple[int, ...],
                      sigma: tuple[int, ...]) -> tuple[object, ...]:
    order = vertex_order(permutation)
    positions = {vertex: position for position, vertex in enumerate(order)}
    rows = []
    for color in (0, 1):
        members = tuple(vertex for vertex in order if sigma[vertex] == color)
        member_positions = tuple(positions[vertex] for vertex in members)
        is_interval = not member_positions or member_positions == tuple(
            range(member_positions[0], member_positions[-1] + 1)
        )
        rows.append((color, members, is_interval))
    return tuple(rows)


def two_step_row(realization: dict[str, object],
                 cell: dict[str, object]) -> dict[str, object]:
    parent_points = tuple(parse_point(row) for row in realization["points"])  # type: ignore[arg-type]
    witness = parse_point(cell["witness"])  # type: ignore[arg-type]
    if len(parent_points) != 5:
        raise AnalysisError("six-point level must have five parent points")
    points = parent_points + (witness,)
    old_n = 4
    lambda_mask = link_mask(points, old_n, 4)
    mu_mask = link_mask(points, old_n, 5)
    lambda_permutation = mask_to_permutation(old_n, lambda_mask)
    mu_permutation = mask_to_permutation(old_n, mu_mask)
    sigma = tuple(orientation(points, i, 4, 5) for i in range(old_n))
    words = []
    for i, j in pairs(old_n):
        word = (
            orientation(points, i, j, 4),
            orientation(points, i, j, 5),
            sigma[i],
            sigma[j],
        )
        if word not in ALLOWED_WORDS:
            raise AnalysisError(f"non-OneChange two-step word {word}")
        words.append(word)
    lambda_intervals = interval_encoding(lambda_permutation, sigma)
    mu_intervals = interval_encoding(mu_permutation, sigma)
    return {
        "id": f"{realization['id']}:{cell['mask_hex']}",
        "old_mask": old_mask(points, old_n),
        "lambda": lambda_permutation,
        "mu": mu_permutation,
        "sigma": sigma,
        "lambda_intervals": lambda_intervals,
        "mu_intervals": mu_intervals,
        "four_words": tuple(words),
    }


def jsonable(value: object) -> object:
    if isinstance(value, tuple):
        return [jsonable(item) for item in value]
    if isinstance(value, list):
        return [jsonable(item) for item in value]
    if isinstance(value, dict):
        return {key: jsonable(item) for key, item in value.items()}
    return value


def collision_report(rows: list[dict[str, object]], level: int) -> dict[str, object]:
    groups: dict[tuple[object, ...], list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        if level == 0:
            key = (row["old_mask"], row["lambda"])
        elif level == 1:
            key = (row["old_mask"], row["lambda"], row["lambda_intervals"])
        else:
            raise AnalysisError(f"unsupported collision level {level}")
        groups[key].append(row)
    bad = []
    for key, members in sorted(
            groups.items(),
            key=lambda item: json.dumps(
                jsonable(item[0]), sort_keys=True, separators=(",", ":")
            )):
        outputs = {member["mu"] for member in members}
        if len(outputs) > 1:
            ordered = sorted(members, key=lambda member: str(member["id"]))
            first = ordered[0]
            second = next(member for member in ordered if member["mu"] != first["mu"])
            bad.append({
                "summary": jsonable(key),
                "first": {"id": first["id"], "mu": jsonable(first["mu"])},
                "second": {"id": second["id"], "mu": jsonable(second["mu"])},
            })
    return {
        "collision_class_count": len(groups),
        "different_output_class_count": len(bad),
        "first_counterexample": bad[0] if bad else None,
        "predicts_mu": not bad,
    }


def produce(certificate_path: Path, summary_path: Path) -> dict[str, object]:
    if sha256_file(certificate_path) != CERTIFICATE_SHA256:
        raise AnalysisError("atlas certificate hash changed")
    if sha256_file(summary_path) != SUMMARY_SHA256:
        raise AnalysisError("frozen summary hash changed")
    certificate = json.loads(certificate_path.read_text())
    summary = json.loads(summary_path.read_text())
    if summary.get("candidate_name") != "two-step-link-block-decoration-v1":
        raise AnalysisError("unexpected summary candidate")
    fixed = certificate["levels"]["6"]["fixed"]
    rows = [
        two_step_row(realization, cell)
        for realization in fixed["realizations"]
        for cell in realization["cells"]
    ]
    common_interval_failures = [
        row["id"]
        for row in rows
        if not all(item[2] for item in row["lambda_intervals"])
        or not all(item[2] for item in row["mu_intervals"])
    ]
    level_zero = collision_report(rows, 0)
    level_one = collision_report(rows, 1)
    label_nonvacuous_instances = 0
    minimum_label_instance_size = 7
    if label_nonvacuous_instances == 0:
        outcome = "DECORATED-NOT-WELL-POSED"
    elif level_one["predicts_mu"]:
        outcome = "DECORATED-COMPRESS"
    else:
        outcome = "DECORATED-LABEL-LOSS"
    compact_rows = [
        {
            "id": row["id"],
            "old_mask": row["old_mask"],
            "lambda": jsonable(row["lambda"]),
            "mu": jsonable(row["mu"]),
            "sigma": jsonable(row["sigma"]),
            "lambda_intervals": jsonable(row["lambda_intervals"]),
            "mu_intervals": jsonable(row["mu_intervals"]),
        }
        for row in rows
    ]
    return {
        "schema_version": 1,
        "outcome": outcome,
        "certificate_sha256": CERTIFICATE_SHA256,
        "frozen_summary_sha256": SUMMARY_SHA256,
        "two_step_instance_count": len(rows),
        "realization_count": len(fixed["realizations"]),
        "four_word_law_passed": True,
        "common_interval_failure_count": len(common_interval_failures),
        "first_common_interval_failure": (
            common_interval_failures[0] if common_interval_failures else None
        ),
        "level_0": level_zero,
        "level_1": level_one,
        "level_2_and_3": {
            "nonvacuous_instance_count": label_nonvacuous_instances,
            "minimum_total_points_for_source_faithful_test": minimum_label_instance_size,
            "reason": (
                "S015 labels need three non-core points in one spike of a convex "
                "core with at least four distinct vertices; the admitted atlas ends at six"
            ),
        },
        "omits_atomic_wiring": True,
        "row_digest": canonical_sha256(compact_rows),
        "rows": compact_rows,
        "claims": {
            "proof_movement": "neutral",
            "n7_opened": False,
            "decorated_mechanism_refuted": False,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = produce(args.certificate, args.summary)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
