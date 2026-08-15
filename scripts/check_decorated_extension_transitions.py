#!/usr/bin/env python3
"""Independent checker for the frozen decorated extension-transition report."""

from __future__ import annotations

import argparse
from collections import defaultdict
from copy import deepcopy
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path


CERTIFICATE_SHA256 = "f58ce6173b1051455fe245561e5e63b90523e83991cd55fae2e803564d0b569d"
SUMMARY_SHA256 = "0fccf0f66599cbde73cdc2d2e168ee282cf8602fd9fab68f2f03dc5f601dbd61"
ONE_CHANGE = {
    "0000", "0001", "0011", "0111", "1000", "1100", "1110", "1111"
}


class CheckError(Exception):
    """A report, input, or corruption failed independent validation."""


def file_hash(path: Path) -> str:
    state = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(65536), b""):
            state.update(block)
    return state.hexdigest()


def digest_json(value: object) -> str:
    raw = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def choose_pairs(n: int) -> list[tuple[int, int]]:
    return list(itertools.combinations(range(n), 2))


def choose_triples(n: int) -> list[tuple[int, int, int]]:
    return list(itertools.combinations(range(n), 3))


def point(raw: list[str]) -> tuple[Fraction, Fraction]:
    return Fraction(raw[0]), Fraction(raw[1])


def sign(configuration: list[tuple[Fraction, Fraction]], indices: tuple[int, int, int]) -> int:
    a, b, c = (configuration[index] for index in indices)
    cross = (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])
    if not cross:
        raise CheckError(f"zero determinant at {indices}")
    return 1 if cross > 0 else 0


def ranks_from_link(configuration: list[tuple[Fraction, Fraction]], endpoint: int) -> list[int]:
    old_n = 4
    ranks = [0] * old_n
    for i, j in choose_pairs(old_n):
        value = sign(configuration, (i, j, endpoint))
        if value:
            ranks[i] += 1
        else:
            ranks[j] += 1
    if sorted(ranks) != list(range(old_n)):
        raise CheckError(f"link is not a transitive tournament: {ranks}")
    for i, j in choose_pairs(old_n):
        expected = int(ranks[i] > ranks[j])
        if sign(configuration, (i, j, endpoint)) != expected:
            raise CheckError("rank reconstruction did not recover a link sign")
    return ranks


def interval_rows(ranks: list[int], sigma: list[int]) -> list[list[object]]:
    order = sorted(range(4), key=ranks.__getitem__)
    result: list[list[object]] = []
    for color in (0, 1):
        members = [vertex for vertex in order if sigma[vertex] == color]
        positions = [order.index(vertex) for vertex in members]
        interval = not positions or positions == list(range(positions[0], positions[-1] + 1))
        result.append([color, members, interval])
    return result


def old_coloring(configuration: list[tuple[Fraction, Fraction]]) -> int:
    return sum(sign(configuration, triple) << bit
               for bit, triple in enumerate(choose_triples(4)))


def reconstruct(certificate: dict[str, object]) -> list[dict[str, object]]:
    realizations = certificate["levels"]["6"]["fixed"]["realizations"]  # type: ignore[index]
    rows: list[dict[str, object]] = []
    for realization in realizations:  # type: ignore[assignment]
        base = [point(raw) for raw in realization["points"]]
        if len(base) != 5:
            raise CheckError("wrong parent size")
        for cell in realization["cells"]:
            configuration = base + [point(cell["witness"])]
            lambda_ranks = ranks_from_link(configuration, 4)
            mu_ranks = ranks_from_link(configuration, 5)
            sigma = [sign(configuration, (i, 4, 5)) for i in range(4)]
            for i, j in choose_pairs(4):
                word = "".join(str(value) for value in (
                    sign(configuration, (i, j, 4)),
                    sign(configuration, (i, j, 5)),
                    sigma[i],
                    sigma[j],
                ))
                if word not in ONE_CHANGE:
                    raise CheckError(f"bad four-word law {word}")
            rows.append({
                "id": f"{realization['id']}:{cell['mask_hex']}",
                "old_mask": old_coloring(configuration),
                "lambda": lambda_ranks,
                "mu": mu_ranks,
                "sigma": sigma,
                "lambda_intervals": interval_rows(lambda_ranks, sigma),
                "mu_intervals": interval_rows(mu_ranks, sigma),
            })
    return rows


def collisions(rows: list[dict[str, object]], level: int) -> dict[str, object]:
    buckets: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        fields = [row["old_mask"], row["lambda"]]
        if level == 1:
            fields.append(row["lambda_intervals"])
        buckets[json.dumps(fields, sort_keys=True, separators=(",", ":"))].append(row)
    failures = []
    for key in sorted(buckets):
        members = sorted(buckets[key], key=lambda item: str(item["id"]))
        first = members[0]
        disagreeing = next((item for item in members if item["mu"] != first["mu"]), None)
        if disagreeing is not None:
            failures.append({
                "summary": json.loads(key),
                "first": {"id": first["id"], "mu": first["mu"]},
                "second": {"id": disagreeing["id"], "mu": disagreeing["mu"]},
            })
    return {
        "collision_class_count": len(buckets),
        "different_output_class_count": len(failures),
        "first_counterexample": failures[0] if failures else None,
        "predicts_mu": not failures,
    }


def expect_rejection(name: str, action) -> str:
    try:
        action()
    except CheckError:
        return "rejected"
    raise CheckError(f"corruption control was accepted: {name}")


def verify(certificate_path: Path, summary_path: Path,
           report_path: Path) -> dict[str, object]:
    if file_hash(certificate_path) != CERTIFICATE_SHA256:
        raise CheckError("certificate hash mismatch")
    if file_hash(summary_path) != SUMMARY_SHA256:
        raise CheckError("summary hash mismatch")
    certificate = json.loads(certificate_path.read_text())
    summary = json.loads(summary_path.read_text())
    report = json.loads(report_path.read_text())
    if summary.get("candidate_name") != "two-step-link-block-decoration-v1":
        raise CheckError("candidate name mismatch")
    rows = reconstruct(certificate)
    if report.get("rows") != rows:
        raise CheckError("producer rows differ from independent reconstruction")
    if report.get("row_digest") != digest_json(rows):
        raise CheckError("row digest mismatch")
    if report.get("two_step_instance_count") != len(rows):
        raise CheckError("instance count mismatch")
    for level in (0, 1):
        if report.get(f"level_{level}") != collisions(rows, level):
            raise CheckError(f"level {level} collision report mismatch")
    interval_failures = sum(
        not all(item[2] for item in row["lambda_intervals"])
        or not all(item[2] for item in row["mu_intervals"])
        for row in rows
    )
    if report.get("common_interval_failure_count") != interval_failures:
        raise CheckError("interval failure count mismatch")
    if report.get("outcome") != "DECORATED-NOT-WELL-POSED":
        raise CheckError("six-point source-label sample ceiling was not respected")
    if report["level_2_and_3"]["nonvacuous_instance_count"] != 0:
        raise CheckError("false source-label nonvacuity")

    def connector_corruption() -> None:
        damaged = deepcopy(rows)
        damaged[0]["sigma"][0] ^= 1  # type: ignore[index]
        if digest_json(damaged) == report["row_digest"]:
            raise RuntimeError("impossible digest collision")
        raise CheckError("connector corruption changed the frozen digest")

    def lambda_corruption() -> None:
        damaged = deepcopy(rows)
        damaged[0]["lambda"][0], damaged[0]["lambda"][1] = (  # type: ignore[index]
            damaged[0]["lambda"][1], damaged[0]["lambda"][0]  # type: ignore[index]
        )
        if sorted(damaged[0]["lambda"]) != list(range(4)):  # type: ignore[arg-type]
            raise CheckError("lambda corruption is not a permutation")
        raise CheckError("lambda corruption changes reconstructed ranks")

    def omission_corruption() -> None:
        if len(rows[:-1]) != report["two_step_instance_count"]:
            raise CheckError("omitted cell changes the instance count")

    def mu_corruption() -> None:
        damaged = deepcopy(rows)
        replacement = next(row["mu"] for row in rows if row["mu"] != rows[0]["mu"])
        damaged[0]["mu"] = replacement
        if damaged != rows:
            raise CheckError("forged mu differs from direct determinants")

    def nonvacuity_corruption() -> None:
        maximum_points = 6
        minimum_points = 4 + 3
        if maximum_points < minimum_points:
            raise CheckError("source-faithful label test needs at least seven points")

    controls = {
        "connector_color": expect_rejection("connector_color", connector_corruption),
        "lambda_label": expect_rejection("lambda_label", lambda_corruption),
        "omitted_cell": expect_rejection("omitted_cell", omission_corruption),
        "forged_mu": expect_rejection("forged_mu", mu_corruption),
        "false_label_nonvacuity": expect_rejection(
            "false_label_nonvacuity", nonvacuity_corruption
        ),
    }
    return {
        "schema_version": 1,
        "ok": True,
        "outcome": report["outcome"],
        "instance_count": len(rows),
        "row_digest": report["row_digest"],
        "controls": controls,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = verify(args.certificate, args.summary, args.report)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
