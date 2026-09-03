#!/usr/bin/env python3
"""Freeze the exact Orchard-XOR v2 panel from authenticated source artifacts.

This builder only extracts coordinates and reconstructs the two admitted
sign-table controls.  It does not enumerate strong subsets, Orchard palettes,
or any outcome of the proposed discriminator.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
from typing import Any, Sequence


ROOT = Path(__file__).resolve().parents[1]
TASK_ID = "orchard-xor-four-fixture-v2"
PANEL_PROTOCOL = "orchard-xor-strict-panel-v2"

SOURCE_BINDINGS = {
    "AGENTS.md": "83bb11d556180c2fd9bab8a29ba928667a7ae69da029d370ad32dbcc28bcbb40",
    "docs/literature_review.md": "7167acc20276d928c45f8c8cb7a97304155271b2b6892e0ed0e414dc113a6a40",
    "runs/experiments/20260822-lcount-fin13/manifest.json": "93b76b26f0bb124b1a5ef2c1914d1ae0b2517b7582147f06f9fa5caba84d924f",
    "runs/agents/20260823-continuous-rolling-bootstrap/execution/equality16-acquisition/fixture.json": "5b59d9d1d2c060c398fa7159b8a1ebab238fd64b6cafc01480c237ab0ef946b9",
    "runs/experiments/20260818-open-world-math-pilot/binary-predecessor-split.json": "e0257283981b98c1019a299978e95fb19b6c8a9a57f08520aa3d0d8bcf3cdb59",
    "runs/experiments/20260818-open-world-math-pilot/binary-predecessor-split-n9.json": "610f29a723d3310385108c096be7ccf8fc7645b2511500d6a0afc45935784eed",
    "runs/agents/20260825-batch008-probes/execution/fd008-ternary-wl-v1/artifact.json": "b9f060b345c5a597413384432f75f8666104ad32dabaad2dc19c92f2919e7d9e",
    "ErdosSzekeres/Decomposable.lean": "96729bad53eb7b6a0e4824762eac0fc56c968e8469a9567fff70164aea35cba4",
    "ErdosSzekeres/StrongPredecessorBicoloring.lean": "19d3452f1213356ad8d1d0e6b9be86fe19ce84c7a2b7ff983f34b010e26015db",
}

EXPECTED_ACTUALS = {
    "fin8-record-1654": (8, 5, "c72803196d31fe52c6f85ea018cfb2043e989c3e5069551136be7984deb9070e"),
    "fin9-record-936": (9, 6, "e59bb6055267829cc2c0ede02c0f11f183d9e27ead53d4e0eb59ec7ae63b070e"),
    "ticket-0037-affine-bad-n13": (13, 6, "8902fdcef5ae402f4878c8543ceb944965cfef6dda981fbad5b014e657a39a80"),
    "pascal-row-d4-equality16-v1": (16, 6, "6f60e414a926da4c89b9e187e94862ebc7e8e4e274925be79c516c56cbd61e14"),
}

CONTROL_SPECS = {
    "ticket-0037-affine-bad-n13::fd008-relaxed": {
        "parent": "ticket-0037-affine-bad-n13",
        "source_hash": "3d970000131f9fa4d8b6063622c35396486d78fc130333dfa6037e53f6630865",
        "flips": [[0, 1, 2], [2, 3, 6], [0, 2, 3], [1, 2, 6]],
    },
    "pascal-row-d4-equality16-v1::fd008-relaxed": {
        "parent": "pascal-row-d4-equality16-v1",
        "source_hash": "c480941b6d1bf82a20ff7d01f15049e328e74c12363fb72309645f4ead01bb8b",
        "flips": [[0, 1, 5], [0, 2, 6], [0, 1, 2], [0, 5, 6]],
    },
}


class PanelBuildError(ValueError):
    """An authenticated source does not match the frozen v2 panel contract."""


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def load_bound(relative: str) -> dict[str, Any]:
    path = ROOT / relative
    expected = SOURCE_BINDINGS[relative]
    if not path.is_file() or file_sha256(path) != expected:
        raise PanelBuildError(f"source binding differs: {relative}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise PanelBuildError(f"cannot parse {relative}: {exc}") from exc
    if not isinstance(value, dict):
        raise PanelBuildError(f"source is not a JSON object: {relative}")
    return value


def authenticate_non_json_bindings() -> None:
    for relative in (
        "AGENTS.md",
        "docs/literature_review.md",
        "ErdosSzekeres/Decomposable.lean",
        "ErdosSzekeres/StrongPredecessorBicoloring.lean",
    ):
        path = ROOT / relative
        if not path.is_file() or file_sha256(path) != SOURCE_BINDINGS[relative]:
            raise PanelBuildError(f"source binding differs: {relative}")


def orientation(points: Sequence[Sequence[int]], a: int, b: int, c: int) -> int:
    ax, ay = points[a]
    bx, by = points[b]
    cx, cy = points[c]
    determinant = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax)
    if determinant == 0:
        raise PanelBuildError(f"degenerate source triple: {(a, b, c)}")
    return 1 if determinant > 0 else -1


def increasing_signs(points: Sequence[Sequence[int]]) -> list[int]:
    return [
        orientation(points, *triple)
        for triple in itertools.combinations(range(len(points)), 3)
    ]


def coordinate_case(case_id: str, points: Any) -> dict[str, Any]:
    n, target_k, expected_hash = EXPECTED_ACTUALS[case_id]
    if (
        not isinstance(points, list)
        or len(points) != n
        or any(
            not isinstance(point, list)
            or len(point) != 2
            or any(type(coordinate) is not int for coordinate in point)
            for point in points
        )
        or canonical_sha256(points) != expected_hash
    ):
        raise PanelBuildError(f"{case_id}: coordinate payload differs")
    increasing_signs(points)
    return {
        "case_id": case_id,
        "role": "actual",
        "model_tier": "realizable_coordinates",
        "target_k": target_k,
        "points": points,
    }


def build_panel() -> dict[str, Any]:
    authenticate_non_json_bindings()
    fin8 = load_bound(
        "runs/experiments/20260818-open-world-math-pilot/binary-predecessor-split.json"
    )
    fin9 = load_bound(
        "runs/experiments/20260818-open-world-math-pilot/binary-predecessor-split-n9.json"
    )
    lcount = load_bound("runs/experiments/20260822-lcount-fin13/manifest.json")
    equality = load_bound(
        "runs/agents/20260823-continuous-rolling-bootstrap/execution/equality16-acquisition/fixture.json"
    )
    fd008 = load_bound(
        "runs/agents/20260825-batch008-probes/execution/fd008-ternary-wl-v1/artifact.json"
    )

    fin8_record = fin8.get("first_not_covered_by_fixed_x_or_parity_rule")
    fin9_record = fin9.get("first_certificate")
    if not isinstance(fin8_record, dict) or fin8_record.get("record_index") != 1654:
        raise PanelBuildError("Fin8 record-1654 source identity differs")
    if not isinstance(fin9_record, dict) or fin9_record.get("record_index") != 936:
        raise PanelBuildError("Fin9 record-936 source identity differs")
    if lcount.get("point_digest_sha256") != EXPECTED_ACTUALS["ticket-0037-affine-bad-n13"][2]:
        raise PanelBuildError("Fin13 manifest point digest differs")
    if equality.get("fixture_id") != "pascal-row-d4-equality16-v1":
        raise PanelBuildError("equality16 fixture identity differs")

    actuals = [
        coordinate_case("fin8-record-1654", fin8_record.get("points")),
        coordinate_case("fin9-record-936", fin9_record.get("points")),
        coordinate_case("ticket-0037-affine-bad-n13", lcount.get("witness_points")),
        coordinate_case("pascal-row-d4-equality16-v1", equality.get("points")),
    ]
    by_id = {case["case_id"]: case for case in actuals}

    fixtures = fd008.get("fixtures")
    if not isinstance(fixtures, list):
        raise PanelBuildError("FD008 fixture array is missing")
    fd_by_id = {
        item.get("fixture_id"): item
        for item in fixtures
        if isinstance(item, dict) and isinstance(item.get("fixture_id"), str)
    }
    controls: list[dict[str, Any]] = []
    for case_id, spec in CONTROL_SPECS.items():
        parent_id = str(spec["parent"])
        parent = by_id[parent_id]
        source = fd_by_id.get(parent_id)
        if not isinstance(source, dict) or source.get("points") != parent["points"]:
            raise PanelBuildError(f"{case_id}: FD008 parent coordinates differ")
        source_control = source.get("control")
        if (
            not isinstance(source_control, dict)
            or source_control.get("eligible") is not True
            or source_control.get("model_tier")
            != "relaxed_nongeometric_sign_table"
            or source_control.get("key") != spec["flips"]
            or source_control.get("control_increasing_sign_bit_sha256")
            != spec["source_hash"]
        ):
            raise PanelBuildError(f"{case_id}: FD008 control binding differs")
        signs = increasing_signs(parent["points"])
        index = {
            tuple(triple): offset
            for offset, triple in enumerate(
                itertools.combinations(range(len(parent["points"])), 3)
            )
        }
        for triple in spec["flips"]:
            signs[index[tuple(triple)]] *= -1
        controls.append(
            {
                "case_id": case_id,
                "role": "control",
                "model_tier": "relaxed_nongeometric_sign_table",
                "eligible": True,
                "parent_case_id": parent_id,
                "target_k": parent["target_k"],
                "point_count": len(parent["points"]),
                "reported_source_sign_sha256": spec["source_hash"],
                "flip_triples": spec["flips"],
                "increasing_signs": signs,
            }
        )

    return {
        "schema_version": 2,
        "protocol": PANEL_PROTOCOL,
        "input_role": "panel",
        "task_id": TASK_ID,
        "source_bindings": SOURCE_BINDINGS,
        "cases": [*actuals, *controls],
    }


def write_once(path: Path, value: dict[str, Any]) -> None:
    resolved = path.resolve()
    try:
        relative = resolved.relative_to((ROOT / "runs" / "agents").resolve())
    except ValueError as exc:
        raise PanelBuildError("panel output must be under runs/agents") from exc
    if not relative.parts:
        raise PanelBuildError("panel output must be a file below runs/agents")
    encoded = json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    resolved.parent.mkdir(parents=True, exist_ok=True)
    try:
        with resolved.open("x", encoding="utf-8") as handle:
            handle.write(encoded)
    except FileExistsError as exc:
        if resolved.read_text(encoding="utf-8") != encoded:
            raise PanelBuildError("immutable panel output already has other bytes") from exc


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    panel = build_panel()
    output = args.output if args.output.is_absolute() else ROOT / args.output
    write_once(output, panel)
    print(
        json.dumps(
            {
                "path": output.resolve().relative_to(ROOT).as_posix(),
                "sha256": file_sha256(output.resolve()),
                "panel_core_sha256": canonical_sha256(panel),
                "case_count": len(panel["cases"]),
                "meaning": "authenticated input freeze only; discriminator not executed",
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
