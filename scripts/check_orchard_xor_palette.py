#!/usr/bin/env python3
"""Exact guarded worker for the two-deletion Orchard-XOR palette.

The worker is deliberately self-contained.  A first run consumes exactly one
panel and one event template through repeated ``--input`` operands and writes a
canonical artifact to an inherited result descriptor.  Replay consumes that
artifact plus the same raw inputs, cold-reconstructs both independent engines,
and emits the normalized event result on stdout.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import os
from pathlib import Path
import sys
from typing import Callable, Iterable, Sequence


TASK_ID = "orchard-xor-four-fixture-v2"
SEMANTIC_CONTRACT_ID = "two-deletion-orchard-xor-strong-predicate-v2"
PRODUCER_ID = "orchard-xor-producer-separator-count-strong-quad-v2"
CHECKER_ID = "orchard-xor-checker-line-sweep-hull-middle-v2"
WORKER_CONTRACT_ID = "ff5c6451c7cd16175fd76725ab0f1741556c828a462b9940a617b4c52d866f85"

PANEL_PROTOCOL = "orchard-xor-strict-panel-v2"
SYNTHETIC_PANEL_PROTOCOL = "orchard-xor-synthetic-panel-v1"
EVENT_TEMPLATE_PROTOCOL = "orchard-xor-event-template-v2"
ARTIFACT_PROTOCOL = "orchard-xor-palette-artifact-v2"
NORMALIZED_PROTOCOL = "research-event-normalized-result-v1"

EXPECTED_CHECKED_PREDICATE = (
    "On the frozen Orchard-XOR v2 panel, do all four target-free realizable "
    "actuals have a passing two-deletion palette cut while at least one "
    "eligible exact-strong relaxed control has none?"
)

SOURCE_BINDINGS = {
    "AGENTS.md": "c873e2e8acd7e0cb282fa975ce972e9e52f52519c537abd2f15e207fbeeb1d54",
    "docs/literature_review.md": "7167acc20276d928c45f8c8cb7a97304155271b2b6892e0ed0e414dc113a6a40",
    "runs/experiments/20260822-lcount-fin13/manifest.json": "93b76b26f0bb124b1a5ef2c1914d1ae0b2517b7582147f06f9fa5caba84d924f",
    "runs/agents/20260823-continuous-rolling-bootstrap/execution/equality16-acquisition/fixture.json": "5b59d9d1d2c060c398fa7159b8a1ebab238fd64b6cafc01480c237ab0ef946b9",
    "runs/experiments/20260818-open-world-math-pilot/binary-predecessor-split.json": "e0257283981b98c1019a299978e95fb19b6c8a9a57f08520aa3d0d8bcf3cdb59",
    "runs/experiments/20260818-open-world-math-pilot/binary-predecessor-split-n9.json": "610f29a723d3310385108c096be7ccf8fc7645b2511500d6a0afc45935784eed",
    "runs/agents/20260825-batch008-probes/execution/fd008-ternary-wl-v1/artifact.json": "b9f060b345c5a597413384432f75f8666104ad32dabaad2dc19c92f2919e7d9e",
    "ErdosSzekeres/Decomposable.lean": "96729bad53eb7b6a0e4824762eac0fc56c968e8469a9567fff70164aea35cba4",
    "ErdosSzekeres/StrongPredecessorBicoloring.lean": "19d3452f1213356ad8d1d0e6b9be86fe19ce84c7a2b7ff983f34b010e26015db",
}

EXPECTED_ACTUAL = {
    "fin8-record-1654": (8, 5, "c72803196d31fe52c6f85ea018cfb2043e989c3e5069551136be7984deb9070e"),
    "fin9-record-936": (9, 6, "e59bb6055267829cc2c0ede02c0f11f183d9e27ead53d4e0eb59ec7ae63b070e"),
    "ticket-0037-affine-bad-n13": (13, 6, "8902fdcef5ae402f4878c8543ceb944965cfef6dda981fbad5b014e657a39a80"),
    "pascal-row-d4-equality16-v1": (16, 6, "6f60e414a926da4c89b9e187e94862ebc7e8e4e274925be79c516c56cbd61e14"),
}

EXPECTED_CONTROLS = {
    "ticket-0037-affine-bad-n13::fd008-relaxed": (
        "ticket-0037-affine-bad-n13", 13, 6,
        "3d970000131f9fa4d8b6063622c35396486d78fc130333dfa6037e53f6630865",
        ((0, 1, 2), (2, 3, 6), (0, 2, 3), (1, 2, 6)),
    ),
    "pascal-row-d4-equality16-v1::fd008-relaxed": (
        "pascal-row-d4-equality16-v1", 16, 6,
        "c480941b6d1bf82a20ff7d01f15049e328e74c12363fb72309645f4ead01bb8b",
        ((0, 1, 5), (0, 2, 6), (0, 1, 2), (0, 5, 6)),
    ),
}

TERMINALS = (
    "ORCHARD-XOR-SEMANTIC-READINESS-STOP",
    "ORCHARD-XOR-KILL",
    "ORCHARD-XOR-LIVE",
    "ORCHARD-XOR-NO-SIGNAL",
)

BRANCH_SEMANTICS = {
    "ORCHARD-XOR-SEMANTIC-READINESS-STOP": (
        "checked_computation", "sidecar", "observes", "candidate-local",
    ),
    "ORCHARD-XOR-KILL": (
        "exact_falsifier", "kill", "refutes", "candidate-local",
    ),
    "ORCHARD-XOR-LIVE": (
        "checked_computation", "live", "supports", "candidate-local",
    ),
    "ORCHARD-XOR-NO-SIGNAL": (
        "checked_computation", "no_signal", "observes", "candidate-local",
    ),
}

KILL_LEARNING_TEXT = {
    "failing_feature": (
        "The literal two-deletion Orchard-XOR palette has no valid predecessor "
        "cut on at least one frozen realizable actual."
    ),
    "strongest_supported_statement": (
        "At the frozen panel scope, the literal Orchard-XOR construction fails "
        "on the first reported actual with zero passing palette rows."
    ),
}


class WorkerError(ValueError):
    """A raw input, artifact, reconstruction, or invocation is invalid."""


def canonical_bytes(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def digest(value: object) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def bytes_sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def exact_keys(value: object, keys: set[str], label: str) -> dict:
    if not isinstance(value, dict) or set(value) != keys:
        raise WorkerError(f"{label} keys differ from the closed contract")
    return value


def require_hex(value: object, label: str) -> str:
    if not isinstance(value, str) or len(value) != 64 or any(ch not in "0123456789abcdef" for ch in value):
        raise WorkerError(f"{label} is not a lowercase SHA-256 value")
    return value


def file_receipt(path: str, raw: bytes) -> dict:
    if not path:
        raise WorkerError("empty input path")
    return {"path": path, "sha256": bytes_sha256(raw)}


def load_json_bytes(raw: bytes, label: str) -> dict:
    try:
        value = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise WorkerError(f"{label} is not valid UTF-8 JSON") from exc
    if not isinstance(value, dict):
        raise WorkerError(f"{label} must be a JSON object")
    return value


def load_raw_inputs(paths: Sequence[str]) -> dict[str, tuple[dict, dict]]:
    if len(paths) != 2:
        raise WorkerError("exactly two --input operands are required")
    loaded: dict[str, tuple[dict, dict]] = {}
    seen_paths: set[str] = set()
    for path in paths:
        if path in seen_paths:
            raise WorkerError("duplicate raw input path")
        seen_paths.add(path)
        try:
            raw = Path(path).read_bytes()
        except OSError as exc:
            raise WorkerError(f"cannot read raw input {path}") from exc
        value = load_json_bytes(raw, f"raw input {path}")
        role = value.get("input_role")
        if role not in {"panel", "event_template"}:
            raise WorkerError("raw input has an undeclared role")
        if role in loaded:
            raise WorkerError(f"duplicate raw input role: {role}")
        loaded[role] = (value, file_receipt(path, raw))
    if set(loaded) != {"panel", "event_template"}:
        raise WorkerError("panel and event_template roles are both required")
    return loaded


def producer_orientation(points: Sequence[Sequence[int]], a: int, b: int, c: int) -> int:
    ax, ay = points[a]
    bx, by = points[b]
    cx, cy = points[c]
    determinant = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax)
    return (determinant > 0) - (determinant < 0)


def producer_permutation_parity(a: int, b: int, c: int) -> tuple[tuple[int, int, int], int]:
    values = (a, b, c)
    if len(set(values)) != 3:
        raise WorkerError("producer orientation received repeated labels")
    inversions = sum(values[i] > values[j] for i in range(3) for j in range(i + 1, 3))
    return tuple(sorted(values)), -1 if inversions & 1 else 1


def producer_sign_access(case: dict) -> tuple[int, Callable[[int, int, int], int]]:
    if case["model_tier"] == "realizable_coordinates":
        points = case["points"]
        n = len(points)
        for triple in itertools.combinations(range(n), 3):
            if producer_orientation(points, *triple) == 0:
                raise WorkerError("producer found a degenerate coordinate triple")

        def chi(a: int, b: int, c: int) -> int:
            return producer_orientation(points, a, b, c)

        return n, chi
    n = case["point_count"]
    triples = list(itertools.combinations(range(n), 3))
    table = dict(zip(triples, case["increasing_signs"], strict=True))

    def chi(a: int, b: int, c: int) -> int:
        key, parity = producer_permutation_parity(a, b, c)
        return parity * table[key]

    return n, chi


def producer_point_in_triangle(
    chi: Callable[[int, int, int], int], x: int, a: int, b: int, c: int
) -> bool:
    triangle_sign = chi(a, b, c)
    return (
        chi(a, b, x) == triangle_sign
        and chi(b, c, x) == triangle_sign
        and chi(c, a, x) == triangle_sign
    )


def producer_coordinate_convex(
    chi: Callable[[int, int, int], int], labels: Sequence[int]
) -> bool:
    for vertex in labels:
        others = [label for label in labels if label != vertex]
        for triangle in itertools.combinations(others, 3):
            if producer_point_in_triangle(chi, vertex, *triangle):
                return False
    return True


def producer_strong_literal(
    chi: Callable[[int, int, int], int], labels: Sequence[int]
) -> bool:
    for a, b, c, d in itertools.combinations(sorted(labels), 4):
        if chi(a, b, c) != chi(a, b, d) or chi(a, c, d) != chi(b, c, d):
            return False
    return True


def producer_edges(
    case: dict, size: int, n: int, chi: Callable[[int, int, int], int]
) -> list[tuple[int, ...]]:
    if size < 3 or size > n:
        return []
    result = []
    for labels in itertools.combinations(range(n), size):
        accepted = (
            producer_coordinate_convex(chi, labels)
            if case["model_tier"] == "realizable_coordinates"
            else producer_strong_literal(chi, labels)
        )
        if accepted:
            result.append(labels)
    return result


def producer_orchard_bits(
    labels: Sequence[int], chi: Callable[[int, int, int], int]
) -> dict[int, int]:
    labels = tuple(sorted(labels))
    if len(labels) < 3:
        raise WorkerError("producer Orchard partition needs at least three labels")
    reference = labels[0]
    bits = {reference: 0}
    threshold = (len(labels) - 3) & 1
    for vertex in labels[1:]:
        parity = 0
        others = [label for label in labels if label not in (reference, vertex)]
        for a, b in itertools.combinations(others, 2):
            if chi(a, b, reference) != chi(a, b, vertex):
                parity ^= 1
        bits[vertex] = parity ^ threshold
    return bits


def producer_cut(colors: Sequence[int]) -> int:
    mask = sum((color & 1) << index for index, color in enumerate(colors))
    return min(mask, ((1 << len(colors)) - 1) ^ mask)


def producer_palette(
    n: int, chi: Callable[[int, int, int], int]
) -> tuple[list[list[int]], bool, list[list[object]]]:
    universe = tuple(range(n))
    rows: list[list[int]] = []
    orbits: list[list[object]] = []
    invariant = True
    for p, q in itertools.combinations(universe, 2):
        without_p = producer_orchard_bits([v for v in universe if v != p], chi)
        without_q = producer_orchard_bits([v for v in universe if v != q], chi)
        survivor = {v: without_p[v] ^ without_q[v] for v in universe if v not in (p, q)}
        ordinary = []
        flipped = []
        for color_p, color_q in itertools.product((0, 1), repeat=2):
            colors = [survivor.get(v, color_p if v == p else color_q) for v in universe]
            alternative = [
                (1 ^ survivor[v]) if v in survivor else (color_p if v == p else color_q)
                for v in universe
            ]
            mask = producer_cut(colors)
            rows.append([p, q, color_p, color_q, mask])
            ordinary.append(mask)
            flipped.append(producer_cut(alternative))
        ordinary.sort()
        flipped.sort()
        invariant = invariant and ordinary == flipped
        orbits.append([p, q, ordinary])
    rows.sort()
    orbits.sort()
    return rows, invariant, orbits


def producer_mask_passes(mask: int, edges: Iterable[Sequence[int]]) -> bool:
    return all(len({(mask >> vertex) & 1 for vertex in edge}) == 2 for edge in edges)


def checker_signed_area(points: Sequence[Sequence[int]], i: int, j: int, k: int) -> int:
    value = (
        points[i][0] * points[j][1]
        + points[j][0] * points[k][1]
        + points[k][0] * points[i][1]
        - points[i][1] * points[j][0]
        - points[j][1] * points[k][0]
        - points[k][1] * points[i][0]
    )
    return (value > 0) - (value < 0)


def checker_sort_parity(a: int, b: int, c: int) -> tuple[tuple[int, int, int], int]:
    values = [a, b, c]
    if len(set(values)) != 3:
        raise WorkerError("checker orientation received repeated labels")
    parity = 1
    for end in (2, 1):
        for index in range(end):
            if values[index] > values[index + 1]:
                values[index], values[index + 1] = values[index + 1], values[index]
                parity = -parity
    return (values[0], values[1], values[2]), parity


def checker_sign_access(case: dict) -> tuple[int, Callable[[int, int, int], int]]:
    if case["model_tier"] == "realizable_coordinates":
        points = case["points"]
        n = len(points)
        for triple in itertools.combinations(range(n), 3):
            if checker_signed_area(points, *triple) == 0:
                raise WorkerError("checker found a degenerate coordinate triple")

        def chi(a: int, b: int, c: int) -> int:
            return checker_signed_area(points, a, b, c)

        return n, chi
    n = case["point_count"]
    triples = list(itertools.combinations(range(n), 3))
    table = dict(zip(triples, case["increasing_signs"], strict=True))

    def chi(a: int, b: int, c: int) -> int:
        key, parity = checker_sort_parity(a, b, c)
        return parity * table[key]

    return n, chi


def checker_hull_size(points: Sequence[Sequence[int]], labels: Sequence[int]) -> int:
    ordered = sorted(labels, key=lambda label: (points[label][0], points[label][1], label))
    if len(ordered) <= 1:
        return len(ordered)
    lower: list[int] = []
    for label in ordered:
        while len(lower) >= 2 and checker_signed_area(points, lower[-2], lower[-1], label) <= 0:
            lower.pop()
        lower.append(label)
    upper: list[int] = []
    for label in reversed(ordered):
        while len(upper) >= 2 and checker_signed_area(points, upper[-2], upper[-1], label) <= 0:
            upper.pop()
        upper.append(label)
    return len(lower[:-1] + upper[:-1])


def checker_middle_determined(
    chi: Callable[[int, int, int], int], labels: Sequence[int]
) -> bool:
    labels = tuple(sorted(labels))
    for middle_index, middle in enumerate(labels):
        expected = None
        for first in labels[:middle_index]:
            for last in labels[middle_index + 1 :]:
                value = chi(first, middle, last)
                if expected is None:
                    expected = value
                elif value != expected:
                    return False
    return True


def checker_edges(
    case: dict, size: int, n: int, chi: Callable[[int, int, int], int]
) -> list[tuple[int, ...]]:
    if size < 3 or size > n:
        return []
    result = []
    for labels in itertools.combinations(range(n), size):
        accepted = (
            checker_hull_size(case["points"], labels) == len(labels)
            if case["model_tier"] == "realizable_coordinates"
            else checker_middle_determined(chi, labels)
        )
        if accepted:
            result.append(labels)
    return result


def checker_orchard_bits(
    labels: Sequence[int], chi: Callable[[int, int, int], int]
) -> dict[int, int]:
    labels = tuple(sorted(labels))
    if len(labels) < 3:
        raise WorkerError("checker Orchard partition needs at least three labels")
    separating = {pair: 0 for pair in itertools.combinations(labels, 2)}
    for a, b in itertools.combinations(labels, 2):
        positive = []
        negative = []
        for vertex in labels:
            if vertex in (a, b):
                continue
            (positive if chi(a, b, vertex) > 0 else negative).append(vertex)
        for x in positive:
            for y in negative:
                separating[(min(x, y), max(x, y))] ^= 1
    reference = labels[0]
    threshold = (len(labels) - 3) & 1
    bits = {reference: 0}
    for vertex in labels[1:]:
        bits[vertex] = separating[(reference, vertex)] ^ threshold
    return bits


def checker_cut(colors: Sequence[int]) -> int:
    forward = 0
    backward = 0
    for label, color in enumerate(colors):
        forward |= (color & 1) << label
        backward |= ((color ^ 1) & 1) << label
    return min(forward, backward)


def checker_palette(
    n: int, chi: Callable[[int, int, int], int]
) -> tuple[list[list[int]], bool, list[list[object]]]:
    universe = tuple(range(n))
    rows = []
    orbits = []
    invariant = True
    for p in range(n):
        for q in range(p + 1, n):
            without_p = checker_orchard_bits(tuple(v for v in universe if v != p), chi)
            without_q = checker_orchard_bits(tuple(v for v in universe if v != q), chi)
            survivor = {v: without_p[v] ^ without_q[v] for v in universe if v not in (p, q)}
            ordinary = []
            flipped = []
            for extension in range(4):
                color_p = extension // 2
                color_q = extension % 2
                colors = []
                alternative = []
                for vertex in universe:
                    if vertex == p:
                        colors.append(color_p)
                        alternative.append(color_p)
                    elif vertex == q:
                        colors.append(color_q)
                        alternative.append(color_q)
                    else:
                        colors.append(survivor[vertex])
                        alternative.append(1 - survivor[vertex])
                mask = checker_cut(colors)
                rows.append([p, q, color_p, color_q, mask])
                ordinary.append(mask)
                flipped.append(checker_cut(alternative))
            ordinary.sort()
            flipped.sort()
            invariant = invariant and ordinary == flipped
            orbits.append([p, q, ordinary])
    rows.sort()
    orbits.sort()
    return rows, invariant, orbits


def checker_mask_passes(mask: int, edges: Iterable[Sequence[int]]) -> bool:
    for edge in edges:
        first = (mask >> edge[0]) & 1
        if all(((mask >> vertex) & 1) == first for vertex in edge[1:]):
            return False
    return True


def validate_case_shape(case: object, *, synthetic: bool) -> dict:
    if not isinstance(case, dict):
        raise WorkerError("panel case must be an object")
    role = case.get("role")
    tier = case.get("model_tier")
    if role == "actual" and tier == "realizable_coordinates":
        exact_keys(case, {"case_id", "role", "model_tier", "target_k", "points"}, "actual case")
        points = case["points"]
        if not isinstance(points, list) or len(points) < 4:
            raise WorkerError("actual points must be a list of length at least four")
        if any(
            not isinstance(point, list)
            or len(point) != 2
            or any(type(coordinate) is not int for coordinate in point)
            for point in points
        ):
            raise WorkerError("coordinates must be integer pairs")
        n = len(points)
    elif role == "control" and tier == "relaxed_nongeometric_sign_table":
        base = {
            "case_id", "role", "model_tier", "eligible", "parent_case_id",
            "target_k", "point_count", "increasing_signs",
        }
        if synthetic:
            exact_keys(case, base, "synthetic control case")
        else:
            exact_keys(
                case,
                base | {"reported_source_sign_sha256", "flip_triples"},
                "strict control case",
            )
        n = case["point_count"]
        if type(n) is not int or n < 4:
            raise WorkerError("control point_count must be at least four")
        triples = n * (n - 1) * (n - 2) // 6
        signs = case["increasing_signs"]
        if not isinstance(signs, list) or len(signs) != triples or any(value not in (-1, 1) for value in signs):
            raise WorkerError("control sign table is incomplete or non-uniform")
        if case["eligible"] is not True:
            raise WorkerError("declared control must be source-eligible")
    else:
        raise WorkerError("case has an undeclared role/model tier")
    target = case.get("target_k")
    if type(target) is not int or not 4 <= target <= n:
        raise WorkerError("case target_k must lie in [4,n]")
    case_id = case.get("case_id")
    if not isinstance(case_id, str) or not case_id:
        raise WorkerError("case_id must be nonempty")
    if synthetic and not case_id.startswith("synthetic-"):
        raise WorkerError("synthetic case identity lacks the synthetic- prefix")
    if synthetic and case_id in set(EXPECTED_ACTUAL) | set(EXPECTED_CONTROLS):
        raise WorkerError("synthetic panel impersonates a strict case identity")
    return case


def producer_raw_signs(points: Sequence[Sequence[int]]) -> list[int]:
    result = []
    for triple in itertools.combinations(range(len(points)), 3):
        value = producer_orientation(points, *triple)
        if value == 0:
            raise WorkerError("producer strict reconstruction found degeneracy")
        result.append(value)
    return result


def checker_raw_signs(points: Sequence[Sequence[int]]) -> list[int]:
    result = []
    for triple in itertools.combinations(range(len(points)), 3):
        value = checker_signed_area(points, *triple)
        if value == 0:
            raise WorkerError("checker strict reconstruction found degeneracy")
        result.append(value)
    return result


def validate_strict_panel_independently(panel: dict) -> None:
    by_id = {case["case_id"]: case for case in panel["cases"]}
    for case_id, (n, target, points_hash) in EXPECTED_ACTUAL.items():
        case = by_id[case_id]
        if case["role"] != "actual" or case["model_tier"] != "realizable_coordinates":
            raise WorkerError(f"{case_id}: strict actual role/tier mismatch")
        if len(case["points"]) != n or case["target_k"] != target or digest(case["points"]) != points_hash:
            raise WorkerError(f"{case_id}: strict coordinate payload mismatch")
    for case_id, (parent_id, n, target, source_hash, flips) in EXPECTED_CONTROLS.items():
        case = by_id[case_id]
        if (
            case["parent_case_id"] != parent_id
            or case["point_count"] != n
            or case["target_k"] != target
            or case["reported_source_sign_sha256"] != source_hash
            or case["flip_triples"] != [list(triple) for triple in flips]
        ):
            raise WorkerError(f"{case_id}: strict control metadata mismatch")
        triple_index = {triple: index for index, triple in enumerate(itertools.combinations(range(n), 3))}
        producer_signs = producer_raw_signs(by_id[parent_id]["points"])
        checker_signs = checker_raw_signs(by_id[parent_id]["points"])
        for triple in flips:
            producer_signs[triple_index[triple]] *= -1
            checker_signs[triple_index[triple]] *= -1
        if producer_signs != case["increasing_signs"] or checker_signs != case["increasing_signs"]:
            raise WorkerError(f"{case_id}: independent strict control reconstruction mismatch")


def validate_panel(panel: dict, *, synthetic_test_only: bool) -> dict:
    if synthetic_test_only:
        exact_keys(
            panel,
            {"schema_version", "protocol", "input_role", "synthetic_only", "task_id", "cases"},
            "synthetic panel",
        )
        if (
            panel["schema_version"] != 1
            or panel["protocol"] != SYNTHETIC_PANEL_PROTOCOL
            or panel["input_role"] != "panel"
            or panel["synthetic_only"] is not True
            or panel["task_id"] != TASK_ID
        ):
            raise WorkerError("synthetic panel identity mismatch")
    else:
        exact_keys(
            panel,
            {"schema_version", "protocol", "input_role", "task_id", "source_bindings", "cases"},
            "strict panel",
        )
        if (
            panel["schema_version"] != 2
            or panel["protocol"] != PANEL_PROTOCOL
            or panel["input_role"] != "panel"
            or panel["task_id"] != TASK_ID
            or panel["source_bindings"] != SOURCE_BINDINGS
        ):
            raise WorkerError("strict panel identity/source binding mismatch")
    cases = panel["cases"]
    if not isinstance(cases, list) or not cases:
        raise WorkerError("panel cases must be a nonempty list")
    validated = [validate_case_shape(case, synthetic=synthetic_test_only) for case in cases]
    identities = [case["case_id"] for case in validated]
    if len(set(identities)) != len(identities):
        raise WorkerError("panel case identities are not unique")
    if synthetic_test_only:
        if not any(case["role"] == "actual" for case in validated) or not any(case["role"] == "control" for case in validated):
            raise WorkerError("synthetic panel needs an actual and a control")
    else:
        if set(identities) != set(EXPECTED_ACTUAL) | set(EXPECTED_CONTROLS):
            raise WorkerError("strict panel identity set mismatch")
        validate_strict_panel_independently(panel)
    return panel


def learning_claim(
    role: str,
    text: str,
    *,
    subject_contract_id: str,
    model_contract_id: str,
    scope_contract_id: str,
    verified_event_core_sha256: str,
) -> dict:
    if role not in KILL_LEARNING_TEXT:
        raise WorkerError("unknown learning role")
    if text != KILL_LEARNING_TEXT[role]:
        raise WorkerError("learning text differs from the frozen terminal semantics")
    core = {
        "role": role,
        "text": text,
        "subject_contract_id": subject_contract_id,
        "model_contract_id": model_contract_id,
        "scope_contract_id": scope_contract_id,
        "verified_event_core_sha256": verified_event_core_sha256,
    }
    return {
        "learning_claim_id": digest(core),
        "text": text,
        "subject_contract_id": subject_contract_id,
    }


def validate_event_template(template: dict, *, synthetic_test_only: bool) -> dict:
    exact_keys(
        template,
        {
            "schema_version", "protocol", "input_role", "synthetic_only",
            "task_id", "semantic_contract_id", "blueprint", "branches",
            "template_core_sha256",
        },
        "event template",
    )
    if (
        template["schema_version"] != 1
        or template["protocol"] != EVENT_TEMPLATE_PROTOCOL
        or template["input_role"] != "event_template"
        or template["synthetic_only"] is not synthetic_test_only
        or template["task_id"] != TASK_ID
        or template["semantic_contract_id"] != SEMANTIC_CONTRACT_ID
    ):
        raise WorkerError("event template identity mismatch")
    blueprint = exact_keys(
        template["blueprint"],
        {
            "claim_contract_id", "primary_contract_id", "subject",
            "subject_contract_id", "model_contract_id", "scope_contract_id",
            "checked_predicate",
        },
        "event template blueprint",
    )
    for key in (
        "claim_contract_id", "primary_contract_id", "subject_contract_id",
        "model_contract_id", "scope_contract_id",
    ):
        require_hex(blueprint[key], f"event template {key}")
    if (
        blueprint["subject"] != "primary_claim"
        or blueprint["claim_contract_id"] != blueprint["primary_contract_id"]
        or blueprint["claim_contract_id"] != blueprint["subject_contract_id"]
    ):
        raise WorkerError("event template primary-claim binding mismatch")
    question = blueprint["checked_predicate"]
    if (
        not isinstance(question, str)
        or not question
        or len(question) > 2000
        or question != EXPECTED_CHECKED_PREDICATE
    ):
        raise WorkerError("event template checked predicate differs from the frozen probe question")
    branches = template["branches"]
    if not isinstance(branches, dict) or set(branches) != set(TERMINALS):
        raise WorkerError("event template branch set mismatch")
    for terminal in TERMINALS:
        branch = exact_keys(
            branches[terminal],
            {
                "kind", "gate_branch", "polarity", "damage_scope_reached",
                "verified_learning_texts",
            },
            f"event branch {terminal}",
        )
        expected = BRANCH_SEMANTICS[terminal]
        observed = (
            branch["kind"], branch["gate_branch"], branch["polarity"],
            branch["damage_scope_reached"],
        )
        if observed != expected:
            raise WorkerError(f"event branch {terminal} semantics mismatch")
        learning_texts = exact_keys(
            branch["verified_learning_texts"],
            {"failing_feature", "strongest_supported_statement"},
            f"event branch {terminal} learning texts",
        )
        if terminal == "ORCHARD-XOR-KILL":
            for role in ("failing_feature", "strongest_supported_statement"):
                if learning_texts[role] != KILL_LEARNING_TEXT[role]:
                    raise WorkerError(f"event branch kill {role} text mismatch")
        elif learning_texts != {"failing_feature": None, "strongest_supported_statement": None}:
            raise WorkerError(f"event branch {terminal} must not freeze negative learning text")
    core = dict(template)
    claimed_hash = core.pop("template_core_sha256")
    if require_hex(claimed_hash, "event template core hash") != digest(core):
        raise WorkerError("event template core hash mismatch")
    return template


def producer_case_report(case: dict) -> dict:
    n, chi = producer_sign_access(case)
    target_k = case["target_k"]
    target = producer_edges(case, target_k, n, chi)
    predecessor = producer_edges(case, target_k - 1, n, chi)
    rows, invariant, orbits = producer_palette(n, chi)
    if not invariant:
        raise WorkerError("producer complement orbit invariant failed")
    passing = [row for row in rows if producer_mask_passes(row[4], predecessor)]
    target_free = not target
    eligible = target_free and (
        case["role"] == "actual"
        or (case.get("eligible") is True and case["model_tier"] == "relaxed_nongeometric_sign_table")
    )
    witness = None
    if passing:
        p, q, color_p, color_q, mask = passing[0]
        witness = {
            "anchors": [p, q],
            "anchor_extension": [color_p, color_q],
            "normalized_cut_mask": mask,
        }
    return case_report_object(case, n, target, predecessor, rows, orbits, passing, eligible, witness)


def checker_case_report(case: dict) -> dict:
    n, chi = checker_sign_access(case)
    target_k = case["target_k"]
    target = checker_edges(case, target_k, n, chi)
    predecessor = checker_edges(case, target_k - 1, n, chi)
    rows, invariant, orbits = checker_palette(n, chi)
    if not invariant:
        raise WorkerError("checker complement orbit invariant failed")
    passing = [row for row in rows if checker_mask_passes(row[4], predecessor)]
    target_free = not target
    eligible = target_free and (
        case["role"] == "actual"
        or (case.get("eligible") is True and case["model_tier"] == "relaxed_nongeometric_sign_table")
    )
    witness = None
    if passing:
        first = passing[0]
        witness = {
            "anchors": first[0:2],
            "anchor_extension": first[2:4],
            "normalized_cut_mask": first[4],
        }
    return case_report_object(case, n, target, predecessor, rows, orbits, passing, eligible, witness)


def case_report_object(
    case: dict,
    n: int,
    target: Sequence[Sequence[int]],
    predecessor: Sequence[Sequence[int]],
    rows: Sequence[Sequence[int]],
    orbits: Sequence[Sequence[object]],
    passing: Sequence[Sequence[int]],
    eligible: bool,
    witness: object,
) -> dict:
    return {
        "case_id": case["case_id"],
        "role": case["role"],
        "model_tier": case["model_tier"],
        "point_count": n,
        "target_k": case["target_k"],
        "predecessor_size": case["target_k"] - 1,
        "reconstructed_target_free": not target,
        "target_edge_count": len(target),
        "target_edges_sha256": digest([list(edge) for edge in target]),
        "predecessor_edge_count": len(predecessor),
        "predecessor_edges_sha256": digest([list(edge) for edge in predecessor]),
        "anchor_pair_count": n * (n - 1) // 2,
        "palette_enumeration_count": len(rows),
        "palette_rows_sha256": digest(list(rows)),
        "complement_invariant": True,
        "complement_orbits_sha256": digest(list(orbits)),
        "passing_palette_count": len(passing),
        "passing_palette_sha256": digest(list(passing)),
        "eligible": eligible,
        "passes": eligible and bool(passing),
        "witness": witness,
    }


def classify(case_reports: Sequence[dict]) -> dict:
    actual = [case for case in case_reports if case["role"] == "actual"]
    controls = [case for case in case_reports if case["role"] == "control" and case["eligible"]]
    ready = bool(actual) and all(case["eligible"] for case in actual) and bool(controls)
    all_actual_pass = ready and all(case["passes"] for case in actual)
    actual_failure = ready and any(not case["passes"] for case in actual)
    control_failure = ready and any(not case["passes"] for case in controls)
    if not ready:
        terminal = "ORCHARD-XOR-SEMANTIC-READINESS-STOP"
    elif actual_failure:
        terminal = "ORCHARD-XOR-KILL"
    elif all_actual_pass and control_failure:
        terminal = "ORCHARD-XOR-LIVE"
    else:
        terminal = "ORCHARD-XOR-NO-SIGNAL"
    return {
        "semantic_readiness": ready,
        "actual_count": len(actual),
        "eligible_control_count": len(controls),
        "all_actual_pass": all_actual_pass,
        "any_actual_fail": actual_failure,
        "any_eligible_control_fail": control_failure,
        "terminal": terminal,
    }


def build_artifact(
    panel: dict,
    panel_receipt: dict,
    event_template: dict,
    event_template_receipt: dict,
    *,
    synthetic_test_only: bool,
) -> dict:
    validate_panel(panel, synthetic_test_only=synthetic_test_only)
    validate_event_template(event_template, synthetic_test_only=synthetic_test_only)
    producer_cases = [producer_case_report(case) for case in panel["cases"]]
    checker_cases = [checker_case_report(case) for case in panel["cases"]]
    if producer_cases != checker_cases:
        raise WorkerError("independent case reconstructions disagree")
    producer_classification = classify(producer_cases)
    checker_classification = classify(checker_cases)
    if producer_classification != checker_classification:
        raise WorkerError("independent classifications disagree")
    producer_core = {
        "schema_version": 2,
        "task_id": TASK_ID,
        "engine": PRODUCER_ID,
        "semantic_contract_id": SEMANTIC_CONTRACT_ID,
        "panel_sha256": digest(panel),
        "cases": producer_cases,
        "classification": producer_classification,
    }
    producer_hash = digest(producer_core)
    checker_core = {
        "schema_version": 2,
        "task_id": TASK_ID,
        "engine": CHECKER_ID,
        "candidate_report_sha256": producer_hash,
        "panel_sha256": digest(panel),
        "accepted": True,
        "classification": checker_classification,
    }
    observation = {
        "panel_sha256": digest(panel),
        "case_count": len(producer_cases),
        "classification": producer_classification,
        "producer_report_sha256": producer_hash,
        "checker_verification_sha256": digest(checker_core),
    }
    terminal = producer_classification["terminal"]
    branch = event_template["branches"][terminal]
    core = {
        "schema_version": 1,
        "protocol": ARTIFACT_PROTOCOL,
        "worker_contract_id": WORKER_CONTRACT_ID,
        "task_id": TASK_ID,
        "semantic_contract_id": SEMANTIC_CONTRACT_ID,
        "producer_engine": PRODUCER_ID,
        "checker_engine": CHECKER_ID,
        "synthetic_test_only": synthetic_test_only,
        "panel_receipt": panel_receipt,
        "event_template_receipt": event_template_receipt,
        "event_blueprint_binding": {
            "blueprint_sha256": digest(event_template["blueprint"]),
            "template_core_sha256": event_template["template_core_sha256"],
            "selected_terminal": terminal,
            "selected_branch_sha256": digest(branch),
        },
        "case_reports": producer_cases,
        "observation": observation,
        "observation_sha256": digest(observation),
        "evidence_level": "implementation_test" if synthetic_test_only else "checked_computation_candidate",
    }
    artifact = dict(core)
    artifact["artifact_core_sha256"] = digest(core)
    return artifact


def validate_artifact_for_event(artifact_raw: bytes, artifact: dict, template: dict) -> None:
    exact_keys(
        artifact,
        {
            "schema_version", "protocol", "worker_contract_id", "task_id",
            "semantic_contract_id", "producer_engine", "checker_engine",
            "synthetic_test_only", "panel_receipt", "event_template_receipt",
            "event_blueprint_binding", "case_reports", "observation",
            "observation_sha256", "evidence_level", "artifact_core_sha256",
        },
        "event artifact",
    )
    if artifact_raw != canonical_bytes(artifact) + b"\n":
        raise WorkerError("event artifact is not canonical JSON plus newline")
    if (
        artifact["schema_version"] != 1
        or artifact["protocol"] != ARTIFACT_PROTOCOL
        or artifact["worker_contract_id"] != WORKER_CONTRACT_ID
        or artifact["task_id"] != TASK_ID
        or artifact["semantic_contract_id"] != SEMANTIC_CONTRACT_ID
        or artifact["producer_engine"] != PRODUCER_ID
        or artifact["checker_engine"] != CHECKER_ID
    ):
        raise WorkerError("event artifact identity mismatch")
    core = dict(artifact)
    claimed_hash = core.pop("artifact_core_sha256")
    if require_hex(claimed_hash, "event artifact core hash") != digest(core):
        raise WorkerError("event artifact core hash mismatch")
    observation = artifact["observation"]
    if artifact["observation_sha256"] != digest(observation):
        raise WorkerError("event artifact observation digest mismatch")
    observation_text = canonical_bytes(observation).decode("utf-8")
    if not observation_text or len(observation_text) > 2000:
        raise WorkerError("event observation exceeds the campaign event envelope")
    terminal = (observation.get("classification") or {}).get("terminal")
    if terminal not in TERMINALS:
        raise WorkerError("event artifact terminal is invalid")
    binding = exact_keys(
        artifact["event_blueprint_binding"],
        {
            "blueprint_sha256", "template_core_sha256", "selected_terminal",
            "selected_branch_sha256",
        },
        "event artifact blueprint binding",
    )
    if (
        binding["blueprint_sha256"] != digest(template["blueprint"])
        or binding["template_core_sha256"] != template["template_core_sha256"]
        or binding["selected_terminal"] != terminal
        or binding["selected_branch_sha256"] != digest(template["branches"][terminal])
    ):
        raise WorkerError("event artifact blueprint binding mismatch")


def event_record(artifact_path: str, artifact_raw: bytes, artifact: dict, template: dict) -> dict:
    """Derive the exact campaign event without any pre-run event-hash field."""

    validate_event_template(
        template,
        synthetic_test_only=artifact.get("synthetic_test_only") is True,
    )
    validate_artifact_for_event(artifact_raw, artifact, template)
    terminal = artifact["observation"]["classification"]["terminal"]
    branch = template["branches"][terminal]
    blueprint = template["blueprint"]
    observation_text = canonical_bytes(artifact["observation"]).decode("utf-8")
    event_core = {
        "kind": branch["kind"],
        "claim_level": "computational_evidence",
        "gate_branch": branch["gate_branch"],
        "binding": {
            "primary_contract_id": blueprint["primary_contract_id"],
            "subject": blueprint["subject"],
            "subject_contract_id": blueprint["subject_contract_id"],
            "model_contract_id": blueprint["model_contract_id"],
            "scope_contract_id": blueprint["scope_contract_id"],
            "polarity": branch["polarity"],
            "damage_scope_reached": branch["damage_scope_reached"],
        },
        "artifact": file_receipt(artifact_path, artifact_raw),
        "observation": observation_text,
    }
    return {
        "event_id": digest(event_core),
        **event_core,
        "verification_receipt": None,
    }


def normalized_result(event: dict, template: dict) -> dict:
    exact_keys(
        event,
        {
            "event_id", "kind", "claim_level", "gate_branch", "binding",
            "artifact", "verification_receipt", "observation",
        },
        "derived event",
    )
    event_core = {
        key: event[key]
        for key in event
        if key not in {"event_id", "verification_receipt"}
    }
    event_core_sha256 = digest(event_core)
    if event["event_id"] != event_core_sha256 or event["verification_receipt"] is not None:
        raise WorkerError("derived event identity mismatch")
    try:
        observation = json.loads(event["observation"])
    except (TypeError, json.JSONDecodeError) as exc:
        raise WorkerError("derived event observation is not canonical JSON") from exc
    if event["observation"] != canonical_bytes(observation).decode("utf-8"):
        raise WorkerError("derived event observation is not canonical compact JSON")
    terminal = (observation.get("classification") or {}).get("terminal")
    if terminal not in TERMINALS:
        raise WorkerError("derived event terminal is invalid")
    branch = template["branches"][terminal]
    blueprint = template["blueprint"]
    binding = event["binding"]
    if (
        event["kind"] != branch["kind"]
        or event["gate_branch"] != branch["gate_branch"]
        or binding["polarity"] != branch["polarity"]
        or binding["damage_scope_reached"] != branch["damage_scope_reached"]
    ):
        raise WorkerError("derived event differs from its terminal branch")
    learning = {"failing_feature": None, "strongest_supported_statement": None}
    falsifier = (
        event["kind"] in {"exact_falsifier", "claim_refuted"}
        and event["gate_branch"] == "kill"
        and binding["polarity"] == "refutes"
    )
    if falsifier:
        texts = branch["verified_learning_texts"]
        learning = {
            role: learning_claim(
                role,
                texts[role],
                subject_contract_id=binding["subject_contract_id"],
                model_contract_id=binding["model_contract_id"],
                scope_contract_id=binding["scope_contract_id"],
                verified_event_core_sha256=event_core_sha256,
            )
            for role in ("failing_feature", "strongest_supported_statement")
        }
    return {
        "schema_version": 1,
        "protocol": NORMALIZED_PROTOCOL,
        "verified_event_core_sha256": event_core_sha256,
        "event_artifact": event["artifact"],
        "claim_contract_id": blueprint["claim_contract_id"],
        "primary_contract_id": binding["primary_contract_id"],
        "subject_contract_id": binding["subject_contract_id"],
        "model_contract_id": binding["model_contract_id"],
        "scope_contract_id": binding["scope_contract_id"],
        "kind": event["kind"],
        "gate_branch": event["gate_branch"],
        "polarity": binding["polarity"],
        "damage_scope_reached": binding["damage_scope_reached"],
        "observation_sha256": bytes_sha256(event["observation"].encode("utf-8")),
        "checked_predicate": blueprint["checked_predicate"],
        "result": binding["polarity"],
        "verified_learning": learning,
    }


def write_all(descriptor: int, data: bytes) -> None:
    if descriptor < 0:
        raise WorkerError("result descriptor must be nonnegative")
    view = memoryview(data)
    while view:
        try:
            written = os.write(descriptor, view)
        except OSError as exc:
            raise WorkerError("cannot write result descriptor") from exc
        if written <= 0:
            raise WorkerError("result descriptor made no progress")
        view = view[written:]


def execute_first_run(input_paths: Sequence[str], result_fd: int, *, synthetic_test_only: bool) -> dict:
    loaded = load_raw_inputs(input_paths)
    panel, panel_receipt = loaded["panel"]
    template, template_receipt = loaded["event_template"]
    artifact = build_artifact(
        panel,
        panel_receipt,
        template,
        template_receipt,
        synthetic_test_only=synthetic_test_only,
    )
    write_all(result_fd, canonical_bytes(artifact) + b"\n")
    return artifact


def execute_replay(
    input_paths: Sequence[str], artifact_path: str, *, synthetic_test_only: bool
) -> dict:
    loaded = load_raw_inputs(input_paths)
    panel, panel_receipt = loaded["panel"]
    template, template_receipt = loaded["event_template"]
    try:
        artifact_raw = Path(artifact_path).read_bytes()
    except OSError as exc:
        raise WorkerError("cannot read event artifact") from exc
    artifact = load_json_bytes(artifact_raw, "event artifact")
    if artifact_raw != canonical_bytes(artifact) + b"\n":
        raise WorkerError("event artifact is not canonical JSON plus newline")
    expected = build_artifact(
        panel,
        panel_receipt,
        template,
        template_receipt,
        synthetic_test_only=synthetic_test_only,
    )
    if artifact != expected:
        raise WorkerError("event artifact disagrees with cold reconstruction")
    event = event_record(artifact_path, artifact_raw, artifact, template)
    return normalized_result(event, template)


def parse_invocation(argv: Sequence[str]) -> dict:
    result_fd = None
    verify_event = None
    normalized_stdout = False
    synthetic_test_only = False
    inputs = []
    index = 0
    while index < len(argv):
        token = argv[index]
        if token in {"--result-fd", "--verify-event", "--input"}:
            if index + 1 >= len(argv):
                raise WorkerError(f"{token} lacks an operand")
            operand = argv[index + 1]
            if token == "--result-fd":
                if result_fd is not None:
                    raise WorkerError("duplicate --result-fd")
                try:
                    result_fd = int(operand)
                except ValueError as exc:
                    raise WorkerError("--result-fd is not an integer") from exc
            elif token == "--verify-event":
                if verify_event is not None:
                    raise WorkerError("duplicate --verify-event")
                verify_event = operand
            else:
                inputs.append(operand)
            index += 2
            continue
        if token == "--normalized-result-stdout":
            if normalized_stdout:
                raise WorkerError("duplicate --normalized-result-stdout")
            normalized_stdout = True
        elif token == "--synthetic-test-only":
            if synthetic_test_only:
                raise WorkerError("duplicate --synthetic-test-only")
            synthetic_test_only = True
        else:
            raise WorkerError(f"unknown argument: {token}")
        index += 1
    first_run = result_fd is not None and verify_event is None and not normalized_stdout
    replay = result_fd is None and verify_event is not None and normalized_stdout
    if not (first_run or replay):
        raise WorkerError("invocation is neither exact first-run nor exact replay mode")
    return {
        "result_fd": result_fd,
        "verify_event": verify_event,
        "inputs": inputs,
        "synthetic_test_only": synthetic_test_only,
        "replay": replay,
    }


def main(argv: Sequence[str] | None = None) -> int:
    try:
        invocation = parse_invocation(list(sys.argv[1:] if argv is None else argv))
        if invocation["replay"]:
            result = execute_replay(
                invocation["inputs"],
                invocation["verify_event"],
                synthetic_test_only=invocation["synthetic_test_only"],
            )
            sys.stdout.buffer.write(canonical_bytes(result) + b"\n")
            sys.stdout.buffer.flush()
        else:
            execute_first_run(
                invocation["inputs"],
                invocation["result_fd"],
                synthetic_test_only=invocation["synthetic_test_only"],
            )
        return 0
    except WorkerError as exc:
        sys.stderr.write(f"orchard-xor worker stop: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
