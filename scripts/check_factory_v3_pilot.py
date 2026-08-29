#!/usr/bin/env python3
"""Check a frozen Factory v3 2x2 context/triage instrumentation pilot.

The checker deliberately consumes a small, closed design manifest rather than
discovering files under a run directory.  Candidate text and adjudication stay
in explicitly private artifacts; ordinary ``result.json`` files and the public
aggregate are authenticated and scanned for verbatim leaks.
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import hmac
import json
import re
import unicodedata
from collections import Counter, defaultdict
from pathlib import Path, PurePosixPath
from typing import Any, Iterable


class PilotError(ValueError):
    """The frozen pilot representation or one of its checks failed."""

    def __init__(self, code: str, detail: str | None = None) -> None:
        if not code.startswith("V3E_"):
            code = "V3E_SCHEMA_INVALID"
        self.code = code
        # Details supplied by deep validators can contain protected identifiers.
        # They are intentionally discarded at the exception boundary.
        self.detail = "frozen pilot validation failed"
        super().__init__(self.code)


HEX = set("0123456789abcdef")
CONTEXT_POLICIES = {"M-full", "M-sparse"}
TRIAGE_POLICIES = {"T-free", "T-skeleton"}
REPLICATES = {"A", "B"}
AUDIT_STATUSES = {"eligible", "rejected"}
DEFECTS = {"target", "producer", "consumer", "gate", "collision", "other"}
TARGET_DEFECTS = {"target", "producer", "consumer"}
ALL_DEFECTS = TARGET_DEFECTS | {"gate"}
STAGES = {"raw", "skeleton", "source", "full-card"}
PRIVATE_BASENAME_PATTERNS = (
    "*-private.json",
    "private-*.json",
    "raw-*.json",
    "evaluation-*.json",
    "audit-*.json",
    "blind-*.json",
    "heldback-*.json",
)
SELECTED_FACTORY_BASENAMES = {
    "result.json", "packet-summary.json", "ideas.md", "report.md",
    "prior-idea-registry.json", "prior-idea-registry.md",
    "root-admission.json", "REPORT.md",
}
LEAK_SHINGLE_TOKENS = 12
LEAK_HMAC_KEY = b"factory-v3-public-leak-scan-v1"
BLIND_PROJECTOR_VERSION = "factory-v3-arm-neutral-v1"
PROVIDER_POLICY = "gpt-5.6-sol:max"

TASK_KEYS = {
    "schema_version", "run_id", "task_id", "wayfinder_ticket", "profile",
    "base_revision", "workspace_fingerprint", "objective", "theorem_contract",
    "inputs", "ownership", "budget", "deliverables", "required_checks",
    "success", "stop", "claims_allowed",
}
RESULT_KEYS = {
    "schema_version", "task_id", "status", "claim_level", "summary", "supports",
    "does_not_support", "changes", "checks", "evidence", "limitations", "blocked_by",
}
RAW_OUTPUT_KEYS = {
    "schema_version", "raw_call_id", "context_policy", "common_prompt_sha256",
    "no_refill", "replacement_count", "attempted_ids", "invocation_id", "candidates",
}
RAW_ROW_KEYS = {
    "id", "raw_text", "sha256", "neutral_annotation", "rejected_title",
    "family_label", "source_title", "source_url", "private_reasoning",
}
EVAL_OUTPUT_KEYS = {
    "schema_version", "evaluator_id", "triage_policy", "replicate", "boundary",
    "projection_sha256", "invocation_id", "candidates",
}
EVAL_ROW_KEYS = {
    "candidate_id", "raw_path", "raw_sha256", "creative_operation", "model_tier",
    "family_signature", "first_terminal", "defect_mask", "stage_reached",
    "source_intervals", "skeleton_frozen_at", "blind_id", "blind_payload",
    "rejected_title", "source_title", "source_url", "private_reasoning",
}
BLIND_PAYLOAD_KEYS = {"projector_version", "statement", "neutral_annotation"}
AUDIT_OUTPUT_KEYS = {
    "schema_version", "auditor_id", "bundle_sha256", "invocation_id", "decisions",
}
PROJECTION_KEYS = {
    "schema_version", "projection_id", "replicate", "candidates", "workspace_fingerprint",
}
PROJECTION_ROW_KEYS = {
    "candidate_id", "raw_call_id", "raw_path", "raw_sha256", "raw_text",
    "neutral_annotation",
}
INVOCATION_KEYS = {
    "call_id", "stage", "invocation_id", "session_id", "provider_policy",
    "start_event", "end_event", "transcript_path", "transcript_sha256",
    "completion_sha256", "task_sha256", "result_sha256", "output_sha256", "input_fingerprint",
    "parent_input_fingerprint",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def compact_hash(value: Any) -> str:
    return sha256(canonical_bytes(value))


def unique_json_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, child in pairs:
        if key in value:
            raise PilotError("V3E_SCHEMA_INVALID")
        value[key] = child
    return value


def load_object(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=unique_json_object
        )
    except (OSError, json.JSONDecodeError) as exc:
        raise PilotError(f"cannot parse {label} {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise PilotError(f"{label} must be a JSON object")
    return value


def require_keys(value: dict[str, Any], required: Iterable[str], label: str) -> None:
    missing = sorted(set(required) - set(value))
    if missing:
        raise PilotError(f"{label} is missing keys: {', '.join(missing)}")


def require_exact_keys(value: Any, expected: set[str], label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != expected:
        raise PilotError("V3E_SCHEMA_INVALID", f"{label} has a non-exact schema")
    return value


def string_leaves(value: Any) -> set[str]:
    if isinstance(value, str):
        return {value} if value else set()
    if isinstance(value, dict):
        found: set[str] = set()
        for child in value.values():
            found |= string_leaves(child)
        return found
    if isinstance(value, list):
        found = set()
        for child in value:
            found |= string_leaves(child)
        return found
    return set()


def require_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise PilotError(f"{label} must be a nonempty string")
    return value


def require_hash(value: Any, label: str) -> str:
    text = require_string(value, label)
    if len(text) != 64 or any(c not in HEX for c in text):
        raise PilotError(f"{label} must be 64 lowercase hexadecimal characters")
    return text


def require_revision(value: Any, label: str) -> str:
    text = require_string(value, label)
    if len(text) not in {40, 64} or any(c not in HEX for c in text):
        raise PilotError(f"{label} must be a 40- or 64-character lowercase hexadecimal revision")
    return text


def normalize_repo_path(root: Path, value: Any, label: str, *, exists: bool = True) -> tuple[str, Path]:
    text = require_string(value, label)
    pure = PurePosixPath(text)
    if pure.is_absolute() or ".." in pure.parts:
        raise PilotError(f"{label} must stay inside the fixture root: {text}")
    path = root.joinpath(*pure.parts)
    if exists and not path.is_file():
        raise PilotError(f"{label} does not exist: {text}")
    try:
        resolved = path.resolve(strict=exists)
        resolved.relative_to(root.resolve())
    except (OSError, ValueError) as exc:
        raise PilotError(f"{label} resolves outside the fixture root") from exc
    return pure.as_posix(), resolved


def matches(path: str, patterns: Iterable[str]) -> bool:
    pure = PurePosixPath(path)
    return any(fnmatch.fnmatch(path, pattern) or pure.match(pattern) for pattern in patterns)


def hash_file(path: Path, expected: Any, label: str) -> str:
    digest = sha256(path.read_bytes())
    if digest != require_hash(expected, f"{label}.sha256"):
        raise PilotError(f"{label} hash mismatch")
    return digest


def task_fingerprint(inputs: list[dict[str, Any]]) -> str:
    return compact_hash(inputs)


def path_owned(path: str, patterns: list[str]) -> bool:
    return any(fnmatch.fnmatch(path, pattern) for pattern in patterns)


def validate_policy_manifest(
    root: Path,
    manifest_ref: Any,
    expected_policy: str,
    label: str,
) -> tuple[str, str, dict[str, str]]:
    """Authenticate a policy descriptor and every generation-visible input."""
    name, path = normalize_repo_path(root, manifest_ref, label)
    manifest = load_object(path, label)
    require_exact_keys(
        manifest,
        {"schema_version", "policy", "inputs", "workspace_fingerprint"},
        label,
    )
    if manifest.get("schema_version") != 1 or manifest.get("policy") != expected_policy:
        raise PilotError(f"{label} identity/policy mismatch")
    inputs = manifest.get("inputs")
    if not isinstance(inputs, list) or not inputs:
        raise PilotError(f"{label}.inputs must be a nonempty array")
    authenticated: dict[str, str] = {}
    for index, item in enumerate(inputs):
        if not isinstance(item, dict) or set(item) != {"path", "sha256"}:
            raise PilotError(f"{label}.inputs[{index}] must contain exactly path and sha256")
        input_name, input_path = normalize_repo_path(root, item["path"], f"{label}.inputs[{index}]")
        if input_name == name or input_name in authenticated:
            raise PilotError(f"{label} has a self-reference or duplicate input: {input_name}")
        authenticated[input_name] = hash_file(input_path, item["sha256"], f"{label}.inputs[{index}]")
    if manifest.get("workspace_fingerprint") != task_fingerprint(inputs):
        raise PilotError(f"{label}.workspace_fingerprint mismatch")
    return name, sha256(path.read_bytes()), authenticated


def task_has_frozen_inputs(task: dict[str, Any], required: dict[str, str], label: str) -> None:
    actual = {item["path"]: item["sha256"] for item in task["inputs"]}
    if actual != required:
        raise PilotError("V3E_STAGE_INPUT_SET_MISMATCH", f"{label} input set is not exact")


def validate_task_result(
    root: Path,
    task_ref: Any,
    result_ref: Any,
    output_ref: str,
    *,
    run_id: str,
    base_revision: str,
    label: str,
) -> tuple[dict[str, Any], dict[str, Any], str, str, set[str]]:
    task_name, task_path = normalize_repo_path(root, task_ref, f"{label}.task")
    result_name, result_path = normalize_repo_path(root, result_ref, f"{label}.result")
    task = load_object(task_path, f"{label} task")
    result = load_object(result_path, f"{label} result")
    require_exact_keys(task, TASK_KEYS, f"{label} task")
    require_exact_keys(result, RESULT_KEYS, f"{label} result")
    require_keys(
        task,
        (
            "schema_version", "run_id", "task_id", "wayfinder_ticket", "profile",
            "base_revision", "workspace_fingerprint", "objective", "theorem_contract",
            "inputs", "ownership", "budget", "deliverables", "required_checks",
            "success", "stop", "claims_allowed",
        ),
        f"{label} task",
    )
    require_keys(
        result,
        (
            "schema_version", "task_id", "status", "claim_level", "summary",
            "supports", "does_not_support", "changes", "checks", "evidence",
            "limitations", "blocked_by",
        ),
        f"{label} result",
    )
    if task.get("schema_version") != 1 or result.get("schema_version") != 1:
        raise PilotError(f"{label} task/result schema_version must be 1")
    if task.get("run_id") != run_id or task.get("base_revision") != base_revision:
        raise PilotError(f"{label} task is not bound to the design run/base revision")
    require_string(task.get("wayfinder_ticket"), f"{label}.wayfinder_ticket")
    require_string(task.get("objective"), f"{label}.objective")
    budget = task.get("budget")
    if not isinstance(budget, dict):
        raise PilotError(f"{label}.budget must be an object")
    for key in ("wall_minutes", "cpu_cores", "memory_gib"):
        if not isinstance(budget.get(key), int) or isinstance(budget.get(key), bool) or budget[key] <= 0:
            raise PilotError(f"{label}.budget.{key} must be a positive integer")
    if not isinstance(budget.get("output_gib"), (int, float)) or isinstance(budget.get("output_gib"), bool) or budget["output_gib"] <= 0:
        raise PilotError(f"{label}.budget.output_gib must be positive")
    task_id = require_string(task.get("task_id"), f"{label}.task_id")
    if result.get("task_id") != task_id:
        raise PilotError(f"{label} task/result task_id mismatch")
    if result.get("status") not in {"completed", "refuted", "blocked", "inconclusive", "superseded"}:
        raise PilotError(f"{label} result is not terminal")
    allowed = task.get("claims_allowed")
    if not isinstance(allowed, list) or result.get("claim_level") not in allowed:
        raise PilotError(f"{label} result exceeds task claim authority")

    inputs = task.get("inputs")
    if not isinstance(inputs, list):
        raise PilotError(f"{label}.inputs must be an array")
    input_names = [item.get("path") for item in inputs if isinstance(item, dict)]
    if len(input_names) != len(inputs) or len(input_names) != len(set(input_names)):
        raise PilotError("V3E_STAGE_INPUT_SET_MISMATCH")
    ownership = task.get("ownership")
    if not isinstance(ownership, dict):
        raise PilotError(f"{label}.ownership must be an object")
    require_exact_keys(ownership, {"read_paths", "write_paths"}, f"{label}.ownership")
    reads = ownership.get("read_paths")
    writes = ownership.get("write_paths")
    if not isinstance(reads, list) or not all(isinstance(x, str) and x for x in reads):
        raise PilotError(f"{label}.ownership.read_paths must be nonempty strings")
    if not isinstance(writes, list) or not all(isinstance(x, str) and x for x in writes):
        raise PilotError(f"{label}.ownership.write_paths must be nonempty strings")
    if set(reads) & set(writes):
        raise PilotError(f"{label} read/write ownership overlaps")
    if any(any(ch in pattern for ch in "*?[") for pattern in writes):
        raise PilotError(f"{label} write ownership must use exact paths, not globs")
    if len(writes) != len(set(writes)):
        raise PilotError(f"{label} repeats a write path")
    if set(reads) != set(input_names):
        raise PilotError("V3E_STAGE_INPUT_SET_MISMATCH", f"{label} read ownership is not exact")
    for index, item in enumerate(inputs):
        if not isinstance(item, dict) or set(item) != {"path", "sha256"}:
            raise PilotError(f"{label}.inputs[{index}] must contain exactly path and sha256")
        name, path = normalize_repo_path(root, item["path"], f"{label}.inputs[{index}]")
        hash_file(path, item["sha256"], f"{label}.inputs[{index}]")
        if not path_owned(name, [*reads, *writes]):
            raise PilotError(f"{label} input is outside ownership: {name}")
    if task.get("workspace_fingerprint") != task_fingerprint(inputs):
        raise PilotError(f"{label} workspace_fingerprint mismatch")

    output_name, _ = normalize_repo_path(root, output_ref, f"{label}.private_output")
    if set(writes) != {output_name, result_name}:
        raise PilotError("V3E_SCHEMA_INVALID", f"{label} write ownership is not exact")
    if output_name not in writes or result_name not in writes:
        raise PilotError(f"{label} does not own its private artifact and result")
    changes = result.get("changes")
    if not isinstance(changes, list) or set(changes) != {output_name, result_name}:
        raise PilotError(f"{label} result changes must be exactly its private artifact and result")
    deliverables = task.get("deliverables")
    if not isinstance(deliverables, list) or set(deliverables) != {output_name, result_name}:
        raise PilotError(f"{label} deliverables must be exactly its private artifact and result")
    for key in ("required_checks", "success", "stop"):
        value = task.get(key)
        if not isinstance(value, list) or not value or not all(isinstance(x, str) and x for x in value):
            raise PilotError(f"{label}.{key} must be a nonempty string array")
    for key in ("supports", "does_not_support", "changes", "checks", "evidence", "limitations"):
        if not isinstance(result.get(key), list):
            raise PilotError("V3E_SCHEMA_INVALID", f"{label}.result.{key} must be an array")
    for check in result["checks"]:
        require_exact_keys(check, {"command", "outcome"}, f"{label}.result.check")
    return task, result, task_name, result_name, set(writes)


def authenticate_spec_files(root: Path, spec: dict[str, Any], label: str) -> None:
    for field in ("task", "result", "private_output"):
        name, path = normalize_repo_path(root, spec[field], f"{label}.{field}")
        hash_file(path, spec[f"{field}_sha256"], f"{label}.{field} ({name})")


def validate_projection(
    root: Path,
    spec: dict[str, Any],
    candidates: dict[str, dict[str, Any]],
    raw_by_id: dict[str, dict[str, Any]],
    replicate: str,
    label: str,
) -> tuple[str, str, set[str], dict[str, Any]]:
    name, path = normalize_repo_path(root, spec["projection"], f"{label}.projection")
    digest = hash_file(path, spec["projection_sha256"], f"{label}.projection")
    projection = load_object(path, f"{label} projection")
    require_exact_keys(projection, PROJECTION_KEYS, f"{label} projection")
    if projection["schema_version"] != 1 or projection["replicate"] != replicate:
        raise PilotError("V3E_EVALUATOR_PROJECTION_MISMATCH")
    rows = projection["candidates"]
    if not isinstance(rows, list) or len(rows) != 20:
        raise PilotError("V3E_EVALUATOR_PROJECTION_MISMATCH")
    if projection["workspace_fingerprint"] != compact_hash(rows):
        raise PilotError("V3E_EVALUATOR_PROJECTION_MISMATCH")
    ids: set[str] = set()
    allocations: Counter[str] = Counter()
    for row in rows:
        require_exact_keys(row, PROJECTION_ROW_KEYS, f"{label} projection row")
        candidate_id = row.get("candidate_id")
        raw = candidates.get(candidate_id)
        if candidate_id in ids or raw is None:
            raise PilotError("V3E_EVALUATOR_PROJECTION_MISMATCH")
        ids.add(candidate_id)
        if (
            row.get("raw_call_id") != raw["raw_call_id"]
            or row.get("raw_path") != raw["raw_path"]
            or row.get("raw_sha256") != raw["sha256"]
            or row.get("raw_text") != raw["raw_text"]
            or row.get("neutral_annotation") != raw["neutral_annotation"]
        ):
            raise PilotError("V3E_EVALUATOR_PROJECTION_MISMATCH")
        allocations[raw["raw_call_id"]] += 1
    if allocations != Counter({call_id: 5 for call_id in raw_by_id}):
        raise PilotError("V3E_EVALUATOR_PROJECTION_MISMATCH")
    return name, digest, ids, projection


def validate_evaluator_wall_intervals(rows: list[dict[str, Any]]) -> None:
    events: list[tuple[int, int]] = []
    for row in rows:
        events.extend((interval[0], interval[1]) for interval in row["source_intervals"])
    events.sort()
    if any(events[index][0] < events[index - 1][1] for index in range(1, len(events))):
        raise PilotError(
            "V3E_SOURCE_INTERVAL_OVERLAP",
            "source-active evaluator wall intervals overlap across candidates",
        )


def validate_invocation_binding(
    record: dict[str, Any] | None,
    stage: str,
    spec: dict[str, Any],
    task: dict[str, Any],
    output: dict[str, Any],
) -> None:
    if record is None or record.get("stage") != stage:
        raise PilotError("V3E_INVOCATION_PROVENANCE_INVALID")
    if (
        record.get("task_sha256") != spec.get("task_sha256")
        or record.get("result_sha256") != spec.get("result_sha256")
        or record.get("output_sha256") != spec.get("private_output_sha256")
        or record.get("input_fingerprint") != task.get("workspace_fingerprint")
        or record.get("parent_input_fingerprint") != task.get("workspace_fingerprint")
        or output.get("invocation_id") != record.get("invocation_id")
    ):
        raise PilotError("V3E_INVOCATION_PROVENANCE_INVALID")


def validate_interval(record: dict[str, Any], boundary: list[Any], policy: str, label: str) -> int:
    if (
        not isinstance(boundary, list) or len(boundary) != 2
        or not all(isinstance(x, int) and not isinstance(x, bool) and x > 0 for x in boundary)
        or boundary[0] >= boundary[1]
    ):
        raise PilotError(f"{label} evaluator boundary must be two increasing positive integers")
    intervals = record.get("source_intervals")
    if not isinstance(intervals, list):
        raise PilotError(f"{label}.source_intervals must be an array")
    previous_end: int | None = None
    duration = 0
    for index, interval in enumerate(intervals):
        if (
            not isinstance(interval, list) or len(interval) != 2
            or not all(isinstance(x, int) and not isinstance(x, bool) and x > 0 for x in interval)
            or interval[0] >= interval[1]
        ):
            raise PilotError(
                "V3E_SOURCE_INTERVAL_INVALID",
                "a source interval is not a positive increasing integer interval",
            )
        start, end = interval
        if start < boundary[0] or end > boundary[1]:
            raise PilotError(f"{label}.source_intervals[{index}] lies outside evaluator boundary")
        if previous_end is not None and start < previous_end:
            raise PilotError(
                "V3E_SOURCE_INTERVAL_OVERLAP",
                "candidate-local source intervals overlap",
            )
        previous_end = end
        duration += end - start
    freeze = record.get("skeleton_frozen_at")
    if policy == "T-free":
        if freeze is not None:
            raise PilotError(f"{label} T-free record must not carry a skeleton freeze")
    else:
        if not isinstance(freeze, int) or isinstance(freeze, bool) or not (boundary[0] <= freeze <= boundary[1]):
            raise PilotError(f"{label} skeleton freeze must be inside evaluator boundary")
        if any(interval[0] < freeze for interval in intervals):
            raise PilotError(
                "V3E_SOURCE_INTERVAL_INVALID",
                "source activity precedes the frozen skeleton",
            )
    return duration


def recompute_aggregate(
    evaluations: list[dict[str, Any]],
    audit_status: dict[str, str],
) -> dict[str, Any]:
    """Return the complete public aggregate derivable from private adjudication."""
    eligible = [row for row in evaluations if audit_status[row["blind_id"]] == "eligible"]
    unresolved = sum(1 for status in audit_status.values() if status == "unresolved")
    rejected = sum(1 for status in audit_status.values() if status == "rejected")

    operation_counts = Counter(row["creative_operation"] for row in evaluations)
    model_counts = Counter(row["model_tier"] for row in evaluations)
    terminal_counts = Counter(row["first_terminal"] for row in evaluations)
    stage_counts = Counter(row["stage_reached"] for row in evaluations)
    defect_counts = Counter(defect for row in evaluations for defect in row["defect_mask"])
    source_by_terminal: defaultdict[str, int] = defaultdict(int)
    events_by_terminal: defaultdict[str, int] = defaultdict(int)
    for row in evaluations:
        source_by_terminal[row["first_terminal"]] += row["source_duration"]
        events_by_terminal[row["first_terminal"]] += row["source_event_count"]

    by_context: dict[str, Any] = {}
    for policy in sorted(CONTEXT_POLICIES):
        rows = [row for row in evaluations if row["context_policy"] == policy]
        accepted = [
            row for row in rows
            if audit_status[row["blind_id"]] == "eligible" and row["first_terminal"] != "collision"
        ]
        by_context[policy] = {
            "evaluation_count": len(rows),
            "eligible_noncolliding_family_signatures": len({row["family_signature"] for row in accepted}),
            "target_producer_consumer_defect_count": sum(
                bool(set(row["defect_mask"]) & TARGET_DEFECTS) for row in rows
            ),
        }

    by_triage: dict[str, Any] = {}
    for policy in sorted(TRIAGE_POLICIES):
        rows = [row for row in evaluations if row["triage_policy"] == policy]
        by_triage[policy] = {
            "evaluation_count": len(rows),
            "defective_source_duration": sum(
                row["source_duration"] for row in rows if set(row["defect_mask"]) & ALL_DEFECTS
            ),
            "full_card_count": sum(row["stage_reached"] == "full-card" for row in rows),
            "source_event_count": sum(row["source_event_count"] for row in rows),
        }

    by_cell: dict[str, Any] = {}
    for context_policy in sorted(CONTEXT_POLICIES):
        by_cell[context_policy] = {}
        for triage_policy in sorted(TRIAGE_POLICIES):
            rows = [
                row for row in evaluations
                if row["context_policy"] == context_policy
                and row["triage_policy"] == triage_policy
            ]
            by_cell[context_policy][triage_policy] = {
                "evaluation_count": len(rows),
                "defective_source_duration": sum(
                    row["source_duration"]
                    for row in rows
                    if set(row["defect_mask"]) & ALL_DEFECTS
                ),
                "full_card_count": sum(row["stage_reached"] == "full-card" for row in rows),
                "source_event_count": sum(row["source_event_count"] for row in rows),
            }

    free_time = by_triage["T-free"]["defective_source_duration"]
    skeleton_time = by_triage["T-skeleton"]["defective_source_duration"]
    family_delta = (
        by_context["M-sparse"]["eligible_noncolliding_family_signatures"]
        - by_context["M-full"]["eligible_noncolliding_family_signatures"]
    )
    defect_delta = (
        by_context["M-sparse"]["target_producer_consumer_defect_count"]
        - by_context["M-full"]["target_producer_consumer_defect_count"]
    )
    saved = free_time - skeleton_time
    full_card_delta = (
        by_triage["T-skeleton"]["full_card_count"]
        - by_triage["T-free"]["full_card_count"]
    )
    return {
        "schema_version": 1,
        "raw_call_count": 4,
        "raw_count": 40,
        "evaluator_block_count": 4,
        "evaluation_count": len(evaluations),
        "auditor_count": 2,
        "audited_count": len(audit_status),
        "eligible_count": len(eligible),
        "rejected_count": rejected,
        "unresolved_count": unresolved,
        "operation_counts": dict(sorted(operation_counts.items())),
        "model_tier_counts": dict(sorted(model_counts.items())),
        "first_terminal_counts": dict(sorted(terminal_counts.items())),
        "defect_counts": dict(sorted(defect_counts.items())),
        "stage_counts": dict(sorted(stage_counts.items())),
        "source_duration_by_terminal": dict(sorted(source_by_terminal.items())),
        "source_event_count": sum(row["source_event_count"] for row in evaluations),
        "source_event_count_by_terminal": dict(sorted(events_by_terminal.items())),
        "by_context": by_context,
        "by_triage": by_triage,
        "by_cell": by_cell,
        "threshold_inputs": {
            "sparse_minus_full_distinct_family_delta": family_delta,
            "sparse_minus_full_defect_delta": defect_delta,
            "source_duration_saved_numerator": saved,
            "source_duration_free_denominator": free_time,
            "skeleton_minus_free_full_card_delta": full_card_delta,
        },
        "threshold_outcomes": {
            "memory_policy": (
                "M-sparse-signal" if family_delta >= 4 and defect_delta <= 4
                else "M-full-reverse" if family_delta <= -4 and defect_delta >= -4
                else "insufficient"
            ),
            "skeleton_policy": (
                "T-skeleton-signal"
                if free_time > 0 and 4 * saved >= free_time and full_card_delta >= -1
                else "insufficient"
            ),
        },
    }


def sensitive_strings(raw_rows: list[dict[str, Any]], evaluations: list[dict[str, Any]]) -> set[str]:
    fields = {
        "id", "raw_text", "rejected_title", "family_label", "source_title",
        "source_url", "private_reasoning", "candidate_id", "family_signature",
    }
    found: set[str] = set()
    for row in [*raw_rows, *evaluations]:
        for key in fields:
            value = row.get(key)
            if isinstance(value, str) and value:
                found.add(value)
    return found


def normalized_text(value: str) -> str:
    return " ".join(unicodedata.normalize("NFKC", value).casefold().split())


def normalized_tokens(value: str) -> list[str]:
    return re.findall(r"\w+", normalized_text(value), flags=re.UNICODE)


def arm_canonical(value: str) -> str:
    return re.sub(r"[^0-9a-z]+", "", normalized_text(value))


def shingle_digests(tokens: list[str]) -> set[bytes]:
    if len(tokens) < LEAK_SHINGLE_TOKENS:
        return set()
    return {
        hmac.new(
            LEAK_HMAC_KEY,
            " ".join(tokens[index:index + LEAK_SHINGLE_TOKENS]).encode("utf-8"),
            hashlib.sha256,
        ).digest()
        for index in range(len(tokens) - LEAK_SHINGLE_TOKENS + 1)
    }


def check_public_leaks(root: Path, public_paths: list[str], secrets: set[str]) -> None:
    protected: list[tuple[bytes, str, set[bytes], str]] = []
    for secret in secrets:
        normalized = normalized_text(secret)
        protected.append((
            secret.encode("utf-8"),
            normalized,
            shingle_digests(normalized_tokens(secret)),
            sha256(normalized.encode("utf-8"))[:16],
        ))
    for name in public_paths:
        _, path = normalize_repo_path(root, name, "public_paths entry")
        data = path.read_bytes()
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise PilotError(
                "V3E_PUBLIC_ARTIFACT_ENCODING",
                f"public_artifact={name}",
            ) from exc
        normalized_public = normalized_text(text)
        public_shingles = shingle_digests(normalized_tokens(text))
        for exact, normalized, protected_shingles, opaque_hit in protected:
            if (
                exact in data
                or (normalized and normalized in normalized_public)
                or bool(protected_shingles & public_shingles)
            ):
                raise PilotError(
                    "V3E_PUBLIC_PRIVATE_TEXT_LEAK",
                    f"public_artifact={name}; opaque_hit={opaque_hit}",
                )


def check_future_manifest(
    root: Path,
    manifest_ref: str,
    private_paths: set[str],
    private_globs: list[str],
) -> None:
    _, path = normalize_repo_path(root, manifest_ref, "future_manifest")
    manifest = load_object(path, "future factory manifest")
    root_resolved = root.resolve()
    private_resolved = {
        root.joinpath(*PurePosixPath(name).parts).resolve(strict=True)
        for name in private_paths
    }
    normalized_private = {normalized_text(name) for name in private_paths}
    for leaf in string_leaves(manifest):
        normalized_leaf = normalized_text(leaf)
        basename = PurePosixPath(leaf).name
        if (
            normalized_leaf in normalized_private
            or matches(normalized_leaf, [normalized_text(pattern) for pattern in private_globs])
            or any(fnmatch.fnmatch(basename, pattern) for pattern in PRIVATE_BASENAME_PATTERNS)
        ):
            raise PilotError("V3E_PRIVATE_PATH_IN_FUTURE_MANIFEST")
        pure_leaf = PurePosixPath(leaf)
        if not pure_leaf.is_absolute() and ".." not in pure_leaf.parts:
            candidate = root.joinpath(*pure_leaf.parts)
            if candidate.exists():
                try:
                    if candidate.resolve(strict=True) in private_resolved:
                        raise PilotError("V3E_PRIVATE_PATH_IN_FUTURE_MANIFEST")
                except OSError:
                    pass
    require_exact_keys(manifest, {"schema_version", "entries"}, "future manifest")
    if manifest["schema_version"] != 1:
        raise PilotError("V3E_SCHEMA_INVALID")
    entries = manifest.get("entries")
    if not isinstance(entries, list):
        raise PilotError("future factory manifest entries must be an array")
    selected: set[str] = set()
    for index, entry in enumerate(entries):
        require_exact_keys(entry, {"path", "sha256"}, f"future manifest entry {index}")
        if not isinstance(entry.get("path"), str):
            raise PilotError(f"future manifest entries[{index}] must contain a path")
        raw_name = entry["path"]
        pure = PurePosixPath(raw_name)
        if pure.is_absolute() or ".." in pure.parts:
            raise PilotError(
                "V3E_PRIVATE_PATH_IN_FUTURE_MANIFEST",
                f"future_entry={index}; path policy violation",
            )
        candidate = root.joinpath(*pure.parts)
        try:
            resolved = candidate.resolve(strict=True)
            canonical_name = resolved.relative_to(root_resolved).as_posix()
        except (OSError, ValueError) as exc:
            raise PilotError(
                "V3E_PRIVATE_PATH_IN_FUTURE_MANIFEST",
                f"future_entry={index}; unresolved or escaping path",
            ) from exc
        name = pure.as_posix()
        hash_file(resolved, entry.get("sha256"), f"future manifest entry {index}")
        if name in selected:
            raise PilotError("V3E_SCHEMA_INVALID")
        selected.add(name)
        if (
            name in private_paths
            or resolved in private_resolved
            or matches(name, private_globs)
            or matches(canonical_name, private_globs)
        ):
            raise PilotError(
                "V3E_PRIVATE_PATH_IN_FUTURE_MANIFEST",
                f"future_entry={index}; private target digest={sha256(name.encode())[:16]}",
            )
    for name in private_paths:
        basename = PurePosixPath(name).name
        if basename in SELECTED_FACTORY_BASENAMES:
            raise PilotError(
                "V3E_PRIVATE_PATH_IN_FUTURE_MANIFEST",
                "a private artifact uses a factory-selected basename",
            )
        if not any(fnmatch.fnmatch(basename, pattern) for pattern in PRIVATE_BASENAME_PATTERNS):
            raise PilotError(
                "V3E_PRIVATE_PATH_IN_FUTURE_MANIFEST",
                "a private artifact lacks a nonselected private basename",
            )
        if name in selected:
            raise PilotError(
                "V3E_PRIVATE_PATH_IN_FUTURE_MANIFEST",
                "a private artifact was selected into the future manifest",
            )


def check_pilot(root: Path, design_path: Path) -> dict[str, Any]:
    root = root.resolve()
    design = load_object(design_path, "pilot design")
    design_keys = {
        "schema_version", "run_id", "base_revision", "common_prompt_sha256",
        "common_prompt", "context_manifests", "triage_contracts", "private_globs",
        "raw_calls", "evaluators", "blind_projector", "blind_bundle",
        "blind_bundle_sha256", "heldback_mapping", "heldback_mapping_sha256",
        "full_memory_manifest", "auditors", "invocations", "public_aggregate",
        "public_aggregate_sha256", "public_paths", "future_manifest",
        "future_manifest_sha256",
    }
    require_exact_keys(design, design_keys, "pilot design")
    require_keys(
        design,
        (
            "schema_version", "run_id", "base_revision", "common_prompt_sha256",
            "common_prompt", "context_manifests", "triage_contracts",
            "private_globs", "raw_calls", "evaluators", "blind_projector", "blind_bundle",
            "blind_bundle_sha256", "heldback_mapping", "heldback_mapping_sha256",
            "full_memory_manifest", "auditors", "invocations", "public_aggregate",
            "public_aggregate_sha256", "public_paths", "future_manifest",
            "future_manifest_sha256",
        ),
        "pilot design",
    )
    if design.get("schema_version") != 1:
        raise PilotError("pilot design schema_version must be 1")
    run_id = require_string(design.get("run_id"), "run_id")
    base_revision = require_revision(design.get("base_revision"), "base_revision")
    common_prompt_sha = require_hash(design.get("common_prompt_sha256"), "common_prompt_sha256")
    common_name, common_path = normalize_repo_path(root, design["common_prompt"], "common_prompt")
    if sha256(common_path.read_bytes()) != common_prompt_sha:
        raise PilotError("common_prompt_sha256 does not authenticate common_prompt")
    context_manifests = design.get("context_manifests")
    triage_contracts = design.get("triage_contracts")
    if not isinstance(context_manifests, dict) or set(context_manifests) != CONTEXT_POLICIES:
        raise PilotError("context_manifests must bind exactly M-full and M-sparse")
    if not isinstance(triage_contracts, dict) or set(triage_contracts) != TRIAGE_POLICIES:
        raise PilotError("triage_contracts must bind exactly T-free and T-skeleton")
    context_inputs: dict[str, tuple[str, str, dict[str, str]]] = {}
    triage_inputs: dict[str, tuple[str, str]] = {}
    for policy, item in context_manifests.items():
        if not isinstance(item, dict) or set(item) != {"path", "sha256"}:
            raise PilotError(f"context_manifests.{policy} must contain exactly path and sha256")
        name, path = normalize_repo_path(root, item["path"], f"context_manifests.{policy}.path")
        digest = hash_file(path, item["sha256"], f"context_manifests.{policy}")
        checked_name, checked_digest, visible_inputs = validate_policy_manifest(
            root, name, policy, f"context_manifests.{policy}"
        )
        if (name, digest) != (checked_name, checked_digest):
            raise PilotError(f"context_manifests.{policy} authentication mismatch")
        context_inputs[policy] = (name, digest, visible_inputs)
    if context_inputs["M-full"][0] == context_inputs["M-sparse"][0]:
        raise PilotError("full and sparse context policies must use distinct frozen manifests")
    for policy, item in triage_contracts.items():
        if not isinstance(item, dict) or set(item) != {"path", "sha256"}:
            raise PilotError(f"triage_contracts.{policy} must contain exactly path and sha256")
        name, path = normalize_repo_path(root, item["path"], f"triage_contracts.{policy}.path")
        triage_inputs[policy] = (name, hash_file(path, item["sha256"], f"triage_contracts.{policy}"))
        contract = load_object(path, f"triage_contracts.{policy}")
        require_exact_keys(contract, {"schema_version", "policy"}, f"triage_contracts.{policy}")
        if contract != {"schema_version": 1, "policy": policy}:
            raise PilotError("V3E_SCHEMA_INVALID")
    if triage_inputs["T-free"][0] == triage_inputs["T-skeleton"][0]:
        raise PilotError("free and skeleton policies must use distinct frozen contracts")
    private_globs = design.get("private_globs")
    if not isinstance(private_globs, list) or not private_globs or not all(
        isinstance(x, str) and x for x in private_globs
    ):
        raise PilotError("private_globs must be a nonempty string array")
    projector_spec = design["blind_projector"]
    require_exact_keys(projector_spec, {"path", "sha256", "version"}, "blind_projector")
    projector_name, projector_path = normalize_repo_path(root, projector_spec["path"], "blind_projector.path")
    hash_file(projector_path, projector_spec["sha256"], "blind_projector")
    projector = load_object(projector_path, "blind projector")
    require_exact_keys(
        projector,
        {"schema_version", "version", "payload_fields"},
        "blind projector",
    )
    if (
        projector["schema_version"] != 1
        or projector["version"] != BLIND_PROJECTOR_VERSION
        or projector_spec["version"] != BLIND_PROJECTOR_VERSION
        or projector["payload_fields"] != sorted(BLIND_PAYLOAD_KEYS)
    ):
        raise PilotError("V3E_BLIND_PAYLOAD_INVALID")
    memory_spec = design["full_memory_manifest"]
    if not isinstance(memory_spec, dict) or set(memory_spec) != {"path", "sha256"}:
        raise PilotError("full_memory_manifest must contain exactly path and sha256")
    memory_ref, memory_path = normalize_repo_path(root, memory_spec["path"], "full_memory_manifest.path")
    hash_file(memory_path, memory_spec["sha256"], "full_memory_manifest")
    memory_name, memory_digest, memory_inputs = validate_policy_manifest(
        root, memory_ref, "M-full", "full_memory_manifest"
    )
    for policy, (_name, _digest, visible) in context_inputs.items():
        for input_name in visible:
            if matches(input_name, private_globs):
                raise PilotError(f"{policy} context manifest includes private pilot path: {input_name}")
    for input_name in memory_inputs:
        if matches(input_name, private_globs):
            raise PilotError(f"full-memory manifest includes private pilot path: {input_name}")

    raw_specs = design.get("raw_calls")
    evaluator_specs = design.get("evaluators")
    auditor_specs = design.get("auditors")
    if not isinstance(raw_specs, list) or len(raw_specs) != 4:
        raise PilotError("pilot requires exactly four raw calls")
    if not isinstance(evaluator_specs, list) or len(evaluator_specs) != 4:
        raise PilotError("pilot requires exactly four evaluator blocks")
    if not isinstance(auditor_specs, list) or len(auditor_specs) != 2:
        raise PilotError("pilot requires exactly two auditors")

    invocation_records = design["invocations"]
    if not isinstance(invocation_records, list) or len(invocation_records) != 10:
        raise PilotError("V3E_INVOCATION_PROVENANCE_INVALID")
    invocation_by_call: dict[str, dict[str, Any]] = {}
    invocation_private_paths: set[str] = set()
    private_objects: list[Any] = []
    seen_invocations: set[str] = set()
    seen_sessions: set[str] = set()
    seen_transcripts: set[str] = set()
    seen_completions: set[str] = set()
    seen_tasks: set[str] = set()
    seen_results: set[str] = set()
    seen_outputs: set[str] = set()
    for record in invocation_records:
        require_exact_keys(record, INVOCATION_KEYS, "invocation record")
        call_id = require_string(record.get("call_id"), "invocation call_id")
        invocation_id = require_string(record.get("invocation_id"), "invocation_id")
        session_id = require_string(record.get("session_id"), "session_id")
        if (
            call_id in invocation_by_call or invocation_id in seen_invocations
            or session_id in seen_sessions
            or record.get("provider_policy") != PROVIDER_POLICY
            or record.get("stage") not in {"raw", "evaluator", "auditor"}
        ):
            raise PilotError("V3E_INVOCATION_PROVENANCE_INVALID")
        start, end = record.get("start_event"), record.get("end_event")
        if (
            not isinstance(start, int) or isinstance(start, bool) or start <= 0
            or not isinstance(end, int) or isinstance(end, bool) or end <= start
        ):
            raise PilotError("V3E_INVOCATION_PROVENANCE_INVALID")
        transcript_name, transcript_path = normalize_repo_path(
            root, record.get("transcript_path"), "invocation transcript"
        )
        transcript_digest = hash_file(
            transcript_path, record.get("transcript_sha256"), "invocation transcript"
        )
        completion_digest = require_hash(record.get("completion_sha256"), "completion_sha256")
        transcript = load_object(transcript_path, "invocation transcript")
        require_exact_keys(
            transcript,
            {
                "schema_version", "invocation_id", "session_id", "output_sha256",
                "completion_sha256",
            },
            "invocation transcript",
        )
        task_digest = require_hash(record.get("task_sha256"), "invocation task_sha256")
        result_digest = require_hash(record.get("result_sha256"), "invocation result_sha256")
        output_digest = require_hash(record.get("output_sha256"), "invocation output_sha256")
        if (
            transcript_digest in seen_transcripts or completion_digest in seen_completions
            or task_digest in seen_tasks or result_digest in seen_results
            or output_digest in seen_outputs or not matches(transcript_name, private_globs)
            or transcript != {
                "schema_version": 1,
                "invocation_id": invocation_id,
                "session_id": session_id,
                "output_sha256": output_digest,
                "completion_sha256": completion_digest,
            }
        ):
            raise PilotError("V3E_INVOCATION_PROVENANCE_INVALID")
        seen_invocations.add(invocation_id)
        seen_sessions.add(session_id)
        seen_transcripts.add(transcript_digest)
        seen_completions.add(completion_digest)
        seen_tasks.add(task_digest)
        seen_results.add(result_digest)
        seen_outputs.add(output_digest)
        invocation_private_paths.add(transcript_name)
        private_objects.append(transcript)
        invocation_by_call[call_id] = record

    all_writes: set[str] = set()
    public_results: set[str] = set()
    private_paths: set[str] = set(invocation_private_paths)
    raw_by_id: dict[str, dict[str, Any]] = {}
    candidates: dict[str, dict[str, Any]] = {}
    raw_rows: list[dict[str, Any]] = []
    context_counts: Counter[str] = Counter()

    for index, spec in enumerate(raw_specs):
        label = f"raw_calls[{index}]"
        if not isinstance(spec, dict):
            raise PilotError(f"{label} must be an object")
        require_exact_keys(
            spec,
            {
                "id", "context_policy", "task", "task_sha256", "result",
                "result_sha256", "private_output", "private_output_sha256",
            }, label,
        )
        authenticate_spec_files(root, spec, label)
        call_id = require_string(spec.get("id"), f"{label}.id")
        if call_id in raw_by_id:
            raise PilotError(f"duplicate raw call id: {call_id}")
        policy = spec.get("context_policy")
        if policy not in CONTEXT_POLICIES:
            raise PilotError(f"{label}.context_policy is invalid")
        task, _result, _task_name, result_name, writes = validate_task_result(
            root, spec["task"], spec["result"], spec["private_output"],
            run_id=run_id, base_revision=base_revision, label=label,
        )
        if task.get("task_id") != call_id or task.get("profile") != "research_question_generator":
            raise PilotError(f"{label} task identity/profile mismatch")
        task_inputs = {item["path"]: item["sha256"] for item in task["inputs"]}
        context_name, context_digest, visible_inputs = context_inputs[policy]
        task_has_frozen_inputs(
            task, {common_name: common_prompt_sha, context_name: context_digest, **visible_inputs},
            f"{label} declared context policy",
        )
        if all_writes & writes:
            raise PilotError(f"write-set collision at {label}: {sorted(all_writes & writes)}")
        all_writes |= writes
        public_results.add(result_name)
        output_name, output_path = normalize_repo_path(root, spec["private_output"], f"{label}.private_output")
        private_paths.add(output_name)
        payload = load_object(output_path, f"{label} private output")
        require_exact_keys(payload, RAW_OUTPUT_KEYS, f"{label} private output")
        private_objects.append(payload)
        if payload.get("schema_version") != 1 or payload.get("raw_call_id") != call_id:
            raise PilotError(f"{label} private output identity mismatch")
        if payload.get("context_policy") != policy or payload.get("common_prompt_sha256") != common_prompt_sha:
            raise PilotError(f"{label} context/common prompt mismatch")
        if payload.get("no_refill") is not True:
            raise PilotError(f"{label} must freeze no_refill=true")
        rows = payload.get("candidates")
        if not isinstance(rows, list) or len(rows) != 10:
            raise PilotError(f"{label} must contain exactly ten frozen raw candidates")
        local_ids: set[str] = set()
        for candidate_index, row in enumerate(rows):
            row_label = f"{label}.candidates[{candidate_index}]"
            if not isinstance(row, dict):
                raise PilotError(f"{row_label} must be an object")
            require_exact_keys(row, RAW_ROW_KEYS, row_label)
            candidate_id = require_string(row.get("id"), f"{row_label}.id")
            if candidate_id in local_ids or candidate_id in candidates:
                raise PilotError(
                    "V3E_RAW_ID_DUPLICATE_OR_REFILL",
                    "the frozen forty-ID set contains a duplicate or refill",
                )
            local_ids.add(candidate_id)
            raw_text = require_string(row.get("raw_text"), f"{row_label}.raw_text")
            raw_digest = sha256(raw_text.encode("utf-8"))
            if raw_digest != require_hash(row.get("sha256"), f"{row_label}.sha256"):
                raise PilotError(f"raw text SHA drift for {candidate_id}")
            enriched = dict(row)
            enriched.update({
                "raw_call_id": call_id,
                "context_policy": policy,
                "raw_path": output_name,
            })
            candidates[candidate_id] = enriched
            raw_rows.append(enriched)
        if payload.get("replacement_count") != 0 or payload.get("attempted_ids") != [
            row["id"] for row in rows
        ]:
            raise PilotError(
                "V3E_RAW_ID_DUPLICATE_OR_REFILL",
                "a raw call records a refill, replacement, or changed attempt order",
            )
        context_counts[policy] += 1
        validate_invocation_binding(invocation_by_call.get(call_id), "raw", spec, task, payload)
        raw_by_id[call_id] = {
            "policy": policy, "path": output_name, "ids": local_ids, "task": task,
        }
    if context_counts != Counter({"M-full": 2, "M-sparse": 2}):
        raise PilotError("raw calls must be balanced two per context policy")
    if len(candidates) != 40:
        raise PilotError("pilot must contain exactly forty globally unique raw IDs")

    eval_by_key: dict[tuple[str, str], dict[str, Any]] = {}
    evaluation_rows: list[dict[str, Any]] = []
    eval_lookup: dict[tuple[str, str], dict[str, Any]] = {}
    for index, spec in enumerate(evaluator_specs):
        label = f"evaluators[{index}]"
        if not isinstance(spec, dict):
            raise PilotError(f"{label} must be an object")
        require_exact_keys(
            spec,
            {
                "id", "triage_policy", "replicate", "task", "task_sha256",
                "result", "result_sha256", "private_output", "private_output_sha256",
                "projection", "projection_sha256",
            }, label,
        )
        authenticate_spec_files(root, spec, label)
        evaluator_id = require_string(spec.get("id"), f"{label}.id")
        policy = spec.get("triage_policy")
        replicate = spec.get("replicate")
        if policy not in TRIAGE_POLICIES or replicate not in REPLICATES:
            raise PilotError(f"{label} has invalid triage policy or replicate")
        if (policy, replicate) in eval_by_key:
            raise PilotError(f"duplicate evaluator arm/replicate: {policy}/{replicate}")
        projection_name, projection_digest, projection_ids, projection = validate_projection(
            root, spec, candidates, raw_by_id, replicate, label
        )
        private_paths.add(projection_name)
        private_objects.append(projection)
        task, _result, _task_name, result_name, writes = validate_task_result(
            root, spec["task"], spec["result"], spec["private_output"],
            run_id=run_id, base_revision=base_revision, label=label,
        )
        if task.get("task_id") != evaluator_id:
            raise PilotError(f"{label} task identity mismatch")
        contract_name, contract_digest = triage_inputs[policy]
        task_has_frozen_inputs(
            task,
            {projection_name: projection_digest, contract_name: contract_digest},
            f"{label} evaluator projection",
        )
        if all_writes & writes:
            raise PilotError(f"write-set collision at {label}: {sorted(all_writes & writes)}")
        all_writes |= writes
        public_results.add(result_name)
        output_name, output_path = normalize_repo_path(root, spec["private_output"], f"{label}.private_output")
        private_paths.add(output_name)
        payload = load_object(output_path, f"{label} private output")
        require_exact_keys(payload, EVAL_OUTPUT_KEYS, f"{label} private output")
        private_objects.append(payload)
        if (
            payload.get("schema_version") != 1 or payload.get("evaluator_id") != evaluator_id
            or payload.get("triage_policy") != policy or payload.get("replicate") != replicate
            or payload.get("projection_sha256") != projection_digest
        ):
            raise PilotError(f"{label} private output identity mismatch")
        boundary = payload.get("boundary")
        rows = payload.get("candidates")
        if not isinstance(rows, list) or len(rows) != 20:
            raise PilotError(f"{label} must contain exactly twenty evaluations")
        local_ids: set[str] = set()
        allocations: Counter[str] = Counter()
        for candidate_index, row in enumerate(rows):
            row_label = f"{label}.candidates[{candidate_index}]"
            if not isinstance(row, dict):
                raise PilotError(f"{row_label} must be an object")
            require_exact_keys(
                row,
                {
                    "candidate_id", "raw_path", "raw_sha256", "creative_operation",
                    "model_tier", "family_signature", "first_terminal", "defect_mask",
                    "stage_reached", "source_intervals", "skeleton_frozen_at",
                    "blind_id", "blind_payload",
                    "rejected_title", "source_title", "source_url", "private_reasoning",
                }, row_label,
            )
            candidate_id = require_string(row.get("candidate_id"), f"{row_label}.candidate_id")
            if candidate_id in local_ids:
                raise PilotError(f"duplicate evaluation candidate in {label}: {candidate_id}")
            local_ids.add(candidate_id)
            raw = candidates.get(candidate_id)
            if raw is None:
                raise PilotError(f"{label} evaluates unknown candidate: {candidate_id}")
            if row.get("raw_path") != raw["raw_path"] or row.get("raw_sha256") != raw["sha256"]:
                raise PilotError(
                    "V3E_FORK_RAW_MISMATCH",
                    "an evaluation does not authenticate the canonical paired raw bytes",
                )
            allocations[raw["raw_call_id"]] += 1
            for key in ("creative_operation", "model_tier", "family_signature", "first_terminal", "blind_id"):
                require_string(row.get(key), f"{row_label}.{key}")
            defects = row.get("defect_mask")
            if not isinstance(defects, list) or len(defects) != len(set(defects)) or not set(defects) <= DEFECTS:
                raise PilotError(f"{row_label}.defect_mask has invalid/duplicate values")
            if row.get("stage_reached") not in STAGES:
                raise PilotError(f"{row_label}.stage_reached is invalid")
            if not isinstance(row.get("blind_payload"), dict) or not row["blind_payload"]:
                raise PilotError(f"{row_label}.blind_payload must be a nonempty object")
            require_exact_keys(row["blind_payload"], BLIND_PAYLOAD_KEYS, f"{row_label}.blind_payload")
            expected_blind_payload = {
                "projector_version": BLIND_PROJECTOR_VERSION,
                "statement": raw["raw_text"],
                "neutral_annotation": raw["neutral_annotation"],
            }
            if row["blind_payload"] != expected_blind_payload:
                raise PilotError("V3E_BLIND_PAYLOAD_INVALID")
            duration = validate_interval(row, boundary, policy, row_label)
            enriched = dict(row)
            enriched.update({
                "context_policy": raw["context_policy"],
                "triage_policy": policy,
                "replicate": replicate,
                "evaluator_id": evaluator_id,
                "source_duration": duration,
                "source_event_count": len(row["source_intervals"]),
            })
            evaluation_rows.append(enriched)
            key = (evaluator_id, candidate_id)
            if key in eval_lookup:
                raise PilotError(f"duplicate evaluator/candidate pair: {key}")
            eval_lookup[key] = enriched
        expected_allocation = Counter({call_id: 5 for call_id in raw_by_id})
        if allocations != expected_allocation:
            raise PilotError(
                "V3E_EVALUATOR_ALLOCATION_IMBALANCE",
                "an evaluator allocation is not exactly 5+5+5+5",
            )
        if local_ids != projection_ids:
            raise PilotError("V3E_EVALUATOR_PROJECTION_MISMATCH")
        validate_evaluator_wall_intervals(rows)
        validate_invocation_binding(
            invocation_by_call.get(evaluator_id), "evaluator", spec, task, payload
        )
        eval_by_key[(policy, replicate)] = {
            "id": evaluator_id, "ids": local_ids, "task": task,
        }
    if set(eval_by_key) != {(policy, rep) for policy in TRIAGE_POLICIES for rep in REPLICATES}:
        raise PilotError("evaluator blocks must cover the complete T by replicate grid")
    for rep in sorted(REPLICATES):
        free_ids = eval_by_key[("T-free", rep)]["ids"]
        skeleton_ids = eval_by_key[("T-skeleton", rep)]["ids"]
        if free_ids != skeleton_ids:
            raise PilotError(f"corresponding free/skeleton replicate {rep} does not fork identical IDs")
    for policy in sorted(TRIAGE_POLICIES):
        first = eval_by_key[(policy, "A")]["ids"]
        second = eval_by_key[(policy, "B")]["ids"]
        if first & second or first | second != set(candidates):
            raise PilotError(f"{policy} evaluator replicates do not partition all forty raw IDs")
    if len(evaluation_rows) != 80:
        raise PilotError("pilot must contain exactly eighty paired evaluations")

    bundle_name, bundle_path = normalize_repo_path(root, design["blind_bundle"], "blind_bundle")
    mapping_name, mapping_path = normalize_repo_path(root, design["heldback_mapping"], "heldback_mapping")
    hash_file(bundle_path, design["blind_bundle_sha256"], "blind_bundle")
    hash_file(mapping_path, design["heldback_mapping_sha256"], "heldback_mapping")
    private_paths |= {bundle_name, mapping_name}
    bundle = load_object(bundle_path, "blind bundle")
    mapping = load_object(mapping_path, "heldback mapping")
    require_exact_keys(bundle, {"schema_version", "projector_version", "items"}, "blind bundle")
    require_exact_keys(mapping, {"schema_version", "items"}, "heldback mapping")
    private_objects.extend([bundle, mapping])
    if (
        bundle.get("schema_version") != 1 or mapping.get("schema_version") != 1
        or bundle.get("projector_version") != BLIND_PROJECTOR_VERSION
    ):
        raise PilotError("blind bundle and heldback mapping schema_version must be 1")
    bundle_items = bundle.get("items")
    mapping_items = mapping.get("items")
    if not isinstance(bundle_items, list) or len(bundle_items) != 80:
        raise PilotError("blind bundle must contain exactly eighty items")
    if not isinstance(mapping_items, list) or len(mapping_items) != 80:
        raise PilotError("heldback mapping must contain exactly eighty items")
    bundle_by_id: dict[str, dict[str, Any]] = {}
    bundle_leaves = string_leaves(bundle)
    forbidden_arm_tokens = [
        *CONTEXT_POLICIES, *TRIAGE_POLICIES,
        *raw_by_id,
        *(value["id"] for value in eval_by_key.values()),
        *candidates,
        *private_paths,
    ]
    for token in forbidden_arm_tokens:
        normalized = arm_canonical(token)
        if normalized and any(normalized in arm_canonical(leaf) for leaf in bundle_leaves):
            raise PilotError("V3E_BLIND_PAYLOAD_INVALID")
    for index, item in enumerate(bundle_items):
        label = f"blind_bundle.items[{index}]"
        if not isinstance(item, dict) or set(item) != {"blind_id", "payload", "payload_sha256"}:
            raise PilotError(f"{label} must contain exactly blind_id, payload, payload_sha256")
        blind_id = require_string(item.get("blind_id"), f"{label}.blind_id")
        if blind_id in bundle_by_id:
            raise PilotError(f"duplicate blind ID: {blind_id}")
        if not isinstance(item.get("payload"), dict) or not item["payload"]:
            raise PilotError(f"{label}.payload must be a nonempty object")
        require_exact_keys(item["payload"], BLIND_PAYLOAD_KEYS, f"{label}.payload")
        if item["payload"].get("projector_version") != BLIND_PROJECTOR_VERSION:
            raise PilotError("V3E_BLIND_PAYLOAD_INVALID")
        if compact_hash(item["payload"]) != require_hash(item.get("payload_sha256"), f"{label}.payload_sha256"):
            raise PilotError(f"blind payload hash mismatch: {blind_id}")
        bundle_by_id[blind_id] = item

    mapped_pairs: set[tuple[str, str]] = set()
    mapping_by_blind: dict[str, dict[str, Any]] = {}
    for index, item in enumerate(mapping_items):
        label = f"heldback_mapping.items[{index}]"
        if not isinstance(item, dict):
            raise PilotError(f"{label} must be an object")
        require_exact_keys(
            item,
            {
                "blind_id", "evaluator_id", "candidate_id", "context_policy",
                "triage_policy", "evaluation_sha256",
            }, label,
        )
        blind_id = require_string(item.get("blind_id"), f"{label}.blind_id")
        if blind_id in mapping_by_blind or blind_id not in bundle_by_id:
            raise PilotError(f"duplicate or unknown heldback blind ID: {blind_id}")
        key = (item.get("evaluator_id"), item.get("candidate_id"))
        row = eval_lookup.get(key)
        if row is None or key in mapped_pairs:
            raise PilotError(f"heldback mapping has duplicate or unknown evaluation: {key}")
        if item.get("context_policy") != row["context_policy"] or item.get("triage_policy") != row["triage_policy"]:
            raise PilotError(f"heldback arm mapping mismatch: {blind_id}")
        if blind_id != row["blind_id"]:
            raise PilotError(f"heldback/evaluation blind ID mismatch: {blind_id}")
        if bundle_by_id[blind_id]["payload"] != row["blind_payload"]:
            raise PilotError(f"blind bundle payload is not the evaluation's opaque payload: {blind_id}")
        evaluation_digest = compact_hash(row["blind_payload"])
        if item.get("evaluation_sha256") != evaluation_digest:
            raise PilotError(f"heldback evaluation hash mismatch: {blind_id}")
        mapped_pairs.add(key)
        mapping_by_blind[blind_id] = item
    if mapped_pairs != set(eval_lookup) or set(mapping_by_blind) != set(bundle_by_id):
        raise PilotError("blind mapping is not a bijection over all eighty evaluations")

    bundle_digest = sha256(bundle_path.read_bytes())
    audit_decisions: list[dict[str, str]] = []
    auditor_ids: set[str] = set()
    for index, spec in enumerate(auditor_specs):
        label = f"auditors[{index}]"
        if not isinstance(spec, dict):
            raise PilotError(f"{label} must be an object")
        require_exact_keys(
            spec,
            {
                "id", "task", "task_sha256", "result", "result_sha256",
                "private_output", "private_output_sha256",
            }, label,
        )
        authenticate_spec_files(root, spec, label)
        auditor_id = require_string(spec.get("id"), f"{label}.id")
        if auditor_id in auditor_ids:
            raise PilotError("the two auditors must be independent task identities")
        auditor_ids.add(auditor_id)
        task, _result, _task_name, result_name, writes = validate_task_result(
            root, spec["task"], spec["result"], spec["private_output"],
            run_id=run_id, base_revision=base_revision, label=label,
        )
        if task.get("task_id") != auditor_id or task.get("profile") != "research_card_auditor":
            raise PilotError(f"{label} task identity/profile mismatch")
        if all_writes & writes:
            raise PilotError(f"write-set collision at {label}: {sorted(all_writes & writes)}")
        all_writes |= writes
        public_results.add(result_name)
        task_has_frozen_inputs(
            task,
            {bundle_name: bundle_digest, memory_name: memory_digest, **memory_inputs},
            f"{label} full-memory audit",
        )
        output_name, output_path = normalize_repo_path(root, spec["private_output"], f"{label}.private_output")
        private_paths.add(output_name)
        payload = load_object(output_path, f"{label} private output")
        require_exact_keys(payload, AUDIT_OUTPUT_KEYS, f"{label} private output")
        private_objects.append(payload)
        if payload.get("schema_version") != 1 or payload.get("auditor_id") != auditor_id:
            raise PilotError(f"{label} private output identity mismatch")
        if payload.get("bundle_sha256") != bundle_digest:
            raise PilotError(f"{label} audited a different bundle")
        decisions = payload.get("decisions")
        if not isinstance(decisions, list) or len(decisions) != 80:
            raise PilotError(f"{label} must decide all eighty blinded items")
        local: dict[str, str] = {}
        for decision in decisions:
            if not isinstance(decision, dict) or set(decision) != {"blind_id", "status"}:
                raise PilotError(f"{label} decision must contain exactly blind_id and status")
            blind_id = decision.get("blind_id")
            status = decision.get("status")
            if blind_id in local or blind_id not in bundle_by_id or status not in AUDIT_STATUSES:
                raise PilotError(f"{label} has duplicate/unknown/invalid auditor decision")
            local[blind_id] = status
        if set(local) != set(bundle_by_id):
            raise PilotError(f"{label} auditor decision coverage mismatch")
        validate_invocation_binding(
            invocation_by_call.get(auditor_id), "auditor", spec, task, payload
        )
        audit_decisions.append(local)

    if set(invocation_by_call) != {
        *(spec["id"] for spec in raw_specs),
        *(spec["id"] for spec in evaluator_specs),
        *(spec["id"] for spec in auditor_specs),
    }:
        raise PilotError("V3E_INVOCATION_PROVENANCE_INVALID")
    auditor_parent_fingerprints = {
        invocation_by_call[spec["id"]]["parent_input_fingerprint"] for spec in auditor_specs
    }
    if len(auditor_parent_fingerprints) != 1:
        raise PilotError("V3E_INVOCATION_PROVENANCE_INVALID")

    adjudicated: dict[str, str] = {}
    for blind_id in sorted(bundle_by_id):
        first, second = audit_decisions[0][blind_id], audit_decisions[1][blind_id]
        adjudicated[blind_id] = first if first == second else "unresolved"
    computed = recompute_aggregate(evaluation_rows, adjudicated)

    public_name, public_path = normalize_repo_path(root, design["public_aggregate"], "public_aggregate")
    hash_file(public_path, design["public_aggregate_sha256"], "public_aggregate")
    public = load_object(public_path, "public aggregate")
    if public != computed:
        raise PilotError(
            "V3E_AGGREGATE_MISMATCH",
            "public aggregate does not exactly match private recomputation",
        )
    public_paths = design.get("public_paths")
    if not isinstance(public_paths, list) or not all(isinstance(x, str) and x for x in public_paths):
        raise PilotError("public_paths must be a string array")
    if len(public_paths) != len(set(public_paths)):
        raise PilotError("public_paths contains duplicates")
    expected_public = public_results | {public_name}
    if set(public_paths) != expected_public:
        raise PilotError("public_paths must be exactly all standard results plus aggregate")
    if any(PurePosixPath(name).name != "result.json" for name in public_results):
        raise PilotError("every standard task result must use basename result.json")
    safe_direct = {
        *CONTEXT_POLICIES, *TRIAGE_POLICIES, *REPLICATES, *AUDIT_STATUSES,
        *DEFECTS, *STAGES, BLIND_PROJECTOR_VERSION,
        *(spec["id"] for spec in raw_specs),
        *(spec["id"] for spec in evaluator_specs),
        *(spec["id"] for spec in auditor_specs),
        *private_paths,
        *(row["creative_operation"] for row in evaluation_rows),
        *(row["model_tier"] for row in evaluation_rows),
        *(row["first_terminal"] for row in evaluation_rows),
    }
    secrets: set[str] = set()
    for private_object in private_objects:
        secrets |= string_leaves(private_object)
    secrets -= safe_direct
    _, future_path = normalize_repo_path(root, design["future_manifest"], "future_manifest")
    hash_file(future_path, design["future_manifest_sha256"], "future_manifest")
    check_future_manifest(root, design["future_manifest"], private_paths, private_globs)
    check_public_leaks(root, [*public_paths, design["future_manifest"]], secrets)
    return computed


def terminal_for_aggregate(aggregate: dict[str, Any]) -> str:
    return (
        "V3U_AUDITOR_DISAGREEMENT"
        if aggregate.get("unresolved_count", 0) > 0
        else "V3_CANARY_VALID"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", required=True, type=Path)
    parser.add_argument("--design", required=True, type=Path)
    args = parser.parse_args()
    root = args.repo_root.resolve()
    design = args.design if args.design.is_absolute() else root / args.design
    try:
        aggregate = check_pilot(root, design.resolve())
    except (PilotError, OSError) as exc:
        code = exc.code if isinstance(exc, PilotError) else "V3E_IO_FAILURE"
        print(code)
        return 1
    print(terminal_for_aggregate(aggregate))
    print(json.dumps(aggregate, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
