#!/usr/bin/env python3
"""Validate a declared rolling-pipeline occupancy board.

The collaboration service is not exposed to repository scripts.  This checker
therefore validates the orchestrator's hash-frozen declaration; it is not
independent process telemetry and must never be reported as such.
"""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import re
import sys
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MAX_AGE_MINUTES = 5.0
MIN_CAPACITY = 4
MAX_CAPACITY = 5
SLOT_IDS = {"root", "worker-1", "worker-2", "worker-3", "worker-4"}
STATES = {"active", "idle", "terminal", "checkpointed"}
CLASSIFICATIONS = {
    "proof-producing",
    "information-gathering",
    "discovery-support",
    "orchestration",
}
TASK_SCHEMA = json.loads(
    (ROOT / "docs/agents/schemas/task-packet.schema.json").read_text(encoding="utf-8")
)
RESULT_SCHEMA = json.loads(
    (ROOT / "docs/agents/schemas/result.schema.json").read_text(encoding="utf-8")
)

_AGENT_VALIDATOR_SPEC = importlib.util.spec_from_file_location(
    "rolling_pipeline_agent_validator", ROOT / "scripts/check_agent_orchestration.py"
)
if _AGENT_VALIDATOR_SPEC is None or _AGENT_VALIDATOR_SPEC.loader is None:
    raise RuntimeError("cannot load canonical agent-task validator")
AGENT_VALIDATOR = importlib.util.module_from_spec(_AGENT_VALIDATOR_SPEC)
_AGENT_VALIDATOR_SPEC.loader.exec_module(AGENT_VALIDATOR)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_repo_path(root: Path, path: Path) -> str:
    """Return one repository-relative identity for an already resolved path."""
    return path.relative_to(root.resolve()).as_posix()


def filesystem_identity(path: Path) -> tuple[int, int] | None:
    """Return a stable local file identity when the filesystem exposes one."""
    try:
        stat = path.stat()
    except OSError:
        return None
    if not stat.st_ino:
        return None
    return stat.st_dev, stat.st_ino


def valid_family(value: Any) -> bool:
    return isinstance(value, str) and bool(value) and value == value.strip()


def repo_file(root: Path, value: Any, label: str, errors: list[str]) -> Path | None:
    if not isinstance(value, str) or not value:
        errors.append(f"{label} must be a nonempty repository-relative path")
        return None
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        errors.append(f"{label} must stay inside the repository")
        return None
    repository_root = root.resolve()
    resolved = (root / path).resolve()
    try:
        resolved.relative_to(repository_root)
    except ValueError:
        errors.append(f"{label} must resolve inside the repository")
        return None
    if not resolved.is_file():
        errors.append(f"{label} does not exist: {value}")
        return None
    return resolved


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def json_equal(left: Any, right: Any) -> bool:
    """Compare values using JSON Schema's value equality rules."""
    if isinstance(left, bool) or isinstance(right, bool):
        return isinstance(left, bool) and isinstance(right, bool) and left == right
    if isinstance(left, (int, float)) and isinstance(right, (int, float)):
        return left == right
    if left is None or right is None:
        return left is None and right is None
    if isinstance(left, list) or isinstance(right, list):
        return (
            isinstance(left, list)
            and isinstance(right, list)
            and len(left) == len(right)
            and all(json_equal(a, b) for a, b in zip(left, right))
        )
    if isinstance(left, dict) or isinstance(right, dict):
        return (
            isinstance(left, dict)
            and isinstance(right, dict)
            and left.keys() == right.keys()
            and all(json_equal(left[key], right[key]) for key in left)
        )
    return type(left) is type(right) and left == right


def is_finite_number(value: Any) -> bool:
    if isinstance(value, bool):
        return False
    if isinstance(value, int):
        return True
    return isinstance(value, float) and math.isfinite(value)


def matches_json_type(value: Any, expected: str) -> bool:
    if expected == "null":
        return value is None
    if expected == "boolean":
        return isinstance(value, bool)
    if expected == "object":
        return isinstance(value, dict)
    if expected == "array":
        return isinstance(value, list)
    if expected == "string":
        return isinstance(value, str)
    if expected == "number":
        return is_finite_number(value)
    if expected == "integer":
        return (
            isinstance(value, int) and not isinstance(value, bool)
        ) or (
            isinstance(value, float) and math.isfinite(value) and value.is_integer()
        )
    return False


def validate_json_schema(
    value: Any,
    schema: dict[str, Any],
    label: str,
    errors: list[str],
) -> None:
    """Validate the dependency-free keyword subset used by the frozen task schema."""
    branches = schema.get("oneOf")
    if isinstance(branches, list):
        matches = 0
        for branch in branches:
            branch_errors: list[str] = []
            validate_json_schema(value, branch, label, branch_errors)
            if not branch_errors:
                matches += 1
        if matches != 1:
            errors.append(f"{label} must match exactly one allowed schema branch")
        return

    if "const" in schema and not json_equal(value, schema["const"]):
        errors.append(f"{label} must equal {schema['const']!r}")
    enum = schema.get("enum")
    if isinstance(enum, list) and not any(json_equal(value, item) for item in enum):
        errors.append(f"{label} is not an allowed value")

    expected = schema.get("type")
    if isinstance(expected, str):
        expected_types = [expected]
    elif isinstance(expected, list):
        expected_types = [item for item in expected if isinstance(item, str)]
    else:
        expected_types = []
    if expected_types and not any(matches_json_type(value, item) for item in expected_types):
        errors.append(f"{label} must have type {' or '.join(expected_types)}")
        return

    if isinstance(value, dict):
        required = schema.get("required", [])
        missing = sorted(key for key in required if key not in value)
        if missing:
            errors.append(f"{label} is missing schema keys: {', '.join(missing)}")
        properties = schema.get("properties", {})
        if schema.get("additionalProperties") is False:
            unexpected = sorted(set(value) - set(properties))
            if unexpected:
                errors.append(f"{label} has unexpected schema keys: {', '.join(unexpected)}")
        if isinstance(properties, dict):
            for key, subschema in properties.items():
                if key in value and isinstance(subschema, dict):
                    validate_json_schema(value[key], subschema, f"{label}.{key}", errors)

    if isinstance(value, list):
        minimum_items = schema.get("minItems")
        if isinstance(minimum_items, int) and len(value) < minimum_items:
            errors.append(f"{label} must contain at least {minimum_items} item(s)")
        if schema.get("uniqueItems") is True:
            for index, item in enumerate(value):
                if any(json_equal(item, prior) for prior in value[:index]):
                    errors.append(f"{label} must contain unique items")
                    break
        item_schema = schema.get("items")
        if isinstance(item_schema, dict):
            for index, item in enumerate(value):
                validate_json_schema(item, item_schema, f"{label}[{index}]", errors)

    if isinstance(value, str):
        minimum_length = schema.get("minLength")
        if isinstance(minimum_length, int) and len(value) < minimum_length:
            errors.append(f"{label} must contain at least {minimum_length} character(s)")
        pattern = schema.get("pattern")
        if isinstance(pattern, str) and re.search(pattern, value) is None:
            errors.append(f"{label} does not match the required pattern")

    if is_finite_number(value):
        minimum = schema.get("minimum")
        if isinstance(minimum, (int, float)) and value < minimum:
            errors.append(f"{label} must be at least {minimum}")
        exclusive_minimum = schema.get("exclusiveMinimum")
        if isinstance(exclusive_minimum, (int, float)) and value <= exclusive_minimum:
            errors.append(f"{label} must be greater than {exclusive_minimum}")


def is_digest(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def validate_hashed_reference(
    value: Any,
    root: Path,
    label: str,
    errors: list[str],
) -> tuple[str, Path] | None:
    if not isinstance(value, dict) or set(value) != {"path", "sha256"}:
        errors.append(f"{label} must contain exactly path and sha256")
        return None
    path_value = value.get("path")
    path = repo_file(root, path_value, f"{label}.path", errors)
    digest = value.get("sha256")
    if not is_digest(digest):
        errors.append(f"{label}.sha256 must be a SHA-256 digest")
    elif path is not None and sha256(path) != digest:
        errors.append(f"{label} hash drift: {path_value}")
    if path is None or not isinstance(path_value, str) or not is_digest(digest):
        return None
    return canonical_repo_path(root, path), path


def validate_task(
    path: Path,
    label: str,
    root: Path,
    run_id: Any,
    manifest: dict[str, Any],
    errors: list[str],
) -> dict[str, Any] | None:
    try:
        task = load_json(path)
    except (OSError, json.JSONDecodeError) as exc:
        errors.append(f"cannot parse {label}: {exc}")
        return None
    schema_errors: list[str] = []
    validate_json_schema(task, TASK_SCHEMA, label, schema_errors)
    errors.extend(f"task JSON schema: {error}" for error in schema_errors)
    canonical_errors: list[str] = []
    AGENT_VALIDATOR.validate_task(task, manifest, label, canonical_errors)
    errors.extend(canonical_errors)
    if not isinstance(task, dict):
        return None
    if task.get("run_id") != run_id:
        errors.append(f"{label}.run_id must match the board run_id")
    inputs = task.get("inputs")
    if isinstance(inputs, list):
        for index, item in enumerate(inputs):
            item_label = f"{label}.inputs[{index}]"
            if not isinstance(item, dict):
                continue
            input_path = repo_file(root, item.get("path"), f"{item_label}.path", errors)
            digest = item.get("sha256")
            if is_digest(digest) and input_path is not None and sha256(input_path) != digest:
                errors.append(f"{item_label} hash drift: {item.get('path')}")
    return task


def validate_board(
    board: Any,
    root: Path,
    *,
    now: datetime | None = None,
    max_age_minutes: float | None = DEFAULT_MAX_AGE_MINUTES,
) -> tuple[list[str], dict[str, int]]:
    errors: list[str] = []
    counts = {"active": 0, "mathematical": 0, "support": 0, "ready": 0}
    if not isinstance(board, dict):
        return ["board must be a JSON object"], counts

    manifest_errors: list[str] = []
    manifest = AGENT_VALIDATOR.validate_manifest(manifest_errors)
    errors.extend(f"canonical task validator: {error}" for error in manifest_errors)

    if type(board.get("schema_version")) is not int or board.get("schema_version") != 1:
        errors.append("schema_version must be 1")
    capacity = board.get("capacity")
    if type(capacity) is not int or not MIN_CAPACITY <= capacity <= MAX_CAPACITY:
        errors.append("capacity must be 4 or 5 (root plus three or four workers)")
        expected_slot_ids = {"root", "worker-1", "worker-2", "worker-3"}
    else:
        expected_slot_ids = {"root"} | {
            f"worker-{index}" for index in range(1, capacity)
        }
    if board.get("mode") not in {"bootstrap", "operational"}:
        errors.append("mode must be bootstrap or operational")
    run_id = board.get("run_id")
    if not isinstance(run_id, str) or not run_id:
        errors.append("run_id must be a nonempty string")
    limitation = board.get("telemetry_limitation")
    if not isinstance(limitation, str) or "not platform telemetry" not in limitation:
        errors.append("telemetry_limitation must say that the board is not platform telemetry")

    updated_at = board.get("updated_at")
    parsed_update: datetime | None = None
    if not isinstance(updated_at, str):
        errors.append("updated_at must be an ISO-8601 timestamp")
    else:
        try:
            parsed_update = datetime.fromisoformat(updated_at.replace("Z", "+00:00"))
            if parsed_update.tzinfo is None:
                raise ValueError("timezone missing")
        except ValueError:
            errors.append("updated_at must be timezone-aware ISO-8601")
    age_limit = DEFAULT_MAX_AGE_MINUTES if max_age_minutes is None else max_age_minutes
    if (
        not isinstance(age_limit, (int, float))
        or isinstance(age_limit, bool)
        or not is_finite_number(age_limit)
        or age_limit <= 0
    ):
        errors.append("max_age_minutes must be positive and finite")
    elif parsed_update is not None:
        clock = now or datetime.now(timezone.utc)
        age_minutes = (clock.astimezone(timezone.utc) - parsed_update.astimezone(timezone.utc)).total_seconds() / 60
        if age_minutes < -1:
            errors.append("updated_at is in the future")
        elif age_minutes > age_limit:
            errors.append(
                f"board heartbeat is stale: {age_minutes:.1f} minutes > {age_limit:.1f}"
            )

    snapshot = board.get("snapshot")
    snapshot_digests: dict[str, str] = {}
    snapshot_file_locations: dict[tuple[int, int], str] = {}
    if not isinstance(snapshot, list) or not snapshot:
        errors.append("snapshot must be a nonempty array")
    else:
        for index, item in enumerate(snapshot):
            label = f"snapshot[{index}]"
            reference = validate_hashed_reference(item, root, label, errors)
            if reference is None:
                continue
            path_value, snapshot_path = reference
            if path_value in snapshot_digests:
                errors.append(f"duplicate snapshot path: {path_value}")
            else:
                snapshot_digests[path_value] = item["sha256"]
            file_id = filesystem_identity(snapshot_path)
            if file_id is not None:
                prior = snapshot_file_locations.get(file_id)
                if prior is not None and prior != path_value:
                    errors.append(
                        f"duplicate snapshot file identity: {prior} and {path_value}"
                    )
                else:
                    snapshot_file_locations[file_id] = path_value

    slots = board.get("slots")
    active_families: Counter[str] = Counter()
    seen_ids: set[str] = set()
    seen_agents: set[str] = set()
    task_locations: dict[str, str] = {}
    task_file_locations: dict[tuple[int, int], str] = {}
    task_file_paths: dict[tuple[int, int], str] = {}
    task_logical_locations: dict[tuple[str, str], str] = {}
    task_logical_paths: dict[tuple[str, str], str] = {}
    task_paths: set[str] = set()
    active_task_paths: set[str] = set()
    lifecycle_task_paths: set[str] = set()
    slot_states: dict[str, str] = {}
    transition_locations: dict[str, str] = {}
    transition_file_locations: dict[tuple[int, int], str] = {}
    if not isinstance(slots, list) or len(slots) != len(expected_slot_ids):
        errors.append(f"slots must contain exactly {len(expected_slot_ids)} entries")
    else:
        for index, slot in enumerate(slots):
            label = f"slots[{index}]"
            if not isinstance(slot, dict):
                errors.append(f"{label} must be an object")
                continue
            slot_id = slot.get("slot_id")
            if slot_id not in expected_slot_ids:
                errors.append(f"{label}.slot_id is not recognized")
            elif slot_id in seen_ids:
                errors.append(f"duplicate slot_id: {slot_id}")
            else:
                seen_ids.add(slot_id)
            state = slot.get("state")
            if state not in STATES:
                errors.append(f"{label}.state is not recognized")
            elif isinstance(slot_id, str):
                slot_states[slot_id] = state
            classification = slot.get("classification")
            if classification not in CLASSIFICATIONS:
                errors.append(f"{label}.classification is not recognized")
            agent_name = slot.get("agent_name")
            if not isinstance(agent_name, str) or not agent_name:
                errors.append(f"{label}.agent_name must be nonempty")
            elif agent_name in seen_agents:
                errors.append(f"duplicate agent_name: {agent_name}")
            else:
                seen_agents.add(agent_name)
            family = slot.get("mechanism_family")
            if family is not None and not valid_family(family):
                errors.append(
                    f"{label}.mechanism_family must be null or a nonempty string without surrounding whitespace"
                )
            if classification in {"proof-producing", "information-gathering"} and not (
                valid_family(family)
            ):
                errors.append(f"{label}.mechanism_family must be nonempty for a mathematical lane")
            task_value = slot.get("task_packet")
            needs_task = slot_id != "root" and state != "idle"
            slot_task: dict[str, Any] | None = None
            if slot_id != "root" and state == "idle" and task_value is not None:
                errors.append(f"{label}.task_packet must be null while the slot is idle")
            elif task_value is not None or needs_task:
                path = repo_file(root, task_value, f"{label}.task_packet", errors)
                if path is not None:
                    task_identity = canonical_repo_path(root, path)
                    prior = task_locations.get(task_identity)
                    if prior is not None:
                        errors.append(
                            f"duplicate task packet in {prior} and {label}: {task_identity}"
                        )
                    else:
                        task_locations[task_identity] = label
                    file_id = filesystem_identity(path)
                    if file_id is not None:
                        prior_file = task_file_locations.get(file_id)
                        if prior_file is not None and prior_file != label:
                            errors.append(
                                f"duplicate task file identity in {prior_file} and {label}: {task_identity}"
                            )
                        else:
                            task_file_locations[file_id] = label
                            task_file_paths[file_id] = task_identity
                    task_paths.add(task_identity)
                    if state == "active":
                        active_task_paths.add(task_identity)
                    if state in {"active", "checkpointed", "terminal"}:
                        lifecycle_task_paths.add(task_identity)
                    slot_task = validate_task(
                        path, f"{label}.task_packet", root, run_id, manifest, errors
                    )
                    if isinstance(slot_task, dict):
                        logical_id = (slot_task.get("run_id"), slot_task.get("task_id"))
                        if all(isinstance(item, str) and item for item in logical_id):
                            prior_logical = task_logical_locations.get(logical_id)
                            if prior_logical is not None and prior_logical != label:
                                errors.append(
                                    f"duplicate logical task {logical_id[0]}/{logical_id[1]} in {prior_logical} and {label}"
                                )
                            else:
                                task_logical_locations[logical_id] = label
                                task_logical_paths[logical_id] = task_identity

            transition = slot.get("transition")
            if state in {"checkpointed", "terminal"}:
                if not isinstance(transition, dict):
                    errors.append(f"{label}.transition is required for {state} state")
                else:
                    reference = validate_hashed_reference(
                        {"path": transition.get("path"), "sha256": transition.get("sha256")},
                        root,
                        f"{label}.transition",
                        errors,
                    )
                    if reference is not None:
                        transition_identity, transition_path = reference
                        prior_transition = transition_locations.get(transition_identity)
                        if prior_transition is not None and prior_transition != label:
                            errors.append(
                                f"duplicate transition artifact in {prior_transition} and {label}: {transition_identity}"
                            )
                        else:
                            transition_locations[transition_identity] = label
                        transition_file_id = filesystem_identity(transition_path)
                        if transition_file_id is not None:
                            prior_transition_file = transition_file_locations.get(
                                transition_file_id
                            )
                            if (
                                prior_transition_file is not None
                                and prior_transition_file != label
                            ):
                                errors.append(
                                    f"duplicate transition file identity in {prior_transition_file} and {label}: {transition_identity}"
                                )
                            else:
                                transition_file_locations[transition_file_id] = label
                    if state == "checkpointed":
                        expected = {"kind", "path", "sha256", "next_action"}
                        if set(transition) != expected:
                            errors.append(f"{label}.transition must contain exactly kind, path, sha256, and next_action")
                        if transition.get("kind") != "checkpoint":
                            errors.append(f"{label}.transition.kind must be checkpoint")
                        if transition.get("next_action") not in {"resume", "supersede"}:
                            errors.append(f"{label}.transition.next_action must be resume or supersede")
                    else:
                        expected = {"kind", "path", "sha256", "reconciliation_state", "next_action"}
                        if set(transition) != expected:
                            errors.append(
                                f"{label}.transition must contain exactly kind, path, sha256, reconciliation_state, and next_action"
                            )
                        if transition.get("kind") != "result":
                            errors.append(f"{label}.transition.kind must be result")
                        reconciliation = transition.get("reconciliation_state")
                        if reconciliation not in {"pending", "admitted"}:
                            errors.append(f"{label}.transition.reconciliation_state must be pending or admitted")
                        expected_action = "admit" if reconciliation == "pending" else "reconcile"
                        if transition.get("next_action") != expected_action:
                            errors.append(f"{label}.transition.next_action must be {expected_action}")
                        if reconciliation == "admitted" and reference is not None:
                            _, result_path = reference
                            try:
                                result = load_json(result_path)
                            except (OSError, json.JSONDecodeError) as exc:
                                errors.append(f"cannot parse {label}.admitted_result: {exc}")
                                result = None
                            result_schema_errors: list[str] = []
                            validate_json_schema(
                                result,
                                RESULT_SCHEMA,
                                f"{label}.admitted_result",
                                result_schema_errors,
                            )
                            errors.extend(
                                f"result JSON schema: {error}"
                                for error in result_schema_errors
                            )
                            canonical_result_errors: list[str] = []
                            AGENT_VALIDATOR.validate_result(
                                result,
                                manifest,
                                f"{label}.admitted_result",
                                canonical_result_errors,
                            )
                            errors.extend(canonical_result_errors)
                            if slot_task is None:
                                errors.append(
                                    f"{label}.admitted_result requires a referenced task packet"
                                )
                            elif isinstance(result, dict):
                                AGENT_VALIDATOR.validate_pair(
                                    slot_task,
                                    result,
                                    f"{label}.admitted_result pair",
                                    errors,
                                )
                    if reference is not None:
                        transition_path, _ = reference
                        if transition_path not in snapshot_digests:
                            errors.append(f"{label}.transition must have a snapshot entry: {transition_path}")
            elif transition is not None:
                errors.append(f"{label}.transition must be null unless state is terminal or checkpointed")

            if state == "active":
                counts["active"] += 1
                if classification in {"proof-producing", "information-gathering"}:
                    counts["mathematical"] += 1
                else:
                    counts["support"] += 1
                if valid_family(family) and classification in {
                    "proof-producing", "information-gathering"
                }:
                    active_families[family] += 1
        if seen_ids != expected_slot_ids:
            errors.append(
                "slot IDs must be root and the contiguous worker range for capacity"
            )

    if any(slot_states.get(slot_id) == "active" for slot_id in expected_slot_ids - {"root"}) and slot_states.get("root") != "active":
        errors.append("root must remain active while any worker is active")

    ready = board.get("ready_queue")
    ready_records: list[dict[str, Any]] = []
    ready_task_paths: set[str] = set()
    if not isinstance(ready, list):
        errors.append("ready_queue must be an array")
    else:
        for index, item in enumerate(ready):
            label = f"ready_queue[{index}]"
            if not isinstance(item, dict):
                errors.append(f"{label} must be an object")
                continue
            task_value = item.get("task_packet")
            path = repo_file(root, task_value, f"{label}.task_packet", errors)
            if path is not None:
                task_identity = canonical_repo_path(root, path)
                prior = task_locations.get(task_identity)
                if prior is not None:
                    errors.append(
                        f"duplicate task packet in {prior} and {label}: {task_identity}"
                    )
                else:
                    task_locations[task_identity] = label
                file_id = filesystem_identity(path)
                if file_id is not None:
                    prior_file = task_file_locations.get(file_id)
                    if prior_file is not None and prior_file != label:
                        errors.append(
                            f"duplicate task file identity in {prior_file} and {label}: {task_identity}"
                        )
                    else:
                        task_file_locations[file_id] = label
                        task_file_paths[file_id] = task_identity
                task_paths.add(task_identity)
                ready_task_paths.add(task_identity)
                queued_task = validate_task(
                    path, f"{label}.task_packet", root, run_id, manifest, errors
                )
                if isinstance(queued_task, dict):
                    logical_id = (queued_task.get("run_id"), queued_task.get("task_id"))
                    if all(isinstance(part, str) and part for part in logical_id):
                        prior_logical = task_logical_locations.get(logical_id)
                        if prior_logical is not None and prior_logical != label:
                            errors.append(
                                f"duplicate logical task {logical_id[0]}/{logical_id[1]} in {prior_logical} and {label}"
                            )
                        else:
                            task_logical_locations[logical_id] = label
                            task_logical_paths[logical_id] = task_identity
            approval_state = item.get("approval_state")
            if approval_state not in {"planned", "approved"}:
                errors.append(f"{label}.approval_state must be planned or approved")
            classification = item.get("classification")
            if classification not in CLASSIFICATIONS - {"orchestration"}:
                errors.append(f"{label}.classification is not dispatchable")
            family = item.get("mechanism_family")
            if family is not None and not valid_family(family):
                errors.append(
                    f"{label}.mechanism_family must be null or a nonempty string without surrounding whitespace"
                )
            if classification in {"proof-producing", "information-gathering"} and not (
                valid_family(family)
            ):
                errors.append(f"{label}.mechanism_family must be nonempty for a mathematical lane")
            compatible_slots = item.get("compatible_slots")
            if not isinstance(compatible_slots, list) or not compatible_slots:
                errors.append(f"{label}.compatible_slots must be a nonempty array")
                compatible_slot_ids: set[str] = set()
            else:
                compatible_slot_ids = {
                    slot_id for slot_id in compatible_slots if isinstance(slot_id, str)
                }
                if len(compatible_slot_ids) != len(compatible_slots) or not compatible_slot_ids <= expected_slot_ids:
                    errors.append(f"{label}.compatible_slots must contain unique recognized slot IDs")
            ready_records.append(
                {
                    "task_packet": task_value,
                    "approval_state": approval_state,
                    "classification": classification,
                    "mechanism_family": family if valid_family(family) else None,
                    "compatible_slots": compatible_slot_ids,
                }
            )
        counts["ready"] = len(ready)

    override = board.get("concentration_override")
    override_families: set[str] = set()
    override_valid = False
    if override is not None:
        if not isinstance(override, dict) or set(override) != {"families", "justification"}:
            errors.append("concentration_override must contain exactly families and justification")
        else:
            families = override.get("families")
            justification = override.get("justification")
            if not isinstance(families, list) or not families or not all(
                valid_family(family) for family in families
            ) or len(set(families)) != len(families):
                errors.append(
                    "concentration_override.families must be unique nonempty strings without surrounding whitespace"
                )
            else:
                override_families = set(families)
            if not isinstance(justification, str) or not justification.strip():
                errors.append("concentration_override.justification must be nonblank")
            else:
                override_valid = bool(override_families)

    overloaded = sorted(family for family, count in active_families.items() if count > 2)
    uncovered = [family for family in overloaded if family not in override_families]
    if uncovered:
        errors.append(
            "more than two mathematical lanes share a mechanism family without a structured concentration_override: "
            + ", ".join(uncovered)
        )
    prospective_override_families = {
        record["mechanism_family"]
        for record in ready_records
        if record["classification"] in {"proof-producing", "information-gathering"}
        and isinstance(record["mechanism_family"], str)
        and active_families[record["mechanism_family"]] >= 2
    }
    if override_families - (set(overloaded) | prospective_override_families):
        errors.append("concentration_override names no active or prospectively overloaded family")

    minimum_ready = board.get("minimum_ready_packets")
    if type(minimum_ready) is not int or minimum_ready < 0:
        errors.append("minimum_ready_packets must be a nonnegative integer")
    elif isinstance(ready, list) and len(ready) < minimum_ready:
        errors.append(
            f"ready queue under floor: {len(ready)} < {minimum_ready}"
        )
    if board.get("mode") == "operational" and isinstance(ready, list):
        unapproved = [item for item in ready if isinstance(item, dict) and item.get("approval_state") != "approved"]
        if unapproved:
            errors.append("operational ready_queue may contain only approved packets")

    operational_wave = board.get("operational_wave")
    approved_wave_tasks: set[str] = set()
    approved_wave_file_paths: dict[tuple[int, int], str] = {}
    approved_wave_logical_paths: dict[tuple[str, str], str] = {}
    if board.get("mode") == "operational":
        wave_reference = validate_hashed_reference(
            operational_wave, root, "operational_wave", errors
        )
        if wave_reference is not None:
            wave_path_value, wave_path = wave_reference
            if wave_path_value not in snapshot_digests:
                errors.append(f"operational_wave must have a snapshot entry: {wave_path_value}")
            try:
                wave = load_json(wave_path)
            except (OSError, json.JSONDecodeError) as exc:
                errors.append(f"cannot parse operational_wave: {exc}")
                wave = None
            expected_wave_keys = {
                "approval_state", "minimum_ready_packets", "approved_task_packets", "thin_wave_reason"
            }
            if not isinstance(wave, dict) or set(wave) != expected_wave_keys:
                errors.append(
                    "operational wave manifest must contain exactly approval_state, minimum_ready_packets, approved_task_packets, and thin_wave_reason"
                )
            else:
                if wave.get("approval_state") != "approved":
                    errors.append("operational wave manifest must be approved")
                wave_floor = wave.get("minimum_ready_packets")
                if type(wave_floor) is not int or wave_floor < 0:
                    errors.append("operational wave minimum_ready_packets must be nonnegative")
                elif wave_floor != minimum_ready:
                    errors.append("board minimum_ready_packets must match the operational wave manifest")
                thin_reason = wave.get("thin_wave_reason")
                if type(wave_floor) is int and wave_floor < 4:
                    if not isinstance(thin_reason, str) or not thin_reason.strip():
                        errors.append("an operational queue floor below four requires an approved thin_wave_reason")
                elif thin_reason is not None:
                    errors.append("thin_wave_reason must be null when the operational queue floor is at least four")
                approved_tasks = wave.get("approved_task_packets")
                if not isinstance(approved_tasks, list):
                    errors.append(
                        "operational wave approved_task_packets must be an array of unique hashed references"
                    )
                else:
                    for index, approved_task in enumerate(approved_tasks):
                        approved_reference = validate_hashed_reference(
                            approved_task,
                            root,
                            f"operational_wave.approved_task_packets[{index}]",
                            errors,
                        )
                        if approved_reference is None:
                            continue
                        approved_identity, approved_path = approved_reference
                        snapshot_digest = snapshot_digests.get(approved_identity)
                        if snapshot_digest is None:
                            errors.append(
                                "operational-wave-approved task must have a snapshot entry: "
                                f"{approved_identity}"
                            )
                        elif snapshot_digest != approved_task["sha256"]:
                            errors.append(
                                "operational-wave-approved task digest must match board snapshot: "
                                f"{approved_identity}"
                            )
                        if approved_identity in approved_wave_tasks:
                            errors.append(
                                "operational wave approved_task_packets must contain unique canonical task paths: "
                                f"{approved_identity}"
                            )
                        approved_wave_tasks.add(approved_identity)
                        approved_file_id = filesystem_identity(approved_path)
                        if approved_file_id is not None:
                            prior_approved_path = approved_wave_file_paths.get(
                                approved_file_id
                            )
                            if (
                                prior_approved_path is not None
                                and prior_approved_path != approved_identity
                            ):
                                errors.append(
                                    "operational wave approved_task_packets name one file more than once: "
                                    f"{prior_approved_path} and {approved_identity}"
                                )
                            else:
                                approved_wave_file_paths[approved_file_id] = approved_identity
                            occupied_path = task_file_paths.get(approved_file_id)
                            if occupied_path is not None and occupied_path != approved_identity:
                                errors.append(
                                    "operational wave and occupancy use different paths for one task file: "
                                    f"{approved_identity} and {occupied_path}"
                                )
                        approved_task = validate_task(
                            approved_path,
                            f"operational_wave.approved_task_packets[{index}]",
                            root,
                            run_id,
                            manifest,
                            errors,
                        )
                        if isinstance(approved_task, dict):
                            approved_logical = (
                                approved_task.get("run_id"),
                                approved_task.get("task_id"),
                            )
                            if all(
                                isinstance(part, str) and part
                                for part in approved_logical
                            ):
                                prior_approved_logical_path = (
                                    approved_wave_logical_paths.get(approved_logical)
                                )
                                if (
                                    prior_approved_logical_path is not None
                                    and prior_approved_logical_path != approved_identity
                                ):
                                    errors.append(
                                        "operational wave approved_task_packets repeat logical task "
                                        f"{approved_logical[0]}/{approved_logical[1]}: "
                                        f"{prior_approved_logical_path} and {approved_identity}"
                                    )
                                else:
                                    approved_wave_logical_paths[approved_logical] = (
                                        approved_identity
                                    )
                                occupied_logical_path = task_logical_paths.get(
                                    approved_logical
                                )
                                if (
                                    occupied_logical_path is not None
                                    and occupied_logical_path != approved_identity
                                ):
                                    errors.append(
                                        "operational wave and occupancy use different paths for logical task "
                                        f"{approved_logical[0]}/{approved_logical[1]}: "
                                        f"{approved_identity} and {occupied_logical_path}"
                                    )
                    for task_path in sorted(active_task_paths):
                        if task_path not in approved_wave_tasks:
                            errors.append(f"active task lacks operational-wave approval: {task_path}")
                    for task_path in sorted(lifecycle_task_paths - active_task_paths):
                        if task_path not in approved_wave_tasks:
                            errors.append(
                                f"lifecycle task lacks operational-wave approval: {task_path}"
                            )
                    for task_path in sorted(ready_task_paths):
                        if task_path not in approved_wave_tasks:
                            errors.append(f"ready task lacks operational-wave approval: {task_path}")
    elif operational_wave is not None:
        errors.append("operational_wave must be null in bootstrap mode")

    for task_path in sorted(task_paths):
        if task_path not in snapshot_digests:
            errors.append(f"task packet must have a snapshot entry: {task_path}")

    vacancy_reason = board.get("vacancy_reason")
    if counts["active"] < 4:
        if not isinstance(vacancy_reason, str) or not vacancy_reason:
            errors.append("sub-capacity board requires an explicit vacancy_reason")
        idle_slots = {slot_id for slot_id, state in slot_states.items() if state == "idle"}

        def dispatchable(record: dict[str, Any]) -> bool:
            if record["approval_state"] != "approved":
                return False
            if not (record["compatible_slots"] & idle_slots):
                return False
            if record["classification"] in {"proof-producing", "information-gathering"}:
                family = record["mechanism_family"]
                if not isinstance(family, str) or not family.strip():
                    return False
                if active_families[family] >= 2 and not (
                    override_valid and family in override_families
                ):
                    return False
            return True

        if any(dispatchable(record) for record in ready_records):
            errors.append("avoidable vacancy: an approved ready packet exists")
    elif vacancy_reason is not None:
        errors.append("vacancy_reason must be null at full occupancy")

    return errors, counts


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--board", required=True, type=Path)
    parser.add_argument(
        "--max-age-minutes",
        type=float,
        default=DEFAULT_MAX_AGE_MINUTES,
        help=f"maximum declared-board age (default: {DEFAULT_MAX_AGE_MINUTES:g} minutes)",
    )
    args = parser.parse_args()
    board_path = args.board if args.board.is_absolute() else ROOT / args.board
    try:
        board = load_json(board_path)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"ERROR: cannot parse board {board_path}: {exc}", file=sys.stderr)
        return 1
    errors, counts = validate_board(
        board, ROOT, max_age_minutes=args.max_age_minutes
    )
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print(
        "rolling pipeline declaration OK: "
        f"active={counts['active']}/{board['capacity']}, mathematical={counts['mathematical']}, "
        f"support={counts['support']}, ready={counts['ready']}"
    )
    print("NOTE: declaration validated; live collaboration state was not independently observed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
