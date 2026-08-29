#!/usr/bin/env python3
"""Persistently schedule authenticated, approved Codex research packets.

The scheduler is deliberately an execution service rather than a research
director.  It may launch only task packets named by an authenticated approved
wave.  Worker process slots and the root-only evidence inbox are independent:
a terminal frees its process lane immediately, but remains unusable as evidence
until root records an authenticated reconciliation receipt.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import fcntl
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import sqlite3
import subprocess
import sys
import time
import tomllib
from typing import Any, Callable, Iterator
import uuid

try:
    from scripts import check_agent_orchestration as orchestration
except ImportError:  # Direct execution places scripts/ on sys.path.
    import check_agent_orchestration as orchestration


ROOT = Path(__file__).resolve().parents[1]
RUNS_ROOT = ROOT / "runs" / "agents"
DEFAULT_SERVICE_DIR = RUNS_ROOT / "research-scheduler-v2"
MANIFEST_PATH = ROOT / "docs" / "agents" / "manifest.toml"
TASK_SCHEMA_PATH = ROOT / "docs" / "agents" / "schemas" / "task-packet.schema.json"
RESULT_SCHEMA_PATH = ROOT / "docs" / "agents" / "schemas" / "result.schema.json"
DISPATCH_SCHEMA_PATH = (
    ROOT / "docs" / "agents" / "schemas" / "research-scheduler-dispatch.schema.json"
)
RESERVE_SCHEMA_PATH = (
    ROOT / "docs" / "agents" / "schemas" / "research-scheduler-reserve.schema.json"
)
LIFECYCLE_SCHEMA_PATH = (
    ROOT / "docs" / "agents" / "schemas" / "wayfinder-thread-lifecycle.schema.json"
)
LIFECYCLE_CHECKER_PATH = ROOT / "scripts" / "check_wayfinder_thread_lifecycle.py"
PROTOCOL = "research-scheduler-v2"
SYSTEMD_UNIT = "erdos-szekeres-research-scheduler-v2.service"
SYSTEMD_DESTINATION = "org.freedesktop.systemd1"
SYSTEMD_MANAGER_PATH = "/org/freedesktop/systemd1"
SYSTEMD_MANAGER_INTERFACE = "org.freedesktop.systemd1.Manager"
ACTIVE_AUTHORIZATION = "active-authorization.json"
AUTHORIZATION_DIR = "authorizations"
DATABASE_NAME = "scheduler.sqlite3"
FORBIDDEN_TASK_IDS = {"sol-factory-refresh-014-current-state-v3"}
TERMINAL_PENDING = {
    "terminal_pending_reconciliation",
    "operational_stop_pending_reconciliation",
}
ACTIVE_STATUSES = {"dispatching", "running"}
FINAL_STATUSES = {"reconciled", "rejected", "superseded"}
SLOT_LABELS = {
    "proof-producing",
    "information-gathering",
    "discovery-support",
    "verification",
}
OCCUPANCY_CLASSES = {"mathematical", "support"}
WEB_SEARCH_MODES = {"disabled", "live"}
REASONING_EFFORTS = {"low", "medium", "high", "xhigh", "max", "ultra"}
HEX64 = re.compile(r"^[0-9a-f]{64}$")


class SchedulerError(ValueError):
    """The scheduler contract, authority, or durable state is invalid."""


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def scheduler_unit_name(service_dir: Path) -> str:
    """Keep the production name stable and isolate acceptance services."""

    if service_dir.resolve() == DEFAULT_SERVICE_DIR.resolve():
        return SYSTEMD_UNIT
    digest = hashlib.sha256(str(service_dir.resolve()).encode()).hexdigest()[:12]
    return f"erdos-szekeres-research-scheduler-v2-{digest}.service"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def atomic_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}-{time.time_ns()}")
    temporary.write_bytes(json_bytes(value))
    os.replace(temporary, path)


def write_once(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json_bytes(value)
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError as exc:
        raise SchedulerError(f"immutable receipt already exists: {repo_relative(path)}") from exc
    with os.fdopen(descriptor, "wb") as handle:
        handle.write(encoded)


def write_once_or_verify(path: Path, encoded: bytes) -> bool:
    """Create an immutable byte string, or accept an identical crash remnant."""

    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError:
        if path.read_bytes() != encoded:
            raise SchedulerError(
                f"immutable crash-recovery artifact differs: {repo_relative(path)}"
            )
        return False
    with os.fdopen(descriptor, "wb") as handle:
        handle.write(encoded)
    return True


def read_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SchedulerError(f"cannot parse {label} {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise SchedulerError(f"{label} must be a JSON object")
    return value


def service_directory(value: Path) -> Path:
    path = value if value.is_absolute() else ROOT / value
    resolved = path.resolve()
    try:
        resolved.relative_to(RUNS_ROOT.resolve())
    except ValueError as exc:
        raise SchedulerError("service directory must be under runs/agents") from exc
    return resolved


def repo_path(value: str | Path, label: str) -> Path:
    path = Path(value)
    resolved = path.resolve() if path.is_absolute() else (ROOT / path).resolve()
    try:
        resolved.relative_to(ROOT.resolve())
    except ValueError as exc:
        raise SchedulerError(f"{label} must remain inside the repository") from exc
    return resolved


def repo_relative(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT.resolve()))
    except ValueError as exc:
        raise SchedulerError(f"path is outside repository: {path}") from exc


def file_receipt(path: Path) -> dict[str, str]:
    return {"path": repo_relative(path), "sha256": sha256(path)}


def current_revision() -> str:
    result = subprocess.run(
        ["git", "--git-dir=.git-data", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if result.returncode != 0:
        raise SchedulerError(f"cannot resolve current revision: {result.stderr.strip()}")
    return result.stdout.strip()


def codex_version(executable: str = "codex") -> str:
    result = subprocess.run(
        [executable, "--version"], cwd=ROOT, text=True, capture_output=True
    )
    if result.returncode != 0:
        raise SchedulerError(f"cannot execute {executable}: {result.stderr.strip()}")
    return result.stdout.strip()


def implementation_paths() -> list[Path]:
    return [
        Path(__file__).resolve(),
        MANIFEST_PATH,
        TASK_SCHEMA_PATH,
        RESULT_SCHEMA_PATH,
        DISPATCH_SCHEMA_PATH,
        RESERVE_SCHEMA_PATH,
        LIFECYCLE_SCHEMA_PATH,
        LIFECYCLE_CHECKER_PATH,
        ROOT / "scripts" / "freeze_agent_context.py",
        ROOT / "scripts" / "check_agent_orchestration.py",
    ]


def implementation_receipts() -> list[dict[str, str]]:
    receipts: list[dict[str, str]] = []
    for path in implementation_paths():
        if not path.is_file():
            raise SchedulerError(f"missing scheduler implementation component: {path}")
        receipts.append(file_receipt(path))
    return receipts


def load_manifest() -> dict[str, Any]:
    try:
        return tomllib.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as exc:
        raise SchedulerError(f"cannot parse agent manifest: {exc}") from exc


def profile_record(profile_id: str) -> dict[str, Any]:
    manifest = load_manifest()
    for profile in manifest.get("profiles", []):
        if isinstance(profile, dict) and profile.get("id") == profile_id:
            return profile
    raise SchedulerError(f"task profile is not registered: {profile_id}")


def validate_task_structure(packet: dict[str, Any], label: str) -> None:
    errors: list[str] = []
    manifest = orchestration.validate_manifest(errors)
    orchestration.validate_task(packet, manifest, label, errors)
    if errors:
        raise SchedulerError("; ".join(errors))


def validate_result_pair(
    task: dict[str, Any], result: dict[str, Any], label: str
) -> None:
    errors: list[str] = []
    manifest = orchestration.validate_manifest(errors)
    orchestration.validate_result(result, manifest, f"{label}.result", errors)
    orchestration.validate_pair(task, result, label, errors)
    if errors:
        raise SchedulerError("; ".join(errors))


def expected_result_path(task: dict[str, Any]) -> Path:
    candidates = [
        item
        for item in task.get("deliverables", [])
        if isinstance(item, str) and Path(item).name == "result.json"
    ]
    if len(candidates) != 1:
        raise SchedulerError("task must declare exactly one result.json deliverable")
    result_path = repo_path(candidates[0], "result deliverable")
    writes = task.get("ownership", {}).get("write_paths", [])
    if candidates[0] not in writes:
        raise SchedulerError("result.json deliverable must be an exact owned write path")
    return result_path


def authenticate_task(
    packet_path: Path,
    packet_sha256: str,
    *,
    require_outputs_absent: bool,
    require_base_revision: bool = True,
) -> dict[str, Any]:
    packet_path = repo_path(packet_path, "task packet")
    if not packet_path.is_file():
        raise SchedulerError(f"task packet does not exist: {repo_relative(packet_path)}")
    if not HEX64.fullmatch(packet_sha256) or sha256(packet_path) != packet_sha256:
        raise SchedulerError("task packet SHA-256 does not authenticate")
    packet = read_json(packet_path, "task packet")
    validate_task_structure(packet, repo_relative(packet_path))
    if packet.get("task_id") in FORBIDDEN_TASK_IDS:
        raise SchedulerError("the immutable historical factory control is not dispatchable")
    if require_base_revision and packet.get("base_revision") not in {
        "NO-COMMIT",
        current_revision(),
    }:
        raise SchedulerError("task base revision is stale")
    inputs = packet.get("inputs", [])
    for item in inputs:
        path = repo_path(item["path"], "task input")
        if not path.is_file() or sha256(path) != item["sha256"]:
            raise SchedulerError(f"task input does not authenticate: {item['path']}")
    profile = profile_record(str(packet.get("profile")))
    profile_path = str(profile.get("path"))
    matching_profile_inputs = [item for item in inputs if item.get("path") == profile_path]
    if len(matching_profile_inputs) != 1:
        raise SchedulerError("task must directly freeze its registered profile")
    result_path = expected_result_path(packet)
    if require_outputs_absent:
        existing = [
            item
            for item in packet.get("deliverables", [])
            if isinstance(item, str) and repo_path(item, "deliverable").exists()
        ]
        if existing:
            raise SchedulerError(
                "task has pre-existing deliverables and cannot be dispatched: "
                + ", ".join(existing)
            )
    packet["_scheduler"] = {
        "path": repo_relative(packet_path),
        "sha256": packet_sha256,
        "profile_path": profile_path,
        "profile_sha256": matching_profile_inputs[0]["sha256"],
        "result_path": repo_relative(result_path),
        "profile_kind": profile.get("kind"),
    }
    return packet


def authenticate_wave(
    wave_path: Path, wave_sha256: str, task_path: Path, task_sha256: str
) -> dict[str, Any]:
    wave_path = repo_path(wave_path, "approved operational wave")
    if not wave_path.is_file() or sha256(wave_path) != wave_sha256:
        raise SchedulerError("operational-wave SHA-256 does not authenticate")
    wave = read_json(wave_path, "approved operational wave")
    required = {
        "approval_state",
        "minimum_ready_packets",
        "approved_task_packets",
        "thin_wave_reason",
    }
    if set(wave) != required:
        raise SchedulerError("operational wave has an unsupported shape")
    if wave.get("approval_state") != "approved":
        raise SchedulerError("operational wave is not approved")
    floor = wave.get("minimum_ready_packets")
    if type(floor) is not int or floor < 0:
        raise SchedulerError("operational wave minimum_ready_packets is invalid")
    thin_reason = wave.get("thin_wave_reason")
    if floor < 4:
        if not isinstance(thin_reason, str) or not thin_reason.strip():
            raise SchedulerError("a thin operational wave requires a reason")
    elif thin_reason is not None:
        raise SchedulerError("a full operational wave cannot carry a thin-wave reason")
    approved = wave.get("approved_task_packets")
    if not isinstance(approved, list):
        raise SchedulerError("operational wave task list is malformed")
    normalized: list[tuple[str, str]] = []
    for item in approved:
        if (
            not isinstance(item, dict)
            or set(item) != {"path", "sha256"}
            or not isinstance(item.get("path"), str)
            or not HEX64.fullmatch(str(item.get("sha256", "")))
        ):
            raise SchedulerError("operational wave contains a malformed task receipt")
        if repo_relative(repo_path(item["path"], "operational-wave task")) != item["path"]:
            raise SchedulerError("operational wave task path is not canonical")
        normalized.append((str(item["path"]), str(item["sha256"])))
    if len(set(normalized)) != len(normalized):
        raise SchedulerError("operational wave repeats a task receipt")
    if len(normalized) < floor:
        raise SchedulerError("operational wave does not meet its minimum-ready floor")
    task_ref = {"path": repo_relative(task_path), "sha256": task_sha256}
    if task_ref not in approved:
        raise SchedulerError("approved wave does not bind this exact task packet")
    return wave


def task_is_builder(task: dict[str, Any]) -> bool:
    if task.get("_scheduler", {}).get("profile_kind") == "builder":
        return True
    writes = task.get("ownership", {}).get("write_paths", [])
    if any(not path.startswith("runs/") for path in writes):
        return True
    commands = "\n".join(task.get("required_checks", [])).lower()
    return any(word in commands for word in ("lake ", "lean ", "solver", "sat "))


def normalized_prefix(pattern: str) -> str:
    wildcard = min(
        [index for token in "*?[" if (index := pattern.find(token)) >= 0]
        or [len(pattern)]
    )
    return pattern[:wildcard].rstrip("/")


def path_patterns_overlap(left: str, right: str) -> bool:
    if fnmatch.fnmatch(left, right) or fnmatch.fnmatch(right, left):
        return True
    left_prefix = normalized_prefix(left)
    right_prefix = normalized_prefix(right)
    if not left_prefix or not right_prefix:
        return True
    return (
        left_prefix == right_prefix
        or left_prefix.startswith(right_prefix + "/")
        or right_prefix.startswith(left_prefix + "/")
    )


def render_worker_prompt(task: dict[str, Any], dispatch: dict[str, Any]) -> str:
    packet = dispatch["task_packet"]
    profile = dispatch["profile"]
    result_path = dispatch["expected_result_path"]
    return f"""Execute exactly one immutable Erdos--Szekeres research task.

Task packet: `{packet['path']}`
Task SHA-256: `{packet['sha256']}`
Profile: `{profile['path']}`
Profile SHA-256: `{profile['sha256']}`
Expected structured result: `{result_path}`

The repository AGENTS.md and the exact task packet are authoritative. Before
substantive work, authenticate the task with
`python3 scripts/check_agent_orchestration.py --task-packet {packet['path']}`
and rehash every declared input. Stop with a schema-valid blocked or
inconclusive result if any authority, input, output-absence, or resource gate
fails. Do not ask the user questions, change the theorem contract, broaden the
task, spawn subagents, edit canonical files, or write outside the exact owned
paths. Checkpoint as required by the packet.

At terminal, write the ordinary result-schema object to `{result_path}`, run
the packet's required terminal validation, and make your final response the
identical raw JSON object with no Markdown fence or extra prose. Agent output
is untrusted until root independently reconciles it; do not edit the
Wayfinder, admit evidence, assign proof movement, or schedule a successor.
"""


def authorization_pointer_path(service_dir: Path) -> Path:
    return service_dir / ACTIVE_AUTHORIZATION


def authorization_path(service_dir: Path, authorization: dict[str, Any]) -> Path:
    encoded = (json.dumps(authorization, indent=2, sort_keys=True) + "\n").encode()
    digest = hashlib.sha256(encoded).hexdigest()
    return service_dir / AUTHORIZATION_DIR / f"{digest}.json"


def make_authorization(args: argparse.Namespace) -> dict[str, Any]:
    service_dir = service_directory(args.service_dir)
    manifest = load_manifest()
    policy = manifest.get("policy", {})
    if args.capacity < 1 or args.capacity > int(policy.get("max_parallel_workers", 1)):
        raise SchedulerError("capacity exceeds manifest policy.max_parallel_workers")
    if args.max_builders < 1 or args.max_builders > int(
        policy.get("max_parallel_builders", 1)
    ):
        raise SchedulerError("max-builders exceeds the manifest policy")
    if args.max_same_family < 1 or args.max_same_family > args.capacity:
        raise SchedulerError("max-same-family must be between one and capacity")
    if args.reserve_floor < 0:
        raise SchedulerError("reserve-floor cannot be negative")
    if args.total_cpu_cores < 1 or args.total_memory_gib < 1 or args.total_output_gib <= 0:
        raise SchedulerError("aggregate resource ceilings must be positive")
    if args.poll_seconds < 2:
        raise SchedulerError("poll-seconds must be at least two")
    if args.reasoning_effort not in REASONING_EFFORTS:
        raise SchedulerError("unsupported reasoning effort")
    executable_path = Path(args.codex_executable)
    resolved_executable = (
        Path(subprocess.check_output(["which", str(executable_path)], text=True).strip())
        if not executable_path.is_absolute()
        else executable_path
    ).resolve()
    if not resolved_executable.is_file():
        raise SchedulerError("resolved Codex executable is not a regular file")
    authorization = {
        "schema_version": 1,
        "protocol": PROTOCOL,
        "created_at": now(),
        "approval_ref": args.approval_ref,
        "service_dir": repo_relative(service_dir),
        "dispatch_enabled": bool(args.dispatch_enabled),
        "provider": {
            "executable": str(resolved_executable),
            "executable_sha256": sha256(resolved_executable),
            "version": codex_version(str(resolved_executable)),
            "allowed_models": list(dict.fromkeys(args.allowed_models)),
            "default_model": args.default_model,
            "default_reasoning_effort": args.reasoning_effort,
        },
        "limits": {
            "capacity": args.capacity,
            "mathematical_target": args.mathematical_target,
            "reserve_floor": args.reserve_floor,
            "max_builders": args.max_builders,
            "max_same_family": args.max_same_family,
            "total_cpu_cores": args.total_cpu_cores,
            "total_memory_gib": args.total_memory_gib,
            "total_output_gib": args.total_output_gib,
            "poll_seconds": args.poll_seconds,
        },
        "authority": {
            "approved_wave_required": True,
            "immutable_task_required": True,
            "approved_reserve_plan_required_for_bulk_import": True,
            "terminal_inbox_separate_from_process_lanes": True,
            "automatic_route_admission": False,
            "automatic_proof_movement": False,
            "automatic_canonical_edits": False,
            "automatic_reconciliation": False,
            "subagents": False,
            "danger_full_access": False,
        },
        "implementation": implementation_receipts(),
    }
    if args.default_model not in authorization["provider"]["allowed_models"]:
        raise SchedulerError("default model must be in allowed-models")
    if args.mathematical_target < 0 or args.mathematical_target > args.capacity:
        raise SchedulerError("mathematical-target must be between zero and capacity")
    return authorization


def verify_authorization(path: Path, service_dir: Path | None = None) -> dict[str, Any]:
    value = read_json(path, "scheduler authorization")
    required = {
        "schema_version",
        "protocol",
        "created_at",
        "approval_ref",
        "service_dir",
        "dispatch_enabled",
        "provider",
        "limits",
        "authority",
        "implementation",
    }
    if set(value) != required or value.get("schema_version") != 1 or value.get("protocol") != PROTOCOL:
        raise SchedulerError("scheduler authorization contract is malformed or unsupported")
    if not isinstance(value.get("approval_ref"), str) or not value["approval_ref"].strip():
        raise SchedulerError("scheduler authorization approval reference is blank")
    resolved_service = service_directory(Path(str(value["service_dir"])))
    if service_dir is not None and resolved_service != service_dir.resolve():
        raise SchedulerError("scheduler authorization binds another service directory")
    if value.get("implementation") != implementation_receipts():
        raise SchedulerError("scheduler implementation drifted after authorization")
    provider = value.get("provider", {})
    provider_keys = {
        "executable",
        "executable_sha256",
        "version",
        "allowed_models",
        "default_model",
        "default_reasoning_effort",
    }
    if not isinstance(provider, dict) or set(provider) != provider_keys:
        raise SchedulerError("scheduler provider authority is malformed")
    allowed_models = provider.get("allowed_models")
    if (
        not isinstance(allowed_models, list)
        or not allowed_models
        or not all(isinstance(model, str) and model for model in allowed_models)
        or len(set(allowed_models)) != len(allowed_models)
        or provider.get("default_model") not in allowed_models
        or provider.get("default_reasoning_effort") not in REASONING_EFFORTS
    ):
        raise SchedulerError("scheduler provider model authority is malformed")
    executable = Path(str(provider.get("executable", ""))).resolve()
    if (
        not executable.is_file()
        or sha256(executable) != provider.get("executable_sha256")
    ):
        raise SchedulerError("Codex executable bytes drifted after authorization")
    if provider.get("version") != codex_version(str(provider.get("executable", "codex"))):
        raise SchedulerError("Codex CLI version drifted after authorization")
    authority = value.get("authority", {})
    true_authority = {
        "approved_wave_required",
        "immutable_task_required",
        "approved_reserve_plan_required_for_bulk_import",
        "terminal_inbox_separate_from_process_lanes",
    }
    false_authority = {
        "automatic_route_admission",
        "automatic_proof_movement",
        "automatic_canonical_edits",
        "automatic_reconciliation",
        "subagents",
        "danger_full_access",
    }
    if not isinstance(authority, dict) or set(authority) != true_authority | false_authority:
        raise SchedulerError("scheduler authority firewall is malformed")
    if any(
        authority.get(key) is not False
        for key in false_authority
    ):
        raise SchedulerError("scheduler authorization exceeds the v2 authority boundary")
    if any(authority.get(key) is not True for key in true_authority):
        raise SchedulerError("scheduler authorization weakened packet or lane admission")
    limits = value.get("limits", {})
    limit_keys = {
        "capacity",
        "mathematical_target",
        "reserve_floor",
        "max_builders",
        "max_same_family",
        "total_cpu_cores",
        "total_memory_gib",
        "total_output_gib",
        "poll_seconds",
    }
    if not isinstance(limits, dict) or set(limits) != limit_keys:
        raise SchedulerError("scheduler resource limits are malformed")
    policy = load_manifest().get("policy", {})
    integer_keys = {
        "capacity",
        "mathematical_target",
        "reserve_floor",
        "max_builders",
        "max_same_family",
        "total_cpu_cores",
        "total_memory_gib",
        "poll_seconds",
    }
    if any(type(limits.get(key)) is not int for key in integer_keys):
        raise SchedulerError("scheduler integer resource limits are malformed")
    if (
        limits["capacity"] < 1
        or limits["capacity"] > int(policy.get("max_parallel_workers", 1))
        or not 0 <= limits["mathematical_target"] <= limits["capacity"]
        or limits["reserve_floor"] < 0
        or not 1 <= limits["max_builders"] <= int(policy.get("max_parallel_builders", 1))
        or not 1 <= limits["max_same_family"] <= limits["capacity"]
        or limits["total_cpu_cores"] < 1
        or limits["total_memory_gib"] < 1
        or not isinstance(limits["total_output_gib"], (int, float))
        or isinstance(limits["total_output_gib"], bool)
        or limits["total_output_gib"] <= 0
        or limits["poll_seconds"] < 2
    ):
        raise SchedulerError("scheduler resource limits exceed the supported envelope")
    return value


def active_authorization(service_dir: Path) -> tuple[Path, dict[str, Any]]:
    pointer = read_json(authorization_pointer_path(service_dir), "active authorization pointer")
    receipt = pointer.get("authorization")
    if not isinstance(receipt, dict):
        raise SchedulerError("active authorization pointer is malformed")
    path = repo_path(str(receipt.get("path")), "active authorization")
    auth_root = (service_dir / AUTHORIZATION_DIR).resolve()
    try:
        path.relative_to(auth_root)
    except ValueError as exc:
        raise SchedulerError("active authorization is outside its immutable directory") from exc
    if sha256(path) != receipt.get("sha256"):
        raise SchedulerError("active authorization pointer hash does not authenticate")
    return path, verify_authorization(path, service_dir)


def command_configure(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    if daemon_receipt(service_dir) is not None:
        raise SchedulerError("stop the live scheduler before rotating authorization")
    authorization = make_authorization(args)
    path = authorization_path(service_dir, authorization)
    write_once(path, authorization)
    verify_authorization(path, service_dir)
    pointer = {
        "schema_version": 1,
        "protocol": PROTOCOL,
        "rotated_at": now(),
        "authorization": file_receipt(path),
    }
    atomic_json(authorization_pointer_path(service_dir), pointer)
    print(
        json.dumps(
            {
                "authorization": file_receipt(path),
                "active_pointer": file_receipt(authorization_pointer_path(service_dir)),
                "dispatch_enabled": authorization["dispatch_enabled"],
                "limits": authorization["limits"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


def database_path(service_dir: Path) -> Path:
    return service_dir / DATABASE_NAME


@contextmanager
def database(service_dir: Path) -> Iterator[sqlite3.Connection]:
    service_dir.mkdir(parents=True, exist_ok=True)
    connection = sqlite3.connect(database_path(service_dir), timeout=30)
    connection.row_factory = sqlite3.Row
    connection.execute("PRAGMA foreign_keys = ON")
    connection.execute("PRAGMA journal_mode = WAL")
    try:
        yield connection
        connection.commit()
    finally:
        connection.close()


def initialize_database(service_dir: Path, authorization: dict[str, Any]) -> None:
    capacity = int(authorization["limits"]["capacity"])
    with database(service_dir) as connection:
        connection.executescript(
            """
            CREATE TABLE IF NOT EXISTS metadata (
              key TEXT PRIMARY KEY,
              value TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS lanes (
              lane_id INTEGER PRIMARY KEY,
              state TEXT NOT NULL,
              job_id TEXT,
              blocked_reason TEXT
            );
            CREATE TABLE IF NOT EXISTS jobs (
              job_id TEXT PRIMARY KEY,
              task_id TEXT NOT NULL UNIQUE,
              receipt_path TEXT NOT NULL,
              receipt_sha256 TEXT NOT NULL,
              task_path TEXT NOT NULL,
              task_sha256 TEXT NOT NULL,
              wave_path TEXT NOT NULL,
              wave_sha256 TEXT NOT NULL,
              approval_ref TEXT NOT NULL,
              slot_label TEXT NOT NULL,
              occupancy_class TEXT NOT NULL,
              mechanism_family TEXT,
              priority INTEGER NOT NULL,
              profile TEXT NOT NULL,
              is_builder INTEGER NOT NULL,
              write_paths_json TEXT NOT NULL,
              expected_result_path TEXT NOT NULL,
              model TEXT NOT NULL,
              reasoning_effort TEXT NOT NULL,
              web_search TEXT NOT NULL,
              sandbox TEXT NOT NULL,
              resume_limit INTEGER NOT NULL,
              resume_count INTEGER NOT NULL DEFAULT 0,
              wall_minutes INTEGER NOT NULL,
              cpu_cores INTEGER NOT NULL,
              memory_gib INTEGER NOT NULL,
              output_gib REAL NOT NULL,
              status TEXT NOT NULL,
              lane_id INTEGER,
              current_attempt INTEGER NOT NULL DEFAULT 0,
              unit_name TEXT,
              created_at TEXT NOT NULL,
              started_at TEXT,
              terminal_at TEXT,
              reconciled_at TEXT,
              last_error TEXT,
              FOREIGN KEY(lane_id) REFERENCES lanes(lane_id)
            );
            CREATE TABLE IF NOT EXISTS attempts (
              job_id TEXT NOT NULL,
              ordinal INTEGER NOT NULL,
              status TEXT NOT NULL,
              unit_name TEXT NOT NULL,
              started_at TEXT NOT NULL,
              ended_at TEXT,
              thread_id TEXT,
              terminal_path TEXT NOT NULL,
              terminal_sha256 TEXT,
              PRIMARY KEY(job_id, ordinal),
              FOREIGN KEY(job_id) REFERENCES jobs(job_id)
            );
            CREATE TABLE IF NOT EXISTS events (
              sequence INTEGER PRIMARY KEY AUTOINCREMENT,
              recorded_at TEXT NOT NULL,
              event TEXT NOT NULL,
              job_id TEXT,
              details_json TEXT NOT NULL
            );
            """
        )
        recorded = connection.execute(
            "SELECT value FROM metadata WHERE key = 'protocol'"
        ).fetchone()
        if recorded is not None and recorded["value"] != PROTOCOL:
            raise SchedulerError("scheduler database protocol is incompatible")
        connection.execute(
            "INSERT OR REPLACE INTO metadata(key, value) VALUES('protocol', ?)",
            (PROTOCOL,),
        )
        connection.execute(
            "INSERT OR REPLACE INTO metadata(key, value) VALUES('capacity', ?)",
            (str(capacity),),
        )
        occupied_above = connection.execute(
            "SELECT lane_id FROM lanes WHERE lane_id > ? AND job_id IS NOT NULL", (capacity,)
        ).fetchall()
        if occupied_above:
            raise SchedulerError("cannot shrink capacity below an occupied lane")
        connection.execute("DELETE FROM lanes WHERE lane_id > ?", (capacity,))
        for lane_id in range(1, capacity + 1):
            connection.execute(
                "INSERT OR IGNORE INTO lanes(lane_id, state, job_id, blocked_reason) VALUES(?, 'free', NULL, NULL)",
                (lane_id,),
            )


def record_event(
    connection: sqlite3.Connection,
    event: str,
    *,
    job_id: str | None = None,
    details: dict[str, Any] | None = None,
) -> None:
    connection.execute(
        "INSERT INTO events(recorded_at, event, job_id, details_json) VALUES(?, ?, ?, ?)",
        (now(), event, job_id, json.dumps(details or {}, sort_keys=True)),
    )


def dispatch_receipt_path(service_dir: Path, job_id: str) -> Path:
    return service_dir / "jobs" / job_id / "dispatch.json"


def worker_prompt_path(service_dir: Path, job_id: str) -> Path:
    return service_dir / "jobs" / job_id / "prompt.md"


def attempt_directory(service_dir: Path, job_id: str, ordinal: int) -> Path:
    return service_dir / "jobs" / job_id / "attempts" / f"{ordinal:03d}"


def lifecycle_inbox_path(service_dir: Path, job_id: str) -> Path:
    return service_dir / "lifecycle-inbox" / f"{job_id}.json"


def lifecycle_inbox(
    service_dir: Path,
    row: sqlite3.Row,
    terminal_path: Path,
    terminal: dict[str, Any],
    *,
    effective_valid: bool,
) -> dict[str, Any]:
    task_path = repo_path(row["task_path"], "lifecycle task packet")
    task = read_json(task_path, "lifecycle task packet")
    ticket = task.get("wayfinder_ticket")
    if not isinstance(ticket, str) or not ticket:
        raise SchedulerError("a scheduled thread must name its owning Wayfinder ticket")
    ticket_path = repo_path(ticket, "owning Wayfinder ticket")
    if not ticket_path.is_file():
        raise SchedulerError("owning Wayfinder ticket is absent")
    dispatch_path = repo_path(row["receipt_path"], "lifecycle dispatch receipt")
    return {
        "schema_version": 1,
        "protocol": "wayfinder-thread-lifecycle-v1",
        "created_at": str(terminal.get("finished_at") or row["terminal_at"] or now()),
        "job_id": row["job_id"],
        "task_packet": file_receipt(task_path),
        "dispatch": file_receipt(dispatch_path),
        "terminal": file_receipt(terminal_path),
        "result": terminal.get("result") if effective_valid else None,
        "wayfinder_ticket": repo_relative(ticket_path),
    }


def prepare_job(
    service_dir: Path,
    authorization_path_value: Path,
    authorization: dict[str, Any],
    args: argparse.Namespace,
    *,
    reserve_plan: dict[str, str] | None,
    created_at: str | None = None,
    require_outputs_absent: bool = True,
) -> dict[str, Any]:
    """Authenticate and render one job without mutating scheduler state."""

    if not authorization["dispatch_enabled"]:
        raise SchedulerError("active authorization is observer-only; dispatch is disabled")
    task_path = repo_path(args.task_packet, "task packet")
    task = authenticate_task(
        task_path,
        args.task_sha256,
        require_outputs_absent=require_outputs_absent,
    )
    wave_path = repo_path(args.operational_wave, "approved operational wave")
    authenticate_wave(wave_path, args.wave_sha256, task_path, args.task_sha256)
    if args.slot_label not in SLOT_LABELS:
        raise SchedulerError("unrecognized slot label")
    if args.occupancy_class not in OCCUPANCY_CLASSES:
        raise SchedulerError("unrecognized occupancy class")
    if args.occupancy_class == "mathematical" and not args.mechanism_family:
        raise SchedulerError("mathematical work requires a mechanism family")
    if args.occupancy_class == "support" and args.mechanism_family is not None:
        raise SchedulerError("support work cannot masquerade as a mathematical family")
    if args.web_search not in WEB_SEARCH_MODES:
        raise SchedulerError("unrecognized web-search mode")
    provider = authorization["provider"]
    model = args.model or provider["default_model"]
    if model not in provider["allowed_models"]:
        raise SchedulerError("requested model is outside the standing authorization")
    effort = args.reasoning_effort or provider["default_reasoning_effort"]
    if effort not in REASONING_EFFORTS:
        raise SchedulerError("unrecognized reasoning effort")
    if args.resume_limit < 0 or args.resume_limit > 1:
        raise SchedulerError("the scheduler permits at most one same-thread crash resume")
    budget = task["budget"]
    limits = authorization["limits"]
    if budget["cpu_cores"] > limits["total_cpu_cores"]:
        raise SchedulerError("task CPU budget exceeds scheduler aggregate ceiling")
    if budget["memory_gib"] > limits["total_memory_gib"]:
        raise SchedulerError("task memory budget exceeds scheduler aggregate ceiling")
    if budget["output_gib"] > limits["total_output_gib"]:
        raise SchedulerError("task output budget exceeds scheduler aggregate ceiling")
    job_id = f"{task['task_id']}-{args.task_sha256[:12]}"
    receipt_path = dispatch_receipt_path(service_dir, job_id)
    prompt_path = worker_prompt_path(service_dir, job_id)
    profile_path = repo_path(task["_scheduler"]["profile_path"], "profile")
    dispatch: dict[str, Any] = {
        "schema_version": 1,
        "protocol": PROTOCOL,
        "job_id": job_id,
        "created_at": created_at or now(),
        "task_packet": file_receipt(task_path),
        "operational_wave": file_receipt(wave_path),
        "reserve_plan": reserve_plan,
        "approval_ref": args.approval_ref,
        "slot_label": args.slot_label,
        "occupancy_class": args.occupancy_class,
        "mechanism_family": args.mechanism_family,
        "priority": args.priority,
        "profile": {
            "id": task["profile"],
            "path": repo_relative(profile_path),
            "sha256": sha256(profile_path),
        },
        "expected_result_path": task["_scheduler"]["result_path"],
        "provider": {
            "model": model,
            "reasoning_effort": effort,
            "web_search": args.web_search,
            "sandbox": "workspace-write" if task["ownership"]["write_paths"] else "read-only",
        },
        "resume_policy": {"max_same_thread_resumes": args.resume_limit},
        "budget": budget,
        "authorization": file_receipt(authorization_path_value),
    }
    prompt = render_worker_prompt(task, dispatch)
    prompt_encoded = prompt.encode("utf-8")
    dispatch["prompt"] = {
        "path": repo_relative(prompt_path),
        "sha256": sha256_bytes(prompt_encoded),
    }
    dispatch_encoded = json_bytes(dispatch)
    return {
        "job_id": job_id,
        "task": task,
        "task_path": task_path,
        "task_sha256": args.task_sha256,
        "wave_path": wave_path,
        "wave_sha256": args.wave_sha256,
        "approval_ref": args.approval_ref,
        "slot_label": args.slot_label,
        "occupancy_class": args.occupancy_class,
        "mechanism_family": args.mechanism_family,
        "priority": args.priority,
        "model": model,
        "reasoning_effort": effort,
        "web_search": args.web_search,
        "resume_limit": args.resume_limit,
        "dispatch": dispatch,
        "dispatch_path": receipt_path,
        "dispatch_encoded": dispatch_encoded,
        "dispatch_sha256": sha256_bytes(dispatch_encoded),
        "prompt_path": prompt_path,
        "prompt_encoded": prompt_encoded,
    }


def persist_prepared_jobs(
    service_dir: Path,
    authorization: dict[str, Any],
    prepared_jobs: list[dict[str, Any]],
    *,
    allow_identical_existing: bool,
) -> tuple[list[str], list[str]]:
    """Crash-safely admit preflighted jobs in one SQLite transaction."""

    initialize_database(service_dir, authorization)
    admitted: list[str] = []
    already_present: list[str] = []
    with database(service_dir) as connection:
        connection.execute("BEGIN IMMEDIATE")
        for prepared in prepared_jobs:
            job_id = prepared["job_id"]
            existing = connection.execute(
                "SELECT * FROM jobs WHERE job_id=? OR task_id=?",
                (job_id, prepared["task"]["task_id"]),
            ).fetchone()
            if existing is not None:
                if not allow_identical_existing:
                    raise SchedulerError("task packet has already entered the scheduler")
                dispatch_path = prepared["dispatch_path"]
                if (
                    existing["job_id"] != job_id
                    or existing["receipt_path"] != repo_relative(dispatch_path)
                    or existing["receipt_sha256"] != prepared["dispatch_sha256"]
                    or not dispatch_path.is_file()
                    or dispatch_path.read_bytes() != prepared["dispatch_encoded"]
                    or not prepared["prompt_path"].is_file()
                    or prepared["prompt_path"].read_bytes() != prepared["prompt_encoded"]
                ):
                    raise SchedulerError("existing job differs from the approved reserve plan")
                already_present.append(job_id)
                continue
            if not allow_identical_existing and (
                prepared["dispatch_path"].exists() or prepared["prompt_path"].exists()
            ):
                raise SchedulerError("job identity has already been frozen")
            write_once_or_verify(prepared["prompt_path"], prepared["prompt_encoded"])
            write_once_or_verify(prepared["dispatch_path"], prepared["dispatch_encoded"])
            task = prepared["task"]
            budget = task["budget"]
            connection.execute(
                """
                INSERT INTO jobs(
                  job_id, task_id, receipt_path, receipt_sha256, task_path,
                  task_sha256, wave_path, wave_sha256, approval_ref, slot_label,
                  occupancy_class, mechanism_family, priority, profile,
                  is_builder, write_paths_json, expected_result_path, model,
                  reasoning_effort, web_search, sandbox, resume_limit,
                  wall_minutes, cpu_cores, memory_gib, output_gib, status,
                  created_at
                ) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'queued', ?)
                """,
                (
                    job_id,
                    task["task_id"],
                    repo_relative(prepared["dispatch_path"]),
                    prepared["dispatch_sha256"],
                    repo_relative(prepared["task_path"]),
                    prepared["task_sha256"],
                    repo_relative(prepared["wave_path"]),
                    prepared["wave_sha256"],
                    prepared["approval_ref"],
                    prepared["slot_label"],
                    prepared["occupancy_class"],
                    prepared["mechanism_family"],
                    prepared["priority"],
                    task["profile"],
                    int(task_is_builder(task)),
                    json.dumps(task["ownership"]["write_paths"], sort_keys=True),
                    task["_scheduler"]["result_path"],
                    prepared["model"],
                    prepared["reasoning_effort"],
                    prepared["web_search"],
                    prepared["dispatch"]["provider"]["sandbox"],
                    prepared["resume_limit"],
                    budget["wall_minutes"],
                    budget["cpu_cores"],
                    budget["memory_gib"],
                    budget["output_gib"],
                    prepared["dispatch"]["created_at"],
                ),
            )
            record_event(
                connection,
                "job-enqueued",
                job_id=job_id,
                details={
                    "dispatch": {
                        "path": repo_relative(prepared["dispatch_path"]),
                        "sha256": prepared["dispatch_sha256"],
                    },
                    "reserve_plan": prepared["dispatch"]["reserve_plan"],
                },
            )
            admitted.append(job_id)
    return admitted, already_present


def command_enqueue(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    authorization_path_value, authorization = active_authorization(service_dir)
    prepared = prepare_job(
        service_dir,
        authorization_path_value,
        authorization,
        args,
        reserve_plan=None,
    )
    persist_prepared_jobs(
        service_dir, authorization, [prepared], allow_identical_existing=False
    )
    print(
        json.dumps(
            {
                "job_id": prepared["job_id"],
                "dispatch": {
                    "path": repo_relative(prepared["dispatch_path"]),
                    "sha256": prepared["dispatch_sha256"],
                },
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


def authenticate_reserve_plan(
    plan_path: Path,
    plan_sha256: str,
    authorization_path_value: Path,
    approval_ref: str,
) -> tuple[dict[str, Any], Path, str]:
    plan_path = repo_path(plan_path, "approved reserve plan")
    if not plan_path.is_file() or not HEX64.fullmatch(plan_sha256) or sha256(plan_path) != plan_sha256:
        raise SchedulerError("reserve-plan SHA-256 does not authenticate")
    plan = read_json(plan_path, "approved reserve plan")
    required = {
        "schema_version",
        "protocol",
        "created_at",
        "approval_state",
        "approval_ref",
        "authorization",
        "operational_wave",
        "minimum_ready_packets",
        "jobs",
    }
    if set(plan) != required or plan.get("schema_version") != 1 or plan.get("protocol") != PROTOCOL:
        raise SchedulerError("reserve plan has an unsupported shape or protocol")
    if not isinstance(plan.get("created_at"), str) or not plan["created_at"].strip():
        raise SchedulerError("reserve plan created_at is invalid")
    if plan.get("approval_state") != "approved" or plan.get("approval_ref") != approval_ref:
        raise SchedulerError("reserve plan does not bind the literal user approval")
    if plan.get("authorization") != file_receipt(authorization_path_value):
        raise SchedulerError("reserve plan does not bind the active standing authorization")
    wave_receipt = plan.get("operational_wave")
    if not isinstance(wave_receipt, dict) or set(wave_receipt) != {"path", "sha256"}:
        raise SchedulerError("reserve plan has a malformed operational-wave receipt")
    wave_path = repo_path(str(wave_receipt.get("path")), "approved operational wave")
    wave_sha256 = str(wave_receipt.get("sha256", ""))
    if not wave_path.is_file() or not HEX64.fullmatch(wave_sha256) or sha256(wave_path) != wave_sha256:
        raise SchedulerError("reserve plan operational wave does not authenticate")
    jobs = plan.get("jobs")
    floor = plan.get("minimum_ready_packets")
    if type(floor) is not int or floor < 0 or not isinstance(jobs, list) or not jobs:
        raise SchedulerError("reserve plan has an invalid floor or empty job list")
    job_keys = {
        "task_packet",
        "slot_label",
        "occupancy_class",
        "mechanism_family",
        "priority",
        "provider",
        "resume_limit",
    }
    task_receipts: list[dict[str, str]] = []
    for job in jobs:
        if not isinstance(job, dict) or set(job) != job_keys:
            raise SchedulerError("reserve plan contains a malformed job specification")
        receipt = job.get("task_packet")
        provider = job.get("provider")
        if (
            not isinstance(receipt, dict)
            or set(receipt) != {"path", "sha256"}
            or not isinstance(provider, dict)
            or set(provider) != {"model", "reasoning_effort", "web_search"}
        ):
            raise SchedulerError("reserve plan contains a malformed task or provider receipt")
        if (
            job.get("slot_label") not in SLOT_LABELS
            or job.get("occupancy_class") not in OCCUPANCY_CLASSES
            or type(job.get("priority")) is not int
            or type(job.get("resume_limit")) is not int
            or job["resume_limit"] not in {0, 1}
            or provider.get("web_search") not in WEB_SEARCH_MODES
            or provider.get("reasoning_effort") not in REASONING_EFFORTS | {None}
            or not (
                provider.get("model") is None
                or isinstance(provider.get("model"), str)
            )
        ):
            raise SchedulerError("reserve plan contains invalid dispatch metadata")
        if job["occupancy_class"] == "mathematical":
            if not isinstance(job.get("mechanism_family"), str) or not job["mechanism_family"].strip():
                raise SchedulerError("reserve mathematical job lacks a mechanism family")
        elif job.get("mechanism_family") is not None:
            raise SchedulerError("reserve support job has a mathematical mechanism family")
        task_receipts.append(receipt)
    if len({(item.get("path"), item.get("sha256")) for item in task_receipts}) != len(task_receipts):
        raise SchedulerError("reserve plan repeats a task packet")
    first_task = task_receipts[0]
    wave = authenticate_wave(
        wave_path,
        wave_sha256,
        repo_path(str(first_task.get("path")), "reserve task packet"),
        str(first_task.get("sha256", "")),
    )
    if floor != wave["minimum_ready_packets"] or len(jobs) < floor:
        raise SchedulerError("reserve plan does not meet the approved wave floor")
    if {
        (str(item.get("path")), str(item.get("sha256"))) for item in task_receipts
    } != {
        (str(item.get("path")), str(item.get("sha256")))
        for item in wave["approved_task_packets"]
    }:
        raise SchedulerError("reserve plan must cover the approved wave exactly")
    return plan, wave_path, wave_sha256


def command_import_reserve(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    authorization_path_value, authorization = active_authorization(service_dir)
    if not authorization["dispatch_enabled"]:
        raise SchedulerError("active authorization is observer-only; reserve import is disabled")
    plan_path = repo_path(args.reserve_plan, "approved reserve plan")
    plan, wave_path, wave_sha256 = authenticate_reserve_plan(
        plan_path, args.reserve_sha256, authorization_path_value, args.approval_ref
    )
    reserve_receipt = file_receipt(plan_path)
    prepared_jobs: list[dict[str, Any]] = []
    for job in plan["jobs"]:
        task_receipt = job["task_packet"]
        provider = job["provider"]
        job_args = argparse.Namespace(
            task_packet=repo_path(task_receipt["path"], "reserve task packet"),
            task_sha256=task_receipt["sha256"],
            operational_wave=wave_path,
            wave_sha256=wave_sha256,
            approval_ref=args.approval_ref,
            slot_label=job["slot_label"],
            occupancy_class=job["occupancy_class"],
            mechanism_family=job["mechanism_family"],
            priority=job["priority"],
            model=provider["model"],
            reasoning_effort=provider["reasoning_effort"],
            web_search=provider["web_search"],
            resume_limit=job["resume_limit"],
        )
        prepared_jobs.append(
            prepare_job(
                service_dir,
                authorization_path_value,
                authorization,
                job_args,
                reserve_plan=reserve_receipt,
                created_at=plan["created_at"],
                require_outputs_absent=False,
            )
        )
    if len({item["job_id"] for item in prepared_jobs}) != len(prepared_jobs):
        raise SchedulerError("reserve plan produces duplicate scheduler job identities")
    initialize_database(service_dir, authorization)
    with database(service_dir) as connection:
        existing_job_ids = {
            row["job_id"]
            for row in connection.execute("SELECT job_id FROM jobs").fetchall()
        }
    for prepared in prepared_jobs:
        if prepared["job_id"] in existing_job_ids:
            continue
        existing_outputs = [
            path
            for path in prepared["task"].get("deliverables", [])
            if isinstance(path, str) and repo_path(path, "deliverable").exists()
        ]
        if existing_outputs:
            raise SchedulerError(
                "reserve task has pre-existing deliverables and cannot be admitted: "
                + ", ".join(existing_outputs)
            )
    admitted, already_present = persist_prepared_jobs(
        service_dir,
        authorization,
        prepared_jobs,
        allow_identical_existing=True,
    )
    import_receipt = {
        "schema_version": 1,
        "protocol": PROTOCOL,
        "created_at": plan["created_at"],
        "approval_ref": args.approval_ref,
        "authorization": file_receipt(authorization_path_value),
        "reserve_plan": reserve_receipt,
        "operational_wave": file_receipt(wave_path),
        "jobs": [item["job_id"] for item in prepared_jobs],
    }
    import_path = service_dir / "imports" / f"{args.reserve_sha256}.json"
    write_once_or_verify(import_path, json_bytes(import_receipt))
    state = scheduler_tick(
        service_dir,
        authorization_path_value,
        authorization,
        launch=not args.no_backfill,
    )
    print(
        json.dumps(
            {
                "import": file_receipt(import_path),
                "admitted": admitted,
                "already_present": already_present,
                "state": state,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


def load_dispatch(service_dir: Path, row: sqlite3.Row) -> dict[str, Any]:
    path = repo_path(row["receipt_path"], "dispatch receipt")
    if not path.is_file() or sha256(path) != row["receipt_sha256"]:
        raise SchedulerError(f"dispatch receipt drifted for {row['job_id']}")
    dispatch = read_json(path, "dispatch receipt")
    required = {
        "schema_version",
        "protocol",
        "job_id",
        "created_at",
        "task_packet",
        "operational_wave",
        "reserve_plan",
        "approval_ref",
        "slot_label",
        "occupancy_class",
        "mechanism_family",
        "priority",
        "profile",
        "expected_result_path",
        "provider",
        "resume_policy",
        "budget",
        "authorization",
        "prompt",
    }
    if (
        set(dispatch) != required
        or dispatch.get("schema_version") != 1
        or dispatch.get("protocol") != PROTOCOL
        or dispatch.get("job_id") != row["job_id"]
    ):
        raise SchedulerError("dispatch receipt identity is malformed")
    for key in ("task_packet", "operational_wave", "authorization", "prompt"):
        receipt = dispatch.get(key)
        if not isinstance(receipt, dict) or set(receipt) != {"path", "sha256"}:
            raise SchedulerError(f"dispatch {key} receipt is malformed")
        receipt_path = repo_path(str(receipt["path"]), f"dispatch {key}")
        if not receipt_path.is_file() or sha256(receipt_path) != receipt["sha256"]:
            raise SchedulerError(f"dispatch {key} receipt does not authenticate")
    reserve = dispatch.get("reserve_plan")
    if reserve is not None:
        if not isinstance(reserve, dict) or set(reserve) != {"path", "sha256"}:
            raise SchedulerError("dispatch reserve-plan receipt is malformed")
        reserve_path = repo_path(str(reserve["path"]), "dispatch reserve plan")
        if not reserve_path.is_file() or sha256(reserve_path) != reserve["sha256"]:
            raise SchedulerError("dispatch reserve-plan receipt does not authenticate")
    return dispatch


def active_rows(connection: sqlite3.Connection) -> list[sqlite3.Row]:
    return connection.execute(
        "SELECT * FROM jobs WHERE status IN ('dispatching', 'running') ORDER BY lane_id"
    ).fetchall()


def candidate_compatible(
    candidate: sqlite3.Row,
    active: list[sqlite3.Row],
    authorization: dict[str, Any],
) -> tuple[bool, str | None]:
    limits = authorization["limits"]
    if candidate["is_builder"] and sum(int(row["is_builder"]) for row in active) >= limits["max_builders"]:
        return False, "builder-limit"
    if candidate["occupancy_class"] == "mathematical":
        same_family = sum(
            1
            for row in active
            if row["occupancy_class"] == "mathematical"
            and row["mechanism_family"] == candidate["mechanism_family"]
        )
        if same_family >= limits["max_same_family"]:
            return False, "mechanism-family-concentration"
    for key in ("cpu_cores", "memory_gib", "output_gib"):
        ceiling_key = {
            "cpu_cores": "total_cpu_cores",
            "memory_gib": "total_memory_gib",
            "output_gib": "total_output_gib",
        }[key]
        if sum(float(row[key]) for row in active) + float(candidate[key]) > float(limits[ceiling_key]):
            return False, f"aggregate-{key}-limit"
    candidate_writes = json.loads(candidate["write_paths_json"])
    for row in active:
        for left in candidate_writes:
            for right in json.loads(row["write_paths_json"]):
                if path_patterns_overlap(left, right):
                    return False, "write-set-overlap"
    return True, None


def worker_unit_name(job_id: str, ordinal: int) -> str:
    digest = hashlib.sha256(job_id.encode()).hexdigest()[:16]
    return f"erdos-es-rs-{digest}-a{ordinal}.service"


def worker_systemd_command(
    service_dir: Path,
    job_id: str,
    ordinal: int,
    row: sqlite3.Row,
    authorization_sha256: str,
) -> list[str]:
    attempt_dir = attempt_directory(service_dir, job_id, ordinal)
    attempt_dir.mkdir(parents=True, exist_ok=True)
    unit = worker_unit_name(job_id, ordinal)
    output_bytes = max(1, int(float(row["output_gib"]) * (1024**3)))
    runtime_seconds = int(row["wall_minutes"]) * 60 + 90
    return [
        "systemd-run",
        "--user",
        f"--unit={unit}",
        "--collect",
        "--service-type=exec",
        "--no-block",
        f"--property=WorkingDirectory={ROOT}",
        "--property=KillMode=control-group",
        f"--property=MemoryMax={int(row['memory_gib'])}G",
        f"--property=CPUQuota={int(row['cpu_cores']) * 100}%",
        f"--property=TasksMax={max(64, int(row['cpu_cores']) * 64)}",
        f"--property=RuntimeMaxSec={runtime_seconds}",
        f"--property=LimitFSIZE={output_bytes}",
        f"--property=StandardOutput=append:{attempt_dir / 'wrapper.log'}",
        f"--property=StandardError=append:{attempt_dir / 'wrapper.log'}",
        "--setenv=PYTHONUNBUFFERED=1",
        "--",
        sys.executable,
        str(Path(__file__).resolve()),
        "worker",
        "--service-dir",
        str(service_dir),
        "--job-id",
        job_id,
        "--attempt",
        str(ordinal),
        "--authorization-sha256",
        authorization_sha256,
    ]


def launch_candidate(
    service_dir: Path,
    connection: sqlite3.Connection,
    candidate: sqlite3.Row,
    lane_id: int,
    authorization_path_value: Path,
    runner: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
) -> None:
    ordinal = int(candidate["current_attempt"]) + 1
    unit = worker_unit_name(candidate["job_id"], ordinal)
    terminal_path = attempt_directory(service_dir, candidate["job_id"], ordinal) / "terminal.json"
    started = now()
    connection.execute(
        "UPDATE lanes SET state='running', job_id=?, blocked_reason=NULL WHERE lane_id=?",
        (candidate["job_id"], lane_id),
    )
    connection.execute(
        """
        UPDATE jobs SET status='dispatching', lane_id=?, current_attempt=?,
          unit_name=?, started_at=COALESCE(started_at, ?), last_error=NULL
        WHERE job_id=? AND status='queued'
        """,
        (lane_id, ordinal, unit, started, candidate["job_id"]),
    )
    connection.execute(
        """
        INSERT INTO attempts(job_id, ordinal, status, unit_name, started_at, terminal_path)
        VALUES(?, ?, 'dispatching', ?, ?, ?)
        """,
        (
            candidate["job_id"],
            ordinal,
            unit,
            started,
            repo_relative(terminal_path),
        ),
    )
    record_event(
        connection,
        "dispatch-attempt-recorded",
        job_id=candidate["job_id"],
        details={"lane_id": lane_id, "attempt": ordinal, "unit": unit},
    )
    connection.commit()  # Attempt is durable before process creation.
    command = worker_systemd_command(
        service_dir,
        candidate["job_id"],
        ordinal,
        candidate,
        sha256(authorization_path_value),
    )
    result = runner(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode != 0:
        reason = f"systemd worker launch failed: {result.stderr.strip()}"
        terminal = synthetic_terminal(
            candidate["job_id"], ordinal, unit, "WORKER-LAUNCH-STOP", reason
        )
        write_once(terminal_path, terminal)
        connection.execute(
            "UPDATE jobs SET last_error=? WHERE job_id=?", (reason, candidate["job_id"])
        )
        record_event(connection, "worker-launch-failed", job_id=candidate["job_id"], details={"reason": reason})
    else:
        connection.execute(
            "UPDATE jobs SET status='running' WHERE job_id=?", (candidate["job_id"],)
        )
        connection.execute(
            "UPDATE attempts SET status='running' WHERE job_id=? AND ordinal=?",
            (candidate["job_id"], ordinal),
        )
        record_event(connection, "worker-launched", job_id=candidate["job_id"], details={"unit": unit})


def synthetic_terminal(
    job_id: str, ordinal: int, unit: str, terminal: str, reason: str
) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "protocol": PROTOCOL,
        "job_id": job_id,
        "attempt": ordinal,
        "unit": unit,
        "terminal": terminal,
        "valid_result": False,
        "reason": reason,
        "thread_id": None,
        "exit_code": None,
        "finished_at": now(),
        "result": None,
        "last_message": None,
        "metrics": {},
    }


def systemd_manager_state() -> str | None:
    result = subprocess.run(
        [
            "busctl",
            "--user",
            "get-property",
            SYSTEMD_DESTINATION,
            SYSTEMD_MANAGER_PATH,
            SYSTEMD_MANAGER_INTERFACE,
            "SystemState",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if result.returncode != 0:
        return None
    matched = re.fullmatch(r's\s+"([^"]+)"\s*', result.stdout)
    return matched.group(1) if matched else None


def systemd_manager_call(
    method: str,
    signature: str | None = None,
    arguments: list[str] | None = None,
    *,
    check: bool = True,
) -> subprocess.CompletedProcess[str]:
    command = [
        "busctl",
        "--user",
        "call",
        SYSTEMD_DESTINATION,
        SYSTEMD_MANAGER_PATH,
        SYSTEMD_MANAGER_INTERFACE,
        method,
    ]
    if signature is not None:
        command.append(signature)
        command.extend(arguments or [])
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if check and result.returncode != 0:
        raise SchedulerError(
            f"systemd manager {method} failed: {result.stderr.strip()}"
        )
    return result


def unit_active(unit: str) -> bool | None:
    unit_result = systemd_manager_call(
        "GetUnit", "s", [unit], check=False
    )
    if unit_result.returncode != 0:
        if "no such unit" in unit_result.stderr.lower() or "not loaded" in unit_result.stderr.lower():
            return False
        return None
    matched = re.fullmatch(r'o\s+"([^"]+)"\s*', unit_result.stdout)
    if matched is None:
        return None
    state_result = subprocess.run(
        [
            "busctl",
            "--user",
            "get-property",
            SYSTEMD_DESTINATION,
            matched.group(1),
            "org.freedesktop.systemd1.Unit",
            "ActiveState",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if state_result.returncode != 0:
        return None
    state = re.fullmatch(r's\s+"([^"]+)"\s*', state_result.stdout)
    return state is not None and state.group(1) in {"active", "activating", "reloading"}


def authenticate_valid_terminal(
    service_dir: Path,
    row: sqlite3.Row,
    terminal: dict[str, Any],
) -> None:
    dispatch = load_dispatch(service_dir, row)
    task = authenticate_task(
        repo_path(row["task_path"], "task packet"),
        row["task_sha256"],
        require_outputs_absent=False,
    )
    expected_path = repo_path(
        dispatch["expected_result_path"], "expected worker result"
    )
    result_receipt = terminal.get("result")
    if (
        not isinstance(result_receipt, dict)
        or result_receipt != file_receipt(expected_path)
    ):
        raise SchedulerError("terminal does not bind the exact expected result")
    result = read_json(expected_path, "worker result")
    last_receipt = terminal.get("last_message")
    if not isinstance(last_receipt, dict):
        raise SchedulerError("terminal lacks an authenticated structured last message")
    last_path = repo_path(
        str(last_receipt.get("path")), "structured last message"
    )
    if (
        not last_path.is_file()
        or sha256(last_path) != last_receipt.get("sha256")
        or read_json(last_path, "structured last message") != result
    ):
        raise SchedulerError("structured last message does not authenticate result.json")
    validate_result_pair(task, result, row["job_id"])


def admit_terminal_file(
    service_dir: Path, connection: sqlite3.Connection, row: sqlite3.Row
) -> bool:
    ordinal = int(row["current_attempt"])
    terminal_path = attempt_directory(service_dir, row["job_id"], ordinal) / "terminal.json"
    if not terminal_path.is_file():
        return False
    terminal = read_json(terminal_path, "worker terminal")
    if terminal.get("protocol") != PROTOCOL or terminal.get("job_id") != row["job_id"] or terminal.get("attempt") != ordinal:
        raise SchedulerError(f"worker terminal identity mismatch for {row['job_id']}")
    effective_valid = terminal.get("valid_result") is True
    validation_error: str | None = None
    if effective_valid:
        try:
            authenticate_valid_terminal(service_dir, row, terminal)
        except (SchedulerError, OSError) as exc:
            effective_valid = False
            validation_error = str(exc)
    status = (
        "terminal_pending_reconciliation"
        if effective_valid
        else "operational_stop_pending_reconciliation"
    )
    finished = str(terminal.get("finished_at") or now())
    digest = sha256(terminal_path)
    terminal_lane = row["lane_id"]
    inbox = lifecycle_inbox(
        service_dir,
        row,
        terminal_path,
        terminal,
        effective_valid=effective_valid,
    )
    inbox_path = lifecycle_inbox_path(service_dir, row["job_id"])
    write_once_or_verify(inbox_path, json_bytes(inbox))
    connection.execute(
        """
        UPDATE attempts SET status=?, ended_at=?, thread_id=?, terminal_sha256=?
        WHERE job_id=? AND ordinal=?
        """,
        (
            "terminal" if effective_valid else "operational-stop",
            finished,
            terminal.get("thread_id"),
            digest,
            row["job_id"],
            ordinal,
        ),
    )
    connection.execute(
        "UPDATE jobs SET status=?, lane_id=NULL, unit_name=NULL, terminal_at=?, last_error=? WHERE job_id=?",
        (
            status,
            finished,
            validation_error or terminal.get("reason"),
            row["job_id"],
        ),
    )
    if terminal_lane is not None:
        connection.execute(
            "UPDATE lanes SET state='free', job_id=NULL, blocked_reason=NULL WHERE lane_id=? AND job_id=?",
            (terminal_lane, row["job_id"]),
        )
    record_event(
        connection,
        "worker-terminal-observed",
        job_id=row["job_id"],
        details={
            "status": status,
            "terminal": file_receipt(terminal_path),
            "lifecycle_inbox": file_receipt(inbox_path),
            "released_lane": terminal_lane,
            "validation_error": validation_error,
        },
    )
    return True


def refresh_active_jobs(
    service_dir: Path, connection: sqlite3.Connection, *, check_units: bool = True
) -> None:
    for row in active_rows(connection):
        if admit_terminal_file(service_dir, connection, row):
            continue
        if not check_units:
            continue
        active = unit_active(str(row["unit_name"]))
        if active is True or active is None:
            continue
        started_at = datetime.fromisoformat(row["started_at"])
        if (datetime.now(timezone.utc) - started_at).total_seconds() < 20:
            continue
        ordinal = int(row["current_attempt"])
        attempt_dir = attempt_directory(service_dir, row["job_id"], ordinal)
        heartbeat_path = attempt_dir / "heartbeat.json"
        resumable_thread: str | None = None
        if heartbeat_path.is_file():
            heartbeat = read_json(heartbeat_path, "lost-worker heartbeat")
            if (
                heartbeat.get("protocol") == PROTOCOL
                and heartbeat.get("job_id") == row["job_id"]
                and heartbeat.get("attempt") == ordinal
                and isinstance(heartbeat.get("thread_id"), str)
                and heartbeat.get("thread_id")
            ):
                resumable_thread = str(heartbeat["thread_id"])
        if (
            resumable_thread is not None
            and int(row["resume_count"]) < int(row["resume_limit"])
        ):
            interruption_path = attempt_dir / "interruption.json"
            write_once(
                interruption_path,
                {
                    "schema_version": 1,
                    "protocol": PROTOCOL,
                    "job_id": row["job_id"],
                    "attempt": ordinal,
                    "unit": row["unit_name"],
                    "interrupted_at": now(),
                    "thread_id": resumable_thread,
                    "disposition": "same-thread-resume-authorized",
                },
            )
            connection.execute(
                """
                UPDATE attempts SET status='interrupted-resumable', ended_at=?,
                  thread_id=? WHERE job_id=? AND ordinal=?
                """,
                (now(), resumable_thread, row["job_id"], ordinal),
            )
            connection.execute(
                """
                UPDATE jobs SET status='queued', lane_id=NULL, unit_name=NULL,
                  resume_count=resume_count+1, last_error=? WHERE job_id=?
                """,
                ("worker unit disappeared; resuming authenticated thread", row["job_id"]),
            )
            connection.execute(
                "UPDATE lanes SET state='free', job_id=NULL, blocked_reason=NULL WHERE lane_id=?",
                (row["lane_id"],),
            )
            record_event(
                connection,
                "worker-interruption-resumable",
                job_id=row["job_id"],
                details={"interruption": file_receipt(interruption_path)},
            )
            continue
        terminal_path = attempt_directory(service_dir, row["job_id"], ordinal) / "terminal.json"
        terminal = synthetic_terminal(
            row["job_id"],
            ordinal,
            str(row["unit_name"]),
            "WORKER-LOST-STOP",
            "worker unit disappeared without an authenticated terminal",
        )
        write_once(terminal_path, terminal)
        admit_terminal_file(service_dir, connection, row)


def scheduler_tick(
    service_dir: Path,
    authorization_path_value: Path,
    authorization: dict[str, Any],
    *,
    launch: bool = True,
    runner: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
    check_units: bool = True,
) -> dict[str, Any]:
    initialize_database(service_dir, authorization)
    launched: list[str] = []
    would_launch: list[str] = []
    gated: dict[str, str] = {}
    with database(service_dir) as connection:
        connection.execute("BEGIN IMMEDIATE")
        refresh_active_jobs(service_dir, connection, check_units=check_units)
        if authorization["dispatch_enabled"]:
            while True:
                free_lane = connection.execute(
                    "SELECT lane_id FROM lanes WHERE state='free' ORDER BY lane_id LIMIT 1"
                ).fetchone()
                if free_lane is None:
                    break
                active = active_rows(connection)
                candidates = connection.execute(
                    """
                    SELECT * FROM jobs WHERE status='queued'
                    ORDER BY CASE occupancy_class WHEN 'mathematical' THEN 0 ELSE 1 END,
                             priority DESC, created_at, job_id
                    """
                ).fetchall()
                selected: sqlite3.Row | None = None
                for candidate in candidates:
                    compatible, reason = candidate_compatible(candidate, active, authorization)
                    if compatible:
                        selected = candidate
                        break
                    gated[candidate["job_id"]] = str(reason)
                if selected is None:
                    break
                if not launch:
                    would_launch.append(selected["job_id"])
                    break
                launch_candidate(
                    service_dir,
                    connection,
                    selected,
                    int(free_lane["lane_id"]),
                    authorization_path_value,
                    runner,
                )
                launched.append(selected["job_id"])
        state = scheduler_state(connection, authorization)
        state["launched_this_tick"] = launched
        state["would_launch_this_tick"] = would_launch
        state["gated_queue"] = gated
    atomic_json(service_dir / "state.json", state)
    return state


def scheduler_state(
    connection: sqlite3.Connection, authorization: dict[str, Any]
) -> dict[str, Any]:
    lanes = [dict(row) for row in connection.execute("SELECT * FROM lanes ORDER BY lane_id")]
    jobs = [
        dict(row)
        for row in connection.execute(
            "SELECT job_id, task_id, status, lane_id, slot_label, occupancy_class, mechanism_family, priority, profile, is_builder, created_at, started_at, terminal_at, reconciled_at, last_error FROM jobs ORDER BY created_at, job_id"
        )
    ]
    active = [job for job in jobs if job["status"] in ACTIVE_STATUSES]
    queued = [job for job in jobs if job["status"] == "queued"]
    pending = [job for job in jobs if job["status"] in TERMINAL_PENDING]
    active_math = sum(job["occupancy_class"] == "mathematical" for job in active)
    queued_math = sum(job["occupancy_class"] == "mathematical" for job in queued)
    limits = authorization["limits"]
    reasons: list[str] = []
    if not authorization["dispatch_enabled"]:
        reasons.append("observer-only-authorization")
    if not queued:
        reasons.append("approved-queue-empty")
    if active_math < limits["mathematical_target"]:
        reasons.append(
            f"mathematical-occupancy-{active_math}-of-{limits['mathematical_target']}"
        )
    if queued_math < limits["reserve_floor"]:
        reasons.append(
            f"mathematical-reserve-{queued_math}-below-floor-{limits['reserve_floor']}"
        )
    occupancy_healthy = (
        authorization["dispatch_enabled"]
        and active_math >= limits["mathematical_target"]
        and queued_math >= limits["reserve_floor"]
    )
    return {
        "schema_version": 1,
        "protocol": PROTOCOL,
        "updated_at": now(),
        "dispatch_enabled": authorization["dispatch_enabled"],
        "capacity": limits["capacity"],
        "mathematical_target": limits["mathematical_target"],
        "active_count": len(active),
        "active_mathematical_count": active_math,
        "queued_count": len(queued),
        "queued_mathematical_count": queued_math,
        "pending_reconciliation_count": len(pending),
        "occupancy_healthy": occupancy_healthy,
        "occupancy_attention_required": not occupancy_healthy,
        "reconciliation_attention_required": bool(pending),
        "attention_required": not occupancy_healthy or bool(pending),
        "lanes": lanes,
        "jobs": jobs,
        "undercapacity_reasons": reasons,
    }


def process_alive(pid: int) -> bool:
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
    except (ProcessLookupError, PermissionError):
        return False
    return True


def process_identity(pid: int) -> dict[str, Any] | None:
    if not process_alive(pid):
        return None
    try:
        stat = (Path("/proc") / str(pid) / "stat").read_text(encoding="utf-8")
        closing = stat.rfind(")")
        if closing < 0:
            return None
        tail = stat[closing + 2 :].split()
        boot_id = Path("/proc/sys/kernel/random/boot_id").read_text(encoding="utf-8").strip()
        return {
            "pid": pid,
            "start_ticks": int(tail[19]),
            "process_group_id": int(tail[2]),
            "boot_id": boot_id,
        }
    except (OSError, IndexError, ValueError):
        return None


def process_tree_rss_bytes(root_pid: int) -> int:
    parents: dict[int, int] = {}
    rss: dict[int, int] = {}
    for proc in Path("/proc").iterdir():
        if not proc.name.isdigit():
            continue
        try:
            stat = (proc / "stat").read_text(encoding="utf-8")
            closing = stat.rfind(")")
            tail = stat[closing + 2 :].split()
            pid = int(proc.name)
            parents[pid] = int(tail[1])
            for line in (proc / "status").read_text(encoding="utf-8").splitlines():
                if line.startswith("VmRSS:"):
                    rss[pid] = int(line.split()[1]) * 1024
                    break
        except (OSError, ValueError, IndexError):
            continue
    descendants = {root_pid}
    changed = True
    while changed:
        changed = False
        for pid, parent in parents.items():
            if parent in descendants and pid not in descendants:
                descendants.add(pid)
                changed = True
    return sum(rss.get(pid, 0) for pid in descendants)


def terminate_process_group(pid: int) -> None:
    identity = process_identity(pid)
    if identity is None:
        return
    try:
        os.killpg(identity["process_group_id"], signal.SIGTERM)
    except ProcessLookupError:
        return
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline and process_alive(pid):
        time.sleep(0.1)
    if process_alive(pid) and process_identity(pid) == identity:
        try:
            os.killpg(identity["process_group_id"], signal.SIGKILL)
        except ProcessLookupError:
            pass


def extract_thread_id(events_path: Path) -> str | None:
    if not events_path.is_file():
        return None
    found: str | None = None

    def inspect(value: Any) -> None:
        nonlocal found
        if isinstance(value, dict):
            for key, item in value.items():
                if key in {"thread_id", "threadId", "session_id", "sessionId"} and isinstance(item, str) and item:
                    found = item
                else:
                    inspect(item)
        elif isinstance(value, list):
            for item in value:
                inspect(item)

    try:
        for line in events_path.read_text(encoding="utf-8", errors="replace").splitlines():
            try:
                inspect(json.loads(line))
            except json.JSONDecodeError:
                continue
    except OSError:
        return None
    return found


def output_size(attempt_dir: Path, task: dict[str, Any]) -> int:
    total = 0
    for path in attempt_dir.rglob("*"):
        if path.is_file():
            try:
                total += path.stat().st_size
            except OSError:
                pass
    for deliverable in task.get("deliverables", []):
        path = repo_path(deliverable, "deliverable")
        if path.is_file():
            try:
                total += path.stat().st_size
            except OSError:
                pass
    return total


def codex_worker_command(
    authorization: dict[str, Any],
    dispatch: dict[str, Any],
    attempt_dir: Path,
    *,
    resume_thread_id: str | None = None,
) -> list[str]:
    provider = dispatch["provider"]
    executable = authorization["provider"]["executable"]
    common = [
        executable,
        "exec",
    ]
    if resume_thread_id is not None:
        common.extend(["resume", resume_thread_id])
    common.extend(
        [
            "--model",
            provider["model"],
            "--config",
            f'model_reasoning_effort="{provider["reasoning_effort"]}"',
            "--config",
            f'web_search="{provider["web_search"]}"',
            "--config",
            'approval_policy="never"',
            "--config",
            "agents.enabled=false",
        ]
    )
    if resume_thread_id is None:
        common.extend(["--sandbox", provider["sandbox"], "--cd", str(ROOT)])
    common.extend(
        [
            "--skip-git-repo-check",
            "--output-schema",
            str(RESULT_SCHEMA_PATH),
            "--output-last-message",
            str(attempt_dir / "last-message.json"),
            "--json",
            "-",
        ]
    )
    return common


def previous_thread_id(service_dir: Path, job_id: str, ordinal: int) -> str | None:
    if ordinal <= 1:
        return None
    previous = attempt_directory(service_dir, job_id, ordinal - 1) / "heartbeat.json"
    if not previous.is_file():
        return None
    value = read_json(previous, "previous worker heartbeat")
    thread_id = value.get("thread_id")
    return thread_id if isinstance(thread_id, str) and thread_id else None


def command_worker(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    authorization_path_value, authorization = active_authorization(service_dir)
    if sha256(authorization_path_value) != args.authorization_sha256:
        raise SchedulerError("worker authorization SHA-256 does not authenticate")
    with database(service_dir) as connection:
        row = connection.execute("SELECT * FROM jobs WHERE job_id=?", (args.job_id,)).fetchone()
    if row is None or int(row["current_attempt"]) != args.attempt:
        raise SchedulerError("worker job/attempt is not current")
    dispatch = load_dispatch(service_dir, row)
    task = authenticate_task(
        repo_path(row["task_path"], "task packet"),
        row["task_sha256"],
        require_outputs_absent=(args.attempt == 1),
    )
    attempt_dir = attempt_directory(service_dir, args.job_id, args.attempt)
    attempt_dir.mkdir(parents=True, exist_ok=True)
    terminal_path = attempt_dir / "terminal.json"
    attempt_receipt = attempt_dir / "attempt.json"
    if terminal_path.exists() or attempt_receipt.exists():
        raise SchedulerError("worker attempt already has an immutable receipt")
    resume_thread = previous_thread_id(service_dir, args.job_id, args.attempt)
    if args.attempt > 1 and resume_thread is None:
        raise SchedulerError("same-thread resume requested without an authenticated thread ID")
    command = codex_worker_command(
        authorization, dispatch, attempt_dir, resume_thread_id=resume_thread
    )
    prompt_path = repo_path(dispatch["prompt"]["path"], "worker prompt")
    if sha256(prompt_path) != dispatch["prompt"]["sha256"]:
        raise SchedulerError("worker prompt drifted")
    prompt = prompt_path.read_text(encoding="utf-8")
    if resume_thread is not None:
        prompt = (
            "Resume the same immutable task after an operational interruption. "
            "Authenticate the checkpoint and exact packet again; do not restart or widen it.\n\n"
            + prompt
        )
    events_path = attempt_dir / "events.jsonl"
    stderr_path = attempt_dir / "stderr.log"
    with events_path.open("xb") as events, stderr_path.open("xb") as errors:
        process = subprocess.Popen(
            command,
            cwd=ROOT,
            stdin=subprocess.PIPE,
            stdout=events,
            stderr=errors,
            start_new_session=True,
        )
        identity = process_identity(process.pid)
        write_once(
            attempt_receipt,
            {
                "schema_version": 1,
                "protocol": PROTOCOL,
                "job_id": args.job_id,
                "attempt": args.attempt,
                "started_at": now(),
                "process_identity": identity,
                "resume_thread_id": resume_thread,
                "command": command,
                "dispatch": file_receipt(repo_path(row["receipt_path"], "dispatch receipt")),
            },
        )
        assert process.stdin is not None
        process.stdin.write(prompt.encode("utf-8"))
        process.stdin.close()
        deadline = time.monotonic() + int(row["wall_minutes"]) * 60
        output_limit = max(1, int(float(row["output_gib"]) * (1024**3)))
        max_rss = 0
        stop_reason: str | None = None
        thread_id = resume_thread
        while process.poll() is None:
            max_rss = max(max_rss, process_tree_rss_bytes(process.pid))
            thread_id = extract_thread_id(events_path) or thread_id
            heartbeat = {
                "schema_version": 1,
                "protocol": PROTOCOL,
                "job_id": args.job_id,
                "attempt": args.attempt,
                "heartbeat_at": now(),
                "process_identity": identity,
                "thread_id": thread_id,
                "rss_bytes": max_rss,
                "output_bytes": output_size(attempt_dir, task),
            }
            atomic_json(attempt_dir / "heartbeat.json", heartbeat)
            if time.monotonic() >= deadline:
                stop_reason = "task wall-clock budget exhausted"
            elif heartbeat["output_bytes"] > output_limit:
                stop_reason = "task output budget exhausted"
            if stop_reason is not None:
                terminate_process_group(process.pid)
                break
            time.sleep(2)
        exit_code = process.wait()
    thread_id = extract_thread_id(events_path) or thread_id
    last_message_path = attempt_dir / "last-message.json"
    terminal: dict[str, Any]
    try:
        if stop_reason is not None:
            raise SchedulerError(stop_reason)
        if exit_code != 0:
            raise SchedulerError(f"Codex worker exited with status {exit_code}")
        if not last_message_path.is_file():
            raise SchedulerError("Codex worker produced no structured last message")
        last_message = read_json(last_message_path, "Codex last message")
        result_path = repo_path(dispatch["expected_result_path"], "expected result")
        if not result_path.is_file():
            raise SchedulerError("worker did not create the expected result.json")
        result = read_json(result_path, "worker result")
        if result != last_message:
            raise SchedulerError("result.json and the structured last message differ")
        validate_result_pair(task, result, args.job_id)
        terminal = {
            "schema_version": 1,
            "protocol": PROTOCOL,
            "job_id": args.job_id,
            "attempt": args.attempt,
            "unit": worker_unit_name(args.job_id, args.attempt),
            "terminal": "RESULT-AWAITING-ROOT-RECONCILIATION",
            "valid_result": True,
            "reason": None,
            "thread_id": thread_id,
            "exit_code": exit_code,
            "finished_at": now(),
            "result": file_receipt(result_path),
            "last_message": file_receipt(last_message_path),
            "metrics": {
                "max_process_tree_rss_bytes": max_rss,
                "captured_output_bytes": output_size(attempt_dir, task),
            },
        }
    except SchedulerError as exc:
        terminal = synthetic_terminal(
            args.job_id,
            args.attempt,
            worker_unit_name(args.job_id, args.attempt),
            "WORKER-OPERATIONAL-STOP",
            str(exc),
        )
        terminal["thread_id"] = thread_id
        terminal["exit_code"] = exit_code
        terminal["metrics"] = {
            "max_process_tree_rss_bytes": max_rss,
            "captured_output_bytes": output_size(attempt_dir, task),
        }
    write_once(terminal_path, terminal)
    return 0 if terminal["valid_result"] else 1


def command_reconcile(
    args: argparse.Namespace,
    *,
    lifecycle_runner: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
) -> int:
    service_dir = service_directory(args.service_dir)
    authorization_path_value, authorization = active_authorization(service_dir)
    initialize_database(service_dir, authorization)
    lifecycle_path = repo_path(args.lifecycle_receipt, "Wayfinder lifecycle receipt")
    if sha256(lifecycle_path) != args.lifecycle_sha256:
        raise SchedulerError("Wayfinder lifecycle receipt SHA-256 does not authenticate")
    lifecycle_check = lifecycle_runner(
        [
            sys.executable,
            str(LIFECYCLE_CHECKER_PATH),
            "check",
            "--service-dir",
            str(service_dir),
            "--job-id",
            args.job_id,
            "--receipt",
            str(lifecycle_path),
            "--receipt-sha256",
            args.lifecycle_sha256,
            "--require-pending",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if lifecycle_check.returncode != 0:
        raise SchedulerError(
            "Wayfinder lifecycle receipt failed independent verification: "
            + lifecycle_check.stderr.strip()
        )
    lifecycle = read_json(lifecycle_path, "Wayfinder lifecycle receipt")
    disposition = lifecycle.get("disposition")
    adjudication = lifecycle.get("adjudication")
    if disposition not in {"accepted", "rejected", "operational"} or not isinstance(
        adjudication, dict
    ):
        raise SchedulerError("Wayfinder lifecycle receipt has malformed adjudication")
    with database(service_dir) as connection:
        connection.execute("BEGIN IMMEDIATE")
        row = connection.execute("SELECT * FROM jobs WHERE job_id=?", (args.job_id,)).fetchone()
        if row is None or row["status"] not in TERMINAL_PENDING:
            raise SchedulerError("job is not awaiting reconciliation")
        terminal_path = attempt_directory(
            service_dir, args.job_id, int(row["current_attempt"])
        ) / "terminal.json"
        terminal = read_json(terminal_path, "worker terminal")
        if sha256(terminal_path) != args.terminal_sha256:
            raise SchedulerError("terminal SHA-256 does not authenticate")
        if terminal.get("valid_result") is True:
            authenticate_valid_terminal(service_dir, row, terminal)
            if disposition == "operational":
                raise SchedulerError("a valid result cannot receive operational disposition")
        elif disposition != "operational":
            raise SchedulerError("an operational stop cannot be accepted as mathematical evidence")
        receipt = {
            "schema_version": 1,
            "protocol": PROTOCOL,
            "job_id": args.job_id,
            "recorded_at": now(),
            "terminal": file_receipt(terminal_path),
            "disposition": disposition,
            "lifecycle_receipt": file_receipt(lifecycle_path),
            "reconciliation_ref": lifecycle["approval_ref"],
            "ledger_edge": adjudication["ledger_edge"],
            "meaning": "root reconciliation recorded after an independently authenticated Wayfinder lifecycle transition",
        }
        receipt_path = service_dir / "reconciliations" / f"{args.job_id}.json"
        write_once(receipt_path, receipt)
        final_status = "reconciled" if disposition in {"accepted", "operational"} else "rejected"
        connection.execute(
            "UPDATE jobs SET status=?, reconciled_at=? WHERE job_id=?",
            (final_status, receipt["recorded_at"], args.job_id),
        )
        record_event(
            connection,
            "root-reconciliation-recorded",
            job_id=args.job_id,
            details=file_receipt(receipt_path),
        )
    state = scheduler_tick(
        service_dir,
        authorization_path_value,
        authorization,
        launch=not args.no_backfill,
    )
    print(json.dumps({"reconciliation": file_receipt(receipt_path), "state": state}, indent=2, sort_keys=True))
    return 0


def daemon_receipt(service_dir: Path) -> dict[str, Any] | None:
    path = service_dir / "service.pid"
    if not path.is_file():
        return None
    value = read_json(path, "scheduler PID receipt")
    pid = value.get("pid")
    expected_identity = value.get("process_identity")
    live_identity = process_identity(pid) if isinstance(pid, int) else None
    if isinstance(expected_identity, dict) and live_identity == expected_identity:
        value["liveness"] = "pid"
        return value
    state_path = service_dir / "service-state.json"
    if state_path.is_file():
        state = read_json(state_path, "scheduler service state")
        try:
            heartbeat = datetime.fromisoformat(str(state["heartbeat_at"]))
            age = (datetime.now(timezone.utc) - heartbeat).total_seconds()
        except (KeyError, ValueError):
            age = 999999
        try:
            current_boot_id = Path("/proc/sys/kernel/random/boot_id").read_text(
                encoding="utf-8"
            ).strip()
        except OSError:
            current_boot_id = None
        if (
            age < 45
            and state.get("service_id") == value.get("service_id")
            and state.get("service_status") not in {"stopped", "error"}
            and isinstance(expected_identity, dict)
            and state.get("process_identity") == expected_identity
            and expected_identity.get("boot_id") == current_boot_id
        ):
            value["liveness"] = "fresh-heartbeat; PID hidden from current namespace"
            return value
    return None


def launch_daemon(service_dir: Path) -> dict[str, Any]:
    existing = daemon_receipt(service_dir)
    if existing is not None:
        return existing
    manager_state = systemd_manager_state()
    if manager_state not in {"running", "degraded"}:
        raise SchedulerError(
            "the user service manager is unavailable; refusing an unsupervised chat-bound fallback"
        )
    service_id = str(uuid.uuid4())
    systemd_unit = scheduler_unit_name(service_dir)
    unit_dir = service_dir / "systemd"
    unit_dir.mkdir(parents=True, exist_ok=True)
    unit_path = unit_dir / systemd_unit
    unit_text = "\n".join(
        [
            "[Unit]",
            "Description=Authenticated Erdos-Szekeres research scheduler",
            "After=network-online.target",
            "Wants=network-online.target",
            "StartLimitIntervalSec=300",
            "StartLimitBurst=3",
            "",
            "[Service]",
            "Type=simple",
            f"WorkingDirectory={ROOT}",
            "KillMode=process",
            "MemoryMax=1G",
            "CPUQuota=50%",
            "TasksMax=64",
            "Restart=on-failure",
            "RestartSec=10",
            "Environment=PYTHONUNBUFFERED=1",
            (
                f"ExecStart={sys.executable} {Path(__file__).resolve()} serve "
                f"--service-dir {service_dir} --service-id {service_id}"
            ),
            f"StandardOutput=append:{service_dir / 'service.log'}",
            f"StandardError=append:{service_dir / 'service.log'}",
            "",
            "[Install]",
            "WantedBy=default.target",
            "",
        ]
    )
    temporary = unit_path.with_name(f".{unit_path.name}.tmp-{os.getpid()}")
    temporary.write_text(unit_text, encoding="utf-8")
    os.replace(temporary, unit_path)
    systemd_manager_call(
        "LinkUnitFiles", "asbb", ["1", str(unit_path), "false", "true"]
    )
    systemd_manager_call("Reload")
    systemd_manager_call(
        "EnableUnitFiles", "asbb", ["1", systemd_unit, "false", "true"]
    )
    systemd_manager_call("Reload")
    systemd_manager_call("ResetFailedUnit", "s", [systemd_unit], check=False)
    systemd_manager_call("StartUnit", "ss", [systemd_unit, "replace"])
    deadline = time.monotonic() + 8
    while time.monotonic() < deadline:
        receipt = daemon_receipt(service_dir)
        if receipt is not None and receipt.get("service_id") == service_id:
            return receipt
        time.sleep(0.1)
    raise SchedulerError("scheduler daemon did not publish a live receipt")


def command_start(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    path, authorization = active_authorization(service_dir)
    requested = repo_path(args.authorization, "scheduler authorization")
    if requested != path or sha256(path) != args.authorization_sha256:
        raise SchedulerError("start does not bind the active authorization")
    initialize_database(service_dir, authorization)
    daemon = launch_daemon(service_dir)
    print(json.dumps({"daemon": daemon, "authorization": file_receipt(path)}, indent=2, sort_keys=True))
    return 0


def command_serve(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    service_dir.mkdir(parents=True, exist_ok=True)
    authorization_path_value, authorization = active_authorization(service_dir)
    initialize_database(service_dir, authorization)
    lock = (service_dir / "service.lock").open("a+")
    try:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as exc:
        raise SchedulerError("another research scheduler holds the service lock") from exc
    pid_receipt = {
        "schema_version": 1,
        "protocol": PROTOCOL,
        "service_id": args.service_id,
        "supervisor_ref": f"systemd-user:{scheduler_unit_name(service_dir)}",
        "implementation_sha256": sha256(Path(__file__).resolve()),
        "authorization": file_receipt(authorization_path_value),
        "pid": os.getpid(),
        "process_identity": process_identity(os.getpid()),
        "started_at": now(),
    }
    atomic_json(service_dir / "service.pid", pid_receipt)
    stop_flag = {"stop": False}

    def stop(_signum: int, _frame: Any) -> None:
        stop_flag["stop"] = True

    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    service_state = {
        "schema_version": 1,
        "protocol": PROTOCOL,
        "service_id": args.service_id,
        "service_status": "running",
        "heartbeat_at": now(),
        "process_identity": pid_receipt["process_identity"],
        "last_error": None,
    }
    while not stop_flag["stop"]:
        try:
            current_path, current_authorization = active_authorization(service_dir)
            if current_path != authorization_path_value or current_authorization != authorization:
                raise SchedulerError("active authorization changed while scheduler was live")
            state = scheduler_tick(service_dir, authorization_path_value, authorization)
            service_state.update(
                {
                    "service_status": "running",
                    "heartbeat_at": now(),
                    "last_scheduler_state": state,
                    "last_error": None,
                }
            )
        except (SchedulerError, OSError, sqlite3.Error, subprocess.SubprocessError) as exc:
            service_state.update(
                {
                    "service_status": "error",
                    "heartbeat_at": now(),
                    "last_error": str(exc),
                }
            )
            atomic_json(service_dir / "service-state.json", service_state)
            return 1
        atomic_json(service_dir / "service-state.json", service_state)
        deadline = time.monotonic() + int(authorization["limits"]["poll_seconds"])
        while not stop_flag["stop"] and time.monotonic() < deadline:
            time.sleep(0.2)
    service_state.update({"service_status": "stopped", "heartbeat_at": now()})
    atomic_json(service_dir / "service-state.json", service_state)
    return 0


def status_payload(service_dir: Path) -> dict[str, Any]:
    path, authorization = active_authorization(service_dir)
    initialize_database(service_dir, authorization)
    with database(service_dir) as connection:
        state = scheduler_state(connection, authorization)
        recent_events = [
            {
                **dict(row),
                "details": json.loads(row["details_json"]),
            }
            for row in connection.execute(
                "SELECT * FROM events ORDER BY sequence DESC LIMIT 20"
            )
        ]
        for event in recent_events:
            event.pop("details_json", None)
    service_state_path = service_dir / "service-state.json"
    return {
        "protocol": PROTOCOL,
        "service_dir": repo_relative(service_dir),
        "daemon_alive": daemon_receipt(service_dir) is not None,
        "daemon": daemon_receipt(service_dir),
        "authorization": file_receipt(path),
        "scheduler": state,
        "service_state": (
            read_json(service_state_path, "scheduler service state")
            if service_state_path.is_file()
            else None
        ),
        "recent_events": recent_events,
    }


def command_status(args: argparse.Namespace) -> int:
    print(json.dumps(status_payload(service_directory(args.service_dir)), indent=2, sort_keys=True))
    return 0


def command_tick(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    path, authorization = active_authorization(service_dir)
    state = scheduler_tick(
        service_dir,
        path,
        authorization,
        launch=not args.dry_run,
        check_units=not args.skip_unit_check,
    )
    print(json.dumps(state, indent=2, sort_keys=True))
    return 0


def command_doctor(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    path, authorization = active_authorization(service_dir)
    initialize_database(service_dir, authorization)
    errors: list[str] = []
    manager_state = systemd_manager_state()
    if manager_state not in {"running", "degraded"}:
        errors.append("user systemd manager is unavailable from this namespace")
    with database(service_dir) as connection:
        rows = connection.execute("SELECT * FROM jobs").fetchall()
        for row in rows:
            try:
                dispatch = load_dispatch(service_dir, row)
                authenticate_task(
                    repo_path(row["task_path"], "task packet"),
                    row["task_sha256"],
                    require_outputs_absent=False,
                )
                authenticate_wave(
                    repo_path(row["wave_path"], "approved wave"),
                    row["wave_sha256"],
                    repo_path(row["task_path"], "task packet"),
                    row["task_sha256"],
                )
                reserve = dispatch.get("reserve_plan")
                if reserve is not None:
                    authenticate_reserve_plan(
                        repo_path(reserve["path"], "dispatch reserve plan"),
                        reserve["sha256"],
                        path,
                        row["approval_ref"],
                    )
            except SchedulerError as exc:
                errors.append(f"{row['job_id']}: {exc}")
    payload = {
        "protocol": PROTOCOL,
        "authorization": file_receipt(path),
        "codex_version": codex_version(authorization["provider"]["executable"]),
        "systemd_state": manager_state,
        "errors": errors,
        "ok": not errors,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if not errors else 1


def command_stop(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    daemon = daemon_receipt(service_dir)
    systemd_unit = scheduler_unit_name(service_dir)
    stopped = systemd_manager_call(
        "StopUnit", "ss", [systemd_unit, "replace"], check=False
    )
    disabled = systemd_manager_call(
        "DisableUnitFiles", "asb", ["1", systemd_unit, "false"], check=False
    )
    inactive_confirmed = False
    deadline = time.monotonic() + 10
    while time.monotonic() < deadline:
        if daemon_receipt(service_dir) is None and unit_active(systemd_unit) is False:
            inactive_confirmed = True
            break
        time.sleep(0.1)
    print(
        json.dumps(
            {
                "daemon_was_alive": daemon is not None,
                "reason": args.reason,
                "systemd_stop_returncode": stopped.returncode,
                "systemd_disable_returncode": disabled.returncode,
                "inactive_confirmed": inactive_confirmed,
                "stderr": "\n".join(
                    item for item in (stopped.stderr.strip(), disabled.stderr.strip()) if item
                ),
                "worker_units_untouched": True,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return (
        0
        if inactive_confirmed
        and ((stopped.returncode == 0 and disabled.returncode == 0) or daemon is None)
        else 1
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    configure = subparsers.add_parser("configure", help="freeze standing scheduler authority")
    configure.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    configure.add_argument("--approval-ref", required=True)
    configure.add_argument("--dispatch-enabled", action="store_true")
    configure.add_argument("--capacity", type=int, default=4)
    configure.add_argument("--mathematical-target", type=int, default=4)
    configure.add_argument("--reserve-floor", type=int, default=4)
    configure.add_argument("--max-builders", type=int, default=1)
    configure.add_argument("--max-same-family", type=int, default=2)
    configure.add_argument("--total-cpu-cores", type=int, default=8)
    configure.add_argument("--total-memory-gib", type=int, default=32)
    configure.add_argument("--total-output-gib", type=float, default=5.0)
    configure.add_argument("--poll-seconds", type=int, default=5)
    configure.add_argument("--codex-executable", default="codex")
    configure.add_argument("--allowed-models", nargs="+", default=["gpt-5.6-sol"])
    configure.add_argument("--default-model", default="gpt-5.6-sol")
    configure.add_argument("--reasoning-effort", default="max")
    configure.set_defaults(function=command_configure)

    enqueue = subparsers.add_parser("enqueue", help="freeze one exact approved dispatch")
    enqueue.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    enqueue.add_argument("--task-packet", required=True, type=Path)
    enqueue.add_argument("--task-sha256", required=True)
    enqueue.add_argument("--operational-wave", required=True, type=Path)
    enqueue.add_argument("--wave-sha256", required=True)
    enqueue.add_argument("--approval-ref", required=True)
    enqueue.add_argument("--slot-label", choices=sorted(SLOT_LABELS), required=True)
    enqueue.add_argument("--occupancy-class", choices=sorted(OCCUPANCY_CLASSES), required=True)
    enqueue.add_argument("--mechanism-family")
    enqueue.add_argument("--priority", type=int, default=0)
    enqueue.add_argument("--model")
    enqueue.add_argument("--reasoning-effort", choices=sorted(REASONING_EFFORTS))
    enqueue.add_argument("--web-search", choices=sorted(WEB_SEARCH_MODES), default="disabled")
    enqueue.add_argument("--resume-limit", type=int, default=0)
    enqueue.set_defaults(function=command_enqueue)

    reserve = subparsers.add_parser(
        "import-reserve",
        help="preflight and import one exact approved reserve plan",
    )
    reserve.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    reserve.add_argument("--reserve-plan", required=True, type=Path)
    reserve.add_argument("--reserve-sha256", required=True)
    reserve.add_argument("--approval-ref", required=True)
    reserve.add_argument(
        "--no-backfill",
        action="store_true",
        help="stage the reserve without starting provider workers",
    )
    reserve.set_defaults(function=command_import_reserve)

    start = subparsers.add_parser("start", help="start the persistent user-systemd service")
    start.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    start.add_argument("--authorization", required=True, type=Path)
    start.add_argument("--authorization-sha256", required=True)
    start.set_defaults(function=command_start)

    serve = subparsers.add_parser("serve", help=argparse.SUPPRESS)
    serve.add_argument("--service-dir", type=Path, required=True)
    serve.add_argument("--service-id", required=True)
    serve.set_defaults(function=command_serve)

    worker = subparsers.add_parser("worker", help=argparse.SUPPRESS)
    worker.add_argument("--service-dir", type=Path, required=True)
    worker.add_argument("--job-id", required=True)
    worker.add_argument("--attempt", type=int, required=True)
    worker.add_argument("--authorization-sha256", required=True)
    worker.set_defaults(function=command_worker)

    reconcile = subparsers.add_parser(
        "reconcile", help="authenticate and close one terminal-inbox item"
    )
    reconcile.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    reconcile.add_argument("--job-id", required=True)
    reconcile.add_argument("--terminal-sha256", required=True)
    reconcile.add_argument("--lifecycle-receipt", type=Path, required=True)
    reconcile.add_argument("--lifecycle-sha256", required=True)
    reconcile.add_argument("--no-backfill", action="store_true")
    reconcile.set_defaults(function=command_reconcile)

    status = subparsers.add_parser("status", help="show process-backed queue and lane telemetry")
    status.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    status.set_defaults(function=command_status)

    tick = subparsers.add_parser("tick", help="run one recovery and backfill transaction")
    tick.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    tick.add_argument("--dry-run", action="store_true")
    tick.add_argument("--skip-unit-check", action="store_true", help=argparse.SUPPRESS)
    tick.set_defaults(function=command_tick)

    doctor = subparsers.add_parser("doctor", help="authenticate scheduler state and dependencies")
    doctor.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    doctor.set_defaults(function=command_doctor)

    stop = subparsers.add_parser("stop", help="stop only the scheduler, not live worker units")
    stop.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    stop.add_argument("--reason", required=True)
    stop.set_defaults(function=command_stop)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        return int(args.function(args))
    except (
        SchedulerError,
        OSError,
        sqlite3.Error,
        subprocess.SubprocessError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
