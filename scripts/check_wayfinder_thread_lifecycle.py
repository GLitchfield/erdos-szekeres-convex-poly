#!/usr/bin/env python3
"""Prepare, seal, and independently verify one worker's Wayfinder lifecycle.

Workers remain untrusted and never edit canonical strategy files.  This tool is
the serialized root-side control plane: it snapshots the pre-integration state,
binds an independently adjudicated terminal to the post-integration state, and
emits the only receipt accepted by the persistent scheduler's reconciliation
command.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sqlite3
import subprocess
import sys
from typing import Any

try:
    from scripts import freeze_agent_context
except ImportError:  # Direct execution places scripts/ on sys.path.
    import freeze_agent_context


ROOT = Path(__file__).resolve().parents[1]
PROTOCOL = "wayfinder-thread-lifecycle-v1"
DRAFT_PROTOCOL = "wayfinder-thread-lifecycle-draft-v1"
SCHEDULER_PROTOCOL = "research-scheduler-v2"
MAP_PATH = Path("docs/wayfinder/map.md")
PORTFOLIO_PATH = Path("docs/wayfinder/frontier-portfolio.md")
MOVEMENTS = {"forward", "neutral", "backward"}
EVIDENCE = {
    "compiling_theorem",
    "checked_computation",
    "proposal",
    "operational_stop",
}
DAMAGE_SCOPES = {
    "candidate-local",
    "subfamily",
    "architecture-level",
    "mechanism-wide",
    "operational-only",
}
PLANNING = {"promote", "retain", "demote", "suspend", "expire"}
DISPOSITIONS = {"accepted", "rejected", "operational"}
FP_RE = re.compile(r"^FP-[0-9]{2}(?:\.[A-Z])?$")
HEX_RE = re.compile(r"^[0-9a-f]{64}$")


class LifecycleError(ValueError):
    """Raised when a lifecycle artifact cannot be authenticated."""


def now() -> str:
    from datetime import datetime, timezone

    return datetime.now(timezone.utc).isoformat()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def repo_path(value: str | Path, label: str) -> Path:
    raw = Path(value)
    resolved = raw.resolve() if raw.is_absolute() else (ROOT / raw).resolve()
    try:
        resolved.relative_to(ROOT.resolve())
    except ValueError as exc:
        raise LifecycleError(f"{label} escapes the repository: {value}") from exc
    if not resolved.is_file():
        raise LifecycleError(f"{label} is not a regular file: {value}")
    if resolved.is_symlink():
        raise LifecycleError(f"{label} cannot be a symlink: {value}")
    return resolved


def repo_relative(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError as exc:
        raise LifecycleError(f"path is outside repository: {path}") from exc


def receipt(path: Path) -> dict[str, str]:
    return {"path": repo_relative(path), "sha256": sha256(path)}


def load_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise LifecycleError(f"cannot parse {label} {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise LifecycleError(f"{label} must be a JSON object")
    return value


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def write_once(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json_bytes(value)
    try:
        descriptor = path.open("xb")
    except FileExistsError as exc:
        raise LifecycleError(f"refusing to overwrite immutable artifact: {path}") from exc
    with descriptor:
        descriptor.write(encoded)


def authenticate_receipt(value: Any, label: str) -> Path:
    if not isinstance(value, dict) or set(value) != {"path", "sha256"}:
        raise LifecycleError(f"{label} receipt is malformed")
    if not isinstance(value["sha256"], str) or HEX_RE.fullmatch(value["sha256"]) is None:
        raise LifecycleError(f"{label} SHA-256 is malformed")
    path = repo_path(str(value["path"]), label)
    if sha256(path) != value["sha256"]:
        raise LifecycleError(f"{label} SHA-256 does not authenticate")
    return path


def current_revision() -> str:
    result = subprocess.run(
        ["git", "--git-dir=.git-data", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if result.returncode != 0:
        raise LifecycleError(f"cannot resolve current revision: {result.stderr.strip()}")
    return result.stdout.strip()


def service_directory(value: Path) -> Path:
    resolved = value.resolve() if value.is_absolute() else (ROOT / value).resolve()
    try:
        resolved.relative_to((ROOT / "runs" / "agents").resolve())
    except ValueError as exc:
        raise LifecycleError("service directory must remain under runs/agents") from exc
    return resolved


def database_job(service_dir: Path, job_id: str) -> tuple[dict[str, Any], dict[str, Any]]:
    database = service_dir / "scheduler.sqlite3"
    if not database.is_file():
        raise LifecycleError("scheduler database is absent")
    connection = sqlite3.connect(f"file:{database}?mode=ro", uri=True)
    connection.row_factory = sqlite3.Row
    try:
        row = connection.execute("SELECT * FROM jobs WHERE job_id=?", (job_id,)).fetchone()
        if row is None:
            raise LifecycleError(f"scheduler job is absent: {job_id}")
        attempt = connection.execute(
            "SELECT * FROM attempts WHERE job_id=? AND ordinal=?",
            (job_id, int(row["current_attempt"])),
        ).fetchone()
        if attempt is None:
            raise LifecycleError("scheduler attempt is absent")
        return dict(row), dict(attempt)
    finally:
        connection.close()


def expected_inbox(service_dir: Path, row: dict[str, Any], attempt: dict[str, Any]) -> dict[str, Any]:
    task_path = repo_path(str(row["task_path"]), "task packet")
    if sha256(task_path) != row["task_sha256"]:
        raise LifecycleError("scheduler task hash drifted")
    task = load_json(task_path, "task packet")
    ticket_value = task.get("wayfinder_ticket")
    if not isinstance(ticket_value, str) or not ticket_value:
        raise LifecycleError("a scheduled thread must name its owning Wayfinder ticket")
    ticket_path = repo_path(ticket_value, "Wayfinder ticket")
    dispatch_path = repo_path(str(row["receipt_path"]), "dispatch receipt")
    terminal_path = repo_path(str(attempt["terminal_path"]), "terminal receipt")
    terminal = load_json(terminal_path, "terminal receipt")
    if (
        terminal.get("protocol") != SCHEDULER_PROTOCOL
        or terminal.get("job_id") != row["job_id"]
        or terminal.get("attempt") != int(row["current_attempt"])
    ):
        raise LifecycleError("terminal identity does not match scheduler state")
    result_value = (
        terminal.get("result")
        if row["status"] in {"terminal_pending_reconciliation", "reconciled", "rejected"}
        else None
    )
    if result_value is not None:
        authenticate_receipt(result_value, "worker result")
    return {
        "schema_version": 1,
        "protocol": PROTOCOL,
        "created_at": str(terminal.get("finished_at") or row.get("terminal_at") or "unknown"),
        "job_id": row["job_id"],
        "task_packet": receipt(task_path),
        "dispatch": receipt(dispatch_path),
        "terminal": receipt(terminal_path),
        "result": result_value,
        "wayfinder_ticket": repo_relative(ticket_path),
    }


def inbox_path(service_dir: Path, job_id: str) -> Path:
    return service_dir / "lifecycle-inbox" / f"{job_id}.json"


def verify_inbox(service_dir: Path, job_id: str, *, require_pending: bool) -> tuple[Path, dict[str, Any], dict[str, Any]]:
    row, attempt = database_job(service_dir, job_id)
    if require_pending and row["status"] not in {
        "terminal_pending_reconciliation",
        "operational_stop_pending_reconciliation",
    }:
        raise LifecycleError("job is not pending Wayfinder reconciliation")
    path = inbox_path(service_dir, job_id)
    actual = load_json(path, "lifecycle inbox")
    expected = expected_inbox(service_dir, row, attempt)
    if actual != expected:
        raise LifecycleError("lifecycle inbox differs from independently reconstructed state")
    return path, row, attempt


def canonical_paths(inbox: dict[str, Any], extras: list[str]) -> list[str]:
    required = {
        MAP_PATH.as_posix(),
        PORTFOLIO_PATH.as_posix(),
        str(inbox["wayfinder_ticket"]),
    }
    required.update(extras)
    paths = sorted(required)
    for value in paths:
        repo_path(value, "canonical lifecycle path")
    return paths


def snapshot_for(paths: list[str], snapshot_id: str) -> dict[str, Any]:
    return freeze_agent_context.build_snapshot(
        root=ROOT,
        snapshot_id=snapshot_id,
        base_revision=current_revision(),
        sources=paths,
    )


def snapshot_receipts(path: Path, *, compare_live: bool) -> dict[str, str]:
    value = load_json(path, "context snapshot")
    errors = freeze_agent_context.validate_snapshot(
        value, root=ROOT, compare_live=compare_live
    )
    if errors:
        raise LifecycleError("invalid context snapshot: " + "; ".join(errors))
    return {entry["path"]: entry["sha256"] for entry in value["source_entries"]}


def validate_adjudication(value: Any, terminal: dict[str, Any]) -> dict[str, Any]:
    required = {
        "disposition",
        "net_proof_movement",
        "evidence",
        "damage_scope",
        "difficulty_displaced",
        "counterfactual_test",
        "planning_consequence",
        "ledger_edge",
        "mathematical_negative",
        "affected_portfolio_entries",
        "failure_genome_anchor",
    }
    if not isinstance(value, dict) or set(value) != required:
        raise LifecycleError("adjudication has unexpected or missing fields")
    disposition = value["disposition"]
    if disposition not in DISPOSITIONS:
        raise LifecycleError("adjudication disposition is invalid")
    if value["net_proof_movement"] not in MOVEMENTS:
        raise LifecycleError("net proof movement is invalid")
    if value["evidence"] not in EVIDENCE:
        raise LifecycleError("evidence classification is invalid")
    if value["damage_scope"] not in DAMAGE_SCOPES:
        raise LifecycleError("damage scope is invalid")
    if value["planning_consequence"] not in PLANNING:
        raise LifecycleError("planning consequence is invalid")
    for key in ("difficulty_displaced", "counterfactual_test", "ledger_edge"):
        if not isinstance(value[key], str) or not value[key].strip():
            raise LifecycleError(f"{key} must be a nonempty string")
    entries = value["affected_portfolio_entries"]
    if (
        not isinstance(entries, list)
        or not entries
        or len(entries) != len(set(entries))
        or any(not isinstance(item, str) or FP_RE.fullmatch(item) is None for item in entries)
    ):
        raise LifecycleError("affected portfolio entries are malformed")
    if type(value["mathematical_negative"]) is not bool:
        raise LifecycleError("mathematical_negative must be boolean")
    valid_terminal = terminal.get("valid_result") is True
    if valid_terminal and disposition == "operational":
        raise LifecycleError("a valid result cannot receive operational disposition")
    if not valid_terminal and disposition != "operational":
        raise LifecycleError("an invalid terminal can receive only operational disposition")
    if disposition == "operational":
        if (
            value["net_proof_movement"] != "neutral"
            or value["evidence"] != "operational_stop"
            or value["damage_scope"] != "operational-only"
            or value["ledger_edge"] != "NONE"
            or value["mathematical_negative"]
            or value["failure_genome_anchor"] is not None
        ):
            raise LifecycleError("operational reconciliation has inconsistent proof-distance fields")
    if value["net_proof_movement"] == "forward" and (
        disposition != "accepted"
        or value["evidence"] != "compiling_theorem"
        or value["ledger_edge"] == "NONE"
        or value["mathematical_negative"]
    ):
        raise LifecycleError("forward movement requires an accepted compiling theorem and named ledger edge")
    anchor = value["failure_genome_anchor"]
    if value["mathematical_negative"]:
        if disposition != "accepted" or not isinstance(anchor, dict) or set(anchor) != {"record", "anchor"}:
            raise LifecycleError("an admitted mathematical negative requires one failure-genome anchor")
        if not isinstance(anchor["anchor"], str) or not anchor["anchor"]:
            raise LifecycleError("failure-genome anchor label is blank")
        authenticate_receipt(anchor["record"], "failure-genome record")
    elif anchor is not None:
        raise LifecycleError("non-negative reconciliation cannot carry a failure-genome anchor")
    return value


def validate_draft(value: dict[str, Any]) -> None:
    if set(value) != {
        "schema_version",
        "protocol",
        "prepared_at",
        "inbox",
        "job_id",
        "canonical_pre_state",
        "pre_snapshot",
    }:
        raise LifecycleError("lifecycle draft has unexpected or missing fields")
    if value.get("schema_version") != 1 or value.get("protocol") != DRAFT_PROTOCOL:
        raise LifecycleError("lifecycle draft protocol is invalid")
    authenticate_receipt(value["inbox"], "lifecycle inbox")
    authenticate_receipt(value["pre_snapshot"], "pre-integration snapshot")
    pre = value["canonical_pre_state"]
    if not isinstance(pre, list) or len(pre) < 3:
        raise LifecycleError("canonical pre-state must contain at least map, portfolio, and ticket")
    paths = []
    for index, item in enumerate(pre):
        if not isinstance(item, dict) or set(item) != {"path", "sha256"}:
            raise LifecycleError(f"canonical pre-state receipt {index} is malformed")
        paths.append(item["path"])
        if not isinstance(item["sha256"], str) or HEX_RE.fullmatch(item["sha256"]) is None:
            raise LifecycleError(f"canonical pre-state SHA-256 {index} is malformed")
    if paths != sorted(paths) or len(paths) != len(set(paths)):
        raise LifecycleError("canonical pre-state paths must be sorted and unique")


def run_check(command: list[str]) -> dict[str, Any]:
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode != 0:
        raise LifecycleError(
            f"lifecycle check failed ({' '.join(command)}): {result.stderr.strip()}"
        )
    return {
        "command": " ".join(command),
        "exit_code": 0,
        "stdout_sha256": sha256_bytes(result.stdout.encode()),
        "stderr_sha256": sha256_bytes(result.stderr.encode()),
    }


def expected_check_commands(inbox: dict[str, Any]) -> list[list[str]]:
    commands = [
        ["python3", "scripts/check_agent_orchestration.py", "--task-packet", inbox["task_packet"]["path"]],
        ["python3", "scripts/wayfinder_status.py"],
        ["python3", "scripts/check_frontier_portfolio.py"],
    ]
    if inbox["result"] is not None:
        commands[0].extend(["--result", inbox["result"]["path"]])
    return commands


def verify_snapshot_state(snapshot_path: Path, state: list[dict[str, str]], label: str) -> None:
    entries = snapshot_receipts(snapshot_path, compare_live=False)
    expected = {item["path"]: item["sha256"] for item in state}
    missing = {path: digest for path, digest in expected.items() if entries.get(path) != digest}
    if missing:
        raise LifecycleError(f"{label} does not embed the exact canonical state: {sorted(missing)}")


def validate_canonical_semantics(
    inbox: dict[str, Any], adjudication: dict[str, Any], post_state: list[dict[str, str]]
) -> None:
    by_path = {item["path"]: item for item in post_state}
    required = {MAP_PATH.as_posix(), PORTFOLIO_PATH.as_posix(), inbox["wayfinder_ticket"]}
    if not required.issubset(by_path):
        raise LifecycleError("post-state omits map, portfolio, or owning ticket")
    terminal_hash = inbox["terminal"]["sha256"]
    ticket_text = repo_path(inbox["wayfinder_ticket"], "owning ticket").read_text(encoding="utf-8")
    required_ticket_strings = [
        terminal_hash,
        adjudication["net_proof_movement"],
        adjudication["evidence"],
        adjudication["damage_scope"],
        adjudication["difficulty_displaced"],
        adjudication["counterfactual_test"],
        adjudication["planning_consequence"],
        adjudication["ledger_edge"],
    ]
    missing = [item for item in required_ticket_strings if item not in ticket_text]
    if missing:
        raise LifecycleError(f"owning ticket does not bind lifecycle adjudication: {missing}")
    portfolio_text = repo_path(PORTFOLIO_PATH, "frontier portfolio").read_text(encoding="utf-8")
    for entry in adjudication["affected_portfolio_entries"]:
        if entry not in portfolio_text:
            raise LifecycleError(f"affected portfolio entry is absent: {entry}")
    anchor = adjudication["failure_genome_anchor"]
    if anchor is not None:
        record_path = authenticate_receipt(anchor["record"], "failure-genome record")
        if anchor["record"] not in post_state:
            raise LifecycleError("failure-genome record is not bound in canonical post-state")
        record_text = record_path.read_text(encoding="utf-8")
        if anchor["anchor"] not in record_text or terminal_hash not in record_text:
            raise LifecycleError("failure-genome record lacks its anchor or terminal hash")


def validate_receipt_structure(value: dict[str, Any]) -> None:
    top = {
        "schema_version",
        "protocol",
        "sealed_at",
        "approval_ref",
        "inbox",
        "job_id",
        "disposition",
        "adjudication",
        "canonical_transition",
        "checks",
    }
    if set(value) != top or value.get("schema_version") != 1 or value.get("protocol") != PROTOCOL:
        raise LifecycleError("lifecycle receipt has unexpected fields or protocol")
    if not isinstance(value.get("sealed_at"), str) or not value["sealed_at"]:
        raise LifecycleError("sealed_at is blank")
    if not isinstance(value.get("approval_ref"), str) or not value["approval_ref"]:
        raise LifecycleError("approval_ref is blank")
    if value.get("disposition") not in DISPOSITIONS:
        raise LifecycleError("receipt disposition is invalid")
    authenticate_receipt(value["inbox"], "lifecycle inbox")
    transition = value.get("canonical_transition")
    if not isinstance(transition, dict) or set(transition) != {
        "pre_state",
        "post_state",
        "changed_paths",
        "pre_snapshot",
        "post_snapshot",
    }:
        raise LifecycleError("canonical transition is malformed")
    for key in ("pre_state", "post_state"):
        state = transition[key]
        if not isinstance(state, list) or len(state) < 3:
            raise LifecycleError(f"{key} must contain at least three receipts")
        paths = []
        for index, item in enumerate(state):
            if not isinstance(item, dict) or set(item) != {"path", "sha256"}:
                raise LifecycleError(f"{key}[{index}] is malformed")
            if not isinstance(item["sha256"], str) or HEX_RE.fullmatch(item["sha256"]) is None:
                raise LifecycleError(f"{key}[{index}] SHA-256 is malformed")
            paths.append(item["path"])
        if paths != sorted(paths) or len(paths) != len(set(paths)):
            raise LifecycleError(f"{key} paths must be sorted and unique")
    if [item["path"] for item in transition["pre_state"]] != [item["path"] for item in transition["post_state"]]:
        raise LifecycleError("canonical transition changes its path inventory")
    changed = transition["changed_paths"]
    if not isinstance(changed, list) or len(changed) < 3 or changed != sorted(set(changed)):
        raise LifecycleError("changed_paths must be a sorted unique array of at least three paths")
    authenticate_receipt(transition["pre_snapshot"], "pre-integration snapshot")
    authenticate_receipt(transition["post_snapshot"], "post-integration snapshot")
    checks = value.get("checks")
    if not isinstance(checks, list) or len(checks) != 3:
        raise LifecycleError("lifecycle receipt must bind exactly three checks")
    for check in checks:
        if not isinstance(check, dict) or set(check) != {"command", "exit_code", "stdout_sha256", "stderr_sha256"}:
            raise LifecycleError("lifecycle check receipt is malformed")
        if check["exit_code"] != 0 or any(
            not isinstance(check[key], str) or HEX_RE.fullmatch(check[key]) is None
            for key in ("stdout_sha256", "stderr_sha256")
        ):
            raise LifecycleError("lifecycle check did not record a successful authenticated output")


def check_receipt(path: Path, service_dir: Path, job_id: str, *, require_pending: bool) -> dict[str, Any]:
    value = load_json(path, "lifecycle receipt")
    validate_receipt_structure(value)
    inbox_path_value, row, attempt = verify_inbox(service_dir, job_id, require_pending=require_pending)
    if value["job_id"] != job_id or value["inbox"] != receipt(inbox_path_value):
        raise LifecycleError("lifecycle receipt does not bind the requested job/inbox")
    inbox = load_json(inbox_path_value, "lifecycle inbox")
    terminal_path = authenticate_receipt(inbox["terminal"], "worker terminal")
    terminal = load_json(terminal_path, "worker terminal")
    adjudication = validate_adjudication(
        {"disposition": value["disposition"], **value["adjudication"]}, terminal
    )
    adjudication.pop("disposition")
    if adjudication != value["adjudication"]:
        raise LifecycleError("receipt adjudication normalization mismatch")
    transition = value["canonical_transition"]
    pre_snapshot_path = authenticate_receipt(transition["pre_snapshot"], "pre-integration snapshot")
    post_snapshot_path = authenticate_receipt(transition["post_snapshot"], "post-integration snapshot")
    verify_snapshot_state(pre_snapshot_path, transition["pre_state"], "pre-integration snapshot")
    verify_snapshot_state(post_snapshot_path, transition["post_state"], "post-integration snapshot")
    pre = {item["path"]: item["sha256"] for item in transition["pre_state"]}
    post = {item["path"]: item["sha256"] for item in transition["post_state"]}
    changed = sorted(path for path in pre if pre[path] != post[path])
    if changed != transition["changed_paths"]:
        raise LifecycleError("changed_paths does not equal the exact pre/post hash delta")
    required_changed = {MAP_PATH.as_posix(), PORTFOLIO_PATH.as_posix(), inbox["wayfinder_ticket"]}
    if not required_changed.issubset(changed):
        raise LifecycleError("map, portfolio, and owning ticket must each record the terminal")
    for item in transition["post_state"]:
        live = repo_path(item["path"], "canonical post-state")
        if sha256(live) != item["sha256"]:
            raise LifecycleError(f"canonical post-state drifted after sealing: {item['path']}")
    validate_canonical_semantics(inbox, value["adjudication"], transition["post_state"])
    expected_commands = expected_check_commands(inbox)
    if [item["command"] for item in value["checks"]] != [" ".join(command) for command in expected_commands]:
        raise LifecycleError("lifecycle receipt binds an unexpected check inventory")
    for command in expected_commands:
        run_check(command)
    return value


def command_prepare(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    inbox_path_value, _row, _attempt = verify_inbox(service_dir, args.job_id, require_pending=True)
    inbox = load_json(inbox_path_value, "lifecycle inbox")
    paths = canonical_paths(inbox, args.canonical_path or [])
    pre_state = [receipt(repo_path(path, "canonical pre-state")) for path in paths]
    snapshot_path = args.pre_snapshot.resolve()
    snapshot = snapshot_for(paths, f"{args.job_id}-pre-integration")
    freeze_agent_context.write_new(snapshot_path, snapshot)
    draft = {
        "schema_version": 1,
        "protocol": DRAFT_PROTOCOL,
        "prepared_at": now(),
        "inbox": receipt(inbox_path_value),
        "job_id": args.job_id,
        "canonical_pre_state": pre_state,
        "pre_snapshot": receipt(snapshot_path),
    }
    write_once(args.output.resolve(), draft)
    print(json.dumps({"draft": receipt(args.output.resolve()), "pre_snapshot": receipt(snapshot_path)}, indent=2, sort_keys=True))
    return 0


def command_seal(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    draft_path = repo_path(args.draft, "lifecycle draft")
    draft = load_json(draft_path, "lifecycle draft")
    validate_draft(draft)
    if draft["job_id"] != args.job_id:
        raise LifecycleError("draft job identity mismatch")
    inbox_path_value, _row, _attempt = verify_inbox(service_dir, args.job_id, require_pending=True)
    if draft["inbox"] != receipt(inbox_path_value):
        raise LifecycleError("draft binds another lifecycle inbox")
    inbox = load_json(inbox_path_value, "lifecycle inbox")
    terminal = load_json(authenticate_receipt(inbox["terminal"], "worker terminal"), "worker terminal")
    raw_adjudication = load_json(repo_path(args.adjudication, "lifecycle adjudication"), "lifecycle adjudication")
    adjudication_with_disposition = validate_adjudication(raw_adjudication, terminal)
    disposition = adjudication_with_disposition["disposition"]
    adjudication = {key: value for key, value in adjudication_with_disposition.items() if key != "disposition"}
    pre_state = draft["canonical_pre_state"]
    post_state = [receipt(repo_path(item["path"], "canonical post-state")) for item in pre_state]
    pre = {item["path"]: item["sha256"] for item in pre_state}
    post = {item["path"]: item["sha256"] for item in post_state}
    changed = sorted(path for path in pre if pre[path] != post[path])
    required_changed = {MAP_PATH.as_posix(), PORTFOLIO_PATH.as_posix(), inbox["wayfinder_ticket"]}
    if not required_changed.issubset(changed):
        raise LifecycleError("map, portfolio, and owning ticket must each change before sealing")
    post_snapshot_path = repo_path(args.post_snapshot, "post-integration snapshot")
    verify_snapshot_state(post_snapshot_path, post_state, "post-integration snapshot")
    validate_canonical_semantics(inbox, adjudication, post_state)
    checks = [run_check(command) for command in expected_check_commands(inbox)]
    lifecycle = {
        "schema_version": 1,
        "protocol": PROTOCOL,
        "sealed_at": now(),
        "approval_ref": args.approval_ref,
        "inbox": receipt(inbox_path_value),
        "job_id": args.job_id,
        "disposition": disposition,
        "adjudication": adjudication,
        "canonical_transition": {
            "pre_state": pre_state,
            "post_state": post_state,
            "changed_paths": changed,
            "pre_snapshot": draft["pre_snapshot"],
            "post_snapshot": receipt(post_snapshot_path),
        },
        "checks": checks,
    }
    validate_receipt_structure(lifecycle)
    write_once(args.output.resolve(), lifecycle)
    check_receipt(args.output.resolve(), service_dir, args.job_id, require_pending=True)
    print(json.dumps({"lifecycle_receipt": receipt(args.output.resolve()), "job_id": args.job_id}, indent=2, sort_keys=True))
    return 0


def command_check(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    path = repo_path(args.receipt, "lifecycle receipt")
    if args.receipt_sha256 is not None and sha256(path) != args.receipt_sha256:
        raise LifecycleError("requested lifecycle receipt SHA-256 does not authenticate")
    value = check_receipt(path, service_dir, args.job_id, require_pending=args.require_pending)
    print(json.dumps({"ok": True, "job_id": value["job_id"], "receipt": receipt(path)}, indent=2, sort_keys=True))
    return 0


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    prepare = subparsers.add_parser("prepare", help="freeze the serial pre-integration state")
    prepare.add_argument("--service-dir", type=Path, required=True)
    prepare.add_argument("--job-id", required=True)
    prepare.add_argument("--output", type=Path, required=True)
    prepare.add_argument("--pre-snapshot", type=Path, required=True)
    prepare.add_argument("--canonical-path", action="append", default=[])
    prepare.set_defaults(function=command_prepare)

    seal = subparsers.add_parser("seal", help="seal a checked post-integration lifecycle receipt")
    seal.add_argument("--service-dir", type=Path, required=True)
    seal.add_argument("--job-id", required=True)
    seal.add_argument("--draft", type=Path, required=True)
    seal.add_argument("--adjudication", type=Path, required=True)
    seal.add_argument("--post-snapshot", type=Path, required=True)
    seal.add_argument("--approval-ref", required=True)
    seal.add_argument("--output", type=Path, required=True)
    seal.set_defaults(function=command_seal)

    check = subparsers.add_parser("check", help="independently authenticate a sealed lifecycle receipt")
    check.add_argument("--service-dir", type=Path, required=True)
    check.add_argument("--job-id", required=True)
    check.add_argument("--receipt", type=Path, required=True)
    check.add_argument("--receipt-sha256")
    check.add_argument("--require-pending", action="store_true")
    check.set_defaults(function=command_check)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        return int(args.function(args))
    except (LifecycleError, OSError, sqlite3.Error) as exc:
        print(f"lifecycle error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
