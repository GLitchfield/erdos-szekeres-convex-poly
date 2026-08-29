#!/usr/bin/env python3
"""Independently check the deterministic scheduler process acceptance receipt."""

from __future__ import annotations

import argparse
from datetime import datetime
import json
from pathlib import Path
import sqlite3
import subprocess
import sys
from typing import Any

try:
    from scripts import check_wayfinder_thread_lifecycle as lifecycle
    from scripts import research_scheduler as scheduler
except ImportError:  # Direct execution places scripts/ on sys.path.
    import check_wayfinder_thread_lifecycle as lifecycle
    import research_scheduler as scheduler


ROOT = Path(__file__).resolve().parents[1]
PROTOCOL = "research-scheduler-local-acceptance-v1"


class AcceptanceCheckError(ValueError):
    pass


def load_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise AcceptanceCheckError(f"cannot parse {label}: {exc}") from exc
    if not isinstance(value, dict):
        raise AcceptanceCheckError(f"{label} must be a JSON object")
    return value


def authenticate(value: Any, label: str) -> Path:
    if not isinstance(value, dict) or set(value) != {"path", "sha256"}:
        raise AcceptanceCheckError(f"{label} receipt is malformed")
    path = scheduler.repo_path(value["path"], label)
    if not path.is_file() or scheduler.sha256(path) != value["sha256"]:
        raise AcceptanceCheckError(f"{label} receipt does not authenticate")
    return path


def rows(database: Path, query: str) -> list[dict[str, Any]]:
    connection = sqlite3.connect(f"file:{database}?mode=ro", uri=True)
    connection.row_factory = sqlite3.Row
    try:
        return [dict(row) for row in connection.execute(query)]
    finally:
        connection.close()


def parse_time(value: str) -> datetime:
    try:
        return datetime.fromisoformat(value)
    except ValueError as exc:
        raise AcceptanceCheckError(f"invalid acceptance timestamp: {value}") from exc


def check(args: argparse.Namespace) -> dict[str, Any]:
    result_path = scheduler.repo_path(args.result, "acceptance result")
    if args.result_sha256 and scheduler.sha256(result_path) != args.result_sha256:
        raise AcceptanceCheckError("acceptance result SHA-256 does not authenticate")
    value = load_json(result_path, "acceptance result")
    required = {
        "schema_version",
        "protocol",
        "run_id",
        "finished_at",
        "approval_ref",
        "provider_calls",
        "network_mode",
        "authorization",
        "operational_wave",
        "reserve_plan",
        "task_packets",
        "daemon_before_restart",
        "daemon_after_restart",
        "restart_started_at",
        "first_terminal_at",
        "fifth_launch_at",
        "database",
        "terminal_count",
        "lifecycle_inbox_count",
        "result",
    }
    if set(value) != required or value.get("schema_version") != 1 or value.get("protocol") != PROTOCOL:
        raise AcceptanceCheckError("acceptance result has unexpected fields or protocol")
    if (
        value["provider_calls"] != 0
        or value["network_mode"] != "disabled"
        or value["terminal_count"] != 5
        or value["lifecycle_inbox_count"] != 5
        or value["result"] != "THREAD-LIFECYCLE-LOCAL-PROCESS-PASS"
    ):
        raise AcceptanceCheckError("acceptance result overstates or misclassifies its boundary")
    authorization_path = authenticate(value["authorization"], "acceptance authorization")
    authorization = scheduler.verify_authorization(authorization_path)
    if (
        not authorization["dispatch_enabled"]
        or authorization["provider"]["version"] != "codex-cli scheduler-acceptance-fake-1"
        or authorization["provider"]["allowed_models"] != ["scheduler-acceptance-fake"]
        or authorization["limits"]["capacity"] != 4
    ):
        raise AcceptanceCheckError("acceptance authorization is not the exact local four-lane envelope")
    wave_path = authenticate(value["operational_wave"], "acceptance wave")
    reserve_path = authenticate(value["reserve_plan"], "acceptance reserve")
    database = authenticate(value["database"], "acceptance database")
    before_path = authenticate(value["daemon_before_restart"], "pre-restart daemon")
    after_path = authenticate(value["daemon_after_restart"], "post-restart daemon")
    before = load_json(before_path, "pre-restart daemon")
    after = load_json(after_path, "post-restart daemon")
    if before.get("service_id") == after.get("service_id"):
        raise AcceptanceCheckError("scheduler service identity did not change across restart")
    if before.get("process_identity", {}).get("boot_id") != after.get("process_identity", {}).get("boot_id"):
        raise AcceptanceCheckError("local restart unexpectedly crossed a boot identity")
    if before.get("authorization") != value["authorization"] or after.get("authorization") != value["authorization"]:
        raise AcceptanceCheckError("scheduler restart changed authorization")
    restart_at = parse_time(value["restart_started_at"])
    if parse_time(after["started_at"]) < restart_at:
        raise AcceptanceCheckError("post-restart daemon predates the recorded restart")

    task_receipts = value["task_packets"]
    if not isinstance(task_receipts, list) or len(task_receipts) != 5:
        raise AcceptanceCheckError("acceptance must bind exactly five tasks")
    task_paths = [authenticate(item, f"acceptance task {index}") for index, item in enumerate(task_receipts)]
    wave = load_json(wave_path, "acceptance wave")
    reserve = load_json(reserve_path, "acceptance reserve")
    if wave.get("approved_task_packets") != task_receipts or len(reserve.get("jobs", [])) != 5:
        raise AcceptanceCheckError("wave/reserve task inventory differs from the acceptance receipt")
    if reserve.get("authorization") != value["authorization"] or reserve.get("operational_wave") != value["operational_wave"]:
        raise AcceptanceCheckError("reserve does not bind the exact authorization and wave")
    for job in reserve["jobs"]:
        if (
            job["provider"] != {
                "model": "scheduler-acceptance-fake",
                "reasoning_effort": "low",
                "web_search": "disabled",
            }
            or job["resume_limit"] != 0
            or job["occupancy_class"] != "mathematical"
        ):
            raise AcceptanceCheckError("acceptance reserve widened provider or retry authority")

    jobs = rows(database, "SELECT * FROM jobs ORDER BY priority DESC, job_id")
    attempts = rows(database, "SELECT * FROM attempts ORDER BY started_at, job_id")
    lanes = rows(database, "SELECT * FROM lanes ORDER BY lane_id")
    events = rows(database, "SELECT * FROM events ORDER BY sequence")
    if len(jobs) != 5 or len(attempts) != 5 or len(lanes) != 4:
        raise AcceptanceCheckError("raw scheduler cardinalities do not match five jobs/four lanes")
    if any(job["status"] != "terminal_pending_reconciliation" or job["lane_id"] is not None for job in jobs):
        raise AcceptanceCheckError("a canary escaped the terminal inbox or retained a process lane")
    if any(attempt["ordinal"] != 1 or attempt["status"] != "terminal" for attempt in attempts):
        raise AcceptanceCheckError("restart caused a duplicate/resumed/nonterminal attempt")
    if any(lane["state"] != "free" or lane["job_id"] is not None for lane in lanes):
        raise AcceptanceCheckError("process lanes are not free after all terminals")

    launch_events = [event for event in events if event["event"] == "worker-launched"]
    terminal_events = [event for event in events if event["event"] == "worker-terminal-observed"]
    if len(launch_events) != 5 or len(terminal_events) != 5:
        raise AcceptanceCheckError("raw event log does not contain five launches and terminals")
    first_terminal_sequence = min(event["sequence"] for event in terminal_events)
    launches_before = [event for event in launch_events if event["sequence"] < first_terminal_sequence]
    launches_after = [event for event in launch_events if event["sequence"] > first_terminal_sequence]
    if len(launches_before) != 4 or len(launches_after) != 1:
        raise AcceptanceCheckError("event order does not prove four initial workers plus one backfill")
    first_terminal = parse_time(value["first_terminal_at"])
    fifth_launch = parse_time(value["fifth_launch_at"])
    latency = (fifth_launch - first_terminal).total_seconds()
    if latency < 0 or latency > 4.5:
        raise AcceptanceCheckError(f"fifth-worker backfill exceeded two poll intervals: {latency:.3f}s")

    service_dir = result_path.parent
    for job, task_path in zip(jobs, task_paths):
        if job["task_path"] != scheduler.repo_relative(task_path) or job["task_sha256"] != scheduler.sha256(task_path):
            raise AcceptanceCheckError("raw job task identity differs from approved inventory")
        terminal_path = scheduler.attempt_directory(service_dir, job["job_id"], 1) / "terminal.json"
        terminal = load_json(terminal_path, "worker terminal")
        if terminal.get("valid_result") is not True or terminal.get("thread_id") != f"acceptance-{job['task_id']}":
            raise AcceptanceCheckError("worker terminal lacks valid result/thread identity")
        result_receipt = terminal.get("result")
        result_file = authenticate(result_receipt, "worker result")
        validation = subprocess.run(
            [
                "python3",
                "scripts/check_agent_orchestration.py",
                "--task-packet",
                scheduler.repo_relative(task_path),
                "--result",
                scheduler.repo_relative(result_file),
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
        )
        if validation.returncode != 0:
            raise AcceptanceCheckError(f"task/result validation failed: {validation.stderr.strip()}")
        inbox_path = scheduler.lifecycle_inbox_path(service_dir, job["job_id"])
        inbox = load_json(inbox_path, "lifecycle inbox")
        expected = lifecycle.expected_inbox(service_dir, job, next(item for item in attempts if item["job_id"] == job["job_id"]))
        if inbox != expected:
            raise AcceptanceCheckError("lifecycle inbox does not independently reconstruct")
        attempt_receipt = load_json(
            scheduler.attempt_directory(service_dir, job["job_id"], 1) / "attempt.json",
            "worker attempt receipt",
        )
        if parse_time(attempt_receipt["started_at"]) >= parse_time(after["started_at"]):
            if job["task_id"] != "scheduler-acceptance-worker-5":
                raise AcceptanceCheckError("an initial worker was relaunched after scheduler restart")
        command = attempt_receipt.get("command", [])
        if not command or Path(command[0]).resolve() != Path(authorization["provider"]["executable"]).resolve():
            raise AcceptanceCheckError("worker attempt did not use the frozen local fake executable")
    return {
        "ok": True,
        "result": scheduler.file_receipt(result_path),
        "four_initial_workers": True,
        "scheduler_restart": True,
        "fifth_backfill_latency_seconds": latency,
        "terminal_lifecycle_inboxes": 5,
        "provider_calls": 0,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--result", type=Path, required=True)
    parser.add_argument("--result-sha256")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        payload = check(args)
    except (AcceptanceCheckError, scheduler.SchedulerError, lifecycle.LifecycleError, OSError, sqlite3.Error) as exc:
        print(f"acceptance check error: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
