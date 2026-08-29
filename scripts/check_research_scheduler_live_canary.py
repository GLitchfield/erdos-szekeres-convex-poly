#!/usr/bin/env python3
"""Independently verify one five-task real-Codex scheduler canary receipt."""

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
PROTOCOL = "research-scheduler-live-acceptance-v1"
CONTROL_PROTOCOL = "research-scheduler-live-canary-barrier-v1"


class LiveCanaryCheckError(ValueError):
    pass


def load_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise LiveCanaryCheckError(f"cannot parse {label}: {exc}") from exc
    if not isinstance(value, dict):
        raise LiveCanaryCheckError(f"{label} must be a JSON object")
    return value


def authenticate(value: Any, label: str) -> Path:
    if not isinstance(value, dict) or set(value) != {"path", "sha256"}:
        raise LiveCanaryCheckError(f"{label} receipt is malformed")
    path = scheduler.repo_path(str(value["path"]), label)
    if not path.is_file() or scheduler.sha256(path) != value["sha256"]:
        raise LiveCanaryCheckError(f"{label} receipt does not authenticate")
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
    except (TypeError, ValueError) as exc:
        raise LiveCanaryCheckError(f"invalid canary timestamp: {value}") from exc


def expected_command_fragments() -> list[str]:
    return [
        "exec",
        "--model",
        "gpt-5.6-sol",
        'model_reasoning_effort="low"',
        'web_search="disabled"',
        'approval_policy="never"',
        "agents.enabled=false",
        "--sandbox",
        "workspace-write",
        "--output-schema",
        "--output-last-message",
        "--json",
    ]


def check(args: argparse.Namespace) -> dict[str, Any]:
    result_path = scheduler.repo_path(args.result, "live-canary acceptance result")
    if args.result_sha256 and scheduler.sha256(result_path) != args.result_sha256:
        raise LiveCanaryCheckError("live-canary result SHA-256 does not authenticate")
    value = load_json(result_path, "live-canary acceptance result")
    required = {
        "schema_version",
        "protocol",
        "run_id",
        "service_dir",
        "finished_at",
        "approval_ref",
        "provider_calls",
        "network_mode",
        "authorization",
        "operational_wave",
        "reserve_plan",
        "task_packets",
        "runner",
        "checker",
        "daemon_before_restart",
        "daemon_after_restart",
        "initial_workers",
        "restart_started_at",
        "first_terminal_at",
        "fifth_launch_at",
        "database",
        "barriers",
        "terminal_count",
        "lifecycle_inbox_count",
        "result",
    }
    if (
        set(value) != required
        or value.get("schema_version") != 1
        or value.get("protocol") != PROTOCOL
    ):
        raise LiveCanaryCheckError("live-canary result has unexpected fields or protocol")
    if (
        value["provider_calls"] != 5
        or value["network_mode"] != "disabled"
        or value["terminal_count"] != 5
        or value["lifecycle_inbox_count"] != 5
        or value["result"] != "THREAD-LIFECYCLE-LIVE-PROCESS-PASS"
    ):
        raise LiveCanaryCheckError("live-canary result overstates or misclassifies its boundary")

    service_dir = scheduler.service_directory(Path(value["service_dir"]))
    authorization_path = authenticate(value["authorization"], "canary authorization")
    authorization = scheduler.verify_authorization(authorization_path, service_dir)
    provider = authorization["provider"]
    limits = authorization["limits"]
    if (
        not authorization["dispatch_enabled"]
        or provider["version"] != "codex-cli 0.150.0"
        or provider["allowed_models"] != ["gpt-5.6-sol"]
        or provider["default_model"] != "gpt-5.6-sol"
        or provider["executable_sha256"]
        != "134063e133f0b4244fa3b251acf973d4fe4b4aeeacbdc135211bf480f59f1477"
        or limits["capacity"] != 4
        or limits["poll_seconds"] != 5
    ):
        raise LiveCanaryCheckError("authorization is not the exact four-lane live envelope")

    runner_path = authenticate(value["runner"], "live-canary runner")
    checker_path = authenticate(value["checker"], "live-canary checker")
    if runner_path.name != "run_research_scheduler_live_canary.py" or checker_path.resolve() != Path(__file__).resolve():
        raise LiveCanaryCheckError("acceptance receipt binds unexpected runner/checker code")

    wave_path = authenticate(value["operational_wave"], "canary wave")
    reserve_path = authenticate(value["reserve_plan"], "canary reserve")
    database = authenticate(value["database"], "canary database")
    before_path = authenticate(value["daemon_before_restart"], "pre-restart daemon")
    after_path = authenticate(value["daemon_after_restart"], "post-restart daemon")
    initial_path = authenticate(value["initial_workers"], "initial-worker observation")
    before = load_json(before_path, "pre-restart daemon")
    after = load_json(after_path, "post-restart daemon")
    initial = load_json(initial_path, "initial-worker observation")
    if before.get("service_id") == after.get("service_id"):
        raise LiveCanaryCheckError("scheduler service identity did not change across restart")
    if before.get("authorization") != value["authorization"] or after.get("authorization") != value["authorization"]:
        raise LiveCanaryCheckError("scheduler restart changed standing authorization")
    if parse_time(after["started_at"]) < parse_time(value["restart_started_at"]):
        raise LiveCanaryCheckError("post-restart service predates the restart observation")
    initial_jobs = initial.get("jobs")
    initial_states = initial.get("unit_states")
    if (
        not isinstance(initial_jobs, list)
        or len(initial_jobs) != 4
        or not isinstance(initial_states, dict)
        or set(initial_states.values()) - {"active", "activating"}
    ):
        raise LiveCanaryCheckError("initial observation does not prove four supervised workers")

    task_receipts = value["task_packets"]
    if not isinstance(task_receipts, list) or len(task_receipts) != 5:
        raise LiveCanaryCheckError("live canary must bind exactly five tasks")
    task_paths = [authenticate(item, f"canary task {index}") for index, item in enumerate(task_receipts, 1)]
    wave = load_json(wave_path, "canary wave")
    reserve = load_json(reserve_path, "canary reserve")
    if wave.get("approved_task_packets") != task_receipts or len(reserve.get("jobs", [])) != 5:
        raise LiveCanaryCheckError("wave/reserve inventory differs from the canary receipt")
    if reserve.get("authorization") != value["authorization"] or reserve.get("operational_wave") != value["operational_wave"]:
        raise LiveCanaryCheckError("reserve does not bind the exact authorization and wave")
    if reserve.get("approval_ref") != value["approval_ref"]:
        raise LiveCanaryCheckError("reserve and acceptance result use different literal approvals")
    expected_provider = {
        "model": "gpt-5.6-sol",
        "reasoning_effort": "low",
        "web_search": "disabled",
    }
    for job in reserve["jobs"]:
        if (
            job.get("provider") != expected_provider
            or job.get("resume_limit") != 0
            or job.get("slot_label") != "verification"
            or job.get("occupancy_class") != "support"
            or job.get("mechanism_family") is not None
        ):
            raise LiveCanaryCheckError("reserve job widens provider, retry, or occupancy authority")

    jobs = rows(database, "SELECT * FROM jobs ORDER BY priority DESC, job_id")
    attempts = rows(database, "SELECT * FROM attempts ORDER BY started_at, job_id")
    lanes = rows(database, "SELECT * FROM lanes ORDER BY lane_id")
    events = rows(database, "SELECT * FROM events ORDER BY sequence")
    if len(jobs) != 5 or len(attempts) != 5 or len(lanes) != 4:
        raise LiveCanaryCheckError("raw scheduler cardinalities differ from five jobs/four lanes")
    if any(job["status"] != "terminal_pending_reconciliation" or job["lane_id"] is not None for job in jobs):
        raise LiveCanaryCheckError("a live canary escaped the terminal inbox or retained a lane")
    if any(attempt["ordinal"] != 1 or attempt["status"] != "terminal" for attempt in attempts):
        raise LiveCanaryCheckError("restart caused a duplicate, resumed, or nonterminal attempt")
    if any(lane["state"] != "free" or lane["job_id"] is not None for lane in lanes):
        raise LiveCanaryCheckError("scheduler lanes are not free at process terminal")

    launch_events = [event for event in events if event["event"] == "worker-launched"]
    terminal_events = [event for event in events if event["event"] == "worker-terminal-observed"]
    if len(launch_events) != 5 or len(terminal_events) != 5:
        raise LiveCanaryCheckError("event log does not contain exactly five launches and terminals")
    first_terminal_sequence = min(event["sequence"] for event in terminal_events)
    launches_before = [event for event in launch_events if event["sequence"] < first_terminal_sequence]
    launches_after = [event for event in launch_events if event["sequence"] > first_terminal_sequence]
    if len(launches_before) != 4 or len(launches_after) != 1:
        raise LiveCanaryCheckError("event order does not prove four initial workers and one backfill")
    latency = (parse_time(value["fifth_launch_at"]) - parse_time(value["first_terminal_at"])).total_seconds()
    if latency < 0 or latency > 11.0:
        raise LiveCanaryCheckError(f"fifth-worker backfill exceeded two poll intervals: {latency:.3f}s")

    barrier_values = value["barriers"]
    if not isinstance(barrier_values, list) or len(barrier_values) != 5:
        raise LiveCanaryCheckError("canary receipt does not bind five barrier records")
    barriers_by_task: dict[str, dict[str, Any]] = {}
    for barrier in barrier_values:
        if not isinstance(barrier, dict) or set(barrier) != {"task_id", "control", "ready", "release", "sentinel"}:
            raise LiveCanaryCheckError("barrier receipt is malformed")
        control_path = authenticate(barrier["control"], "barrier control")
        ready_path = authenticate(barrier["ready"], "barrier ready marker")
        release_path = authenticate(barrier["release"], "barrier release marker")
        control = load_json(control_path, "barrier control")
        if (
            control.get("protocol") != CONTROL_PROTOCOL
            or control.get("sentinel") != barrier["sentinel"]
            or ready_path.read_text(encoding="utf-8").strip() != f"{barrier['sentinel']}-READY"
            or release_path.read_text(encoding="utf-8").strip() != f"{barrier['sentinel']}-RELEASE"
        ):
            raise LiveCanaryCheckError("barrier bytes do not match the immutable control")
        barriers_by_task[str(barrier["task_id"])] = barrier
    if len(barriers_by_task) != 5:
        raise LiveCanaryCheckError("barrier records repeat a task identity")

    attempts_by_job = {attempt["job_id"]: attempt for attempt in attempts}
    task_paths_by_receipt = {scheduler.repo_relative(path): path for path in task_paths}
    thread_ids: set[str] = set()
    required_fragments = expected_command_fragments()
    for job in jobs:
        task_path = task_paths_by_receipt.get(job["task_path"])
        if task_path is None or scheduler.sha256(task_path) != job["task_sha256"]:
            raise LiveCanaryCheckError("raw job task identity differs from approved inventory")
        task = load_json(task_path, "canary task")
        barrier = barriers_by_task.get(task["task_id"])
        if barrier is None:
            raise LiveCanaryCheckError("task lacks a matching barrier receipt")
        attempt = attempts_by_job[job["job_id"]]
        terminal_path = scheduler.repo_path(attempt["terminal_path"], "worker terminal")
        terminal = load_json(terminal_path, "worker terminal")
        thread_id = terminal.get("thread_id")
        if terminal.get("valid_result") is not True or not isinstance(thread_id, str) or not thread_id:
            raise LiveCanaryCheckError("worker terminal lacks a valid result or real thread identity")
        thread_ids.add(thread_id)
        result_file = authenticate(terminal.get("result"), "worker result")
        last_message = authenticate(terminal.get("last_message"), "worker last message")
        result = load_json(result_file, "worker result")
        if result != load_json(last_message, "worker last message"):
            raise LiveCanaryCheckError("worker result differs from its structured final message")
        if result.get("claim_level") != "proposal" or barrier["sentinel"] not in str(result.get("summary", "")):
            raise LiveCanaryCheckError("worker result lacks its proposal ceiling or sentinel")
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
            raise LiveCanaryCheckError(f"task/result validation failed: {validation.stderr.strip()}")
        attempt_receipt = load_json(
            scheduler.attempt_directory(service_dir, job["job_id"], 1) / "attempt.json",
            "worker attempt receipt",
        )
        command = attempt_receipt.get("command")
        if not isinstance(command, list) or not command:
            raise LiveCanaryCheckError("worker attempt lacks a command array")
        if Path(command[0]).resolve() != Path(provider["executable"]).resolve() or "resume" in command:
            raise LiveCanaryCheckError("worker command changed provider identity or used a retry")
        joined = "\n".join(str(item) for item in command)
        if any(fragment not in joined for fragment in required_fragments):
            raise LiveCanaryCheckError("worker command omitted a frozen provider safety setting")
        inbox_path = scheduler.lifecycle_inbox_path(service_dir, job["job_id"])
        inbox = load_json(inbox_path, "lifecycle inbox")
        expected_inbox = lifecycle.expected_inbox(service_dir, job, attempt)
        if inbox != expected_inbox:
            raise LiveCanaryCheckError("lifecycle inbox differs from independent reconstruction")
    if len(thread_ids) != 5:
        raise LiveCanaryCheckError("five provider attempts did not produce five distinct thread identities")

    return {
        "ok": True,
        "result": scheduler.file_receipt(result_path),
        "real_provider_calls": 5,
        "four_initial_workers": True,
        "scheduler_restart": True,
        "fifth_backfill_latency_seconds": latency,
        "valid_terminal_lifecycle_inboxes": 5,
        "network_mode": "disabled",
        "same_thread_resumes": 0,
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
    except (
        LiveCanaryCheckError,
        scheduler.SchedulerError,
        lifecycle.LifecycleError,
        OSError,
        sqlite3.Error,
    ) as exc:
        print(f"live canary check error: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
