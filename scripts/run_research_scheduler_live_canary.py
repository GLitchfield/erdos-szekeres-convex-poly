#!/usr/bin/env python3
"""Run one exact, separately approved five-task real-Codex scheduler canary."""

from __future__ import annotations

import argparse
from contextlib import redirect_stdout
from datetime import datetime, timezone
import io
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import time
from types import SimpleNamespace
from typing import Any, Callable

try:
    from scripts import research_scheduler as scheduler
except ImportError:  # Direct execution places scripts/ on sys.path.
    import research_scheduler as scheduler


ROOT = Path(__file__).resolve().parents[1]
PROTOCOL = "research-scheduler-live-acceptance-v1"
CONTROL_PROTOCOL = "research-scheduler-live-canary-barrier-v1"
EXPECTED_TASK_COUNT = 5


class LiveCanaryError(ValueError):
    pass


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise LiveCanaryError(f"cannot parse {label} {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise LiveCanaryError(f"{label} must be a JSON object")
    return value


def write_once_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError as exc:
        raise LiveCanaryError(f"refusing to overwrite immutable canary artifact: {path}") from exc
    with os.fdopen(descriptor, "wb") as handle:
        handle.write(encoded)


def write_release(path: Path, sentinel: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = f"{sentinel}-RELEASE\n".encode("utf-8")
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError:
        if path.read_bytes() != encoded:
            raise LiveCanaryError(f"release marker differs from the exact canary marker: {path}")
        return
    with os.fdopen(descriptor, "wb") as handle:
        handle.write(encoded)


def quiet(call: Callable[..., int], *args: Any, **kwargs: Any) -> None:
    with redirect_stdout(io.StringIO()):
        code = call(*args, **kwargs)
    if code != 0:
        raise LiveCanaryError(f"{call.__name__} returned {code}")


def wait_until(predicate: Callable[[], bool], seconds: float, label: str) -> None:
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline:
        if predicate():
            return
        time.sleep(0.5)
    raise LiveCanaryError(f"deadline expired while waiting for {label}")


def raw_rows(service_dir: Path, query: str) -> list[dict[str, Any]]:
    database = service_dir / scheduler.DATABASE_NAME
    if not database.is_file():
        return []
    connection = sqlite3.connect(f"file:{database}?mode=ro", uri=True)
    connection.row_factory = sqlite3.Row
    try:
        return [dict(row) for row in connection.execute(query)]
    finally:
        connection.close()


def raw_jobs(service_dir: Path) -> list[dict[str, Any]]:
    return raw_rows(
        service_dir,
        "SELECT * FROM jobs ORDER BY priority DESC, job_id",
    )


def raw_attempts(service_dir: Path) -> list[dict[str, Any]]:
    return raw_rows(
        service_dir,
        "SELECT * FROM attempts ORDER BY started_at, job_id",
    )


def raw_events(service_dir: Path) -> list[dict[str, Any]]:
    rows = raw_rows(service_dir, "SELECT * FROM events ORDER BY sequence")
    for row in rows:
        row["details"] = json.loads(row.pop("details_json"))
    return rows


def raw_unit_state(unit: str) -> str | None:
    get_unit = subprocess.run(
        [
            "busctl",
            "--user",
            "call",
            scheduler.SYSTEMD_DESTINATION,
            scheduler.SYSTEMD_MANAGER_PATH,
            scheduler.SYSTEMD_MANAGER_INTERFACE,
            "GetUnit",
            "s",
            unit,
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if get_unit.returncode != 0:
        return None
    import re

    matched = re.fullmatch(r'o\s+"([^"]+)"\s*', get_unit.stdout)
    if matched is None:
        return None
    state = subprocess.run(
        [
            "busctl",
            "--user",
            "get-property",
            scheduler.SYSTEMD_DESTINATION,
            matched.group(1),
            "org.freedesktop.systemd1.Unit",
            "ActiveState",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if state.returncode != 0:
        return None
    matched_state = re.fullmatch(r's\s+"([^"]+)"\s*', state.stdout)
    return matched_state.group(1) if matched_state is not None else None


def freeze_database(source: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        raise LiveCanaryError(f"refusing to overwrite database snapshot: {destination}")
    source_connection = sqlite3.connect(f"file:{source}?mode=ro", uri=True)
    destination_connection = sqlite3.connect(destination)
    try:
        source_connection.backup(destination_connection)
    finally:
        destination_connection.close()
        source_connection.close()


def control_from_task(task_path: Path) -> dict[str, Any]:
    task = load_json(task_path, "canary task")
    candidates = [
        scheduler.repo_path(item["path"], "canary control")
        for item in task.get("inputs", [])
        if isinstance(item, dict)
        and isinstance(item.get("path"), str)
        and "/controls/live-canary-" in item["path"]
    ]
    if len(candidates) != 1:
        raise LiveCanaryError(f"task does not bind exactly one live-canary control: {task_path}")
    control_path = candidates[0]
    expected = next(item for item in task["inputs"] if scheduler.repo_path(item["path"], "control") == control_path)
    if scheduler.sha256(control_path) != expected["sha256"]:
        raise LiveCanaryError(f"canary control drifted: {control_path}")
    control = load_json(control_path, "canary control")
    if (
        control.get("schema_version") != 1
        or control.get("protocol") != CONTROL_PROTOCOL
        or not isinstance(control.get("sentinel"), str)
        or control.get("wait_seconds") != 480
    ):
        raise LiveCanaryError(f"canary control has an unsupported contract: {control_path}")
    ready = scheduler.repo_path(str(control.get("ready_path")), "ready marker")
    release = scheduler.repo_path(str(control.get("release_path")), "release marker")
    if scheduler.repo_relative(ready) not in task["deliverables"]:
        raise LiveCanaryError("ready marker is not an exact task deliverable")
    if scheduler.repo_relative(release) not in task["ownership"]["read_paths"]:
        raise LiveCanaryError("release marker is outside the task's read ownership")
    return {
        "task_id": task["task_id"],
        "task_path": task_path,
        "control_path": control_path,
        "ready_path": ready,
        "release_path": release,
        "sentinel": control["sentinel"],
    }


def authenticate_inventory(
    service_dir: Path,
    authorization_path: Path,
    authorization_sha256: str,
    reserve_path: Path,
    reserve_sha256: str,
    approval_ref: str,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    active_path, authorization = scheduler.active_authorization(service_dir)
    if active_path != authorization_path or scheduler.sha256(active_path) != authorization_sha256:
        raise LiveCanaryError("active scheduler authorization differs from the approved receipt")
    if not authorization["dispatch_enabled"]:
        raise LiveCanaryError("approved scheduler authorization is not dispatch enabled")
    if scheduler.sha256(reserve_path) != reserve_sha256:
        raise LiveCanaryError("reserve-plan SHA-256 does not authenticate")
    reserve, _wave_path, _wave_sha = scheduler.authenticate_reserve_plan(
        reserve_path,
        reserve_sha256,
        active_path,
        approval_ref,
    )
    jobs = reserve.get("jobs", [])
    if len(jobs) != EXPECTED_TASK_COUNT:
        raise LiveCanaryError("live canary must bind exactly five reserve jobs")
    barriers: list[dict[str, Any]] = []
    for index, job in enumerate(jobs, 1):
        if (
            job.get("slot_label") != "verification"
            or job.get("occupancy_class") != "support"
            or job.get("mechanism_family") is not None
            or job.get("provider")
            != {
                "model": "gpt-5.6-sol",
                "reasoning_effort": "low",
                "web_search": "disabled",
            }
            or job.get("resume_limit") != 0
        ):
            raise LiveCanaryError(f"reserve job {index} widens the live-canary envelope")
        task_receipt = job["task_packet"]
        task_path = scheduler.repo_path(task_receipt["path"], "canary task")
        scheduler.authenticate_task(
            task_path,
            task_receipt["sha256"],
            require_outputs_absent=True,
        )
        barrier = control_from_task(task_path)
        if barrier["ready_path"].exists() or barrier["release_path"].exists():
            raise LiveCanaryError("a canary barrier identity is already spent")
        barriers.append(barrier)
    return reserve, barriers


def import_reserve(
    service_dir: Path,
    reserve_path: Path,
    reserve_sha256: str,
    approval_ref: str,
) -> None:
    quiet(
        scheduler.command_import_reserve,
        SimpleNamespace(
            service_dir=service_dir,
            reserve_plan=reserve_path,
            reserve_sha256=reserve_sha256,
            approval_ref=approval_ref,
            no_backfill=True,
        ),
    )


def start(service_dir: Path, authorization_path: Path, authorization_sha256: str) -> dict[str, Any]:
    quiet(
        scheduler.command_start,
        SimpleNamespace(
            service_dir=service_dir,
            authorization=authorization_path,
            authorization_sha256=authorization_sha256,
        ),
    )
    receipt = scheduler.daemon_receipt(service_dir)
    if receipt is None:
        raise LiveCanaryError("scheduler daemon did not publish a live receipt")
    return receipt


def stop(service_dir: Path, reason: str) -> None:
    quiet(
        scheduler.command_stop,
        SimpleNamespace(service_dir=service_dir, reason=reason),
    )


def valid_terminal_count(service_dir: Path) -> int:
    count = 0
    attempts = {row["job_id"]: row for row in raw_attempts(service_dir)}
    for job in raw_jobs(service_dir):
        if job["status"] not in scheduler.TERMINAL_PENDING:
            continue
        attempt = attempts.get(job["job_id"])
        if attempt is None:
            continue
        terminal_path = scheduler.repo_path(attempt["terminal_path"], "canary terminal")
        terminal = load_json(terminal_path, "canary terminal")
        if terminal.get("valid_result") is True:
            count += 1
    return count


def run(args: argparse.Namespace) -> Path:
    service_dir = scheduler.service_directory(args.service_dir)
    authorization_path = scheduler.repo_path(args.authorization, "approved authorization")
    reserve_path = scheduler.repo_path(args.reserve_plan, "approved reserve")
    output = scheduler.repo_path(args.output, "live-canary acceptance result")
    if output.exists():
        raise LiveCanaryError("live-canary acceptance output already exists")
    if scheduler.daemon_receipt(service_dir) is None:
        raise LiveCanaryError("the exact dispatch-enabled scheduler must be live before canary staging")
    reserve, barriers = authenticate_inventory(
        service_dir,
        authorization_path,
        args.authorization_sha256,
        reserve_path,
        args.reserve_sha256,
        args.approval_ref,
    )
    launched = False
    daemon_before: dict[str, Any] | None = None
    daemon_after: dict[str, Any] | None = None
    first_terminal_at: str | None = None
    fifth_launch_at: str | None = None
    try:
        stop(service_dir, "ticket0087-live-canary-stage-approved-reserve")
        if scheduler.daemon_receipt(service_dir) is not None:
            raise LiveCanaryError("scheduler remained live after the staging stop")
        if raw_jobs(service_dir):
            raise LiveCanaryError("production scheduler job table was nonempty before canary import")
        import_reserve(
            service_dir,
            reserve_path,
            args.reserve_sha256,
            args.approval_ref,
        )
        staged = raw_jobs(service_dir)
        if len(staged) != EXPECTED_TASK_COUNT or any(row["status"] != "queued" for row in staged):
            raise LiveCanaryError("staged reserve is not exactly five queued jobs")
        daemon_before = start(service_dir, authorization_path, args.authorization_sha256)
        launched = True
        initial = barriers[:4]
        wait_until(
            lambda: all(item["ready_path"].is_file() for item in initial),
            args.ready_timeout,
            "four real-provider ready markers",
        )
        jobs = raw_jobs(service_dir)
        active = [row for row in jobs if row["status"] in scheduler.ACTIVE_STATUSES]
        queued = [row for row in jobs if row["status"] == "queued"]
        if len(active) != 4 or len(queued) != 1:
            raise LiveCanaryError("raw database does not show four live workers and one queued backfill")
        initial_states = {row["job_id"]: raw_unit_state(str(row["unit_name"])) for row in active}
        if set(initial_states.values()) - {"active", "activating"}:
            raise LiveCanaryError(f"initial worker units are not independently active: {initial_states}")
        initial_observation = output.parent / "observations" / "initial-workers.json"
        write_once_json(
            initial_observation,
            {"observed_at": now(), "jobs": active, "unit_states": initial_states},
        )
        before_path = output.parent / "observations" / "daemon-before-restart.json"
        write_once_json(before_path, daemon_before)
        restart_started_at = now()
        stop(service_dir, "ticket0087-live-canary-restart")
        post_stop_states = {
            row["job_id"]: raw_unit_state(str(row["unit_name"])) for row in active
        }
        if set(post_stop_states.values()) - {"active", "activating"}:
            raise LiveCanaryError(
                f"scheduler restart stop killed or detached a worker: {post_stop_states}"
            )
        daemon_after = start(service_dir, authorization_path, args.authorization_sha256)
        if daemon_after.get("service_id") == daemon_before.get("service_id"):
            raise LiveCanaryError("scheduler restart reused its old service identity")
        after_path = output.parent / "observations" / "daemon-after-restart.json"
        write_once_json(after_path, daemon_after)
        if len(raw_attempts(service_dir)) != 4:
            raise LiveCanaryError("scheduler restart duplicated or lost an initial attempt")

        write_release(barriers[0]["release_path"], barriers[0]["sentinel"])
        first_job_id = next(
            row["job_id"] for row in jobs if row["task_id"] == barriers[0]["task_id"]
        )
        fifth_job_id = next(
            row["job_id"] for row in jobs if row["task_id"] == barriers[4]["task_id"]
        )

        def backfilled() -> bool:
            nonlocal first_terminal_at, fifth_launch_at
            events = raw_events(service_dir)
            first_terminal = [
                event
                for event in events
                if event["event"] == "worker-terminal-observed"
                and event["job_id"] == first_job_id
            ]
            fifth_launch = [
                event
                for event in events
                if event["event"] == "worker-launched" and event["job_id"] == fifth_job_id
            ]
            if first_terminal and fifth_launch and barriers[4]["ready_path"].is_file():
                first_terminal_at = first_terminal[0]["recorded_at"]
                fifth_launch_at = fifth_launch[0]["recorded_at"]
                return True
            return False

        wait_until(backfilled, args.backfill_timeout, "fifth real-provider backfill")
        if len(raw_attempts(service_dir)) != 5:
            raise LiveCanaryError("fifth backfill did not create exactly one attempt")
        if not scheduler.lifecycle_inbox_path(service_dir, first_job_id).is_file():
            raise LiveCanaryError("first provider terminal lacks a lifecycle-inbox item")
        for barrier in barriers[1:]:
            write_release(barrier["release_path"], barrier["sentinel"])
        wait_until(
            lambda: valid_terminal_count(service_dir) == EXPECTED_TASK_COUNT,
            args.terminal_timeout,
            "five valid real-provider terminal inboxes",
        )
        final_jobs = raw_jobs(service_dir)
        if any(
            row["status"] != "terminal_pending_reconciliation" or row["lane_id"] is not None
            for row in final_jobs
        ):
            raise LiveCanaryError("a live canary job escaped the valid terminal inbox or retained a lane")
        stop(service_dir, "ticket0087-live-canary-process-complete")
        database_snapshot = output.parent / "observations" / "live-process-terminal.sqlite3"
        freeze_database(service_dir / scheduler.DATABASE_NAME, database_snapshot)
        barrier_receipts = []
        for barrier in barriers:
            barrier_receipts.append(
                {
                    "task_id": barrier["task_id"],
                    "control": scheduler.file_receipt(barrier["control_path"]),
                    "ready": scheduler.file_receipt(barrier["ready_path"]),
                    "release": scheduler.file_receipt(barrier["release_path"]),
                    "sentinel": barrier["sentinel"],
                }
            )
        task_receipts = [job["task_packet"] for job in reserve["jobs"]]
        final = {
            "schema_version": 1,
            "protocol": PROTOCOL,
            "run_id": output.parent.name,
            "service_dir": scheduler.repo_relative(service_dir),
            "finished_at": now(),
            "approval_ref": args.approval_ref,
            "provider_calls": 5,
            "network_mode": "disabled",
            "authorization": scheduler.file_receipt(authorization_path),
            "operational_wave": reserve["operational_wave"],
            "reserve_plan": scheduler.file_receipt(reserve_path),
            "task_packets": task_receipts,
            "runner": scheduler.file_receipt(Path(__file__).resolve()),
            "checker": scheduler.file_receipt(
                ROOT / "scripts" / "check_research_scheduler_live_canary.py"
            ),
            "daemon_before_restart": scheduler.file_receipt(before_path),
            "daemon_after_restart": scheduler.file_receipt(after_path),
            "initial_workers": scheduler.file_receipt(initial_observation),
            "restart_started_at": restart_started_at,
            "first_terminal_at": first_terminal_at,
            "fifth_launch_at": fifth_launch_at,
            "database": scheduler.file_receipt(database_snapshot),
            "barriers": barrier_receipts,
            "terminal_count": 5,
            "lifecycle_inbox_count": 5,
            "result": "THREAD-LIFECYCLE-LIVE-PROCESS-PASS",
        }
        write_once_json(output, final)
        return output
    finally:
        if launched:
            for barrier in barriers:
                try:
                    write_release(barrier["release_path"], barrier["sentinel"])
                except (OSError, LiveCanaryError):
                    pass
            if scheduler.daemon_receipt(service_dir) is not None:
                try:
                    stop(service_dir, "ticket0087-live-canary-finalizer")
                except (scheduler.SchedulerError, LiveCanaryError):
                    pass


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--service-dir",
        type=Path,
        default=Path("runs/agents/research-scheduler-v2"),
    )
    parser.add_argument("--authorization", type=Path, required=True)
    parser.add_argument("--authorization-sha256", required=True)
    parser.add_argument("--reserve-plan", type=Path, required=True)
    parser.add_argument("--reserve-sha256", required=True)
    parser.add_argument("--approval-ref", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--ready-timeout", type=int, default=300)
    parser.add_argument("--backfill-timeout", type=int, default=180)
    parser.add_argument("--terminal-timeout", type=int, default=300)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        output = run(args)
    except (LiveCanaryError, scheduler.SchedulerError, OSError, sqlite3.Error) as exc:
        stop_path = scheduler.repo_path(args.output, "live-canary output").with_name(
            "live-canary-operational-stop.json"
        )
        try:
            write_once_json(
                stop_path,
                {
                    "schema_version": 1,
                    "protocol": PROTOCOL,
                    "terminal": "THREAD-LIFECYCLE-LIVE-OPERATIONAL-STOP",
                    "stopped_at": now(),
                    "reason": str(exc),
                    "retry_authorized": False,
                },
            )
        except (OSError, LiveCanaryError):
            pass
        print(f"live canary error: {exc}", file=sys.stderr)
        return 1
    print(json.dumps({"acceptance_result": scheduler.file_receipt(output)}, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
