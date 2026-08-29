#!/usr/bin/env python3
"""Run the deterministic, no-network scheduler process acceptance canary."""

from __future__ import annotations

import argparse
from contextlib import redirect_stdout
from datetime import datetime, timezone
import io
import json
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
PROTOCOL = "research-scheduler-local-acceptance-v1"
APPROVAL_REF = "user-2026-08-27-ticket0087-local-no-provider-canary"
FAKE_CODEX = ROOT / "scripts" / "scheduler_acceptance_fake_codex.py"
TICKET = ROOT / "docs" / "wayfinder" / "tickets" / "0087-enforce-thread-wayfinder-lifecycle.md"


class AcceptanceError(ValueError):
    pass


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_once(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with path.open("x", encoding="utf-8") as handle:
            json.dump(value, handle, indent=2, sort_keys=True)
            handle.write("\n")
    except FileExistsError as exc:
        raise AcceptanceError(f"refusing to overwrite acceptance artifact: {path}") from exc


def quiet(call: Callable[..., int], *args: Any, **kwargs: Any) -> None:
    with redirect_stdout(io.StringIO()):
        code = call(*args, **kwargs)
    if code != 0:
        raise AcceptanceError(f"{call.__name__} returned {code}")


def wait_until(predicate: Callable[[], bool], seconds: float, label: str) -> None:
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline:
        if predicate():
            return
        time.sleep(0.2)
    raise AcceptanceError(f"deadline expired while waiting for {label}")


def raw_jobs(service_dir: Path) -> list[dict[str, Any]]:
    database = service_dir / scheduler.DATABASE_NAME
    if not database.is_file():
        return []
    connection = sqlite3.connect(f"file:{database}?mode=ro", uri=True)
    connection.row_factory = sqlite3.Row
    try:
        return [dict(row) for row in connection.execute("SELECT * FROM jobs ORDER BY priority DESC, job_id")]
    finally:
        connection.close()


def raw_attempts(service_dir: Path) -> list[dict[str, Any]]:
    database = service_dir / scheduler.DATABASE_NAME
    connection = sqlite3.connect(f"file:{database}?mode=ro", uri=True)
    connection.row_factory = sqlite3.Row
    try:
        return [dict(row) for row in connection.execute("SELECT * FROM attempts ORDER BY started_at, job_id")]
    finally:
        connection.close()


def raw_events(service_dir: Path) -> list[dict[str, Any]]:
    database = service_dir / scheduler.DATABASE_NAME
    connection = sqlite3.connect(f"file:{database}?mode=ro", uri=True)
    connection.row_factory = sqlite3.Row
    try:
        result = []
        for row in connection.execute("SELECT * FROM events ORDER BY sequence"):
            value = dict(row)
            value["details"] = json.loads(value.pop("details_json"))
            result.append(value)
        return result
    finally:
        connection.close()


def freeze_database(source: Path, destination: Path) -> None:
    """Create an immutable, transaction-consistent process-boundary snapshot."""
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        raise AcceptanceError(f"refusing to overwrite database snapshot: {destination}")
    source_connection = sqlite3.connect(f"file:{source}?mode=ro", uri=True)
    destination_connection = sqlite3.connect(destination)
    try:
        source_connection.backup(destination_connection)
    finally:
        destination_connection.close()
        source_connection.close()


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


def configure(service_dir: Path) -> tuple[Path, str]:
    args = SimpleNamespace(
        service_dir=service_dir,
        approval_ref=APPROVAL_REF,
        dispatch_enabled=True,
        capacity=4,
        mathematical_target=4,
        reserve_floor=1,
        max_builders=1,
        max_same_family=2,
        total_cpu_cores=4,
        total_memory_gib=8,
        total_output_gib=1.0,
        poll_seconds=2,
        codex_executable=str(FAKE_CODEX),
        allowed_models=["scheduler-acceptance-fake"],
        default_model="scheduler-acceptance-fake",
        reasoning_effort="low",
    )
    quiet(scheduler.command_configure, args)
    path, _authorization = scheduler.active_authorization(service_dir)
    return path, scheduler.sha256(path)


def make_tasks(service_dir: Path) -> tuple[list[dict[str, str]], Path, Path, list[dict[str, str]]]:
    profile = ROOT / "docs" / "agents" / "profiles" / "research-lead-investigator.md"
    task_receipts: list[dict[str, str]] = []
    controls: list[dict[str, str]] = []
    for index in range(1, 6):
        task_id = f"scheduler-acceptance-worker-{index}"
        control_path = service_dir / "controls" / f"{task_id}.json"
        ready_path = service_dir / "barrier" / "ready" / task_id
        release_path = service_dir / "barrier" / "release" / task_id
        control = {
            "schema_version": 1,
            "protocol": "scheduler-acceptance-control-v1",
            "ready_path": scheduler.repo_relative(ready_path),
            "release_path": scheduler.repo_relative(release_path),
            "wait_seconds": 180,
        }
        write_once(control_path, control)
        output_dir = service_dir / "outputs" / task_id
        report_path = output_dir / "report.md"
        result_path = output_dir / "result.json"
        task = {
            "schema_version": 1,
            "run_id": service_dir.name,
            "task_id": task_id,
            "wayfinder_ticket": scheduler.repo_relative(TICKET),
            "profile": "research_lead_investigator",
            "base_revision": scheduler.current_revision(),
            "workspace_fingerprint": f"ticket0087-local-canary-{index}",
            "objective": "Wait at the deterministic local acceptance barrier, then emit one proposal-only process receipt.",
            "theorem_contract": None,
            "inputs": [scheduler.file_receipt(profile), scheduler.file_receipt(control_path)],
            "ownership": {
                "read_paths": [scheduler.repo_relative(profile), scheduler.repo_relative(control_path)],
                "write_paths": [scheduler.repo_relative(report_path), scheduler.repo_relative(result_path)],
            },
            "budget": {"wall_minutes": 3, "cpu_cores": 1, "memory_gib": 1, "output_gib": 0.01},
            "required_checks": ["Authenticate the exact acceptance control and release barrier."],
            "success": ["Return one schema-valid proposal-only local process receipt."],
            "stop": ["Stop on any input, ownership, resource, or barrier mismatch."],
            "deliverables": [scheduler.repo_relative(report_path), scheduler.repo_relative(result_path)],
            "claims_allowed": ["proposal"],
        }
        task_path = service_dir / "tasks" / f"{task_id}.json"
        write_once(task_path, task)
        scheduler.authenticate_task(task_path, scheduler.sha256(task_path), require_outputs_absent=True)
        task_receipts.append(scheduler.file_receipt(task_path))
        controls.append(
            {
                "task_id": task_id,
                "ready_path": scheduler.repo_relative(ready_path),
                "release_path": scheduler.repo_relative(release_path),
            }
        )
    wave = {
        "approval_state": "approved",
        "minimum_ready_packets": 5,
        "approved_task_packets": task_receipts,
        "thin_wave_reason": None,
    }
    wave_path = service_dir / "approved-operational-wave.json"
    write_once(wave_path, wave)
    return task_receipts, wave_path, service_dir / "approved-reserve.json", controls


def make_reserve(
    service_dir: Path,
    authorization_path: Path,
    task_receipts: list[dict[str, str]],
    wave_path: Path,
    reserve_path: Path,
) -> None:
    jobs = []
    for index, task in enumerate(task_receipts, 1):
        jobs.append(
            {
                "task_packet": task,
                "slot_label": "information-gathering",
                "occupancy_class": "mathematical",
                "mechanism_family": f"acceptance-family-{index}",
                "priority": 10 - index,
                "provider": {
                    "model": "scheduler-acceptance-fake",
                    "reasoning_effort": "low",
                    "web_search": "disabled",
                },
                "resume_limit": 0,
            }
        )
    reserve = {
        "schema_version": 1,
        "protocol": scheduler.PROTOCOL,
        "created_at": now(),
        "approval_state": "approved",
        "approval_ref": APPROVAL_REF,
        "authorization": scheduler.file_receipt(authorization_path),
        "operational_wave": scheduler.file_receipt(wave_path),
        "minimum_ready_packets": 5,
        "jobs": jobs,
    }
    write_once(reserve_path, reserve)
    quiet(
        scheduler.command_import_reserve,
        SimpleNamespace(
            service_dir=service_dir,
            reserve_plan=reserve_path,
            reserve_sha256=scheduler.sha256(reserve_path),
            approval_ref=APPROVAL_REF,
            no_backfill=True,
        ),
    )


def start(service_dir: Path, authorization_path: Path, authorization_sha: str) -> dict[str, Any]:
    quiet(
        scheduler.command_start,
        SimpleNamespace(
            service_dir=service_dir,
            authorization=authorization_path,
            authorization_sha256=authorization_sha,
        ),
    )
    receipt_value = scheduler.daemon_receipt(service_dir)
    if receipt_value is None:
        raise AcceptanceError("scheduler daemon did not remain live")
    return receipt_value


def stop(service_dir: Path, reason: str) -> None:
    quiet(
        scheduler.command_stop,
        SimpleNamespace(service_dir=service_dir, reason=reason),
    )


def release(control: dict[str, str]) -> None:
    path = ROOT / control["release_path"]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("release\n", encoding="utf-8")


def run(args: argparse.Namespace) -> Path:
    service_dir = (ROOT / "runs" / "agents" / args.run_id).resolve()
    if service_dir.exists():
        raise AcceptanceError(f"acceptance service directory already exists: {service_dir}")
    service_dir.mkdir(parents=True)
    authorization_path, authorization_sha = configure(service_dir)
    task_receipts, wave_path, reserve_path, controls = make_tasks(service_dir)
    make_reserve(service_dir, authorization_path, task_receipts, wave_path, reserve_path)
    daemon_before: dict[str, Any] | None = None
    daemon_after: dict[str, Any] | None = None
    first_terminal_at: str | None = None
    fifth_launch_at: str | None = None
    try:
        daemon_before = start(service_dir, authorization_path, authorization_sha)
        ready_first_four = [ROOT / item["ready_path"] for item in controls[:4]]
        wait_until(lambda: all(path.is_file() for path in ready_first_four), 30, "four worker barriers")
        jobs = raw_jobs(service_dir)
        if sum(row["status"] in {"dispatching", "running"} for row in jobs) != 4:
            raise AcceptanceError("raw database does not show four live worker jobs")
        if sum(row["status"] == "queued" for row in jobs) != 1:
            raise AcceptanceError("raw database does not show one queued reserve job")
        active_units = {
            row["job_id"]: raw_unit_state(str(row["unit_name"]))
            for row in jobs
            if row["status"] in {"dispatching", "running"}
        }
        if set(active_units.values()) - {"active", "activating"}:
            raise AcceptanceError(f"four worker units are not independently active: {active_units}")
        pre_restart_path = service_dir / "observations" / "pre-restart-daemon.json"
        write_once(pre_restart_path, daemon_before)
        restart_started = now()
        stop(service_dir, "ticket0087-acceptance-restart")
        for row in jobs:
            if row["status"] in {"dispatching", "running"} and raw_unit_state(str(row["unit_name"])) not in {"active", "activating"}:
                raise AcceptanceError("scheduler stop killed an independently supervised worker")
        daemon_after = start(service_dir, authorization_path, authorization_sha)
        if daemon_after["service_id"] == daemon_before["service_id"]:
            raise AcceptanceError("scheduler restart reused the old service identity")
        post_restart_path = service_dir / "observations" / "post-restart-daemon.json"
        write_once(post_restart_path, daemon_after)
        if len(raw_attempts(service_dir)) != 4:
            raise AcceptanceError("scheduler restart duplicated or lost a worker attempt")
        release(controls[0])

        def backfilled() -> bool:
            nonlocal first_terminal_at, fifth_launch_at
            events = raw_events(service_dir)
            terminal_events = [event for event in events if event["event"] == "worker-terminal-observed"]
            fifth_id = f"scheduler-acceptance-worker-5-{task_receipts[4]['sha256'][:12]}"
            fifth_events = [
                event
                for event in events
                if event["event"] == "worker-launched" and event["job_id"] == fifth_id
            ]
            if terminal_events and fifth_events and (ROOT / controls[4]["ready_path"]).is_file():
                first_terminal_at = terminal_events[0]["recorded_at"]
                fifth_launch_at = fifth_events[0]["recorded_at"]
                return True
            return False

        wait_until(backfilled, 12, "same-cycle fifth-worker backfill")
        if len(raw_attempts(service_dir)) != 5:
            raise AcceptanceError("fifth backfill did not create exactly one new attempt")
        if not lifecycle_inbox_present(service_dir, task_receipts[0]):
            raise AcceptanceError("first terminal lacks its Wayfinder lifecycle inbox")
        for control in controls[1:]:
            release(control)
        wait_until(
            lambda: sum(
                row["status"] in scheduler.TERMINAL_PENDING for row in raw_jobs(service_dir)
            )
            == 5,
            30,
            "five terminal inbox items",
        )
        final_jobs = raw_jobs(service_dir)
        if any(row["lane_id"] is not None for row in final_jobs):
            raise AcceptanceError("a terminal job still owns a process lane")
        if any(row["status"] not in scheduler.TERMINAL_PENDING for row in final_jobs):
            raise AcceptanceError("acceptance job escaped the reconciliation inbox")
        stop(service_dir, "ticket0087-local-acceptance-complete")
        database_snapshot = service_dir / "observations" / "process-terminal.sqlite3"
        freeze_database(service_dir / scheduler.DATABASE_NAME, database_snapshot)
        final = {
            "schema_version": 1,
            "protocol": PROTOCOL,
            "run_id": args.run_id,
            "finished_at": now(),
            "approval_ref": APPROVAL_REF,
            "provider_calls": 0,
            "network_mode": "disabled",
            "authorization": scheduler.file_receipt(authorization_path),
            "operational_wave": scheduler.file_receipt(wave_path),
            "reserve_plan": scheduler.file_receipt(reserve_path),
            "task_packets": task_receipts,
            "daemon_before_restart": scheduler.file_receipt(pre_restart_path),
            "daemon_after_restart": scheduler.file_receipt(post_restart_path),
            "restart_started_at": restart_started,
            "first_terminal_at": first_terminal_at,
            "fifth_launch_at": fifth_launch_at,
            "database": scheduler.file_receipt(database_snapshot),
            "terminal_count": 5,
            "lifecycle_inbox_count": 5,
            "result": "THREAD-LIFECYCLE-LOCAL-PROCESS-PASS",
        }
        output = service_dir / "acceptance-result.json"
        write_once(output, final)
        return output
    finally:
        for control in controls:
            release(control)
        if scheduler.daemon_receipt(service_dir) is not None:
            try:
                stop(service_dir, "ticket0087-local-acceptance-finalizer")
            except (scheduler.SchedulerError, AcceptanceError):
                pass


def lifecycle_inbox_present(service_dir: Path, task_receipt: dict[str, str]) -> bool:
    job_id = f"scheduler-acceptance-worker-1-{task_receipt['sha256'][:12]}"
    return scheduler.lifecycle_inbox_path(service_dir, job_id).is_file()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-id", required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        output = run(args)
    except (AcceptanceError, scheduler.SchedulerError, OSError, sqlite3.Error) as exc:
        print(f"acceptance error: {exc}", file=sys.stderr)
        return 1
    print(json.dumps({"acceptance_result": scheduler.file_receipt(output)}, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
