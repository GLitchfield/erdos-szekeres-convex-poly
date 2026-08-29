#!/usr/bin/env python3
"""Regression tests for the persistent authenticated research scheduler."""

from __future__ import annotations

from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from scripts import research_scheduler as scheduler


class ResearchSchedulerTests(unittest.TestCase):
    def setUp(self) -> None:
        scheduler.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=scheduler.RUNS_ROOT)
        self.service_dir = Path(self.temp.name)

    def tearDown(self) -> None:
        self.temp.cleanup()

    def write_json(self, path: Path, value: object) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    def authorization(self, *, dispatch_enabled: bool = True, capacity: int = 4) -> dict:
        executable = str(
            Path(subprocess.check_output(["which", "codex"], text=True).strip()).resolve()
        )
        return {
            "schema_version": 1,
            "protocol": scheduler.PROTOCOL,
            "created_at": scheduler.now(),
            "approval_ref": "test-standing-authorization",
            "service_dir": scheduler.repo_relative(self.service_dir),
            "dispatch_enabled": dispatch_enabled,
            "provider": {
                "executable": executable,
                "executable_sha256": scheduler.sha256(Path(executable)),
                "version": scheduler.codex_version(executable),
                "allowed_models": ["gpt-5.6-sol"],
                "default_model": "gpt-5.6-sol",
                "default_reasoning_effort": "max",
            },
            "limits": {
                "capacity": capacity,
                "mathematical_target": capacity,
                "reserve_floor": capacity,
                "max_builders": 1,
                "max_same_family": 2,
                "total_cpu_cores": 8,
                "total_memory_gib": 32,
                "total_output_gib": 5.0,
                "poll_seconds": 5,
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
            "implementation": scheduler.implementation_receipts(),
        }

    def activate(self, authorization: dict) -> tuple[Path, str]:
        path = scheduler.authorization_path(self.service_dir, authorization)
        scheduler.write_once(path, authorization)
        scheduler.atomic_json(
            scheduler.authorization_pointer_path(self.service_dir),
            {
                "schema_version": 1,
                "protocol": scheduler.PROTOCOL,
                "rotated_at": scheduler.now(),
                "authorization": scheduler.file_receipt(path),
            },
        )
        return path, scheduler.sha256(path)

    def task_and_wave(self, name: str = "task-a") -> tuple[Path, str, Path, str, dict]:
        snapshot = self.service_dir / f"{name}-snapshot.txt"
        snapshot.write_text("frozen input\n", encoding="utf-8")
        profile = scheduler.ROOT / "docs/agents/profiles/research-lead-investigator.md"
        output_dir = self.service_dir / "outputs" / name
        result_path = output_dir / "result.json"
        report_path = output_dir / "report.md"
        task = {
            "schema_version": 1,
            "run_id": "scheduler-test",
            "task_id": name,
            "wayfinder_ticket": "docs/wayfinder/tickets/0087-enforce-thread-wayfinder-lifecycle.md",
            "profile": "research_lead_investigator",
            "base_revision": scheduler.current_revision(),
            "workspace_fingerprint": f"fingerprint-{name}",
            "objective": f"Execute bounded test task {name}.",
            "theorem_contract": None,
            "inputs": [
                scheduler.file_receipt(snapshot),
                scheduler.file_receipt(profile),
            ],
            "ownership": {
                "read_paths": [
                    scheduler.repo_relative(snapshot),
                    scheduler.repo_relative(profile),
                ],
                "write_paths": [
                    scheduler.repo_relative(report_path),
                    scheduler.repo_relative(result_path),
                ],
            },
            "budget": {
                "wall_minutes": 1,
                "cpu_cores": 1,
                "memory_gib": 1,
                "output_gib": 0.01,
            },
            "required_checks": ["Authenticate the frozen test input."],
            "success": ["Return a schema-valid bounded result."],
            "stop": ["Stop on input drift."],
            "deliverables": [
                scheduler.repo_relative(report_path),
                scheduler.repo_relative(result_path),
            ],
            "claims_allowed": ["proposal"],
        }
        task_path = self.service_dir / f"{name}-task.json"
        self.write_json(task_path, task)
        task_digest = scheduler.sha256(task_path)
        wave = {
            "approval_state": "approved",
            "minimum_ready_packets": 1,
            "approved_task_packets": [
                {"path": scheduler.repo_relative(task_path), "sha256": task_digest}
            ],
            "thin_wave_reason": "test",
        }
        wave_path = self.service_dir / f"{name}-wave.json"
        self.write_json(wave_path, wave)
        return task_path, task_digest, wave_path, scheduler.sha256(wave_path), task

    def enqueue_args(
        self,
        task_path: Path,
        task_digest: str,
        wave_path: Path,
        wave_digest: str,
        **changes,
    ) -> SimpleNamespace:
        values = {
            "service_dir": self.service_dir,
            "task_packet": task_path,
            "task_sha256": task_digest,
            "operational_wave": wave_path,
            "wave_sha256": wave_digest,
            "approval_ref": "exact-test-approval",
            "slot_label": "information-gathering",
            "occupancy_class": "mathematical",
            "mechanism_family": "test-family",
            "priority": 0,
            "model": None,
            "reasoning_effort": None,
            "web_search": "disabled",
            "resume_limit": 0,
        }
        values.update(changes)
        return SimpleNamespace(**values)

    def reserve_plan(
        self,
        names: list[str],
        authorization_path: Path,
        *,
        model: str | None = None,
    ) -> tuple[Path, str]:
        task_receipts: list[dict[str, str]] = []
        jobs: list[dict] = []
        for index, name in enumerate(names):
            task_path, task_digest, _, _, _ = self.task_and_wave(name)
            receipt = {
                "path": scheduler.repo_relative(task_path),
                "sha256": task_digest,
            }
            task_receipts.append(receipt)
            jobs.append(
                {
                    "task_packet": receipt,
                    "slot_label": "information-gathering",
                    "occupancy_class": "mathematical",
                    "mechanism_family": f"family-{index}",
                    "priority": len(names) - index,
                    "provider": {
                        "model": model,
                        "reasoning_effort": None,
                        "web_search": "disabled",
                    },
                    "resume_limit": 0,
                }
            )
        floor = len(names)
        wave = {
            "approval_state": "approved",
            "minimum_ready_packets": floor,
            "approved_task_packets": task_receipts,
            "thin_wave_reason": None if floor >= 4 else "bounded scheduler test",
        }
        wave_path = self.service_dir / "reserve-wave.json"
        self.write_json(wave_path, wave)
        plan = {
            "schema_version": 1,
            "protocol": scheduler.PROTOCOL,
            "created_at": "2026-08-26T00:00:00+00:00",
            "approval_state": "approved",
            "approval_ref": "exact-test-approval",
            "authorization": scheduler.file_receipt(authorization_path),
            "operational_wave": scheduler.file_receipt(wave_path),
            "minimum_ready_packets": floor,
            "jobs": jobs,
        }
        plan_path = self.service_dir / "reserve-plan.json"
        self.write_json(plan_path, plan)
        return plan_path, scheduler.sha256(plan_path)

    def import_args(self, plan_path: Path, plan_digest: str, **changes) -> SimpleNamespace:
        values = {
            "service_dir": self.service_dir,
            "reserve_plan": plan_path,
            "reserve_sha256": plan_digest,
            "approval_ref": "exact-test-approval",
            "no_backfill": True,
        }
        values.update(changes)
        return SimpleNamespace(**values)

    def enqueue_one(self, name: str = "task-a", **changes) -> tuple[str, dict]:
        self.activate(self.authorization())
        task_path, task_digest, wave_path, wave_digest, task = self.task_and_wave(name)
        args = self.enqueue_args(task_path, task_digest, wave_path, wave_digest, **changes)
        with redirect_stdout(io.StringIO()):
            scheduler.command_enqueue(args)
        return f"{name}-{task_digest[:12]}", task

    @staticmethod
    def result(task_id: str) -> dict:
        return {
            "schema_version": 1,
            "task_id": task_id,
            "status": "completed",
            "claim_level": "proposal",
            "summary": "Bounded test result.",
            "supports": ["scheduler test"],
            "does_not_support": ["mathematical proof"],
            "changes": [],
            "checks": [{"command": "test", "outcome": "passed"}],
            "evidence": [],
            "limitations": ["synthetic"],
            "blocked_by": None,
        }

    def lifecycle_receipt(self, job_id: str, disposition: str = "accepted") -> tuple[Path, str]:
        path = self.service_dir / f"{job_id}-lifecycle.json"
        self.write_json(
            path,
            {
                "schema_version": 1,
                "protocol": "wayfinder-thread-lifecycle-v1",
                "sealed_at": scheduler.now(),
                "approval_ref": "test-root-reconciliation",
                "inbox": {"path": "synthetic", "sha256": "0" * 64},
                "job_id": job_id,
                "disposition": disposition,
                "adjudication": {"ledger_edge": "NONE"},
                "canonical_transition": {},
                "checks": [],
            },
        )
        return path, scheduler.sha256(path)

    def test_empty_scheduler_reports_honest_undercapacity(self) -> None:
        _, _ = self.activate(self.authorization())
        scheduler.initialize_database(self.service_dir, self.authorization())
        with scheduler.database(self.service_dir) as connection:
            state = scheduler.scheduler_state(connection, self.authorization())
        self.assertEqual(state["active_count"], 0)
        self.assertEqual(state["queued_count"], 0)
        self.assertIn("approved-queue-empty", state["undercapacity_reasons"])
        self.assertIn("mathematical-occupancy-0-of-4", state["undercapacity_reasons"])

    def test_daemon_receipt_rejects_pid_reuse_identity_mismatch(self) -> None:
        identity = scheduler.process_identity(os.getpid())
        self.assertIsNotNone(identity)
        receipt = {
            "schema_version": 1,
            "protocol": scheduler.PROTOCOL,
            "service_id": "test-service",
            "supervisor_ref": f"systemd-user:{scheduler.SYSTEMD_UNIT}",
            "implementation_sha256": scheduler.sha256(Path(scheduler.__file__)),
            "authorization": {"path": "test", "sha256": "0" * 64},
            "pid": os.getpid(),
            "process_identity": identity,
            "started_at": scheduler.now(),
        }
        scheduler.atomic_json(self.service_dir / "service.pid", receipt)
        self.assertIsNotNone(scheduler.daemon_receipt(self.service_dir))
        receipt["process_identity"] = {**identity, "start_ticks": identity["start_ticks"] + 1}
        scheduler.atomic_json(self.service_dir / "service.pid", receipt)
        self.assertIsNone(scheduler.daemon_receipt(self.service_dir))

    def test_observer_authorization_refuses_enqueue(self) -> None:
        self.activate(self.authorization(dispatch_enabled=False))
        task_path, task_digest, wave_path, wave_digest, _ = self.task_and_wave()
        with self.assertRaisesRegex(scheduler.SchedulerError, "observer-only"):
            scheduler.command_enqueue(
                self.enqueue_args(task_path, task_digest, wave_path, wave_digest)
            )

    def test_authorization_rejects_unknown_capability_and_limit_widening(self) -> None:
        authorization = self.authorization()
        authorization["authority"]["unknown_future_capability"] = False
        self.activate(authorization)
        with self.assertRaisesRegex(scheduler.SchedulerError, "authority firewall"):
            scheduler.active_authorization(self.service_dir)

        widened = self.authorization()
        widened["limits"]["capacity"] = 5
        self.activate(widened)
        with self.assertRaisesRegex(scheduler.SchedulerError, "supported envelope"):
            scheduler.active_authorization(self.service_dir)

    def test_enqueue_binds_exact_task_wave_prompt_and_authority(self) -> None:
        job_id, _ = self.enqueue_one()
        with scheduler.database(self.service_dir) as connection:
            row = connection.execute("SELECT * FROM jobs WHERE job_id=?", (job_id,)).fetchone()
            self.assertIsNotNone(row)
            self.assertEqual(row["status"], "queued")
            dispatch = scheduler.load_dispatch(self.service_dir, row)
        self.assertEqual(dispatch["task_packet"]["sha256"], row["task_sha256"])
        self.assertEqual(dispatch["operational_wave"]["sha256"], row["wave_sha256"])
        self.assertEqual(dispatch["provider"]["sandbox"], "workspace-write")
        prompt = scheduler.repo_path(dispatch["prompt"]["path"], "prompt").read_text(encoding="utf-8")
        self.assertIn("do not edit the\nWayfinder", prompt)
        self.assertIn("identical raw JSON object", prompt)

    def test_enqueue_rejects_stale_wave_and_preexisting_output(self) -> None:
        self.activate(self.authorization())
        task_path, task_digest, wave_path, wave_digest, task = self.task_and_wave()
        stale_wave = json.loads(wave_path.read_text(encoding="utf-8"))
        stale_wave["approved_task_packets"] = []
        self.write_json(wave_path, stale_wave)
        wave_digest = scheduler.sha256(wave_path)
        with self.assertRaisesRegex(scheduler.SchedulerError, "operational wave"):
            scheduler.command_enqueue(
                self.enqueue_args(task_path, task_digest, wave_path, wave_digest)
            )
        stale_wave["approved_task_packets"] = [
            {"path": scheduler.repo_relative(task_path), "sha256": task_digest}
        ]
        self.write_json(wave_path, stale_wave)
        wave_digest = scheduler.sha256(wave_path)
        result_path = scheduler.repo_path(task["deliverables"][-1], "result")
        result_path.parent.mkdir(parents=True, exist_ok=True)
        result_path.write_text("{}\n", encoding="utf-8")
        with self.assertRaisesRegex(scheduler.SchedulerError, "pre-existing deliverables"):
            scheduler.command_enqueue(
                self.enqueue_args(task_path, task_digest, wave_path, wave_digest)
            )

    def test_forbidden_historical_control_never_authenticates(self) -> None:
        task_path, task_digest, _, _, task = self.task_and_wave()
        task["task_id"] = "sol-factory-refresh-014-current-state-v3"
        self.write_json(task_path, task)
        task_digest = scheduler.sha256(task_path)
        with self.assertRaisesRegex(scheduler.SchedulerError, "historical factory control"):
            scheduler.authenticate_task(
                task_path, task_digest, require_outputs_absent=True
            )

    def test_candidate_gates_family_builder_resources_and_write_overlap(self) -> None:
        authorization = self.authorization()
        base = {
            "job_id": "candidate",
            "is_builder": 0,
            "occupancy_class": "mathematical",
            "mechanism_family": "family-a",
            "cpu_cores": 1,
            "memory_gib": 1,
            "output_gib": 0.01,
            "write_paths_json": json.dumps(["runs/agents/a/result.json"]),
        }
        active = [
            {**base, "job_id": "one"},
            {**base, "job_id": "two", "write_paths_json": "[]"},
        ]
        self.assertEqual(
            scheduler.candidate_compatible(base, active, authorization)[1],
            "mechanism-family-concentration",
        )
        other_family = {**base, "mechanism_family": "family-b"}
        self.assertEqual(
            scheduler.candidate_compatible(other_family, [active[0]], authorization)[1],
            "write-set-overlap",
        )
        builder = {**base, "is_builder": 1, "mechanism_family": "family-b", "write_paths_json": "[]"}
        active_builder = [{**active[0], "is_builder": 1, "write_paths_json": "[]"}]
        self.assertEqual(
            scheduler.candidate_compatible(builder, active_builder, authorization)[1],
            "builder-limit",
        )

    def test_worker_commands_disable_subagents_and_bind_resource_caps(self) -> None:
        authorization = self.authorization()
        dispatch = {
            "provider": {
                "model": "gpt-5.6-sol",
                "reasoning_effort": "max",
                "web_search": "disabled",
                "sandbox": "workspace-write",
            }
        }
        attempt_dir = self.service_dir / "attempt"
        command = scheduler.codex_worker_command(authorization, dispatch, attempt_dir)
        joined = " ".join(command)
        self.assertIn("agents.enabled=false", command)
        self.assertIn('approval_policy="never"', command)
        self.assertIn("--sandbox workspace-write", joined)
        self.assertNotIn("danger", joined)
        row = {
            "output_gib": 0.01,
            "wall_minutes": 2,
            "memory_gib": 3,
            "cpu_cores": 2,
        }
        systemd = scheduler.worker_systemd_command(
            self.service_dir, "job", 1, row, "a" * 64
        )
        systemd_joined = " ".join(systemd)
        self.assertIn("MemoryMax=3G", systemd_joined)
        self.assertIn("CPUQuota=200%", systemd_joined)
        self.assertIn("RuntimeMaxSec=210", systemd_joined)
        self.assertIn("KillMode=control-group", systemd_joined)
        self.assertTrue(scheduler.worker_unit_name("job", 1).endswith(".service"))

    def test_stop_waits_for_authenticated_daemon_and_unit_inactivity(self) -> None:
        args = SimpleNamespace(service_dir=self.service_dir, reason="test-stop")
        completed = subprocess.CompletedProcess([], 0, stdout="", stderr="")
        with (
            patch.object(scheduler, "daemon_receipt", side_effect=[{"service_id": "old"}, None]),
            patch.object(scheduler, "unit_active", return_value=False),
            patch.object(scheduler, "systemd_manager_call", return_value=completed),
            redirect_stdout(io.StringIO()) as output,
        ):
            code = scheduler.command_stop(args)
        self.assertEqual(code, 0)
        self.assertTrue(json.loads(output.getvalue())["inactive_confirmed"])

    def test_tick_fills_four_lanes_from_four_approved_distinct_packets(self) -> None:
        authorization = self.authorization()
        authorization_path, _ = self.activate(authorization)
        for index in range(4):
            task_path, task_digest, wave_path, wave_digest, _ = self.task_and_wave(
                f"fill-{index}"
            )
            args = self.enqueue_args(
                task_path,
                task_digest,
                wave_path,
                wave_digest,
                mechanism_family=f"family-{index}",
            )
            with redirect_stdout(io.StringIO()):
                scheduler.command_enqueue(args)

        launched_commands: list[list[str]] = []

        def fake_runner(command, **_kwargs):
            launched_commands.append(command)
            return subprocess.CompletedProcess(command, 0, stdout="", stderr="")

        state = scheduler.scheduler_tick(
            self.service_dir,
            authorization_path,
            authorization,
            runner=fake_runner,
            check_units=False,
        )
        self.assertEqual(state["active_count"], 4)
        self.assertEqual(state["active_mathematical_count"], 4)
        self.assertEqual(len(state["launched_this_tick"]), 4)
        self.assertEqual(len(launched_commands), 4)
        self.assertTrue(all(lane["state"] == "running" for lane in state["lanes"]))

    def test_approved_reserve_import_is_complete_crash_idempotent_and_dispatchable(self) -> None:
        authorization = self.authorization()
        authorization_path, _ = self.activate(authorization)
        plan_path, plan_digest = self.reserve_plan(
            [f"reserve-{index}" for index in range(8)], authorization_path
        )
        first_output = io.StringIO()
        with redirect_stdout(first_output):
            scheduler.command_import_reserve(self.import_args(plan_path, plan_digest))
        first = json.loads(first_output.getvalue())
        self.assertEqual(len(first["admitted"]), 8)
        self.assertEqual(first["already_present"], [])
        with scheduler.database(self.service_dir) as connection:
            state = scheduler.scheduler_state(connection, authorization)
        self.assertEqual(state["queued_mathematical_count"], 8)
        self.assertFalse(state["occupancy_healthy"])

        second_output = io.StringIO()
        with redirect_stdout(second_output):
            scheduler.command_import_reserve(self.import_args(plan_path, plan_digest))
        second = json.loads(second_output.getvalue())
        self.assertEqual(second["admitted"], [])
        self.assertEqual(len(second["already_present"]), 8)

        launched_commands: list[list[str]] = []

        def fake_runner(command, **_kwargs):
            launched_commands.append(command)
            return subprocess.CompletedProcess(command, 0, stdout="", stderr="")

        state = scheduler.scheduler_tick(
            self.service_dir,
            authorization_path,
            authorization,
            runner=fake_runner,
            check_units=False,
        )
        self.assertEqual(state["active_mathematical_count"], 4)
        self.assertEqual(state["queued_mathematical_count"], 4)
        self.assertTrue(state["occupancy_healthy"])
        self.assertEqual(len(launched_commands), 4)

    def test_reserve_preflight_failure_admits_no_partial_batch(self) -> None:
        authorization = self.authorization()
        authorization_path, _ = self.activate(authorization)
        plan_path, _ = self.reserve_plan(
            ["preflight-good", "preflight-bad"],
            authorization_path,
        )
        plan = json.loads(plan_path.read_text(encoding="utf-8"))
        plan["jobs"][1]["provider"]["model"] = "not-authorized"
        self.write_json(plan_path, plan)
        plan_digest = scheduler.sha256(plan_path)
        with self.assertRaisesRegex(scheduler.SchedulerError, "outside the standing authorization"):
            scheduler.command_import_reserve(self.import_args(plan_path, plan_digest))
        scheduler.initialize_database(self.service_dir, authorization)
        with scheduler.database(self.service_dir) as connection:
            count = connection.execute("SELECT COUNT(*) AS count FROM jobs").fetchone()["count"]
        self.assertEqual(count, 0)

    def test_reserve_plan_must_cover_approved_wave_exactly(self) -> None:
        authorization = self.authorization()
        authorization_path, _ = self.activate(authorization)
        plan_path, _ = self.reserve_plan(
            ["coverage-a", "coverage-b"], authorization_path
        )
        plan = json.loads(plan_path.read_text(encoding="utf-8"))
        plan["jobs"].pop()
        wave_path = scheduler.repo_path(
            plan["operational_wave"]["path"], "test operational wave"
        )
        wave = json.loads(wave_path.read_text(encoding="utf-8"))
        wave["minimum_ready_packets"] = 1
        wave["thin_wave_reason"] = "coverage test"
        self.write_json(wave_path, wave)
        plan["minimum_ready_packets"] = 1
        plan["operational_wave"] = scheduler.file_receipt(wave_path)
        self.write_json(plan_path, plan)
        digest = scheduler.sha256(plan_path)
        with self.assertRaisesRegex(scheduler.SchedulerError, "cover the approved wave exactly"):
            scheduler.command_import_reserve(self.import_args(plan_path, digest))
        scheduler.initialize_database(self.service_dir, authorization)
        with scheduler.database(self.service_dir) as connection:
            count = connection.execute("SELECT COUNT(*) AS count FROM jobs").fetchone()["count"]
        self.assertEqual(count, 0)

    def test_reserve_import_rejects_nonidentical_crash_remnant(self) -> None:
        authorization = self.authorization()
        authorization_path, _ = self.activate(authorization)
        plan_path, digest = self.reserve_plan(["crash-remnant"], authorization_path)
        plan = json.loads(plan_path.read_text(encoding="utf-8"))
        task_receipt = plan["jobs"][0]["task_packet"]
        task = json.loads(
            scheduler.repo_path(task_receipt["path"], "test task").read_text(
                encoding="utf-8"
            )
        )
        job_id = f"{task['task_id']}-{task_receipt['sha256'][:12]}"
        prompt_path = scheduler.worker_prompt_path(self.service_dir, job_id)
        prompt_path.parent.mkdir(parents=True, exist_ok=True)
        prompt_path.write_text("corrupted crash remnant\n", encoding="utf-8")
        with self.assertRaisesRegex(scheduler.SchedulerError, "crash-recovery artifact differs"):
            scheduler.command_import_reserve(self.import_args(plan_path, digest))
        scheduler.initialize_database(self.service_dir, authorization)
        with scheduler.database(self.service_dir) as connection:
            count = connection.execute("SELECT COUNT(*) AS count FROM jobs").fetchone()["count"]
        self.assertEqual(count, 0)

    def test_valid_terminal_enters_inbox_and_lane_backfills_before_reconciliation(self) -> None:
        job_id, task = self.enqueue_one()
        authorization_path, authorization = scheduler.active_authorization(self.service_dir)
        next_path, next_digest, next_wave, next_wave_digest, _ = self.task_and_wave("next-task")
        with redirect_stdout(io.StringIO()):
            scheduler.command_enqueue(
                self.enqueue_args(
                    next_path,
                    next_digest,
                    next_wave,
                    next_wave_digest,
                    mechanism_family="next-family",
                )
            )
        next_job_id = f"next-task-{next_digest[:12]}"
        attempt_dir = scheduler.attempt_directory(self.service_dir, job_id, 1)
        attempt_dir.mkdir(parents=True, exist_ok=True)
        result = self.result(task["task_id"])
        result_path = scheduler.repo_path(task["deliverables"][-1], "result")
        self.write_json(result_path, result)
        last_path = attempt_dir / "last-message.json"
        self.write_json(last_path, result)
        terminal = {
            "schema_version": 1,
            "protocol": scheduler.PROTOCOL,
            "job_id": job_id,
            "attempt": 1,
            "unit": scheduler.worker_unit_name(job_id, 1),
            "terminal": "RESULT-AWAITING-ROOT-RECONCILIATION",
            "valid_result": True,
            "reason": None,
            "thread_id": "thread-test",
            "exit_code": 0,
            "finished_at": scheduler.now(),
            "result": scheduler.file_receipt(result_path),
            "last_message": scheduler.file_receipt(last_path),
            "metrics": {},
        }
        scheduler.write_once(attempt_dir / "terminal.json", terminal)
        with scheduler.database(self.service_dir) as connection:
            connection.execute(
                "UPDATE lanes SET state='running', job_id=? WHERE lane_id=1", (job_id,)
            )
            connection.execute(
                "UPDATE jobs SET status='running', lane_id=1, current_attempt=1, unit_name=?, started_at=? WHERE job_id=?",
                (scheduler.worker_unit_name(job_id, 1), scheduler.now(), job_id),
            )
            connection.execute(
                "INSERT INTO attempts(job_id, ordinal, status, unit_name, started_at, terminal_path) VALUES(?, 1, 'running', ?, ?, ?)",
                (
                    job_id,
                    scheduler.worker_unit_name(job_id, 1),
                    scheduler.now(),
                    scheduler.repo_relative(attempt_dir / "terminal.json"),
                ),
            )
        launched_commands: list[list[str]] = []

        def fake_runner(command, **_kwargs):
            launched_commands.append(command)
            return subprocess.CompletedProcess(command, 0, stdout="", stderr="")

        state = scheduler.scheduler_tick(
            self.service_dir,
            authorization_path,
            authorization,
            runner=fake_runner,
            check_units=False,
        )
        self.assertEqual(state["pending_reconciliation_count"], 1)
        self.assertEqual(state["active_count"], 1)
        self.assertEqual(state["lanes"][0]["state"], "running")
        self.assertEqual(state["lanes"][0]["job_id"], next_job_id)
        self.assertEqual(len(launched_commands), 1)
        lifecycle_path, lifecycle_digest = self.lifecycle_receipt(job_id)
        reconcile = SimpleNamespace(
            service_dir=self.service_dir,
            job_id=job_id,
            terminal_sha256=scheduler.sha256(attempt_dir / "terminal.json"),
            lifecycle_receipt=lifecycle_path,
            lifecycle_sha256=lifecycle_digest,
            no_backfill=True,
        )
        with redirect_stdout(io.StringIO()):
            scheduler.command_reconcile(
                reconcile,
                lifecycle_runner=lambda command, **_kwargs: subprocess.CompletedProcess(
                    command, 0, stdout="{}", stderr=""
                ),
            )
        with scheduler.database(self.service_dir) as connection:
            lane = connection.execute("SELECT * FROM lanes WHERE lane_id=1").fetchone()
            old_job = connection.execute("SELECT * FROM jobs WHERE job_id=?", (job_id,)).fetchone()
        self.assertEqual(lane["state"], "running")
        self.assertEqual(lane["job_id"], next_job_id)
        self.assertEqual(old_job["status"], "reconciled")

    def test_reconciliation_refuses_result_drift_after_terminal(self) -> None:
        job_id, task = self.enqueue_one()
        authorization_path, authorization = scheduler.active_authorization(self.service_dir)
        attempt_dir = scheduler.attempt_directory(self.service_dir, job_id, 1)
        attempt_dir.mkdir(parents=True, exist_ok=True)
        result = self.result(task["task_id"])
        result_path = scheduler.repo_path(task["deliverables"][-1], "result")
        self.write_json(result_path, result)
        last_path = attempt_dir / "last-message.json"
        self.write_json(last_path, result)
        terminal = {
            "schema_version": 1,
            "protocol": scheduler.PROTOCOL,
            "job_id": job_id,
            "attempt": 1,
            "unit": scheduler.worker_unit_name(job_id, 1),
            "terminal": "RESULT-AWAITING-ROOT-RECONCILIATION",
            "valid_result": True,
            "reason": None,
            "thread_id": "thread-test",
            "exit_code": 0,
            "finished_at": scheduler.now(),
            "result": scheduler.file_receipt(result_path),
            "last_message": scheduler.file_receipt(last_path),
            "metrics": {},
        }
        scheduler.write_once(attempt_dir / "terminal.json", terminal)
        with scheduler.database(self.service_dir) as connection:
            connection.execute(
                "UPDATE lanes SET state='running', job_id=? WHERE lane_id=1", (job_id,)
            )
            connection.execute(
                "UPDATE jobs SET status='running', lane_id=1, current_attempt=1, unit_name=?, started_at=? WHERE job_id=?",
                (scheduler.worker_unit_name(job_id, 1), scheduler.now(), job_id),
            )
            connection.execute(
                "INSERT INTO attempts(job_id, ordinal, status, unit_name, started_at, terminal_path) VALUES(?, 1, 'running', ?, ?, ?)",
                (
                    job_id,
                    scheduler.worker_unit_name(job_id, 1),
                    scheduler.now(),
                    scheduler.repo_relative(attempt_dir / "terminal.json"),
                ),
            )
        scheduler.scheduler_tick(
            self.service_dir,
            authorization_path,
            authorization,
            launch=False,
            check_units=False,
        )
        result["summary"] = "Drifted after terminal."
        self.write_json(result_path, result)
        lifecycle_path, lifecycle_digest = self.lifecycle_receipt(job_id)
        reconcile = SimpleNamespace(
            service_dir=self.service_dir,
            job_id=job_id,
            terminal_sha256=scheduler.sha256(attempt_dir / "terminal.json"),
            lifecycle_receipt=lifecycle_path,
            lifecycle_sha256=lifecycle_digest,
            no_backfill=True,
        )
        with self.assertRaisesRegex(scheduler.SchedulerError, "exact expected result"):
            scheduler.command_reconcile(
                reconcile,
                lifecycle_runner=lambda command, **_kwargs: subprocess.CompletedProcess(
                    command, 0, stdout="{}", stderr=""
                ),
            )

    def test_forged_valid_terminal_is_downgraded_to_operational_stop(self) -> None:
        job_id, _ = self.enqueue_one()
        authorization_path, authorization = scheduler.active_authorization(self.service_dir)
        attempt_dir = scheduler.attempt_directory(self.service_dir, job_id, 1)
        attempt_dir.mkdir(parents=True, exist_ok=True)
        forged = scheduler.synthetic_terminal(
            job_id, 1, scheduler.worker_unit_name(job_id, 1), "FAKE", "fake"
        )
        forged["valid_result"] = True
        forged["result"] = {"path": "missing.json", "sha256": "0" * 64}
        forged["last_message"] = {"path": "missing.json", "sha256": "0" * 64}
        scheduler.write_once(attempt_dir / "terminal.json", forged)
        with scheduler.database(self.service_dir) as connection:
            connection.execute(
                "UPDATE lanes SET state='running', job_id=? WHERE lane_id=1", (job_id,)
            )
            connection.execute(
                "UPDATE jobs SET status='running', lane_id=1, current_attempt=1, unit_name=?, started_at=? WHERE job_id=?",
                (scheduler.worker_unit_name(job_id, 1), scheduler.now(), job_id),
            )
            connection.execute(
                "INSERT INTO attempts(job_id, ordinal, status, unit_name, started_at, terminal_path) VALUES(?, 1, 'running', ?, ?, ?)",
                (
                    job_id,
                    scheduler.worker_unit_name(job_id, 1),
                    scheduler.now(),
                    scheduler.repo_relative(attempt_dir / "terminal.json"),
                ),
            )
        state = scheduler.scheduler_tick(
            self.service_dir,
            authorization_path,
            authorization,
            launch=False,
            check_units=False,
        )
        job = next(item for item in state["jobs"] if item["job_id"] == job_id)
        self.assertEqual(job["status"], "operational_stop_pending_reconciliation")
        self.assertEqual(state["lanes"][0]["state"], "free")
        with scheduler.database(self.service_dir) as connection:
            attempt = connection.execute(
                "SELECT status FROM attempts WHERE job_id=? AND ordinal=1", (job_id,)
            ).fetchone()
        self.assertEqual(attempt["status"], "operational-stop")

    def test_lost_worker_with_thread_id_gets_one_same_thread_resume(self) -> None:
        job_id, _ = self.enqueue_one(resume_limit=1)
        authorization_path, authorization = scheduler.active_authorization(self.service_dir)
        attempt_dir = scheduler.attempt_directory(self.service_dir, job_id, 1)
        attempt_dir.mkdir(parents=True, exist_ok=True)
        scheduler.atomic_json(
            attempt_dir / "heartbeat.json",
            {
                "schema_version": 1,
                "protocol": scheduler.PROTOCOL,
                "job_id": job_id,
                "attempt": 1,
                "heartbeat_at": scheduler.now(),
                "thread_id": "thread-resume",
            },
        )
        old = "2000-01-01T00:00:00+00:00"
        with scheduler.database(self.service_dir) as connection:
            connection.execute(
                "UPDATE lanes SET state='running', job_id=? WHERE lane_id=1", (job_id,)
            )
            connection.execute(
                "UPDATE jobs SET status='running', lane_id=1, current_attempt=1, unit_name='lost-unit', started_at=? WHERE job_id=?",
                (old, job_id),
            )
            connection.execute(
                "INSERT INTO attempts(job_id, ordinal, status, unit_name, started_at, terminal_path) VALUES(?, 1, 'running', 'lost-unit', ?, ?)",
                (job_id, old, scheduler.repo_relative(attempt_dir / "terminal.json")),
            )
        original = scheduler.unit_active
        scheduler.unit_active = lambda _unit: False
        try:
            state = scheduler.scheduler_tick(
                self.service_dir,
                authorization_path,
                authorization,
                launch=False,
            )
        finally:
            scheduler.unit_active = original
        job = next(item for item in state["jobs"] if item["job_id"] == job_id)
        self.assertEqual(job["status"], "queued")
        self.assertTrue((attempt_dir / "interruption.json").is_file())
        self.assertEqual(state["lanes"][0]["state"], "free")


if __name__ == "__main__":
    unittest.main()
