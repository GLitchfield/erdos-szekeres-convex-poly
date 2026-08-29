#!/usr/bin/env python3
"""Tests for the serialized Wayfinder thread-lifecycle control plane."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sqlite3
import tempfile
import unittest
from unittest.mock import patch

from scripts import check_wayfinder_thread_lifecycle as lifecycle
from scripts import freeze_agent_context


class WayfinderThreadLifecycleTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.old_root = lifecycle.ROOT
        lifecycle.ROOT = self.root
        self.service = self.root / "runs" / "agents" / "scheduler-test"
        self.service.mkdir(parents=True)
        self.map_path = self.root / lifecycle.MAP_PATH
        self.portfolio_path = self.root / lifecycle.PORTFOLIO_PATH
        self.ticket_path = self.root / "docs/wayfinder/tickets/0087-test.md"
        self.write(self.map_path, "map pre\n")
        self.write(self.portfolio_path, "### FP-14 — process\nportfolio pre\n")
        self.write(self.ticket_path, "# Ticket\nticket pre\n")
        self.task_path = self.service / "task.json"
        self.dispatch_path = self.service / "dispatch.json"
        self.result_path = self.service / "result.json"
        self.terminal_path = self.service / "terminal.json"
        self.job_id = "lifecycle-test-job"
        self.write_json(
            self.task_path,
            {
                "task_id": "lifecycle-test",
                "wayfinder_ticket": "docs/wayfinder/tickets/0087-test.md",
                "ownership": {"write_paths": ["runs/agents/scheduler-test/result.json"]},
            },
        )
        self.write_json(self.dispatch_path, {"job_id": self.job_id})
        self.write_json(
            self.result_path,
            {
                "task_id": "lifecycle-test",
                "status": "completed",
                "changes": ["runs/agents/scheduler-test/result.json"],
            },
        )
        self.write_json(
            self.terminal_path,
            {
                "schema_version": 1,
                "protocol": lifecycle.SCHEDULER_PROTOCOL,
                "job_id": self.job_id,
                "attempt": 1,
                "valid_result": True,
                "finished_at": "2026-08-27T00:00:00+00:00",
                "result": lifecycle.receipt(self.result_path),
            },
        )
        self.make_database("terminal_pending_reconciliation")
        row, attempt = lifecycle.database_job(self.service, self.job_id)
        self.write_json(
            lifecycle.inbox_path(self.service, self.job_id),
            lifecycle.expected_inbox(self.service, row, attempt),
        )

    def tearDown(self) -> None:
        lifecycle.ROOT = self.old_root
        self.temp.cleanup()

    @staticmethod
    def write(path: Path, value: str) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value, encoding="utf-8")

    @staticmethod
    def write_json(path: Path, value: object) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    def make_database(self, status: str) -> None:
        connection = sqlite3.connect(self.service / "scheduler.sqlite3")
        try:
            connection.execute(
                """
                CREATE TABLE jobs(
                  job_id TEXT, task_path TEXT, task_sha256 TEXT,
                  receipt_path TEXT, current_attempt INTEGER,
                  status TEXT, terminal_at TEXT
                )
                """
            )
            connection.execute(
                """
                CREATE TABLE attempts(
                  job_id TEXT, ordinal INTEGER, terminal_path TEXT
                )
                """
            )
            connection.execute(
                "INSERT INTO jobs VALUES(?, ?, ?, ?, 1, ?, ?)",
                (
                    self.job_id,
                    lifecycle.repo_relative(self.task_path),
                    lifecycle.sha256(self.task_path),
                    lifecycle.repo_relative(self.dispatch_path),
                    status,
                    "2026-08-27T00:00:00+00:00",
                ),
            )
            connection.execute(
                "INSERT INTO attempts VALUES(?, 1, ?)",
                (self.job_id, lifecycle.repo_relative(self.terminal_path)),
            )
            connection.commit()
        finally:
            connection.close()

    @staticmethod
    def fake_check(command: list[str]) -> dict[str, object]:
        return {
            "command": " ".join(command),
            "exit_code": 0,
            "stdout_sha256": "0" * 64,
            "stderr_sha256": "0" * 64,
        }

    def neutral_adjudication(self) -> dict[str, object]:
        return {
            "disposition": "accepted",
            "net_proof_movement": "neutral",
            "evidence": "proposal",
            "damage_scope": "candidate-local",
            "difficulty_displaced": "No destination obligation became smaller.",
            "counterfactual_test": "Earlier knowledge would improve allocation only.",
            "planning_consequence": "retain",
            "ledger_edge": "NONE",
            "mathematical_negative": False,
            "affected_portfolio_entries": ["FP-14"],
            "failure_genome_anchor": None,
        }

    def prepare(self) -> tuple[Path, Path]:
        draft = self.service / "draft.json"
        pre_snapshot = self.service / "pre-snapshot.json"
        args = argparse.Namespace(
            service_dir=self.service,
            job_id=self.job_id,
            output=draft,
            pre_snapshot=pre_snapshot,
            canonical_path=[],
        )
        with patch.object(lifecycle, "current_revision", return_value="test-revision"):
            lifecycle.command_prepare(args)
        return draft, pre_snapshot

    def integrate(self, adjudication: dict[str, object]) -> Path:
        terminal_hash = lifecycle.sha256(self.terminal_path)
        exact = [
            terminal_hash,
            str(adjudication["net_proof_movement"]),
            str(adjudication["evidence"]),
            str(adjudication["damage_scope"]),
            str(adjudication["difficulty_displaced"]),
            str(adjudication["counterfactual_test"]),
            str(adjudication["planning_consequence"]),
            str(adjudication["ledger_edge"]),
        ]
        self.write(self.ticket_path, "# Ticket\n" + "\n".join(exact) + "\n")
        self.write(self.map_path, "map post\nload-bearing edge NONE\n")
        self.write(self.portfolio_path, "### FP-14 — process\nportfolio post\n")
        path = self.service / "adjudication.json"
        self.write_json(path, adjudication)
        return path

    def post_snapshot(self) -> Path:
        path = self.service / "post-snapshot.json"
        payload = freeze_agent_context.build_snapshot(
            root=self.root,
            snapshot_id="post-test",
            base_revision="test-revision",
            sources=[
                lifecycle.MAP_PATH.as_posix(),
                lifecycle.PORTFOLIO_PATH.as_posix(),
                "docs/wayfinder/tickets/0087-test.md",
            ],
        )
        freeze_agent_context.write_new(path, payload)
        return path

    def test_complete_lifecycle_seals_and_rechecks(self) -> None:
        draft, _ = self.prepare()
        adjudication = self.neutral_adjudication()
        adjudication_path = self.integrate(adjudication)
        post_snapshot = self.post_snapshot()
        output = self.service / "lifecycle.json"
        args = argparse.Namespace(
            service_dir=self.service,
            job_id=self.job_id,
            draft=draft,
            adjudication=adjudication_path,
            post_snapshot=post_snapshot,
            approval_ref="test-root-approval",
            output=output,
        )
        with patch.object(lifecycle, "run_check", side_effect=self.fake_check):
            lifecycle.command_seal(args)
            checked = lifecycle.check_receipt(
                output, self.service, self.job_id, require_pending=True
            )
        self.assertEqual(checked["disposition"], "accepted")
        self.assertEqual(
            set(checked["canonical_transition"]["changed_paths"]),
            {
                lifecycle.MAP_PATH.as_posix(),
                lifecycle.PORTFOLIO_PATH.as_posix(),
                "docs/wayfinder/tickets/0087-test.md",
            },
        )

    def test_seal_rejects_missing_portfolio_transition(self) -> None:
        draft, _ = self.prepare()
        old_portfolio = self.portfolio_path.read_text(encoding="utf-8")
        adjudication_path = self.integrate(self.neutral_adjudication())
        self.write(self.portfolio_path, old_portfolio)
        post_snapshot = self.post_snapshot()
        args = argparse.Namespace(
            service_dir=self.service,
            job_id=self.job_id,
            draft=draft,
            adjudication=adjudication_path,
            post_snapshot=post_snapshot,
            approval_ref="test-root-approval",
            output=self.service / "lifecycle.json",
        )
        with self.assertRaisesRegex(lifecycle.LifecycleError, "map, portfolio, and owning ticket"):
            lifecycle.command_seal(args)

    def test_forward_requires_compiling_theorem_and_named_edge(self) -> None:
        value = self.neutral_adjudication()
        value["net_proof_movement"] = "forward"
        terminal = lifecycle.load_json(self.terminal_path, "terminal")
        with self.assertRaisesRegex(lifecycle.LifecycleError, "forward movement"):
            lifecycle.validate_adjudication(value, terminal)

    def test_mathematical_negative_requires_failure_genome(self) -> None:
        value = self.neutral_adjudication()
        value["mathematical_negative"] = True
        terminal = lifecycle.load_json(self.terminal_path, "terminal")
        with self.assertRaisesRegex(lifecycle.LifecycleError, "failure-genome anchor"):
            lifecycle.validate_adjudication(value, terminal)

    def test_operational_stop_forbids_mathematical_fields(self) -> None:
        terminal = lifecycle.load_json(self.terminal_path, "terminal")
        terminal["valid_result"] = False
        value = self.neutral_adjudication()
        value.update(
            {
                "disposition": "operational",
                "evidence": "operational_stop",
                "damage_scope": "operational-only",
            }
        )
        lifecycle.validate_adjudication(value, terminal)
        value["ledger_edge"] = "D-HALF"
        with self.assertRaisesRegex(lifecycle.LifecycleError, "operational reconciliation"):
            lifecycle.validate_adjudication(value, terminal)


if __name__ == "__main__":
    unittest.main()
