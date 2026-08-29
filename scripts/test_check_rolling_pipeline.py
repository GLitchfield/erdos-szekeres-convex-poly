#!/usr/bin/env python3
"""Unit tests for check_rolling_pipeline.py."""

from __future__ import annotations

from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("check_rolling_pipeline.py")
SPEC = importlib.util.spec_from_file_location("check_rolling_pipeline", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class RollingPipelineTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / "snapshot.txt").write_text("frozen\n", encoding="utf-8")
        for name in ("a", "b", "c", "d", "e"):
            self.write_json(f"{name}.json", self.task(name))

    def tearDown(self) -> None:
        self.temp.cleanup()

    def digest(self, path: str) -> str:
        return hashlib.sha256((self.root / path).read_bytes()).hexdigest()

    def write_json(self, path: str, value: object) -> None:
        (self.root / path).write_text(json.dumps(value), encoding="utf-8")

    def snapshot_entry(self, path: str) -> dict[str, str]:
        return {"path": path, "sha256": self.digest(path)}

    def task(self, name: str) -> dict:
        return {
            "schema_version": 1,
            "run_id": "test",
            "task_id": name,
            "wayfinder_ticket": None,
            "profile": "formal_proof_reviewer",
            "base_revision": "test-base",
            "workspace_fingerprint": "test-fingerprint",
            "objective": f"Test task {name}",
            "theorem_contract": None,
            "inputs": [
                {
                    "path": "snapshot.txt",
                    "sha256": hashlib.sha256(b"frozen\n").hexdigest(),
                }
            ],
            "ownership": {"read_paths": ["snapshot.txt"], "write_paths": []},
            "budget": {
                "wall_minutes": 1,
                "cpu_cores": 1,
                "memory_gib": 1,
                "output_gib": 0.01,
            },
            "required_checks": ["check"],
            "success": ["success"],
            "stop": ["stop"],
            "deliverables": ["result"],
            "claims_allowed": ["proposal"],
        }

    def result(self, task_id: str) -> dict:
        return {
            "schema_version": 1,
            "task_id": task_id,
            "status": "completed",
            "claim_level": "proposal",
            "summary": f"Completed {task_id}",
            "supports": ["bounded result"],
            "does_not_support": ["mathematical proof"],
            "changes": [],
            "checks": [],
            "evidence": [],
            "limitations": [],
            "blocked_by": None,
        }

    def board(self) -> dict:
        return {
            "schema_version": 1,
            "run_id": "test",
            "mode": "bootstrap",
            "updated_at": "2026-08-23T12:00:00-04:00",
            "capacity": 4,
            "telemetry_limitation": "orchestrator declaration; not platform telemetry",
            "snapshot": [
                self.snapshot_entry(path)
                for path in ("snapshot.txt", "a.json", "b.json", "c.json", "d.json")
            ],
            "slots": [
                {
                    "slot_id": "root",
                    "agent_name": "/root",
                    "state": "active",
                    "classification": "orchestration",
                    "mechanism_family": None,
                    "task_packet": None,
                },
                {
                    "slot_id": "worker-1",
                    "agent_name": "/root/a",
                    "state": "active",
                    "classification": "information-gathering",
                    "mechanism_family": "family-a",
                    "task_packet": "a.json",
                },
                {
                    "slot_id": "worker-2",
                    "agent_name": "/root/b",
                    "state": "active",
                    "classification": "information-gathering",
                    "mechanism_family": "family-a",
                    "task_packet": "b.json",
                },
                {
                    "slot_id": "worker-3",
                    "agent_name": "/root/c",
                    "state": "active",
                    "classification": "discovery-support",
                    "mechanism_family": None,
                    "task_packet": "c.json",
                },
            ],
            "ready_queue": [],
            "minimum_ready_packets": 0,
            "operational_wave": None,
            "vacancy_reason": None,
            "concentration_override": None,
        }

    def add_snapshot(self, board: dict, path: str) -> None:
        board["snapshot"] = [
            item for item in board["snapshot"] if item["path"] != path
        ]
        board["snapshot"].append(self.snapshot_entry(path))

    def queue_item(
        self,
        *,
        task: str = "d.json",
        approval: str = "approved",
        classification: str = "discovery-support",
        family: str | None = None,
        compatible_slots: list[str] | None = None,
    ) -> dict:
        return {
            "task_packet": task,
            "approval_state": approval,
            "classification": classification,
            "mechanism_family": family,
            "compatible_slots": compatible_slots or ["worker-3"],
        }

    def make_operational(
        self,
        board: dict,
        *,
        floor: int = 0,
        thin_reason: str | None = "approved thin-wave exception",
        approved_tasks: list[str | dict[str, str]] | None = None,
    ) -> None:
        approved = (
            ["a.json", "b.json", "c.json", "d.json"]
            if approved_tasks is None
            else approved_tasks
        )
        approved_references = [
            self.snapshot_entry(task) if isinstance(task, str) else deepcopy(task)
            for task in approved
        ]
        wave = {
            "approval_state": "approved",
            "minimum_ready_packets": floor,
            "approved_task_packets": approved_references,
            "thin_wave_reason": thin_reason if floor < 4 else None,
        }
        self.write_json("wave.json", wave)
        self.add_snapshot(board, "wave.json")
        board["mode"] = "operational"
        board["minimum_ready_packets"] = floor
        board["operational_wave"] = self.snapshot_entry("wave.json")

    def rewrite_operational_wave(self, board: dict, wave: dict) -> None:
        self.write_json("wave.json", wave)
        self.add_snapshot(board, "wave.json")
        board["operational_wave"] = self.snapshot_entry("wave.json")

    def add_transition(
        self,
        board: dict,
        slot_index: int,
        *,
        state: str,
        reconciliation_state: str = "pending",
    ) -> None:
        path = f"transition-{slot_index}.json"
        self.write_json(path, {"state": state})
        self.add_snapshot(board, path)
        board["slots"][slot_index]["state"] = state
        if state == "checkpointed":
            board["slots"][slot_index]["transition"] = {
                "kind": "checkpoint",
                "path": path,
                "sha256": self.digest(path),
                "next_action": "resume",
            }
        else:
            board["slots"][slot_index]["transition"] = {
                "kind": "result",
                "path": path,
                "sha256": self.digest(path),
                "reconciliation_state": reconciliation_state,
                "next_action": "admit" if reconciliation_state == "pending" else "reconcile",
            }

    def validate(self, board: dict, max_age_minutes: float | None = 5) -> list[str]:
        errors, _ = MODULE.validate_board(
            board,
            self.root,
            now=datetime(2026, 8, 23, 16, 1, tzinfo=timezone.utc),
            max_age_minutes=max_age_minutes,
        )
        return errors

    def assert_error(self, board: dict, fragment: str, max_age_minutes: float | None = 5) -> None:
        errors = self.validate(board, max_age_minutes)
        self.assertTrue(any(fragment in error for error in errors), errors)

    def test_valid_full_bootstrap(self) -> None:
        self.assertEqual(self.validate(self.board()), [])

    def test_valid_five_slot_bootstrap(self) -> None:
        board = self.board()
        board["capacity"] = 5
        self.add_snapshot(board, "e.json")
        board["slots"].append(
            {
                "slot_id": "worker-4",
                "agent_name": "/root/e",
                "state": "active",
                "classification": "discovery-support",
                "mechanism_family": None,
                "task_packet": "e.json",
            }
        )
        self.assertEqual(self.validate(board), [])

    def test_rejects_boolean_schema_version(self) -> None:
        board = self.board()
        board["schema_version"] = True
        self.assert_error(board, "schema_version must be 1")

    def test_detects_stale_heartbeat(self) -> None:
        board = self.board()
        board["updated_at"] = "2026-08-23T11:00:00-04:00"
        self.assert_error(board, "stale")

    def test_default_freshness_cannot_be_disabled_with_none(self) -> None:
        board = self.board()
        board["updated_at"] = "2026-08-23T11:00:00-04:00"
        self.assert_error(board, "stale", max_age_minutes=None)

    def test_rejects_nan_freshness_bound(self) -> None:
        self.assert_error(self.board(), "positive and finite", max_age_minutes=float("nan"))

    def test_rejects_positive_infinite_freshness_bound(self) -> None:
        self.assert_error(self.board(), "positive and finite", max_age_minutes=float("inf"))

    def test_rejects_negative_infinite_freshness_bound(self) -> None:
        self.assert_error(self.board(), "positive and finite", max_age_minutes=float("-inf"))

    def test_detects_snapshot_hash_drift(self) -> None:
        board = self.board()
        board["snapshot"][0]["sha256"] = "0" * 64
        self.assert_error(board, "hash drift")

    def test_requires_every_task_in_snapshot(self) -> None:
        board = self.board()
        board["snapshot"] = [item for item in board["snapshot"] if item["path"] != "a.json"]
        self.assert_error(board, "task packet must have a snapshot entry: a.json")

    def test_detects_duplicate_snapshot_path(self) -> None:
        board = self.board()
        board["snapshot"].append(deepcopy(board["snapshot"][0]))
        self.assert_error(board, "duplicate snapshot path")

    def test_canonical_task_validator_rejects_task_id_only(self) -> None:
        board = self.board()
        self.write_json("a.json", {"task_id": "a"})
        self.add_snapshot(board, "a.json")
        self.assert_error(board, "is missing keys")

    def test_task_schema_rejects_null_objective(self) -> None:
        board = self.board()
        task = self.task("a")
        task["objective"] = None
        self.write_json("a.json", task)
        self.add_snapshot(board, "a.json")
        self.assert_error(board, "objective must have type string")

    def test_task_schema_rejects_unexpected_top_level_property(self) -> None:
        board = self.board()
        task = self.task("a")
        task["unexpected"] = True
        self.write_json("a.json", task)
        self.add_snapshot(board, "a.json")
        self.assert_error(board, "unexpected schema keys: unexpected")

    def test_authenticates_task_inputs(self) -> None:
        board = self.board()
        (self.root / "snapshot.txt").write_text("drifted\n", encoding="utf-8")
        self.add_snapshot(board, "snapshot.txt")
        self.assert_error(board, "inputs[0] hash drift")

    def test_detects_duplicate_agent(self) -> None:
        board = self.board()
        board["slots"][2]["agent_name"] = board["slots"][1]["agent_name"]
        self.assert_error(board, "duplicate agent_name")

    def test_detects_duplicate_active_task(self) -> None:
        board = self.board()
        board["slots"][2]["task_packet"] = board["slots"][1]["task_packet"]
        self.assert_error(board, "duplicate task packet")

    def test_detects_duplicate_active_task_path_alias(self) -> None:
        board = self.board()
        board["slots"][2]["task_packet"] = "./a.json"
        board["snapshot"].append(
            {"path": "./a.json", "sha256": self.digest("a.json")}
        )
        self.assert_error(board, "duplicate task packet")

    def test_detects_duplicate_logical_task_at_distinct_path(self) -> None:
        board = self.board()
        self.write_json("alias.json", self.task("a"))
        self.add_snapshot(board, "alias.json")
        board["slots"][2]["task_packet"] = "alias.json"
        self.assert_error(board, "duplicate logical task test/a")

    def test_detects_hard_link_to_occupied_task(self) -> None:
        board = self.board()
        os.link(self.root / "a.json", self.root / "alias.json")
        self.add_snapshot(board, "alias.json")
        board["slots"][2]["task_packet"] = "alias.json"
        self.assert_error(board, "duplicate task file identity")

    def test_detects_active_and_queued_task_duplication(self) -> None:
        board = self.board()
        board["ready_queue"] = [self.queue_item(task="a.json")]
        self.assert_error(board, "duplicate task packet")

    def test_root_must_remain_active_while_worker_is_active(self) -> None:
        board = self.board()
        self.add_transition(board, 0, state="terminal")
        board["vacancy_reason"] = "root attempted to finish"
        self.assert_error(board, "root must remain active")

    def test_mathematical_lane_requires_family(self) -> None:
        board = self.board()
        board["slots"][1]["mechanism_family"] = None
        self.assert_error(board, "must be nonempty for a mathematical lane")

    def test_detects_family_overconcentration(self) -> None:
        board = self.board()
        board["slots"][3]["classification"] = "information-gathering"
        board["slots"][3]["mechanism_family"] = "family-a"
        self.assert_error(board, "more than two")

    def test_rejects_family_with_trailing_whitespace(self) -> None:
        board = self.board()
        board["slots"][3]["classification"] = "information-gathering"
        board["slots"][3]["mechanism_family"] = "family-a "
        self.assert_error(board, "without surrounding whitespace")

    def test_concentration_override_requires_nonblank_justification(self) -> None:
        board = self.board()
        board["slots"][3]["classification"] = "information-gathering"
        board["slots"][3]["mechanism_family"] = "family-a"
        board["concentration_override"] = {
            "families": ["family-a"],
            "justification": "   ",
        }
        self.assert_error(board, "justification must be nonblank")

    def test_valid_structured_concentration_override(self) -> None:
        board = self.board()
        board["slots"][3]["classification"] = "information-gathering"
        board["slots"][3]["mechanism_family"] = "family-a"
        board["concentration_override"] = {
            "families": ["family-a"],
            "justification": "All three lanes test distinct frozen mathematical gates.",
        }
        self.assertEqual(self.validate(board), [])

    def test_checkpoint_requires_authenticated_transition(self) -> None:
        board = self.board()
        board["slots"][3]["state"] = "checkpointed"
        board["vacancy_reason"] = "restart recovery"
        self.assert_error(board, "transition is required")

    def test_valid_checkpoint_transition(self) -> None:
        board = self.board()
        self.add_transition(board, 3, state="checkpointed")
        board["vacancy_reason"] = "restart recovery"
        self.assertEqual(self.validate(board), [])

    def test_terminal_waiting_for_reconciliation_is_not_avoidable_vacancy(self) -> None:
        board = self.board()
        self.add_transition(board, 3, state="terminal")
        board["vacancy_reason"] = "terminal awaiting admission"
        board["ready_queue"] = [self.queue_item()]
        self.assertEqual(self.validate(board), [])

    def test_admitted_transition_requires_schema_valid_result(self) -> None:
        board = self.board()
        self.add_transition(
            board, 3, state="terminal", reconciliation_state="admitted"
        )
        board["vacancy_reason"] = "terminal awaiting reconciliation"
        self.assert_error(board, "result JSON schema")

    def test_admitted_transition_result_must_match_task(self) -> None:
        board = self.board()
        self.add_transition(
            board, 3, state="terminal", reconciliation_state="admitted"
        )
        path = board["slots"][3]["transition"]["path"]
        self.write_json(path, self.result("d"))
        self.add_snapshot(board, path)
        board["slots"][3]["transition"]["sha256"] = self.digest(path)
        board["vacancy_reason"] = "terminal awaiting reconciliation"
        self.assert_error(board, "task IDs do not match")

    def test_valid_admitted_transition_result(self) -> None:
        board = self.board()
        self.add_transition(
            board, 3, state="terminal", reconciliation_state="admitted"
        )
        path = board["slots"][3]["transition"]["path"]
        self.write_json(path, self.result("c"))
        self.add_snapshot(board, path)
        board["slots"][3]["transition"]["sha256"] = self.digest(path)
        board["vacancy_reason"] = "terminal awaiting reconciliation"
        self.assertEqual(self.validate(board), [])

    def test_idle_compatible_approved_packet_is_avoidable_vacancy(self) -> None:
        board = self.board()
        board["slots"][3]["state"] = "idle"
        board["slots"][3]["task_packet"] = None
        board["vacancy_reason"] = "awaiting dispatch"
        board["ready_queue"] = [self.queue_item()]
        self.assert_error(board, "avoidable vacancy")

    def test_family_incompatible_packet_is_not_avoidable_vacancy(self) -> None:
        board = self.board()
        board["slots"][3]["state"] = "idle"
        board["slots"][3]["task_packet"] = None
        board["vacancy_reason"] = "approved packet would exceed family cap"
        board["ready_queue"] = [
            self.queue_item(
                classification="information-gathering",
                family="family-a",
            )
        ]
        self.assertEqual(self.validate(board), [])

    def test_queue_requires_compatible_slots(self) -> None:
        board = self.board()
        item = self.queue_item()
        item["compatible_slots"] = []
        board["ready_queue"] = [item]
        self.assert_error(board, "compatible_slots must be a nonempty array")

    def test_positive_ready_floor_is_enforced(self) -> None:
        board = self.board()
        board["minimum_ready_packets"] = 1
        self.assert_error(board, "ready queue under floor")

    def test_rejects_boolean_ready_floor(self) -> None:
        board = self.board()
        board["minimum_ready_packets"] = False
        self.assert_error(board, "must be a nonnegative integer")

    def test_operational_mode_requires_wave_provenance(self) -> None:
        board = self.board()
        board["mode"] = "operational"
        board["operational_wave"] = None
        self.assert_error(board, "operational_wave")

    def test_valid_operational_thin_wave(self) -> None:
        board = self.board()
        self.make_operational(board)
        self.assertEqual(self.validate(board), [])

    def test_operational_approved_only_task_requires_snapshot(self) -> None:
        board = self.board()
        self.make_operational(board)
        board["snapshot"] = [
            item for item in board["snapshot"] if item["path"] != "d.json"
        ]
        self.assert_error(
            board,
            "operational-wave-approved task must have a snapshot entry: d.json",
        )

    def test_operational_approved_only_task_cannot_drift_after_snapshot(self) -> None:
        board = self.board()
        self.write_json("e.json", self.task("e"))
        self.add_snapshot(board, "e.json")
        self.make_operational(
            board,
            approved_tasks=["a.json", "b.json", "c.json", "d.json", "e.json"],
        )
        self.assertEqual(self.validate(board), [])
        wave_digest = board["operational_wave"]["sha256"]
        self.write_json("e.json", self.task("changed-logical-id"))
        self.assertEqual(board["operational_wave"]["sha256"], wave_digest)
        self.assert_error(board, "snapshot", max_age_minutes=5)

    def test_operational_task_id_drift_rejects_after_snapshot_refresh(self) -> None:
        board = self.board()
        self.write_json("e.json", self.task("e"))
        self.add_snapshot(board, "e.json")
        self.make_operational(
            board,
            approved_tasks=["a.json", "b.json", "c.json", "d.json", "e.json"],
        )
        self.assertEqual(self.validate(board), [])
        wave_digest = board["operational_wave"]["sha256"]
        self.write_json("e.json", self.task("changed-logical-id"))
        self.add_snapshot(board, "e.json")
        self.assertEqual(board["operational_wave"]["sha256"], wave_digest)
        self.assert_error(board, "approved_task_packets[4] hash drift")

    def test_operational_same_task_id_byte_drift_rejects_after_snapshot_refresh(self) -> None:
        board = self.board()
        self.write_json("e.json", self.task("e"))
        self.add_snapshot(board, "e.json")
        self.make_operational(
            board,
            approved_tasks=["a.json", "b.json", "c.json", "d.json", "e.json"],
        )
        self.assertEqual(self.validate(board), [])
        wave_digest = board["operational_wave"]["sha256"]
        changed = self.task("e")
        changed["objective"] = "Changed bytes with the same task ID"
        self.write_json("e.json", changed)
        self.add_snapshot(board, "e.json")
        self.assertEqual(board["operational_wave"]["sha256"], wave_digest)
        self.assert_error(board, "approved_task_packets[4] hash drift")

    def test_operational_wave_digest_must_match_board_snapshot(self) -> None:
        board = self.board()
        self.make_operational(board)
        wave = json.loads((self.root / "wave.json").read_text(encoding="utf-8"))
        wave["approved_task_packets"][3]["sha256"] = "0" * 64
        self.rewrite_operational_wave(board, wave)
        self.assert_error(board, "digest must match board snapshot: d.json")

    def test_operational_wave_rejects_legacy_bare_string_entry(self) -> None:
        board = self.board()
        self.make_operational(board)
        wave = json.loads((self.root / "wave.json").read_text(encoding="utf-8"))
        wave["approved_task_packets"][0] = "a.json"
        self.rewrite_operational_wave(board, wave)
        self.assert_error(board, "must contain exactly path and sha256")

    def test_operational_wave_rejects_incomplete_hashed_reference(self) -> None:
        board = self.board()
        self.make_operational(board)
        wave = json.loads((self.root / "wave.json").read_text(encoding="utf-8"))
        wave["approved_task_packets"][0] = {"path": "a.json"}
        self.rewrite_operational_wave(board, wave)
        self.assert_error(board, "must contain exactly path and sha256")

    def test_operational_wave_rejects_extra_hashed_reference_key(self) -> None:
        board = self.board()
        self.make_operational(board)
        wave = json.loads((self.root / "wave.json").read_text(encoding="utf-8"))
        wave["approved_task_packets"][0]["task_id"] = "a"
        self.rewrite_operational_wave(board, wave)
        self.assert_error(board, "must contain exactly path and sha256")

    def test_operational_wave_rejects_malformed_task_digest(self) -> None:
        board = self.board()
        self.make_operational(board)
        wave = json.loads((self.root / "wave.json").read_text(encoding="utf-8"))
        wave["approved_task_packets"][0]["sha256"] = "g" * 64
        self.rewrite_operational_wave(board, wave)
        self.assert_error(board, "sha256 must be a SHA-256 digest")

    def test_operational_wave_rejects_canonical_task_path_alias(self) -> None:
        board = self.board()
        self.make_operational(board)
        wave = json.loads((self.root / "wave.json").read_text(encoding="utf-8"))
        wave["approved_task_packets"].append(
            {"path": "./a.json", "sha256": self.digest("a.json")}
        )
        self.rewrite_operational_wave(board, wave)
        self.assert_error(board, "unique canonical task paths: a.json")

    def test_operational_wave_rejects_task_inode_alias(self) -> None:
        board = self.board()
        os.link(self.root / "d.json", self.root / "alias.json")
        self.make_operational(board)
        wave = json.loads((self.root / "wave.json").read_text(encoding="utf-8"))
        wave["approved_task_packets"].append(self.snapshot_entry("alias.json"))
        self.rewrite_operational_wave(board, wave)
        self.assert_error(board, "name one file more than once")

    def test_operational_wave_rejects_duplicate_logical_task(self) -> None:
        board = self.board()
        self.write_json("alias.json", self.task("d"))
        self.add_snapshot(board, "alias.json")
        self.make_operational(board)
        wave = json.loads((self.root / "wave.json").read_text(encoding="utf-8"))
        wave["approved_task_packets"].append(self.snapshot_entry("alias.json"))
        self.rewrite_operational_wave(board, wave)
        self.assert_error(board, "repeat logical task test/d")

    def test_operational_floor_matches_wave_manifest(self) -> None:
        board = self.board()
        self.make_operational(board, floor=1)
        board["minimum_ready_packets"] = 0
        self.assert_error(board, "must match the operational wave manifest")

    def test_operational_wave_rejects_boolean_floor(self) -> None:
        board = self.board()
        self.make_operational(board, floor=False)
        self.assert_error(board, "operational wave minimum_ready_packets must be nonnegative")

    def test_operational_floor_below_four_requires_thin_reason(self) -> None:
        board = self.board()
        self.make_operational(board, floor=0, thin_reason=None)
        self.assert_error(board, "requires an approved thin_wave_reason")

    def test_operational_active_tasks_require_approval(self) -> None:
        board = self.board()
        self.make_operational(
            board,
            approved_tasks=["a.json", "b.json", "d.json"],
        )
        self.assert_error(board, "active task lacks operational-wave approval: c.json")

    def test_operational_terminal_task_retains_wave_approval(self) -> None:
        board = self.board()
        self.add_transition(board, 3, state="terminal")
        board["vacancy_reason"] = "terminal awaiting admission"
        self.make_operational(
            board,
            approved_tasks=["a.json", "b.json", "d.json"],
        )
        self.assert_error(board, "lifecycle task lacks operational-wave approval: c.json")

    def test_operational_approved_terminal_task_is_valid(self) -> None:
        board = self.board()
        self.add_transition(board, 3, state="terminal")
        board["vacancy_reason"] = "terminal awaiting admission"
        self.make_operational(board)
        self.assertEqual(self.validate(board), [])

    def test_operational_queue_requires_approval(self) -> None:
        board = self.board()
        board["ready_queue"] = [self.queue_item(approval="planned")]
        self.make_operational(board)
        self.assert_error(board, "only approved")


if __name__ == "__main__":
    unittest.main()
