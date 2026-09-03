#!/usr/bin/env python3
"""Offline regressions for continuous-generator v3 state transitions.

Every process boundary in this module is mocked.  The tests intentionally pin
fail-closed behavior at crash/retry boundaries; several are expected to fail
until the corresponding production repairs are integrated.
"""

from __future__ import annotations

from contextlib import nullcontext
import copy
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
from typing import Callable
import unittest
from unittest import mock
import warnings

from scripts import continuous_idea_generator as generator
from scripts import test_continuous_idea_generator as base_tests


class RecordingStdin:
    def __init__(self, *, fail_write: bool = False) -> None:
        self.fail_write = fail_write
        self.payloads: list[bytes] = []
        self.closed = False

    def write(self, payload: bytes) -> int:
        if self.fail_write:
            raise BrokenPipeError("injected prompt-delivery failure")
        self.payloads.append(payload)
        return len(payload)

    def close(self) -> None:
        self.closed = True


class FakeProcess:
    def __init__(
        self,
        *,
        pid: int = 4242,
        poll_value: int | None = 0,
        fail_stdin: bool = False,
        poll_callback: Callable[[], None] | None = None,
    ) -> None:
        self.pid = pid
        self.args: list[str] = []
        self.returncode = poll_value
        self.stdin = RecordingStdin(fail_write=fail_stdin)
        self.poll_value = poll_value
        self.poll_callback = poll_callback
        self.poll_callback_ran = False

    def poll(self) -> int | None:
        if self.poll_callback is not None and not self.poll_callback_ran:
            self.poll_callback_ran = True
            self.poll_callback()
        return self.poll_value

    def __enter__(self) -> "FakeProcess":
        return self

    def __exit__(self, *_args: object) -> None:
        return None

    def communicate(
        self, input: object = None, timeout: float | None = None
    ) -> tuple[str, str]:
        del input, timeout
        self.returncode = self.poll_value
        return "", ""

    def wait(self, timeout: float | None = None) -> int | None:
        del timeout
        self.returncode = self.poll_value
        return self.poll_value


class ContinuousIdeaGeneratorV3Regressions(unittest.TestCase):
    def setUp(self) -> None:
        self.synthetic_migration = mock.patch.object(
            generator,
            "validate_accounting_migration_root",
            return_value=(
                {
                    "fixture": "synthetic-empty-migration",
                    "entries": [],
                    "path_templates": {
                        "queue": "runs/agents/unused/{campaign_id}.json"
                    },
                },
                [],
                [],
            ),
        )
        self.synthetic_migration.start()
        self.addCleanup(self.synthetic_migration.stop)
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)

    @staticmethod
    def _configured_authorization(
        service_dir: Path, *, approval_ref: str = "v3-regression-approval"
    ) -> tuple[Path, dict]:
        return base_tests.ContinuousIdeaGeneratorTests.configured_authorization(
            service_dir, approval_ref=approval_ref
        )

    @staticmethod
    def _seed_batch(
        service_dir: Path, campaign_id: str, seed_count: int = 2
    ) -> Path:
        return base_tests.ContinuousIdeaGeneratorTests.authenticated_seed_batch(
            service_dir, campaign_id, seed_count
        )

    @staticmethod
    def _claim_bundle(
        service_dir: Path,
        *,
        seed_path: Path,
        campaign_id: str,
        seed_id: str = "S01",
        suffix: str = "primary",
    ) -> SimpleNamespace:
        batch = json.loads(seed_path.read_text(encoding="utf-8"))
        selected = [
            seed for seed in batch["seeds"] if seed.get("seed_id") == seed_id
        ]
        if len(selected) != 1:
            raise AssertionError("claim fixture requires one selected seed")
        selected_seed = selected[0]
        first_test = selected_seed["first_test"]

        brief = json.loads(
            (generator.ROOT / "templates/research-development-brief.json").read_text(
                encoding="utf-8"
            )
        )
        brief_id = f"{campaign_id}-{seed_id}-{suffix}"
        brief["brief_id"] = brief_id
        brief["task_id"] = brief_id
        brief["seed"] = {
            "batch_path": generator.repo_relative(seed_path),
            "batch_sha256": generator.sha256(seed_path),
            "seed_id": seed_id,
        }
        brief["target_ref"] = selected_seed["target_ref"]
        brief["probe"]["question"] = first_test["question"]
        brief["probe"]["live_signal"] = first_test["live_signal"]
        brief["probe"]["kill_signal"] = first_test["kill_signal"]

        contract = brief["evidence_contract"]
        contract["statement"] = brief["probe"]["question"]
        contract["target_ref"] = brief["target_ref"]
        contract["model"] = copy.deepcopy(selected_seed["model"])
        contract["model_contract_id"] = generator.canonical_json_sha256(
            contract["model"]
        )
        contract["scope"]["candidate"] = {
            "campaign_id": campaign_id,
            "seed_id": seed_id,
            "seed_batch_sha256": generator.sha256(seed_path),
        }
        scope_core = {
            key: value
            for key, value in contract["scope"].items()
            if key != "scope_contract_id"
        }
        contract["scope"]["scope_contract_id"] = (
            generator.canonical_json_sha256(scope_core)
        )
        contract_core = {
            key: value for key, value in contract.items() if key != "contract_id"
        }
        contract["contract_id"] = generator.canonical_json_sha256(contract_core)

        map_path = generator.ROOT / "docs/wayfinder/map.md"
        brief["selected_context"] = [
            {
                "path": generator.repo_relative(map_path),
                "sha256": generator.sha256(map_path),
                "purpose": "Authenticate the named destination dependency.",
            }
        ]
        work_dir = service_dir / "investigations" / suffix
        brief_path = work_dir / "development-brief.json"
        evidence_path = work_dir / "evidence.md"
        receipt_path = work_dir / "development-receipt.json"
        reconciliation_path = work_dir / "root-reconciliation.json"
        feedback_source_path = work_dir / "feedback.json"
        task_path = work_dir / "task.json"
        generator.atomic_json(brief_path, brief)

        task = base_tests.ContinuousIdeaGeneratorTests.standing_first_test_task(
            service_dir,
            brief=brief,
            brief_path=brief_path,
            seed_path=seed_path,
            context_paths=[map_path],
            evidence_path=evidence_path,
        )
        generator.atomic_json(task_path, task)
        args = SimpleNamespace(
            service_dir=service_dir,
            campaign_id=campaign_id,
            seed_id=seed_id,
            seed_batch_sha256=generator.sha256(seed_path),
            development_brief=brief_path,
            development_brief_sha256=generator.sha256(brief_path),
            task_packet=task_path,
            task_packet_sha256=generator.sha256(task_path),
        )
        return SimpleNamespace(
            args=args,
            batch=batch,
            selected_seed=selected_seed,
            brief=brief,
            brief_path=brief_path,
            task=task,
            task_path=task_path,
            contract=contract,
            evidence_path=evidence_path,
            receipt_path=receipt_path,
            reconciliation_path=reconciliation_path,
            feedback_source_path=feedback_source_path,
            claim_path=generator.seed_claim_path(
                service_dir, campaign_id, seed_id
            ),
        )

    @staticmethod
    def _write_neutral_feedback(
        service_dir: Path,
        *,
        seed_path: Path,
        campaign_id: str,
        seed_id: str,
        bundle: SimpleNamespace,
    ) -> SimpleNamespace:
        bundle.evidence_path.write_text(
            '{"terminal":"NO_DISCRIMINATING_SIGNAL"}\n', encoding="utf-8"
        )
        receipt = json.loads(
            (generator.ROOT / "templates/research-development-receipt.json").read_text(
                encoding="utf-8"
            )
        )
        receipt["brief_id"] = bundle.brief["brief_id"]
        receipt["brief_sha256"] = generator.sha256(bundle.brief_path)
        event = receipt["evidence_events"][0]
        event["artifact"] = generator.file_receipt(bundle.evidence_path)
        event["binding"] = {
            "primary_contract_id": bundle.contract["contract_id"],
            "subject": "primary_claim",
            "subject_contract_id": bundle.contract["contract_id"],
            "model_contract_id": bundle.contract["model_contract_id"],
            "scope_contract_id": bundle.contract["scope"]["scope_contract_id"],
            "polarity": "observes",
            "damage_scope_reached": "candidate-local",
        }
        event_core = {
            key: value
            for key, value in event.items()
            if key not in {"event_id", "verification_receipt"}
        }
        event["event_id"] = generator.canonical_json_sha256(event_core)
        envelope_path, output_bytes = (
            base_tests.ContinuousIdeaGeneratorTests.write_execution_envelope(
                brief=bundle.brief,
                brief_path=bundle.brief_path,
                task=bundle.task,
                task_path=bundle.task_path,
                claim_path=bundle.claim_path,
            )
        )
        receipt["execution_envelope"] = generator.file_receipt(envelope_path)
        receipt["resource_use"].update(
            {
                "wall_minutes": 1,
                "active_minutes": 1,
                "cpu_seconds": 1,
                "peak_memory_mib": 1,
                "artifact_bytes": output_bytes,
                "source_requests": 0,
            }
        )
        generator.atomic_json(bundle.receipt_path, receipt)

        evidence = {
            "level": "proposal",
            "event_ids": [event["event_id"]],
            "contract_id": bundle.contract["contract_id"],
            "model_contract_id": bundle.contract["model_contract_id"],
            "scope_contract_id": bundle.contract["scope"]["scope_contract_id"],
            "damage_scope": "candidate-local",
        }
        reconciled_at = datetime.now(timezone.utc).isoformat()
        not_established = {
            "status": "not-established",
            "text": None,
            "subject_contract_id": None,
            "evidence_event_ids": [],
            "learning_claim_id": None,
        }
        feedback = {
            "schema_version": 3,
            "feedback_id": f"{campaign_id}:{seed_id}",
            "seed": {
                "registry_id": f"continuous:{campaign_id}:{seed_id}",
                "campaign_id": campaign_id,
                "seed_id": seed_id,
                "seed_batch": generator.file_receipt(seed_path),
            },
            "investigation": {
                "brief_id": bundle.brief["brief_id"],
                "brief_sha256": generator.sha256(bundle.brief_path),
                "development_receipt": generator.file_receipt(bundle.receipt_path),
                "terminal": "NO_DISCRIMINATING_SIGNAL",
            },
            "evidence": evidence,
            "proof_distance": {
                "net_proof_movement": "neutral",
                "forward_reduction_receipt": None,
                "difficulty_displaced": "The original producer remains open.",
                "demonstrably_smaller": False,
                "counterfactual_test": "Prior knowledge would not reduce the proof.",
                "planning_consequence": "expire",
            },
            "learned": {
                "failing_feature": copy.deepcopy(not_established),
                "strongest_supported_statement": copy.deepcopy(not_established),
                "surviving_structure": copy.deepcopy(not_established),
                "representation_blindness": copy.deepcopy(not_established),
                "anti_duplication_warning": copy.deepcopy(not_established),
            },
            "next_discriminating_test": {
                "status": "not-established",
                "question": None,
                "changed_mathematical_information": None,
                "ceiling_minutes": None,
                "stop_signal": None,
            },
            "canonical_failure_memory_ref": None,
            "claim_candidate": None,
            "queue_disposition": "investigated-do-not-reselect",
        }
        feedback_core_sha256 = generator.canonical_json_sha256(feedback)
        generator.atomic_json(
            bundle.reconciliation_path,
            {
                "schema_version": 2,
                "protocol": "research-root-reconciliation-v2",
                "feedback_id": f"{campaign_id}:{seed_id}",
                "reconciled_at": reconciled_at,
                "seed_claim": generator.file_receipt(bundle.claim_path),
                "development_receipt": generator.file_receipt(bundle.receipt_path),
                "admitted_feedback_core_sha256": feedback_core_sha256,
                "standing_first_test": copy.deepcopy(bundle.brief["authority"]),
                "decision": "admit-immutable-feedback",
            },
        )
        feedback["root_admission"] = {
            "reconciled_at": reconciled_at,
            "admitted_feedback_core_sha256": feedback_core_sha256,
            "reconciliation": generator.file_receipt(bundle.reconciliation_path),
        }
        generator.atomic_json(bundle.feedback_source_path, feedback)
        return SimpleNamespace(
            args=SimpleNamespace(
                service_dir=service_dir,
                campaign_id=campaign_id,
                seed_id=seed_id,
                seed_batch_sha256=generator.sha256(seed_path),
                feedback=bundle.feedback_source_path,
                feedback_sha256=generator.sha256(bundle.feedback_source_path),
            ),
            feedback=feedback,
        )

    @staticmethod
    def _freeze_and_queue(
        service_dir: Path,
        authorization_path: Path,
        authorization: dict,
        *,
        campaign_id: str,
        requested_seed_count: int = 1,
    ) -> tuple[Path, Path, dict]:
        frozen = generator.freeze_campaign_packet(
            service_dir,
            campaign_id,
            "context_rich",
            authorization_path,
            authorization,
            requested_seed_count,
        )
        packet_path = generator.ROOT / frozen["packet"]["path"]
        packet = generator.verify_packet(packet_path)
        generator.queue_packet(
            service_dir,
            packet_path,
            generator.sha256(packet_path),
            packet["prompt"]["sha256"],
            packet["task"]["sha256"],
            authorization["approval_ref"],
        )
        return (
            service_dir / "queue" / f"{campaign_id}.json",
            packet_path,
            packet,
        )

    @staticmethod
    def _process_identity(pid: int = 4242) -> dict:
        return {
            "pid": pid,
            "boot_id": "offline-test-boot",
            "start_ticks": 12345,
            "process_group_id": pid,
        }

    def _create_closed_v3_seed_batch(
        self,
        service_dir: Path,
        *,
        campaign_id: str,
        seed_count: int = 1,
        freeze_launch_reserve: bool = False,
    ) -> tuple[Path, dict]:
        if generator.active_authorization_pointer_path(service_dir).is_file():
            authorization_path, authorization = (
                generator.active_standing_authorization(service_dir)
            )
        else:
            authorization_path, authorization = self._configured_authorization(
                service_dir
            )
        requested_seed_count = max(1, seed_count)
        queue_path, packet_path, packet = self._freeze_and_queue(
            service_dir,
            authorization_path,
            authorization,
            campaign_id=campaign_id,
            requested_seed_count=requested_seed_count,
        )
        response = json.loads(
            (generator.ROOT / "templates/research-seed-batch.json").read_text(
                encoding="utf-8"
            )
        )
        response["campaign_id"] = campaign_id
        response["generation_mode"] = packet["generation_mode"]
        response["requested_seed_count"] = requested_seed_count
        response["snapshot"] = packet["snapshot"]
        response["terminal"] = "SEED-BATCH-COMPLETE"
        seed_template = response["seeds"][0]
        response["seeds"] = []
        for ordinal in range(seed_count):
            seed = copy.deepcopy(seed_template)
            seed["seed_id"] = f"S{ordinal + 1:02d}"
            seed["title"] = f"V3 regression seed {ordinal + 1} for {campaign_id}"
            seed["mechanism"]["operation"] += (
                f" V3 regression {campaign_id}, variant {ordinal + 1}."
            )
            response["seeds"].append(seed)
        response["generation_metrics"]["private_seed_count"] = seed_count
        batch_dir = packet_path.parent
        process = FakeProcess(
            poll_value=0,
            poll_callback=lambda: generator.atomic_json(
                batch_dir / "raw-response.json", response
            ),
        )
        identity = self._process_identity(process.pid)
        reserve_context = (
            mock.patch.object(
                generator,
                "active_reserve",
                return_value=generator.active_reserve(service_dir),
            )
            if freeze_launch_reserve
            else nullcontext()
        )
        with (
            mock.patch.object(generator.subprocess, "Popen", return_value=process),
            mock.patch.object(
                generator,
                "codex_version",
                return_value=authorization["provider"]["cli_version"],
            ),
            mock.patch.object(generator, "process_identity", return_value=identity),
            mock.patch.object(generator, "set_affinity"),
            reserve_context,
        ):
            result = generator.run_provider(
                service_dir, queue_path, {}, {"stop": False}
            )
        self.assertEqual(result["terminal"], "SEED-BATCH-COMPLETE")
        seed_path = batch_dir / "seed-batch.json"
        batch = json.loads(seed_path.read_text(encoding="utf-8"))
        generator.validate_v3_result_receipt(
            service_dir, batch_dir / "result-receipt.json", seed_path, batch
        )
        accounting = generator.validate_accounting_chain(
            service_dir, authorization
        )
        closed = accounting["closed_v3_by_campaign"][campaign_id]
        self.assertEqual(
            closed["result_receipt"],
            generator.file_receipt(batch_dir / "result-receipt.json"),
        )
        self.assertEqual(
            closed["seed_batch_receipt"], generator.file_receipt(seed_path)
        )
        self.assertEqual(generator.pending_queue(service_dir), [])
        self.assertEqual(
            [
                (item["seed_id"], item["state"])
                for item in generator.seed_inventory(service_dir)
                if item["campaign_id"] == campaign_id
            ],
            [(f"S{ordinal + 1:02d}", "ready") for ordinal in range(seed_count)],
        )
        return seed_path, batch

    def _restore_exact_outcome_tail_crash(
        self,
        service_dir: Path,
        *,
        campaign_id: str,
    ) -> SimpleNamespace:
        seed_path, batch = self._create_closed_v3_seed_batch(
            service_dir,
            campaign_id=campaign_id,
        )
        authorization_path, authorization = (
            generator.active_standing_authorization(service_dir)
        )
        event_paths = sorted(
            generator.accounting_event_directory(service_dir).glob("*.json")
        )
        outcome_path = event_paths[-1]
        outcome = json.loads(outcome_path.read_text(encoding="utf-8"))
        self.assertEqual(outcome.get("event_type"), "outcome")
        attempt_path = generator.authenticate_receipt(
            outcome.get("attempt_event"), "fixture unresolved attempt"
        )
        attempt = json.loads(attempt_path.read_text(encoding="utf-8"))
        self.assertEqual(attempt.get("event_type"), "attempt")
        head_path = generator.accounting_head_path(service_dir)
        generator.atomic_json(
            head_path,
            {
                "schema_version": 1,
                "protocol": generator.INVOCATION_LEDGER_PROTOCOL,
                "baseline": authorization["accounting_baseline"],
                "event_count": attempt["event_index"],
                "charged_count": attempt["charged_ordinal"],
                "last_event": generator.file_receipt(attempt_path),
                "unresolved_attempt_ordinal": attempt["charged_ordinal"],
                "updated_at": generator.now(),
            },
        )
        return SimpleNamespace(
            service_dir=service_dir,
            campaign_id=campaign_id,
            authorization_path=authorization_path,
            authorization=authorization,
            seed_path=seed_path,
            batch=batch,
            result_path=seed_path.parent / "result-receipt.json",
            attempt_path=attempt_path,
            outcome_path=outcome_path,
            head_path=head_path,
        )

    @staticmethod
    def _root_import_bundle(
        service_dir: Path,
        source_run: Path,
        *,
        authorization_path: Path,
        authorization: dict,
        campaign_id: str,
    ) -> SimpleNamespace:
        base_tests.ContinuousIdeaGeneratorTests.build_authenticated_snapshot(
            service_dir,
            source_run / "snapshot",
            campaign_id=campaign_id,
            purpose="root_fallback",
            authorization_path=authorization_path,
            authorization=authorization,
        )
        snapshot_path = source_run / "snapshot" / "packet-summary.json"
        batch = json.loads(
            (generator.ROOT / "templates/research-seed-batch.json").read_text(
                encoding="utf-8"
            )
        )
        batch["campaign_id"] = campaign_id
        batch["requested_seed_count"] = 1
        batch["terminal"] = "SEED-BATCH-COMPLETE"
        batch["snapshot"] = generator.file_receipt(snapshot_path)
        batch["seeds"][0]["mechanism"]["operation"] += f" Fixture {campaign_id}."
        source_path = source_run / "seed-batch.json"
        generator.atomic_json(source_path, batch)
        screen_path = base_tests.ContinuousIdeaGeneratorTests.root_semantic_screen(
            service_dir,
            batch_path=source_path,
            authorization_path=authorization_path,
            approval_ref=authorization["approval_ref"],
        )
        args = SimpleNamespace(
            service_dir=service_dir,
            seed_batch=source_path,
            seed_batch_sha256=generator.sha256(source_path),
            semantic_screen=screen_path,
            semantic_screen_sha256=generator.sha256(screen_path),
            approval_ref=authorization["approval_ref"],
        )
        return SimpleNamespace(
            args=args,
            source_path=source_path,
            screen_path=screen_path,
            snapshot_path=snapshot_path,
            batch=batch,
        )

    def test_validated_learning_export_is_required_and_rejects_fabricated_state(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            run_root = Path(raw)
            service_dir = run_root / "service"
            authorization_path, authorization = self._configured_authorization(
                service_dir
            )
            snapshot_dir = run_root / "source" / "snapshot"
            with self.assertRaisesRegex(
                ValueError, r"require(?:s)? a validated learning export"
            ):
                generator.build_sol_idea_packet.build_packet(
                    snapshot_dir,
                    1024,
                    service_dir,
                    campaign_id="validated-export-required",
                    purpose="root_fallback",
                )

            accounting = generator.validate_accounting_chain(
                service_dir, authorization
            )
            export_path = snapshot_dir / "validated-learning-export.json"
            generator.materialize_validated_learning_export(
                service_dir,
                export_path,
                authorization_path=authorization_path,
                authorization=authorization,
                accounting=accounting,
                excluded_campaign_id="validated-export-required",
            )
            generator.build_sol_idea_packet.build_packet(
                snapshot_dir,
                1024,
                service_dir,
                campaign_id="validated-export-required",
                purpose="root_fallback",
                validated_learning_export=export_path,
            )
            self.assertTrue((snapshot_dir / "packet-summary.json").is_file())

            campaign_id = "fabricated-learning-state"
            seed_path, _batch = self._create_closed_v3_seed_batch(
                service_dir, campaign_id=campaign_id
            )
            accounting = generator.validate_accounting_chain(
                service_dir, authorization
            )
            claim_path = generator.seed_claim_path(service_dir, campaign_id, "S01")
            generator.atomic_json(claim_path, {"fabricated": True})
            with self.assertRaises(
                (generator.ServiceError, generator.campaign.CampaignError)
            ):
                generator.materialize_validated_learning_export(
                    service_dir,
                    run_root / "forged-claim-export.json",
                    authorization_path=authorization_path,
                    authorization=authorization,
                    accounting=accounting,
                    excluded_campaign_id="next-campaign",
                )
            claim_path.rename(claim_path.with_suffix(".fabricated"))

            bundle = self._claim_bundle(
                service_dir,
                seed_path=seed_path,
                campaign_id=campaign_id,
            )
            with mock.patch("builtins.print"):
                generator.command_claim(bundle.args)
            feedback_path = generator.seed_feedback_path(
                service_dir, campaign_id, "S01"
            )
            generator.atomic_json(feedback_path, {"fabricated": True})
            with self.assertRaises(
                (generator.ServiceError, generator.campaign.CampaignError)
            ):
                generator.materialize_validated_learning_export(
                    service_dir,
                    run_root / "forged-feedback-export.json",
                    authorization_path=authorization_path,
                    authorization=authorization,
                    accounting=accounting,
                    excluded_campaign_id="next-campaign",
                )

    def test_snapshot_current_replay_and_historical_attestation_are_separate(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            run_root = Path(raw)
            service_dir = run_root / "service"
            authorization_path, authorization = self._configured_authorization(
                service_dir
            )
            campaign_id = "snapshot-temporal-modes"
            snapshot_dir = run_root / "source" / "snapshot"
            base_tests.ContinuousIdeaGeneratorTests.build_authenticated_snapshot(
                service_dir,
                snapshot_dir,
                campaign_id=campaign_id,
                purpose="root_fallback",
                authorization_path=authorization_path,
                authorization=authorization,
            )
            snapshot_path = snapshot_dir / "packet-summary.json"
            generator.validate_snapshot_build_receipt(
                snapshot_path,
                service_dir=service_dir,
                campaign_id=campaign_id,
                purpose="root_fallback",
                mode="current",
            )
            admission_path = generator.admit_snapshot_build(
                snapshot_path,
                service_dir=service_dir,
                campaign_id=campaign_id,
                purpose="root_fallback",
            )
            with (
                mock.patch.object(
                    generator,
                    "materialize_validated_learning_export",
                    side_effect=AssertionError("historical mode consulted live state"),
                ),
                mock.patch.object(
                    generator.build_sol_idea_packet,
                    "build_packet",
                    side_effect=AssertionError("historical mode reran the builder"),
                ),
            ):
                generator.validate_snapshot_admission(
                    admission_path,
                    snapshot_path=snapshot_path,
                    service_dir=service_dir,
                    campaign_id=campaign_id,
                    purpose="root_fallback",
                )

    def test_verify_packet_rejects_relocated_canonical_artifact(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization_path, authorization = self._configured_authorization(
                service_dir
            )
            _queue_path, packet_path, packet = self._freeze_and_queue(
                service_dir,
                authorization_path,
                authorization,
                campaign_id="packet-artifact-relocation",
            )
            snapshot_path = generator.authenticate_receipt(
                packet["snapshot"], "fixture packet snapshot"
            )
            relocated_path = packet_path.parent / "relocated-packet-summary.json"
            relocated_path.write_bytes(snapshot_path.read_bytes())
            packet["snapshot"] = generator.file_receipt(relocated_path)
            generator.atomic_json(packet_path, packet)
            with self.assertRaisesRegex(
                generator.ServiceError,
                "packet snapshot is outside its canonical batch layout",
            ):
                generator.verify_packet(packet_path, mode="historical")

    def test_post_cold_replay_state_drift_prevents_snapshot_admission(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            run_root = Path(raw)
            service_dir = run_root / "service"
            authorization_path, authorization = self._configured_authorization(
                service_dir
            )
            state_seed_path, _state_batch = self._create_closed_v3_seed_batch(
                service_dir,
                campaign_id="state-before-replay",
            )
            state_claim = self._claim_bundle(
                service_dir,
                seed_path=state_seed_path,
                campaign_id="state-before-replay",
            )
            campaign_id = "post-replay-state-drift"
            snapshot_dir = run_root / "source" / "snapshot"
            base_tests.ContinuousIdeaGeneratorTests.build_authenticated_snapshot(
                service_dir,
                snapshot_dir,
                campaign_id=campaign_id,
                purpose="root_fallback",
                authorization_path=authorization_path,
                authorization=authorization,
            )
            snapshot_path = snapshot_dir / "packet-summary.json"
            real_validate = generator.validate_snapshot_build_receipt
            mutated = False

            def validate_then_mutate(*args, **kwargs):
                nonlocal mutated
                result = real_validate(*args, **kwargs)
                if kwargs.get("mode", "current") == "current" and not mutated:
                    with mock.patch("builtins.print"):
                        generator.command_claim(state_claim.args)
                    mutated = True
                return result

            with mock.patch.object(
                generator,
                "validate_snapshot_build_receipt",
                side_effect=validate_then_mutate,
            ):
                with self.assertRaisesRegex(
                    generator.ServiceError, "snapshot state changed after cold replay"
                ):
                    generator.admit_snapshot_build(
                        snapshot_path,
                        service_dir=service_dir,
                        campaign_id=campaign_id,
                        purpose="root_fallback",
                    )
            self.assertTrue(mutated)
            self.assertFalse(generator.snapshot_admission_path(snapshot_path).exists())

    def test_post_cold_replay_component_drift_prevents_snapshot_admission(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            run_root = Path(raw)
            service_dir = run_root / "service"
            authorization_path, authorization = self._configured_authorization(
                service_dir
            )
            campaign_id = "post-replay-component-drift"
            snapshot_dir = run_root / "source" / "snapshot"
            base_tests.ContinuousIdeaGeneratorTests.build_authenticated_snapshot(
                service_dir,
                snapshot_dir,
                campaign_id=campaign_id,
                purpose="root_fallback",
                authorization_path=authorization_path,
                authorization=authorization,
            )
            snapshot_path = snapshot_dir / "packet-summary.json"
            real_validate = generator.validate_snapshot_build_receipt
            real_sha256 = generator.sha256
            builder_path = Path(generator.build_sol_idea_packet.__file__).resolve()
            replay_finished = False

            def validate_then_drift(*args, **kwargs):
                nonlocal replay_finished
                result = real_validate(*args, **kwargs)
                replay_finished = True
                return result

            def component_drift(path: Path) -> str:
                if replay_finished and Path(path).resolve() == builder_path:
                    return "d" * 64
                return real_sha256(Path(path))

            with (
                mock.patch.object(
                    generator,
                    "validate_snapshot_build_receipt",
                    side_effect=validate_then_drift,
                ),
                mock.patch.object(generator, "sha256", side_effect=component_drift),
            ):
                with self.assertRaisesRegex(
                    generator.ServiceError,
                    r"standing supporting implementation .* hash mismatch",
                ):
                    generator.admit_snapshot_build(
                        snapshot_path,
                        service_dir=service_dir,
                        campaign_id=campaign_id,
                        purpose="root_fallback",
                    )
            self.assertTrue(replay_finished)
            self.assertFalse(generator.snapshot_admission_path(snapshot_path).exists())

    def test_root_import_requires_one_source_run_for_snapshot_and_screen(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            run_root = Path(raw)
            service_dir = run_root / "service"
            authorization_path, authorization = self._configured_authorization(
                service_dir
            )
            bundle = self._root_import_bundle(
                service_dir,
                run_root / "root-source",
                authorization_path=authorization_path,
                authorization=authorization,
                campaign_id="20260831-root-seeds-containment",
            )
            outside_screen = run_root / "other-source" / "semantic-screen.json"
            generator.atomic_json(
                outside_screen,
                json.loads(bundle.screen_path.read_text(encoding="utf-8")),
            )
            args = copy.copy(bundle.args)
            args.semantic_screen = outside_screen
            args.semantic_screen_sha256 = generator.sha256(outside_screen)
            with self.assertRaisesRegex(
                generator.ServiceError,
                "root semantic screen must remain inside its source run",
            ):
                generator.command_import_root_batch(args)
            self.assertFalse(
                (service_dir / "batches" / bundle.batch["campaign_id"]).exists()
            )

    def test_root_import_postwrite_drift_leaves_no_visibility_commit(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            run_root = Path(raw)
            service_dir = run_root / "service"
            authorization_path, authorization = self._configured_authorization(
                service_dir
            )
            campaign_id = "20260831-root-seeds-postwrite-drift"
            bundle = self._root_import_bundle(
                service_dir,
                run_root / "root-source",
                authorization_path=authorization_path,
                authorization=authorization,
                campaign_id=campaign_id,
            )
            real_currency = generator.snapshot_currency
            calls = 0

            def drift_on_postwrite(*args, **kwargs):
                nonlocal calls
                calls += 1
                if calls == 3:
                    return False, ["workspace_manifest_changed"]
                return real_currency(*args, **kwargs)

            with mock.patch.object(
                generator, "snapshot_currency", side_effect=drift_on_postwrite
            ):
                with self.assertRaisesRegex(
                    generator.ServiceError, "snapshot changed during commit"
                ):
                    generator.command_import_root_batch(bundle.args)
            self.assertEqual(calls, 3)
            batch_dir = service_dir / "batches" / campaign_id
            self.assertTrue((batch_dir / "seed-batch.json").is_file())
            self.assertFalse((batch_dir / "result-receipt.json").exists())
            status = generator.service_status(service_dir)
            self.assertIsNotNone(status["inventory_error"])
            self.assertEqual(status["seed_inventory_counts"]["ready"], 0)

    def test_historical_provider_result_rejects_fabricated_transform(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            campaign_id = "fabricated-provider-transform"
            seed_path, batch = self._create_closed_v3_seed_batch(
                service_dir, campaign_id=campaign_id
            )
            batch_dir = seed_path.parent
            report_path = batch_dir / "dedup-report.json"
            report = json.loads(report_path.read_text(encoding="utf-8"))
            report["accepted_seed_count"] = 0
            generator.atomic_json(report_path, report)
            result_path = batch_dir / "result-receipt.json"
            result = json.loads(result_path.read_text(encoding="utf-8"))
            result["receipts"]["dedup_report"] = generator.file_receipt(
                report_path
            )
            generator.atomic_json(result_path, result)
            with self.assertRaisesRegex(
                generator.ServiceError, "not the frozen v1 transform"
            ):
                generator.validate_v3_result_receipt(
                    service_dir, result_path, seed_path, batch
                )

    def test_historical_root_result_rejects_fabricated_transform(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            run_root = Path(raw)
            service_dir = run_root / "service"
            authorization_path, authorization = self._configured_authorization(
                service_dir
            )
            campaign_id = "20260831-root-seeds-fabricated-transform"
            bundle = self._root_import_bundle(
                service_dir,
                run_root / "root-source",
                authorization_path=authorization_path,
                authorization=authorization,
                campaign_id=campaign_id,
            )
            with mock.patch("builtins.print"):
                generator.command_import_root_batch(bundle.args)
            seed_path = service_dir / "batches" / campaign_id / "seed-batch.json"
            batch = json.loads(seed_path.read_text(encoding="utf-8"))
            report_path = seed_path.parent / "dedup-report.json"
            report = json.loads(report_path.read_text(encoding="utf-8"))
            report["accepted_seed_count"] = 0
            generator.atomic_json(report_path, report)
            result_path = seed_path.parent / "result-receipt.json"
            result = json.loads(result_path.read_text(encoding="utf-8"))
            result["receipts"]["dedup_report"] = generator.file_receipt(
                report_path
            )
            generator.atomic_json(result_path, result)
            with self.assertRaisesRegex(
                generator.ServiceError, "not the frozen v1 transform"
            ):
                generator.validate_v3_result_receipt(
                    service_dir, result_path, seed_path, batch
                )

    def test_historical_root_result_rejects_run_split_and_relocation(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            run_root = Path(raw)
            service_dir = run_root / "service"
            authorization_path, authorization = self._configured_authorization(
                service_dir
            )
            campaign_id = "20260831-root-seeds-historical-layout"
            bundle = self._root_import_bundle(
                service_dir,
                run_root / "root-source",
                authorization_path=authorization_path,
                authorization=authorization,
                campaign_id=campaign_id,
            )
            with mock.patch("builtins.print"):
                generator.command_import_root_batch(bundle.args)
            seed_path = service_dir / "batches" / campaign_id / "seed-batch.json"
            batch = json.loads(seed_path.read_text(encoding="utf-8"))
            result_path = seed_path.parent / "result-receipt.json"
            original = json.loads(result_path.read_text(encoding="utf-8"))
            generator.validate_v3_result_receipt(
                service_dir, result_path, seed_path, batch
            )

            other_run = run_root / "other-source"
            other_run.mkdir()
            split_source = other_run / "seed-batch.json"
            split_source.write_bytes(bundle.source_path.read_bytes())
            split = copy.deepcopy(original)
            split["receipts"]["source_seed_batch"] = generator.file_receipt(
                split_source
            )
            generator.atomic_json(result_path, split)
            with self.assertRaisesRegex(
                generator.ServiceError,
                "root result snapshot is outside its frozen source-run layout",
            ):
                generator.validate_v3_result_receipt(
                    service_dir, result_path, seed_path, batch
                )

            split_screen = other_run / "semantic-screen.json"
            split_screen.write_bytes(bundle.screen_path.read_bytes())
            split = copy.deepcopy(original)
            split["receipts"]["semantic_screen"] = generator.file_receipt(
                split_screen
            )
            generator.atomic_json(result_path, split)
            with self.assertRaisesRegex(
                generator.ServiceError,
                "root result semantic screen is outside its source run",
            ):
                generator.validate_v3_result_receipt(
                    service_dir, result_path, seed_path, batch
                )

            relocated_report = seed_path.parent / "relocated-dedup-report.json"
            canonical_report = seed_path.parent / "dedup-report.json"
            relocated_report.write_bytes(canonical_report.read_bytes())
            relocated = copy.deepcopy(original)
            relocated["receipts"]["dedup_report"] = generator.file_receipt(
                relocated_report
            )
            generator.atomic_json(result_path, relocated)
            with self.assertRaisesRegex(
                generator.ServiceError,
                "root result dedup_report is outside its canonical destination layout",
            ):
                generator.validate_v3_result_receipt(
                    service_dir, result_path, seed_path, batch
                )

    def test_exact_claim_retry_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            self._configured_authorization(service_dir)
            seed_path, _batch = self._create_closed_v3_seed_batch(
                service_dir, campaign_id="claim-retry", seed_count=2
            )
            bundle = self._claim_bundle(
                service_dir,
                seed_path=seed_path,
                campaign_id="claim-retry",
            )
            with mock.patch("builtins.print"):
                self.assertEqual(generator.command_claim(bundle.args), 0)
            original = bundle.claim_path.read_bytes()
            with mock.patch("builtins.print"):
                self.assertEqual(generator.command_claim(bundle.args), 0)
            self.assertEqual(bundle.claim_path.read_bytes(), original)
            inventory = generator.seed_inventory(service_dir)
            self.assertEqual(
                {item["seed_id"]: item["state"] for item in inventory},
                {"S01": "investigating", "S02": "ready"},
            )

    def test_claim_retry_with_different_contract_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            self._configured_authorization(service_dir)
            seed_path, _batch = self._create_closed_v3_seed_batch(
                service_dir, campaign_id="claim-contract", seed_count=2
            )
            original_bundle = self._claim_bundle(
                service_dir,
                seed_path=seed_path,
                campaign_id="claim-contract",
                suffix="original",
            )
            different_bundle = self._claim_bundle(
                service_dir,
                seed_path=seed_path,
                campaign_id="claim-contract",
                suffix="different-contract",
            )
            with mock.patch("builtins.print"):
                generator.command_claim(original_bundle.args)
            original = original_bundle.claim_path.read_bytes()
            with self.assertRaisesRegex(
                generator.ServiceError,
                r"(?i)(existing|immutable|prior).*(claim|contract).*(differ|another)|"
                r"(claim|contract).*(differ|another)",
            ):
                with mock.patch("builtins.print"):
                    generator.command_claim(different_bundle.args)
            self.assertEqual(original_bundle.claim_path.read_bytes(), original)

    def test_sibling_remains_ready_after_claim_and_feedback(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            self._configured_authorization(service_dir)
            campaign_id = "sibling-ready"
            seed_path, _batch = self._create_closed_v3_seed_batch(
                service_dir, campaign_id=campaign_id, seed_count=2
            )
            bundle = self._claim_bundle(
                service_dir,
                seed_path=seed_path,
                campaign_id=campaign_id,
            )
            with mock.patch("builtins.print"):
                generator.command_claim(bundle.args)
            self.assertEqual(
                {
                    item["seed_id"]: item["state"]
                    for item in generator.seed_inventory(service_dir)
                },
                {"S01": "investigating", "S02": "ready"},
            )
            feedback = self._write_neutral_feedback(
                service_dir,
                seed_path=seed_path,
                campaign_id=campaign_id,
                seed_id="S01",
                bundle=bundle,
            )
            with mock.patch("builtins.print"):
                generator.command_reconcile(feedback.args)
            self.assertEqual(
                {
                    item["seed_id"]: item["state"]
                    for item in generator.seed_inventory(service_dir)
                },
                {"S01": "investigated", "S02": "ready"},
            )
            self.assertEqual(
                generator.active_reserve(service_dir)[0]["seed_ids"], ["S02"]
            )

    def test_cross_campaign_drift_suppresses_ready_but_preserves_memory(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization_path, authorization = self._configured_authorization(
                service_dir
            )
            first_id = "currency-source-a"
            first_seed_path, _first_batch = self._create_closed_v3_seed_batch(
                service_dir, campaign_id=first_id
            )
            first_claim = self._claim_bundle(
                service_dir,
                seed_path=first_seed_path,
                campaign_id=first_id,
            )
            with mock.patch("builtins.print"):
                generator.command_claim(first_claim.args)

            stale_id = "currency-target-b"
            stale_seed_path, stale_batch = self._create_closed_v3_seed_batch(
                service_dir,
                campaign_id=stale_id,
                freeze_launch_reserve=True,
            )
            result = json.loads(
                (stale_seed_path.parent / "result-receipt.json").read_text(
                    encoding="utf-8"
                )
            )
            admission_path = generator.authenticate_receipt(
                result["receipts"]["snapshot_admission"],
                "fixture target snapshot admission",
            )
            admission = json.loads(admission_path.read_text(encoding="utf-8"))
            self.assertEqual(
                generator.snapshot_currency(
                    admission,
                    service_dir=service_dir,
                    campaign_id=stale_id,
                ),
                (True, []),
            )

            feedback = self._write_neutral_feedback(
                service_dir,
                seed_path=first_seed_path,
                campaign_id=first_id,
                seed_id="S01",
                bundle=first_claim,
            )
            with mock.patch("builtins.print"):
                generator.command_reconcile(feedback.args)
            current, reasons = generator.snapshot_currency(
                admission,
                service_dir=service_dir,
                campaign_id=stale_id,
            )
            self.assertFalse(current)
            self.assertIn("validated_learning_export_changed", reasons)
            inventory = generator.seed_inventory(service_dir)
            self.assertEqual(
                [
                    item["state"]
                    for item in inventory
                    if item["campaign_id"] == first_id
                ],
                ["investigated"],
            )
            self.assertFalse(
                any(item["campaign_id"] == stale_id for item in inventory)
            )
            self.assertFalse(
                any(
                    item["campaign_id"] == stale_id
                    for item in generator.active_reserve(service_dir)
                )
            )

            accounting = generator.validate_accounting_chain(
                service_dir, authorization
            )
            export = generator.materialize_validated_learning_export(
                service_dir,
                service_dir / "historical-memory-probe.json",
                authorization_path=authorization_path,
                authorization=authorization,
                accounting=accounting,
                excluded_campaign_id="historical-memory-probe",
            )
            historical_memory = generator.frozen_generated_seed_memory(export)
            self.assertIn(
                generator.seed_fingerprint(stale_batch["seeds"][0]),
                historical_memory,
            )
            self.assertEqual(
                historical_memory[
                    generator.seed_fingerprint(stale_batch["seeds"][0])
                ],
                {"campaign_id": stale_id, "seed_id": "S01"},
            )

            stale_claim = self._claim_bundle(
                service_dir,
                seed_path=stale_seed_path,
                campaign_id=stale_id,
                suffix="stale-result",
            )
            with self.assertRaisesRegex(
                generator.ServiceError, "exact ready state"
            ):
                with mock.patch("builtins.print"):
                    generator.command_claim(stale_claim.args)
            self.assertFalse(stale_claim.claim_path.exists())

    def test_result_marker_cannot_release_pending_reservation(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization_path, authorization = self._configured_authorization(
                service_dir
            )
            queue_path, packet_path, _packet = self._freeze_and_queue(
                service_dir,
                authorization_path,
                authorization,
                campaign_id="fabricated-result-marker",
                requested_seed_count=3,
            )
            self.assertEqual(generator.pending_queue(service_dir), [queue_path])
            self.assertEqual(generator.pending_reserved_capacity(service_dir), 3)

            marker_path = packet_path.parent / "result-receipt.json"
            generator.atomic_json(marker_path, {"fabricated": "marker-only"})
            for action in (
                lambda: generator.pending_queue(service_dir),
                lambda: generator.pending_reserved_capacity(service_dir),
            ):
                with self.assertRaisesRegex(
                    generator.ServiceError, "partial result marker"
                ):
                    action()
            marker_path.unlink()
            self.assertEqual(generator.pending_queue(service_dir), [queue_path])
            self.assertEqual(generator.pending_reserved_capacity(service_dir), 3)

    def test_queue_object_path_and_children_are_exact(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization_path, authorization = self._configured_authorization(
                service_dir
            )
            queue_path, _packet_path, _packet = self._freeze_and_queue(
                service_dir,
                authorization_path,
                authorization,
                campaign_id="closed-queue-object",
                requested_seed_count=2,
            )
            original = json.loads(queue_path.read_text(encoding="utf-8"))
            hostile = copy.deepcopy(original)
            hostile.update(
                {
                    "schema_version": 999,
                    "protocol": "fabricated-protocol",
                    "approval_ref": "fabricated-approval",
                    "route_or_experiment_authority": "fabricated-route",
                    "extra": "not-closed",
                }
            )
            generator.atomic_json(queue_path, hostile)
            with self.assertRaisesRegex(
                generator.ServiceError, "closed-object contract"
            ):
                generator.authenticate_queue(queue_path)
            with self.assertRaisesRegex(
                generator.ServiceError, "closed-object contract"
            ):
                generator.pending_reserved_capacity(service_dir)

            generator.atomic_json(queue_path, original)
            relocated = queue_path.with_name("relocated-entry.json")
            queue_path.rename(relocated)
            with self.assertRaisesRegex(
                generator.ServiceError, "canonical campaign path"
            ):
                generator.authenticate_queue(relocated)
            with self.assertRaisesRegex(
                generator.ServiceError, "canonical campaign path"
            ):
                generator.pending_queue(service_dir)
            relocated.rename(queue_path)

            non_json = queue_path.parent / "unexpected.txt"
            non_json.write_text("hostile current queue child\n", encoding="utf-8")
            with self.assertRaisesRegex(
                generator.ServiceError, "non-JSON"
            ):
                generator.pending_queue(service_dir)
            non_json.unlink()
            directory_child = queue_path.parent / "directory.json"
            directory_child.mkdir()
            with self.assertRaisesRegex(
                generator.ServiceError, "non-JSON"
            ):
                generator.pending_queue(service_dir)

    def test_service_state_subtree_symlinks_fail_closed(self) -> None:
        with self.subTest(subtree="accounting-baselines"):
            with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
                run_root = Path(raw)
                service_dir = run_root / "service"
                service_dir.mkdir()
                outside = run_root / "outside-accounting"
                outside.mkdir()
                (service_dir / generator.ACCOUNTING_BASELINE_DIRECTORY).symlink_to(
                    outside, target_is_directory=True
                )
                with self.assertRaisesRegex(
                    generator.ServiceError, "symlink alias"
                ):
                    self._configured_authorization(service_dir)
                self.assertEqual(list(outside.iterdir()), [])

        with self.subTest(subtree="queue"):
            with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
                run_root = Path(raw)
                service_dir = run_root / "service"
                authorization_path, authorization = self._configured_authorization(
                    service_dir
                )
                self._freeze_and_queue(
                    service_dir,
                    authorization_path,
                    authorization,
                    campaign_id="queue-subtree-alias",
                )
                queue_dir = service_dir / "queue"
                outside = run_root / "outside-queue"
                queue_dir.rename(outside)
                queue_dir.symlink_to(outside, target_is_directory=True)
                with self.assertRaisesRegex(
                    generator.ServiceError, "symlink alias"
                ):
                    generator.pending_queue(service_dir)
                with self.assertRaisesRegex(
                    generator.ServiceError, "symlink alias"
                ):
                    generator.pending_reserved_capacity(service_dir)

        with self.subTest(subtree="claims"):
            with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
                run_root = Path(raw)
                service_dir = run_root / "service"
                self._configured_authorization(service_dir)
                campaign_id = "claim-subtree-alias"
                seed_path, _batch = self._create_closed_v3_seed_batch(
                    service_dir, campaign_id=campaign_id
                )
                bundle = self._claim_bundle(
                    service_dir,
                    seed_path=seed_path,
                    campaign_id=campaign_id,
                )
                outside = run_root / "outside-claims"
                outside.mkdir()
                (service_dir / "claims").symlink_to(
                    outside, target_is_directory=True
                )
                with self.assertRaisesRegex(
                    generator.ServiceError, "symlink alias"
                ):
                    with mock.patch("builtins.print"):
                        generator.command_claim(bundle.args)
                self.assertFalse((outside / campaign_id / "S01.json").exists())

    def test_missing_accounting_head_blocks_inventory_and_claim(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            campaign_id = "missing-accounting-head"
            seed_path, _batch = self._create_closed_v3_seed_batch(
                service_dir, campaign_id=campaign_id
            )
            bundle = self._claim_bundle(
                service_dir,
                seed_path=seed_path,
                campaign_id=campaign_id,
            )
            head_path = generator.accounting_head_path(service_dir)
            head_path.rename(head_path.with_suffix(".missing"))

            actions = {
                "inventory": lambda: generator.seed_inventory(service_dir),
                "pending": lambda: generator.pending_queue(service_dir),
                "claim": lambda: generator.command_claim(bundle.args),
            }
            for label, action in actions.items():
                with self.subTest(action=label):
                    with self.assertRaisesRegex(
                        generator.ServiceError,
                        r"(?i)(cannot read invocation accounting head|accounting.*head.*missing)",
                    ):
                        with mock.patch("builtins.print"):
                            action()
            self.assertFalse(bundle.claim_path.exists())

    def test_new_activation_survives_old_component_topology_and_rollback_fails(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            current_components = generator.implementation_component_paths()
            self.assertGreater(len(current_components), 2)
            old_components = current_components[:-1]
            with mock.patch.object(
                generator,
                "implementation_component_paths",
                return_value=old_components,
            ):
                first_path, first = self._configured_authorization(
                    service_dir, approval_ref="first-component-topology"
                )
            first_activation = generator.validate_authorization_activation_chain(
                service_dir, verify_latest_current=False
            )
            assert first_activation is not None
            with self.assertRaisesRegex(
                generator.ServiceError, "helper or schema path identity drifted"
            ):
                generator.verify_standing_authorization(
                    first_path, service_dir=service_dir, mode="current"
                )
            generator.verify_standing_authorization(
                first_path, service_dir=service_dir, mode="historical"
            )

            second_path, _second = self._configured_authorization(
                service_dir, approval_ref="second-component-topology"
            )
            self.assertEqual(
                generator.active_standing_authorization(service_dir)[0], second_path
            )

            generator.atomic_json(
                generator.active_authorization_pointer_path(service_dir),
                {
                    "schema_version": 1,
                    "protocol": generator.PROTOCOL_VERSION,
                    "activated_at": first_activation["activated_at"],
                    "authorization": generator.file_receipt(first_path),
                    "activation_event": first_activation["last_event"],
                },
            )
            with self.assertRaisesRegex(
                generator.ServiceError, "not the authenticated latest activation"
            ):
                generator.active_standing_authorization(service_dir)
            self.assertEqual(first["approval_ref"], "first-component-topology")

    def test_prepare_next_cycle_reuses_held_state_lock(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization_path, authorization = self._configured_authorization(
                service_dir
            )
            real_lock = generator.locked_service_state
            with real_lock(service_dir):
                with mock.patch.object(
                    generator,
                    "locked_service_state",
                    side_effect=AssertionError("nested service-state lock"),
                ):
                    prepared = generator.prepare_next_cycle(
                        service_dir,
                        authorization_path,
                        authorization,
                        state_lock_held=True,
                    )
            self.assertEqual(prepared["requested_seed_count"], 5)
            queue_path = generator.authenticate_receipt(
                prepared["queue"], "prepared queue"
            )
            self.assertEqual(generator.pending_queue(service_dir), [queue_path])

    def test_start_and_serve_recover_one_exact_outcome_tail(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            start_service = Path(raw) / "start-service"
            start_fixture = self._restore_exact_outcome_tail_crash(
                start_service,
                campaign_id="recover-outcome-tail-start",
            )
            with self.assertRaisesRegex(
                generator.ServiceError, "head/event count differs"
            ):
                generator.validate_accounting_chain(
                    start_service, start_fixture.authorization
                )
            start_args = SimpleNamespace(
                service_dir=start_service,
                authorization=start_fixture.authorization_path,
                authorization_sha256=generator.sha256(
                    start_fixture.authorization_path
                ),
            )
            expected_authorization = generator.file_receipt(
                start_fixture.authorization_path
            )
            real_preflight = generator.accounting_transition_preflight
            with (
                mock.patch.object(
                    generator,
                    "accounting_transition_preflight",
                    wraps=real_preflight,
                ) as start_preflight,
                mock.patch.object(
                    generator,
                    "launch_daemon",
                    return_value={
                        "standing_authorization": expected_authorization
                    },
                ) as launch,
                mock.patch("builtins.print"),
            ):
                self.assertEqual(generator.command_start(start_args), 0)
            start_preflight.assert_called_once_with(
                start_service, start_fixture.authorization
            )
            launch.assert_called_once_with(
                start_service,
                expected_authorization=expected_authorization,
            )
            start_accounting = generator.validate_accounting_chain(
                start_service, start_fixture.authorization
            )
            self.assertIsNone(start_accounting["unresolved_attempt_ordinal"])
            self.assertEqual(
                [item["state"] for item in generator.seed_inventory(start_service)],
                ["ready"],
            )

            serve_service = Path(raw) / "serve-service"
            serve_fixture = self._restore_exact_outcome_tail_crash(
                serve_service,
                campaign_id="recover-outcome-tail-serve",
            )
            serve_args = SimpleNamespace(
                service_dir=serve_service,
                service_id="outcome-tail-regression",
                supervisor_ref="mocked-supervisor",
            )
            real_preflight = generator.accounting_transition_preflight
            with (
                mock.patch.object(
                    generator,
                    "accounting_transition_preflight",
                    wraps=real_preflight,
                ) as serve_preflight,
                mock.patch.object(
                    generator,
                    "generation_gate",
                    return_value={"ready": False, "reason": "test-quiescent"},
                ),
                mock.patch.object(
                    generator,
                    "stop_requested",
                    side_effect=[False, True, True],
                ),
                mock.patch.object(
                    generator,
                    "daemon_process_identity",
                    return_value=self._process_identity(os.getpid()),
                ),
                mock.patch.object(generator.signal, "signal"),
                mock.patch.object(generator.time, "sleep"),
            ):
                with warnings.catch_warnings():
                    warnings.simplefilter("ignore", ResourceWarning)
                    self.assertEqual(generator.command_serve(serve_args), 0)
            serve_preflight.assert_called_once_with(
                serve_service, serve_fixture.authorization
            )
            serve_accounting = generator.validate_accounting_chain(
                serve_service, serve_fixture.authorization
            )
            self.assertIsNone(serve_accounting["unresolved_attempt_ordinal"])
            self.assertEqual(
                [item["state"] for item in generator.seed_inventory(serve_service)],
                ["ready"],
            )

    def test_outcome_tail_preflight_rejects_altered_tail(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            fixture = self._restore_exact_outcome_tail_crash(
                service_dir,
                campaign_id="reject-altered-outcome-tail",
            )
            head_before = fixture.head_path.read_bytes()
            altered = json.loads(fixture.outcome_path.read_text(encoding="utf-8"))
            altered["seed_count"] = int(altered["seed_count"]) + 1
            generator.atomic_json(fixture.outcome_path, altered)
            with self.assertRaisesRegex(
                generator.ServiceError, "not the exact recoverable outcome"
            ):
                generator.accounting_transition_preflight(
                    service_dir, fixture.authorization
                )
            self.assertEqual(fixture.head_path.read_bytes(), head_before)
            with self.assertRaisesRegex(
                generator.ServiceError, "head/event count differs"
            ):
                generator.validate_accounting_chain(
                    service_dir, fixture.authorization
                )

    def test_outcome_tail_preflight_rejects_multiple_tails(self) -> None:
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            fixture = self._restore_exact_outcome_tail_crash(
                service_dir,
                campaign_id="reject-multiple-outcome-tails",
            )
            head_before = fixture.head_path.read_bytes()
            extra_path = (
                generator.accounting_event_directory(service_dir)
                / "000003-outcome-000001.json"
            )
            generator.atomic_json(extra_path, {"fabricated": "second tail"})
            with self.assertRaisesRegex(
                generator.ServiceError, "head/event count differs"
            ):
                generator.accounting_transition_preflight(
                    service_dir, fixture.authorization
                )
            self.assertEqual(fixture.head_path.read_bytes(), head_before)
            with self.assertRaisesRegex(
                generator.ServiceError, "head/event count differs"
            ):
                generator.validate_accounting_chain(
                    service_dir, fixture.authorization
                )

    def test_post_popen_failures_terminate_child_before_unwinding(self) -> None:
        cases = ("provider-start-write", "provider-start-validation", "prompt-write")
        for case in cases:
            with self.subTest(case=case):
                with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
                    service_dir = Path(raw)
                    campaign_id = f"cleanup-{case}"
                    authorization_path, authorization = (
                        self._configured_authorization(service_dir)
                    )
                    entry_path, packet_path, packet = self._freeze_and_queue(
                        service_dir,
                        authorization_path,
                        authorization,
                        campaign_id=campaign_id,
                    )
                    process = FakeProcess(
                        poll_value=None, fail_stdin=case == "prompt-write"
                    )
                    identity = self._process_identity(process.pid)
                    real_write_once = generator.write_once

                    def selective_write(path: Path, value: object) -> None:
                        if case == "provider-start-write" and Path(path).name == (
                            "provider-start.json"
                        ):
                            raise OSError("injected provider-start write failure")
                        real_write_once(Path(path), value)

                    validation_patch = (
                        mock.patch.object(
                            generator,
                            "validate_provider_start",
                            side_effect=generator.ServiceError(
                                "injected provider-start validation failure"
                            ),
                        )
                        if case == "provider-start-validation"
                        else mock.patch.object(
                            generator,
                            "validate_provider_start",
                            wraps=generator.validate_provider_start,
                        )
                    )
                    terminate = mock.Mock()
                    with (
                        mock.patch.object(
                            generator.subprocess, "Popen", return_value=process
                        ) as popen,
                        mock.patch.object(
                            generator,
                            "codex_version",
                            return_value=authorization["provider"]["cli_version"],
                        ),
                        mock.patch.object(
                            generator, "process_identity", return_value=identity
                        ),
                        mock.patch.object(
                            generator, "process_alive", return_value=True
                        ),
                        mock.patch.object(generator, "set_affinity"),
                        mock.patch.object(
                            generator, "terminate_provider", terminate
                        ),
                        mock.patch.object(
                            generator,
                            "write_once",
                            side_effect=selective_write,
                        ),
                        validation_patch,
                    ):
                        caught: BaseException | None = None
                        try:
                            generator.run_provider(
                                service_dir, entry_path, {}, {"stop": False}
                            )
                        except (
                            BrokenPipeError,
                            OSError,
                            generator.ServiceError,
                        ) as exc:
                            caught = exc
                    self.assertIsNotNone(caught)
                    popen.assert_called_once()
                    terminate.assert_called_once_with(process.pid, identity)
                    self.assertEqual(process.stdin.payloads, [])
                    accounting = generator.validate_accounting_chain(
                        service_dir, authorization
                    )
                    self.assertEqual(accounting["unresolved_attempt_ordinal"], 1)
                    self.assertEqual(accounting["event_count"], 1)
                    batch_dir = packet_path.parent
                    self.assertFalse((batch_dir / "result-receipt.json").exists())
                    self.assertFalse((batch_dir / "seed-batch.json").exists())


if __name__ == "__main__":
    unittest.main()
