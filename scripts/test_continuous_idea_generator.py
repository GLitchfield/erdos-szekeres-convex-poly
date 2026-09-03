#!/usr/bin/env python3
"""Regression tests for the bounded continuous idea generator."""

from __future__ import annotations

import json
import copy
from datetime import datetime, timezone
import hashlib
import os
from pathlib import Path
import stat
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

from scripts import continuous_idea_generator as generator

REAL_MIGRATION_VALIDATOR = generator.validate_accounting_migration_root


class ContinuousIdeaGeneratorTests(unittest.TestCase):
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

    def test_validated_learning_export_digest_preserves_unicode(self) -> None:
        receipt = {"path": "AGENTS.md", "sha256": "0" * 64}
        learning = [{"kind": "unicode-π", "receipt": receipt}]
        inputs: list[dict[str, str]] = []
        value = {
            "schema_version": 1,
            "protocol": generator.build_sol_idea_packet.VALIDATED_LEARNING_EXPORT_PROTOCOL,
            "service_dir": "runs/agents/unicode-export-test",
            "excluded_campaign_id": "unicode-export-test",
            "standing_authorization": receipt,
            "accounting_checkpoint": {},
            "validator_components": {
                key: receipt
                for key in (
                    "generator",
                    "campaign",
                    "first_test_guard",
                    "seed_schema",
                    "brief_schema",
                    "task_schema",
                    "development_receipt_schema",
                    "event_verification_schema",
                    "first_test_execution_envelope_schema",
                    "feedback_schema",
                )
            },
            "continuous_entries": [],
            "learning_receipts": learning,
            "input_receipts": inputs,
            "learning_epoch_sha256": generator.canonical_json_sha256(learning),
            "current_input_fingerprint_sha256": generator.canonical_json_sha256(inputs),
        }
        value["export_core_sha256"] = generator.canonical_json_sha256(value)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            path = Path(raw) / "validated-learning-export.json"
            generator.atomic_json(path, value)
            loaded = generator.build_sol_idea_packet.load_validated_learning_export(
                path, authenticate_inputs=False
            )
        self.assertEqual(loaded, value)

    @staticmethod
    def authorization_args(**changes):
        values = {
            "approval_ref": "test-standing-approval",
            "generation_modes": list(generator.DEFAULT_GENERATION_MODES),
            "wall_minutes": 90,
            "ready_seed_target": 10,
            "max_total_invocations": 100,
            "max_consecutive_provider_stops": 2,
            "max_consecutive_zero_seed_batches": 2,
            "max_inline_bytes": 1024,
        }
        values.update(changes)
        return SimpleNamespace(**values)

    @classmethod
    def configured_authorization(
        cls, service_dir: Path, *, approval_ref: str = "test-standing-approval"
    ) -> tuple[Path, dict]:
        authorization = generator.make_standing_authorization(
            service_dir, cls.authorization_args(approval_ref=approval_ref)
        )
        path = generator.authorization_file_path(service_dir, authorization)
        generator.write_once(path, authorization)
        generator.append_authorization_activation(service_dir, path, authorization)
        generator.active_standing_authorization(service_dir)
        return path, authorization

    @classmethod
    def build_authenticated_snapshot(
        cls,
        service_dir: Path,
        snapshot_dir: Path,
        *,
        campaign_id: str,
        purpose: str,
        authorization_path: Path | None = None,
        authorization: dict | None = None,
    ) -> dict:
        """Build a snapshot only through the generator's validated export."""
        if authorization_path is None or authorization is None:
            authorization_path, authorization = (
                generator.active_standing_authorization(service_dir)
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
            excluded_campaign_id=campaign_id,
        )
        return generator.build_sol_idea_packet.build_packet(
            snapshot_dir,
            int(authorization["limits"]["max_inline_bytes"]),
            service_dir,
            campaign_id=campaign_id,
            purpose=purpose,
            validated_learning_export=export_path,
        )

    @staticmethod
    def standing_first_test_task(
        service_dir: Path,
        *,
        brief: dict,
        brief_path: Path,
        seed_path: Path,
        context_paths: list[Path],
        evidence_path: Path,
    ) -> dict:
        """Freeze the exact non-Lean first-test execution contract used by claims."""
        # The standing contract admits only authenticated ``scripts/*.py``
        # checkers.  This module is a stable offline fixture component; the test
        # never executes it through the first-test guard.
        checker_path = generator.ROOT / "scripts/test_continuous_idea_generator.py"
        seed_rel = generator.repo_relative(seed_path)
        checker_rel = generator.repo_relative(checker_path)
        evidence_rel = generator.repo_relative(evidence_path)
        try:
            run_id = service_dir.resolve().relative_to(generator.RUNS_ROOT).parts[0]
        except (ValueError, IndexError) as exc:
            raise AssertionError("test service must be under runs/agents") from exc
        inputs = [
            generator.file_receipt(seed_path),
            *(generator.file_receipt(path) for path in context_paths),
            generator.file_receipt(brief_path),
            generator.file_receipt(checker_path),
        ]
        by_path = {item["path"]: item for item in inputs}
        inputs = [by_path[path] for path in sorted(by_path)]
        execution = {
            "protocol": "ticket-0119-first-test-execution-v1",
            "contract_id": "0" * 64,
            "guard_component": generator.file_receipt(
                generator.ROOT / "scripts/run_first_test_guarded.py"
            ),
            "engine": "python_exact",
            "argv_template": [
                "/usr/bin/python3",
                "-B",
                checker_rel,
                "--seed-batch",
                seed_rel,
                "--output-fd",
                "{output_fd:normalized_result}",
            ],
            "cwd": ".",
            "input_receipts": [
                generator.file_receipt(checker_path),
                generator.file_receipt(seed_path),
            ],
            "outputs": [
                {
                    "role": "normalized_result",
                    "path": evidence_rel,
                    "media_type": "application/json",
                }
            ],
            "normalized_result_role": "normalized_result",
            "process_model": "one-filtered-process-no-children-v1",
        }
        execution["contract_id"] = generator.canonical_json_sha256(
            {key: value for key, value in execution.items() if key != "contract_id"}
        )
        return {
            "schema_version": 2,
            "run_id": run_id,
            "task_id": brief["task_id"],
            "wayfinder_ticket": generator.campaign.TICKET_0119,
            "profile": "test-first-investigator",
            "base_revision": "test-revision",
            "workspace_fingerprint": "test-workspace",
            "objective": "Execute the frozen candidate-local first test.",
            "theorem_contract": None,
            "inputs": inputs,
            "ownership": {
                "read_paths": [item["path"] for item in inputs],
                "write_paths": [evidence_rel],
            },
            "budget": {
                "wall_minutes": 30,
                "cpu_cores": 1,
                "memory_gib": 1,
                "output_gib": 0.01,
            },
            "required_checks": ["Authenticate the frozen candidate and controls."],
            "success": ["Return one pre-admission terminal."],
            "stop": ["Stop within the standing first-test envelope."],
            "deliverables": [evidence_rel],
            "claims_allowed": ["proposal"],
            "standing_first_test": copy.deepcopy(brief["authority"]),
            "first_test_execution": execution,
        }

    @staticmethod
    def write_execution_envelope(
        *,
        brief: dict,
        brief_path: Path,
        task: dict,
        task_path: Path,
        claim_path: Path,
    ) -> tuple[Path, int]:
        """Write the root-owned PASS envelope authenticating the fixture output."""
        execution = task["first_test_execution"]
        manifest = []
        for output in execution["outputs"]:
            output_path = generator.ROOT / output["path"]
            manifest.append(
                {
                    "role": output["role"],
                    "path": output["path"],
                    "sha256": generator.sha256(output_path),
                    "bytes": output_path.stat().st_size,
                    "materialized": True,
                }
            )
        output_bytes = sum(item["bytes"] for item in manifest)
        empty_sha = hashlib.sha256(b"").hexdigest()
        next_fd = 20
        argv = []
        for item in execution["argv_template"]:
            if item.startswith("{output_fd:"):
                argv.append(str(next_fd))
                next_fd += 1
            else:
                argv.append(item)
        claim = json.loads(claim_path.read_text(encoding="utf-8"))
        envelope = {
            "schema_version": 1,
            "protocol": "research-first-test-execution-envelope-v1",
            "envelope_id": "0" * 64,
            "guard_component": copy.deepcopy(execution["guard_component"]),
            "identity": {
                "seed_claim": generator.file_receipt(claim_path),
                "claim_id": claim["claim_id"],
                "development_brief": generator.file_receipt(brief_path),
                "brief_id": brief["brief_id"],
                "task_packet": generator.file_receipt(task_path),
                "task_id": task["task_id"],
                "execution_contract_id": execution["contract_id"],
            },
            "launch": {
                "started_at": "2026-08-31T12:00:00Z",
                "finished_at": "2026-08-31T12:01:00Z",
                "boot_id": "offline-test-boot",
                "outer_pid": 100,
                "sandbox_pid": 101,
                "sandbox_start_ticks": 1000,
                "process_group": 101,
                "argv": argv,
                "cwd": "/work",
            },
            "enforced_policy": {
                "wall_seconds": task["budget"]["wall_minutes"] * 60,
                "cpu_affinity": list(range(task["budget"]["cpu_cores"])),
                "memory_bytes": task["budget"]["memory_gib"] * (1024**3),
                "output_bytes": int(task["budget"]["output_gib"] * (1024**3)),
                "process_model": "one-filtered-process-no-children-v1",
                "network": "new-net-namespace-plus-seccomp-kill",
                "repository": "sparse-authenticated-inputs-read-only",
                "persistent_writes": [
                    item["path"] for item in execution["outputs"]
                ],
                "seccomp_policy_sha256": "a" * 64,
                "namespace_inodes": {
                    "user": 1,
                    "mount": 2,
                    "pid": 3,
                    "net": 4,
                    "ipc": 5,
                    "uts": 6,
                    "cgroup": 7,
                },
            },
            "observation": {
                "exit_code": 0,
                "signal": None,
                "wall_seconds": 60.0,
                "cpu_seconds": 1.0,
                "peak_aggregate_rss_bytes": 1024 * 1024,
                "worker_output_bytes": output_bytes,
                "writes": manifest,
                "stdout": {"sha256": empty_sha, "bytes": 0},
                "stderr": {"sha256": empty_sha, "bytes": 0},
                "forbidden_attempts": "none",
                "violations": [],
            },
            "terminal": "PASS",
        }
        envelope["envelope_id"] = generator.canonical_json_sha256(
            {key: value for key, value in envelope.items() if key != "envelope_id"}
        )
        envelope_path = (
            generator.RUNS_ROOT
            / task["run_id"]
            / "root-receipts"
            / f"{task['task_id']}.execution-envelope.json"
        )
        generator.atomic_json(envelope_path, envelope)
        return envelope_path, output_bytes

    def test_real_migration_root_authenticates_exact_30_plus_6(self) -> None:
        with mock.patch.object(
            generator,
            "validate_accounting_migration_root",
            REAL_MIGRATION_VALIDATOR,
        ):
            root, charged, excluded = generator.validate_accounting_migration_root(
                generator.ROOT / generator.DEFAULT_SERVICE_DIR
            )
        self.assertEqual(root["totals"], {"charged": 30, "excluded": 6, "all": 36})
        self.assertEqual(len(charged), 30)
        self.assertEqual(len(excluded), 6)

    def test_real_migration_root_rejects_an_alternate_service(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            with mock.patch.object(
                generator,
                "validate_accounting_migration_root",
                REAL_MIGRATION_VALIDATOR,
            ):
                with self.assertRaisesRegex(
                    generator.ServiceError, "canonical continuous-generator service"
                ):
                    generator.validate_accounting_migration_root(Path(raw))

    def test_first_v3_configuration_requires_exact_36_queue_artifacts(self) -> None:
        canonical = json.loads(generator.MIGRATION_ROOT.read_text(encoding="utf-8"))
        campaign_ids = [str(entry[0]) for entry in canonical["entries"]]
        self.assertEqual(len(campaign_ids), 36)
        self.assertEqual(len(set(campaign_ids)), 36)

        for variant in (
            "exact",
            "missing",
            "extra",
            "non_json",
            "directory",
            "symlink_alias",
        ):
            with self.subTest(variant=variant):
                with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
                    service_dir = Path(raw)
                    queue_dir = service_dir / "queue"
                    queue_dir.mkdir(parents=True)
                    observed = list(campaign_ids)
                    if variant == "missing":
                        observed.pop()
                    for campaign_id in observed:
                        generator.atomic_json(
                            queue_dir / f"{campaign_id}.json",
                            {"historical_queue_fixture": campaign_id},
                        )
                    if variant == "extra":
                        generator.atomic_json(
                            queue_dir / "unrecorded-campaign.json",
                            {"historical_queue_fixture": "unrecorded-campaign"},
                        )
                    elif variant == "non_json":
                        (queue_dir / "README.txt").write_text(
                            "not a migration queue artifact\n", encoding="utf-8"
                        )
                    elif variant == "directory":
                        (queue_dir / "unexpected-child").mkdir()
                    elif variant == "symlink_alias":
                        alias = queue_dir / f"{campaign_ids[-1]}.json"
                        alias.unlink()
                        alias.symlink_to(queue_dir / f"{campaign_ids[0]}.json")

                    migration = copy.deepcopy(canonical)
                    migration["path_templates"]["queue"] = (
                        generator.repo_relative(queue_dir) + "/{campaign_id}.json"
                    )
                    with (
                        mock.patch.object(
                            generator,
                            "validate_accounting_migration_root",
                            return_value=(migration, [], []),
                        ),
                        mock.patch.object(
                            generator.subprocess,
                            "run",
                            return_value=SimpleNamespace(stdout="inactive"),
                        ),
                        mock.patch.object(
                            generator.shutil, "which", return_value="/bin/true"
                        ),
                        mock.patch.object(
                            generator, "codex_version", return_value="offline-test"
                        ),
                        mock.patch("builtins.print"),
                    ):
                        if variant == "exact":
                            self.assertEqual(
                                generator._command_configure_locked(
                                    self.authorization_args(), service_dir
                                ),
                                0,
                            )
                        else:
                            with self.assertRaisesRegex(
                                generator.ServiceError,
                                "queue artifacts outside the authenticated migration root",
                            ):
                                generator._command_configure_locked(
                                    self.authorization_args(), service_dir
                                )

    @classmethod
    def ledgered_attempt(
        cls,
        service_dir: Path,
        *,
        campaign_id: str = "ledgered-attempt",
    ) -> tuple[Path, dict, Path, Path]:
        authorization_path, authorization = cls.configured_authorization(
            service_dir
        )
        queue_path, packet_path, packet = cls.frozen_queue(
            service_dir,
            authorization_path=authorization_path,
            authorization=authorization,
            campaign_id=campaign_id,
        )
        generator.begin_invocation_event(
            service_dir,
            authorization_path=authorization_path,
            authorization=authorization,
            entry_path=queue_path,
            packet_path=packet_path,
            packet=packet,
            started_at=datetime.now(timezone.utc).isoformat(),
            command=generator.provider_argv(packet, packet_path.parent),
        )
        return authorization_path, authorization, packet_path, queue_path

    @staticmethod
    def frozen_queue(
        service_dir: Path,
        *,
        authorization_path: Path,
        authorization: dict,
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
        packet = generator.verify_packet(packet_path, mode="current")
        generator.queue_packet(
            service_dir,
            packet_path,
            generator.sha256(packet_path),
            packet["prompt"]["sha256"],
            packet["task"]["sha256"],
            authorization["approval_ref"],
        )
        return service_dir / "queue" / f"{campaign_id}.json", packet_path, packet

    @classmethod
    def completed_provider_attempt(
        cls,
        service_dir: Path,
        *,
        authorization_path: Path,
        authorization: dict,
        campaign_id: str,
        terminal: str,
        seed_count: int,
        requested_seed_count: int | None = None,
    ) -> dict:
        requested = (
            requested_seed_count
            if requested_seed_count is not None
            else max(1, seed_count)
        )
        queue_path, packet_path, packet = cls.frozen_queue(
            service_dir,
            authorization_path=authorization_path,
            authorization=authorization,
            campaign_id=campaign_id,
            requested_seed_count=requested,
        )
        started_at = datetime.now(timezone.utc).isoformat()
        attempt = generator.begin_invocation_event(
            service_dir,
            authorization_path=authorization_path,
            authorization=authorization,
            entry_path=queue_path,
            packet_path=packet_path,
            packet=packet,
            started_at=started_at,
            command=generator.provider_argv(packet, packet_path.parent),
        )
        identity = {
            "pid": 4242,
            "boot_id": "offline-test-boot",
            "start_ticks": 12345,
            "process_group_id": 4242,
        }
        generator.atomic_json(
            packet_path.parent / "provider-start.json",
            {
                "schema_version": 1,
                "protocol": generator.PROTOCOL_VERSION,
                "campaign_id": campaign_id,
                "pid": identity["pid"],
                "process_identity": identity,
                "started_at": started_at,
                "attempt_event": attempt["ledger_event"],
                "prompt": packet["prompt"],
                "meaning": (
                    "durable process acknowledgement committed before prompt delivery"
                ),
            },
        )
        if terminal in {"SEED-BATCH-COMPLETE", "SEED-BATCH-NOVELTY-STOP"}:
            response = json.loads(
                (generator.ROOT / "templates/research-seed-batch.json").read_text(
                    encoding="utf-8"
                )
            )
            response["campaign_id"] = campaign_id
            response["generation_mode"] = packet["generation_mode"]
            response["requested_seed_count"] = packet["requested_seed_count"]
            response["snapshot"] = packet["snapshot"]
            seed_template = response["seeds"][0]
            response["seeds"] = []
            for ordinal in range(seed_count):
                seed = copy.deepcopy(seed_template)
                seed["seed_id"] = f"S{ordinal + 1:02d}"
                seed["title"] = f"Offline seed {ordinal + 1} for {campaign_id}"
                seed["mechanism"]["operation"] += (
                    f" Offline accounting fixture {campaign_id}, variant {ordinal + 1}."
                )
                response["seeds"].append(seed)
            response["generation_metrics"]["private_seed_count"] = seed_count
            response["terminal"] = terminal
            generator.atomic_json(packet_path.parent / "raw-response.json", response)
            exit_code = 0
            stop_reason = None
        else:
            exit_code = 1
            stop_reason = "offline provider-stop fixture"
        result = generator.finalize_provider(
            packet_path.parent,
            packet_path,
            packet,
            exit_code,
            stop_reason,
            started_at,
        )
        if result.get("terminal") != terminal:
            raise AssertionError(
                f"provider fixture reached {result.get('terminal')}, expected {terminal}"
            )
        if not result.get("terminal_reason"):
            raise AssertionError("provider fixture omitted its terminal reason")
        return result

    @staticmethod
    def authenticated_seed_batch(
        service_dir: Path, campaign_id: str, seed_count: int = 2
    ) -> Path:
        snapshot_path = service_dir / f"snapshot-{campaign_id}.json"
        generator.atomic_json(snapshot_path, {"snapshot": campaign_id})
        batch = json.loads(
            (generator.ROOT / "templates/research-seed-batch.json").read_text(
                encoding="utf-8"
            )
        )
        first = batch["seeds"][0]
        seeds = []
        for ordinal in range(seed_count):
            seed = copy.deepcopy(first)
            seed["seed_id"] = f"S{ordinal + 1:02d}"
            seed["title"] = f"Queue seed {ordinal + 1}"
            seed["mechanism"]["operation"] += f" Variant {ordinal + 1}."
            seeds.append(seed)
        batch["campaign_id"] = campaign_id
        batch["snapshot"] = generator.file_receipt(snapshot_path)
        batch["seeds"] = seeds
        batch["generation_metrics"]["private_seed_count"] = seed_count
        batch["terminal"] = (
            "SEED-BATCH-COMPLETE"
            if seed_count == 5
            else "SEED-BATCH-NOVELTY-STOP"
        )
        path = service_dir / "batches" / campaign_id / "seed-batch.json"
        generator.atomic_json(path, batch)
        return path

    @staticmethod
    def root_semantic_screen(
        service_dir: Path,
        *,
        batch_path: Path,
        authorization_path: Path,
        approval_ref: str,
    ) -> Path:
        batch = json.loads(batch_path.read_text(encoding="utf-8"))
        snapshot_path = generator.authenticate_receipt(
            batch["snapshot"], "test root snapshot"
        )
        build_path = snapshot_path.parent / generator.build_sol_idea_packet.SNAPSHOT_BUILD_RECEIPT_NAME
        build = json.loads(build_path.read_text(encoding="utf-8"))
        prior_path = generator.authenticate_receipt(
            build["outputs"]["prior_idea_registry_json"], "test prior registry"
        )
        judgments = {
            name: {
                "status": "pass",
                "rationale": f"Test fixture passed {name}.",
                "record_refs": [],
            }
            for name in (
                "semantic_duplicate_absent",
                "target_equivalence_screened",
                "model_tier_and_return_status_explicit",
                "failure_memory_respected",
                "novelty_or_source_status_reviewed",
                "family_correlation_reviewed",
                "no_padding",
            )
        }
        reviews = []
        for seed in batch["seeds"]:
            reviews.append(
                {
                    "seed_id": seed["seed_id"],
                    "seed_sha256": generator.canonical_json_sha256(seed),
                    "working_model_tier": seed["model"]["working_tier"],
                    "machine_checks": {
                        "schema_valid": "pass",
                        "identity_bound": "pass",
                        "snapshot_bound": "pass",
                        "proposal_only": "pass",
                        "literal_duplicate_absent": "pass",
                        "first_test_within_30_minutes": "pass",
                    },
                    "root_judgment_checks": copy.deepcopy(judgments),
                    "decision": "pass",
                    "rationale": "Test fixture admits this proposal to the queue only.",
                }
            )
        path = batch_path.parent / "semantic-screen.json"
        generator.atomic_json(
            path,
            {
                "schema_version": 1,
                "protocol": "research-root-semantic-screen-v1",
                "screen_id": f"screen:{batch['campaign_id']}",
                "screened_at": datetime.now(timezone.utc).isoformat(),
                "reviewer": "root",
                "authority": "proposal_queue_screen_only",
                "campaign_id": batch["campaign_id"],
                "approval_ref": approval_ref,
                "standing_authorization": generator.file_receipt(
                    authorization_path
                ),
                "seed_batch": generator.file_receipt(batch_path),
                "snapshot": generator.file_receipt(snapshot_path),
                "snapshot_build": generator.file_receipt(build_path),
                "prior_idea_registry": generator.file_receipt(prior_path),
                "feedback_epoch_sha256": build["input_state"][
                    "learning_epoch_sha256"
                ],
                "seed_reviews": reviews,
                "overall_decision": "pass",
                "claim_level": "proposal",
            },
        )
        return path

    def test_provider_schema_binds_identity_and_snapshot(self) -> None:
        snapshot = {"path": "runs/agents/test/snapshot.json", "sha256": "a" * 64}
        schema = generator.provider_schema("campaign-01", "context_rich", snapshot)
        properties = schema["properties"]
        self.assertEqual(properties["campaign_id"]["const"], "campaign-01")
        self.assertEqual(properties["generation_mode"]["const"], "context_rich")
        self.assertEqual(properties["requested_seed_count"]["const"], 5)
        self.assertIn("requested_seed_count", schema["required"])
        self.assertEqual(properties["snapshot"]["properties"]["path"]["const"], snapshot["path"])
        self.assertEqual(
            properties["terminal"]["enum"],
            ["SEED-BATCH-COMPLETE", "SEED-BATCH-NOVELTY-STOP"],
        )

    def test_provider_schema_removes_transport_unsupported_constraints(self) -> None:
        snapshot = {"path": "runs/agents/test/snapshot.json", "sha256": "b" * 64}
        schema = generator.provider_schema("campaign-02", "failure_dual", snapshot)
        seed = schema["$defs"]["seed"]
        self.assertIn("title", seed["properties"])
        self.assertNotIn("maxLength", seed["properties"]["title"])
        self.assertNotIn("title", schema)
        self.assertNotIn("$schema", schema)

    def test_provider_schema_types_every_const_and_enum(self) -> None:
        snapshot = {"path": "runs/agents/test/snapshot.json", "sha256": "e" * 64}
        schema = generator.provider_schema("campaign-03", "recombination", snapshot)

        def inspect(value) -> None:
            if isinstance(value, dict):
                if "const" in value or "enum" in value:
                    self.assertIn("type", value)
                for item in value.values():
                    inspect(item)
            elif isinstance(value, list):
                for item in value:
                    inspect(item)

        inspect(schema)

    def test_prompt_states_cross_field_model_invariants(self) -> None:
        snapshot = {"path": "runs/agents/test/snapshot.json", "sha256": "f" * 64}
        prompt = generator.make_prompt(
            "campaign-model-rule",
            "failure_dual",
            snapshot,
            generator.ROOT / "runs/agents/test-prompt",
        )
        self.assertIn("copy the exact same tier string", prompt)
        self.assertIn("set `bridge_ref` to null", prompt)
        self.assertIn("`verified_bridge` always requires", prompt)
        self.assertIn("root-admitted", prompt)
        self.assertIn("inferred` only as question-generating residue", prompt)

    def test_stop_batch_validates_without_promoting_a_claim(self) -> None:
        packet = {
            "campaign_id": "campaign-stop",
            "generation_mode": "context_rich",
            "snapshot": {"path": "runs/agents/test/snapshot.json", "sha256": "c" * 64},
        }
        batch = generator.stop_batch(packet, "SEED-BATCH-PROVIDER-STOP")
        generator.campaign.validate_seed_batch(batch, authenticate=False)
        self.assertEqual(batch["seeds"], [])
        self.assertEqual(batch["claim_level"], "proposal")

    def test_provider_command_is_read_only_single_agent_sol_max(self) -> None:
        packet = {
            "provider": {"model": "gpt-5.6-sol", "reasoning_effort": "max"}
        }
        batch_dir = generator.ROOT / "runs/agents/test-command"
        argv = generator.provider_argv(packet, batch_dir)
        joined = " ".join(argv)
        self.assertIn("gpt-5.6-sol", argv)
        self.assertIn('model_reasoning_effort="max"', argv)
        self.assertIn('web_search="live"', argv)
        self.assertIn("agents.enabled=false", argv)
        self.assertIn("--sandbox read-only", joined)
        self.assertIn("--ephemeral", argv)
        self.assertIn("--skip-git-repo-check", argv)
        self.assertNotIn("danger-full-access", argv)

    def test_active_reserve_requires_exact_consumption_receipt(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            campaign_id = "reserve-test"
            batch_dir = service_dir / "batches" / campaign_id
            batch_dir.mkdir(parents=True)
            snapshot_path = service_dir / "snapshot.json"
            generator.atomic_json(snapshot_path, {"snapshot": "test"})
            seed_batch = json.loads(
                (generator.ROOT / "templates/research-seed-batch.json").read_text(
                    encoding="utf-8"
                )
            )
            seed_batch["campaign_id"] = campaign_id
            seed_batch["snapshot"] = generator.file_receipt(snapshot_path)
            seed_path = batch_dir / "seed-batch.json"
            generator.atomic_json(seed_path, seed_batch)
            migration = {
                "entries": [[campaign_id]],
                "path_templates": {
                    "queue": "runs/agents/unused/{campaign_id}.json"
                },
            }
            with mock.patch.object(
                generator,
                "validate_accounting_migration_root",
                return_value=(migration, [], []),
            ):
                self.assertEqual(len(generator.active_reserve(service_dir)), 1)
                consumed_path = service_dir / "consumed" / f"{campaign_id}.json"
                generator.atomic_json(consumed_path, {"campaign_id": campaign_id})
                with self.assertRaises(generator.ServiceError):
                    generator.active_reserve(service_dir)
                generator.atomic_json(
                    consumed_path,
                    {
                        "schema_version": 1,
                        "protocol": "continuous-idea-generator-v2.1",
                        "campaign_id": campaign_id,
                        "consumed_at": datetime.now(timezone.utc).isoformat(),
                        "seed_batch": generator.file_receipt(seed_path),
                        "reconciliation_ref": "docs/wayfinder/tickets/test.md",
                        "meaning": "reserve released; this receipt does not admit or schedule any seed",
                    },
                )
                self.assertEqual(generator.active_reserve(service_dir), [])

    def test_claim_and_feedback_change_only_one_seed_state(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            campaign_id = "individual-state-test"
            authorization_path, authorization = self.configured_authorization(
                service_dir
            )
            self.completed_provider_attempt(
                service_dir,
                authorization_path=authorization_path,
                authorization=authorization,
                campaign_id=campaign_id,
                terminal="SEED-BATCH-COMPLETE",
                seed_count=2,
            )
            seed_path = service_dir / "batches" / campaign_id / "seed-batch.json"
            self.assertEqual(
                sum(item["seed_count"] for item in generator.active_reserve(service_dir)),
                2,
            )

            brief = json.loads(
                (generator.ROOT / "templates/research-development-brief.json").read_text(
                    encoding="utf-8"
                )
            )
            batch = json.loads(seed_path.read_text(encoding="utf-8"))
            selected_seed = batch["seeds"][0]
            first_test = selected_seed["first_test"]
            brief["brief_id"] = "individual-state-test-S01-probe"
            brief["task_id"] = brief["brief_id"]
            brief["seed"] = {
                "batch_path": generator.repo_relative(seed_path),
                "batch_sha256": generator.sha256(seed_path),
                "seed_id": "S01",
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
                "seed_id": "S01",
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
            brief_path = service_dir / "investigation" / "development-brief.json"
            generator.atomic_json(brief_path, brief)
            evidence_path = service_dir / "investigation" / "evidence.md"
            receipt_path = service_dir / "investigation" / "development-receipt.json"
            reconciliation_path = (
                service_dir / "investigation" / "root-reconciliation.json"
            )
            feedback_path = service_dir / "investigation" / "feedback.json"
            task_path = service_dir / "investigation" / "task.json"
            task = self.standing_first_test_task(
                service_dir,
                brief=brief,
                brief_path=brief_path,
                seed_path=seed_path,
                context_paths=[map_path],
                evidence_path=evidence_path,
            )
            generator.atomic_json(task_path, task)
            with mock.patch("builtins.print"):
                generator.command_claim(
                    SimpleNamespace(
                        service_dir=service_dir,
                        campaign_id=campaign_id,
                        seed_id="S01",
                        seed_batch_sha256=generator.sha256(seed_path),
                        development_brief=brief_path,
                        development_brief_sha256=generator.sha256(brief_path),
                        task_packet=task_path,
                        task_packet_sha256=generator.sha256(task_path),
                    )
                )
            inventory = generator.seed_inventory(service_dir)
            self.assertEqual(
                {item["seed_id"]: item["state"] for item in inventory},
                {"S01": "investigating", "S02": "ready"},
            )

            evidence_path.write_text(
                '{"terminal":"NO_DISCRIMINATING_SIGNAL"}\n', encoding="utf-8"
            )
            receipt = json.loads(
                (generator.ROOT / "templates/research-development-receipt.json").read_text(
                    encoding="utf-8"
                )
            )
            receipt["brief_id"] = brief["brief_id"]
            receipt["brief_sha256"] = generator.sha256(brief_path)
            event = receipt["evidence_events"][0]
            event["artifact"] = generator.file_receipt(evidence_path)
            event["binding"] = {
                "primary_contract_id": contract["contract_id"],
                "subject": "primary_claim",
                "subject_contract_id": contract["contract_id"],
                "model_contract_id": contract["model_contract_id"],
                "scope_contract_id": contract["scope"]["scope_contract_id"],
                "polarity": "observes",
                "damage_scope_reached": "candidate-local",
            }
            event_core = {
                key: value
                for key, value in event.items()
                if key not in {"event_id", "verification_receipt"}
            }
            event["event_id"] = generator.canonical_json_sha256(event_core)
            envelope_path, output_bytes = self.write_execution_envelope(
                brief=brief,
                brief_path=brief_path,
                task=task,
                task_path=task_path,
                claim_path=generator.seed_claim_path(
                    service_dir, campaign_id, "S01"
                ),
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
            generator.atomic_json(receipt_path, receipt)
            evidence = {
                "level": "proposal",
                "event_ids": [event["event_id"]],
                "contract_id": contract["contract_id"],
                "model_contract_id": contract["model_contract_id"],
                "scope_contract_id": contract["scope"]["scope_contract_id"],
                "damage_scope": "candidate-local",
            }
            reconciled_at = datetime.now(timezone.utc).isoformat()
            claim_path = generator.seed_claim_path(service_dir, campaign_id, "S01")
            not_established = {
                "status": "not-established",
                "text": None,
                "subject_contract_id": None,
                "evidence_event_ids": [],
                "learning_claim_id": None,
            }
            feedback = {
                "schema_version": 3,
                "feedback_id": f"{campaign_id}:S01",
                "seed": {
                    "registry_id": f"continuous:{campaign_id}:S01",
                    "campaign_id": campaign_id,
                    "seed_id": "S01",
                    "seed_batch": generator.file_receipt(seed_path),
                },
                "investigation": {
                    "brief_id": brief["brief_id"],
                    "brief_sha256": generator.sha256(brief_path),
                    "development_receipt": generator.file_receipt(receipt_path),
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
                reconciliation_path,
                {
                    "schema_version": 2,
                    "protocol": "research-root-reconciliation-v2",
                    "feedback_id": f"{campaign_id}:S01",
                    "reconciled_at": reconciled_at,
                    "seed_claim": generator.file_receipt(claim_path),
                    "development_receipt": generator.file_receipt(receipt_path),
                    "admitted_feedback_core_sha256": feedback_core_sha256,
                    "standing_first_test": copy.deepcopy(brief["authority"]),
                    "decision": "admit-immutable-feedback",
                },
            )
            feedback["root_admission"] = {
                "reconciled_at": reconciled_at,
                "admitted_feedback_core_sha256": feedback_core_sha256,
                "reconciliation": generator.file_receipt(reconciliation_path),
            }
            unsupported = copy.deepcopy(feedback)
            unsupported["evidence"]["level"] = "compiling_theorem"
            unsupported["evidence"]["event_ids"] = []
            unsupported["proof_distance"].update(
                {
                    "net_proof_movement": "forward",
                    "demonstrably_smaller": True,
                }
            )
            unsupported_path = (
                service_dir / "investigation" / "unsupported-feedback.json"
            )
            generator.atomic_json(unsupported_path, unsupported)
            claim = generator.validate_seed_claim(
                claim_path,
                campaign_id=campaign_id,
                seed_id="S01",
                seed_path=seed_path,
            )
            with self.assertRaisesRegex(
                generator.ServiceError,
                "feedback evidence level is invalid",
            ):
                generator.validate_investigation_feedback(
                    unsupported_path,
                    claim=claim,
                    campaign_id=campaign_id,
                    seed_id="S01",
                    seed_path=seed_path,
                )

            false_verified = copy.deepcopy(feedback)
            false_verified["learned"]["surviving_structure"] = {
                "status": "verified",
                "text": "A proposal-only event cannot verify this structure.",
                "subject_contract_id": contract["contract_id"],
                "evidence_event_ids": [event["event_id"]],
                "learning_claim_id": "f" * 64,
            }
            false_verified_path = (
                service_dir / "investigation" / "false-verified-feedback.json"
            )
            generator.atomic_json(false_verified_path, false_verified)
            with self.assertRaisesRegex(
                generator.ServiceError,
                r"cannot (?:be verifier-established|verify mathematical learning|be verified by a Ticket-0119 standing first test)",
            ):
                generator.validate_investigation_feedback(
                    false_verified_path,
                    claim=claim,
                    campaign_id=campaign_id,
                    seed_id="S01",
                    seed_path=seed_path,
                )
            broad_damage = copy.deepcopy(feedback)
            broad_damage["evidence"]["damage_scope"] = "architecture-level"
            broad_damage_path = (
                service_dir / "investigation" / "broad-damage-feedback.json"
            )
            generator.atomic_json(broad_damage_path, broad_damage)
            with self.assertRaisesRegex(
                generator.ServiceError, "damage scope is invalid"
            ):
                generator.validate_investigation_feedback(
                    broad_damage_path,
                    claim=claim,
                    campaign_id=campaign_id,
                    seed_id="S01",
                    seed_path=seed_path,
                )
            generator.atomic_json(feedback_path, feedback)
            with mock.patch("builtins.print"):
                generator.command_reconcile(
                    SimpleNamespace(
                        service_dir=service_dir,
                        campaign_id=campaign_id,
                        seed_id="S01",
                        seed_batch_sha256=generator.sha256(seed_path),
                        feedback=feedback_path,
                        feedback_sha256=generator.sha256(feedback_path),
                    )
                )
            inventory = generator.seed_inventory(service_dir)
            self.assertEqual(
                {item["seed_id"]: item["state"] for item in inventory},
                {"S01": "investigated", "S02": "ready"},
            )

    def test_literal_seed_fingerprint_ignores_cosmetic_identity(self) -> None:
        batch = json.loads(
            (generator.ROOT / "templates/research-seed-batch.json").read_text(
                encoding="utf-8"
            )
        )
        first = batch["seeds"][0]
        renamed = copy.deepcopy(first)
        renamed["seed_id"] = "RENAMED"
        renamed["title"] = "Cosmetically renamed"
        renamed["lineage"]["parent_refs"] = ["UNRELATED-LABEL"]
        self.assertEqual(
            generator.seed_fingerprint(first), generator.seed_fingerprint(renamed)
        )

    def test_claim_changes_service_scoped_learning_epoch(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with (
            tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw,
            tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as other_raw,
        ):
            service_dir = Path(raw)
            other_service = Path(other_raw)
            campaign_id = "epoch-claim-test"
            seed_path = self.authenticated_seed_batch(
                service_dir, campaign_id, 1
            )
            before = generator.build_sol_idea_packet.current_feedback_epoch_sha256(
                service_dir
            )
            other_before = (
                generator.build_sol_idea_packet.current_feedback_epoch_sha256(
                    other_service
                )
            )
            brief_path = service_dir / "investigation" / "brief.json"
            generator.atomic_json(brief_path, {"brief": "epoch fixture"})
            claim_path = generator.seed_claim_path(
                service_dir, campaign_id, "S01"
            )
            generator.atomic_json(
                claim_path,
                {
                    "seed": {
                        "campaign_id": campaign_id,
                        "seed_id": "S01",
                        "seed_batch": generator.file_receipt(seed_path),
                    },
                    "development_brief": generator.file_receipt(brief_path),
                },
            )
            after = generator.build_sol_idea_packet.current_feedback_epoch_sha256(
                service_dir
            )
            other_after = (
                generator.build_sol_idea_packet.current_feedback_epoch_sha256(
                    other_service
                )
            )
            self.assertNotEqual(before, after)
            self.assertEqual(other_before, other_after)

    def test_post_provider_filter_drops_prior_literal_core(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            prior = json.loads(
                (generator.ROOT / "templates/research-seed-batch.json").read_text(
                    encoding="utf-8"
                )
            )
            prior["campaign_id"] = "prior"
            prior_fingerprint = generator.seed_fingerprint(prior["seeds"][0])
            known_memory = {
                prior_fingerprint: {"campaign_id": "prior", "seed_id": "S01"}
            }
            current = copy.deepcopy(prior)
            current["campaign_id"] = "current"
            current["seeds"][0]["seed_id"] = "RENAMED"
            current["seeds"][0]["title"] = "Renamed duplicate"
            source_path = service_dir / "current-source.json"
            generator.atomic_json(source_path, current)
            filtered, report = generator.deduplicate_provider_batch(
                service_dir,
                current,
                known_memory=known_memory,
                source_receipt=generator.file_receipt(source_path),
            )
            self.assertEqual(filtered["terminal"], "SEED-BATCH-NOVELTY-STOP")
            self.assertEqual(filtered["seeds"], [])
            self.assertEqual(
                filtered["generation_metrics"]["literal_duplicates_removed"], 1
            )
            self.assertEqual(report["accepted_seed_count"], 0)
            self.assertEqual(
                report["transform_protocol"], generator.DEDUP_TRANSFORM_PROTOCOL
            )
            self.assertEqual(report["source"], generator.file_receipt(source_path))
            self.assertEqual(report["prior_fingerprint_count"], 1)
            self.assertEqual(
                report["prior_fingerprint_memory_sha256"],
                generator.canonical_json_sha256(
                    [
                        {
                            "fingerprint": prior_fingerprint,
                            "campaign_id": "prior",
                            "seed_id": "S01",
                        }
                    ]
                ),
            )
            self.assertEqual(report["accepted"], [])

    def test_root_import_rejects_literal_core_in_generated_memory(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            run_root = Path(raw)
            service_dir = run_root / "service"
            source_run = run_root / "root-source"
            approval_ref = "Ticket 0119 test"
            authorization_path, authorization = self.configured_authorization(
                service_dir, approval_ref=approval_ref
            )
            prior_campaign = "root-dedup-prior"
            self.completed_provider_attempt(
                service_dir,
                authorization_path=authorization_path,
                authorization=authorization,
                campaign_id=prior_campaign,
                terminal="SEED-BATCH-COMPLETE",
                seed_count=1,
            )
            prior_path = (
                service_dir / "batches" / prior_campaign / "seed-batch.json"
            )
            consumed_path = service_dir / "consumed" / f"{prior_campaign}.json"
            generator.atomic_json(
                consumed_path,
                {
                    "schema_version": 1,
                    "protocol": "continuous-idea-generator-v2.1",
                    "campaign_id": prior_campaign,
                    "consumed_at": datetime.now(timezone.utc).isoformat(),
                    "seed_batch": generator.file_receipt(prior_path),
                    "reconciliation_ref": "docs/wayfinder/tickets/0119-adopt-self-refilling-investigation-loop.md",
                    "meaning": "reserve released; this receipt does not admit or schedule any seed",
                },
            )
            snapshot_dir = source_run / "snapshot"
            self.build_authenticated_snapshot(
                service_dir,
                snapshot_dir,
                campaign_id="20260831-root-seeds-001",
                purpose="root_fallback",
                authorization_path=authorization_path,
                authorization=authorization,
            )
            summary_path = snapshot_dir / "packet-summary.json"
            batch = json.loads(prior_path.read_text(encoding="utf-8"))
            batch["campaign_id"] = "20260831-root-seeds-001"
            batch["requested_seed_count"] = 1
            batch["terminal"] = "SEED-BATCH-COMPLETE"
            batch["snapshot"] = generator.file_receipt(summary_path)
            source_path = source_run / "seed-batch.json"
            generator.atomic_json(source_path, batch)
            semantic_path = self.root_semantic_screen(
                service_dir,
                batch_path=source_path,
                authorization_path=authorization_path,
                approval_ref=approval_ref,
            )
            args = SimpleNamespace(
                service_dir=service_dir,
                seed_batch=source_path,
                seed_batch_sha256=generator.sha256(source_path),
                semantic_screen=semantic_path,
                semantic_screen_sha256=generator.sha256(semantic_path),
                approval_ref=approval_ref,
            )
            with self.assertRaisesRegex(
                generator.ServiceError, "repeats generated seed memory"
            ):
                generator.command_import_root_batch(args)
            self.assertFalse(
                (service_dir / "batches" / batch["campaign_id"]).exists()
            )

    def test_positive_root_import_is_batch_screen_and_approval_bound(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            run_root = Path(raw)
            service_dir = run_root / "service"
            source_run = run_root / "root-source"
            approval_ref = "Ticket 0119 root import test"
            authorization_path, authorization = self.configured_authorization(
                service_dir, approval_ref=approval_ref
            )
            campaign_id = "20260831-root-seeds-positive"
            snapshot_dir = source_run / "snapshot"
            self.build_authenticated_snapshot(
                service_dir,
                snapshot_dir,
                campaign_id=campaign_id,
                purpose="root_fallback",
                authorization_path=authorization_path,
                authorization=authorization,
            )
            summary_path = snapshot_dir / "packet-summary.json"
            batch = json.loads(
                (generator.ROOT / "templates/research-seed-batch.json").read_text(
                    encoding="utf-8"
                )
            )
            batch["campaign_id"] = campaign_id
            batch["requested_seed_count"] = 1
            batch["terminal"] = "SEED-BATCH-COMPLETE"
            batch["snapshot"] = generator.file_receipt(summary_path)
            source_path = source_run / "seed-batch.json"
            generator.atomic_json(source_path, batch)
            screen_path = self.root_semantic_screen(
                service_dir,
                batch_path=source_path,
                authorization_path=authorization_path,
                approval_ref=approval_ref,
            )
            args = SimpleNamespace(
                service_dir=service_dir,
                seed_batch=source_path,
                seed_batch_sha256=generator.sha256(source_path),
                semantic_screen=screen_path,
                semantic_screen_sha256=generator.sha256(screen_path),
                approval_ref=approval_ref,
            )
            with mock.patch("builtins.print"):
                generator.command_import_root_batch(args)
            destination = service_dir / "batches" / campaign_id / "seed-batch.json"
            result_path = destination.parent / "result-receipt.json"
            imported = json.loads(destination.read_text(encoding="utf-8"))
            generator.validate_v3_result_receipt(
                service_dir, result_path, destination, imported
            )
            result = json.loads(result_path.read_text(encoding="utf-8"))
            accounting = generator.validate_accounting_chain(
                service_dir, authorization
            )
            checkpoint = result["root_commit"]["accounting_checkpoint"]
            self.assertEqual(checkpoint["baseline"], accounting["baseline"])
            self.assertEqual(checkpoint["event_count"], accounting["event_count"])
            self.assertEqual(checkpoint["charged_count"], accounting["charged_count"])
            self.assertEqual(
                checkpoint["unresolved_attempt_ordinal"],
                accounting["unresolved_attempt_ordinal"],
            )
            result["approval_ref"] = "different approval"
            generator.atomic_json(result_path, result)
            with self.assertRaisesRegex(
                generator.ServiceError, "not bound to its import packet"
            ):
                generator.validate_v3_result_receipt(
                    service_dir, result_path, destination, imported
                )

    def test_snapshot_receipt_requires_cold_builder_reproduction(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            run_root = Path(raw)
            service_dir = run_root / "service"
            authorization_path, authorization = self.configured_authorization(
                service_dir
            )
            campaign_id = "snapshot-cold-replay"
            snapshot_dir = run_root / "source" / "snapshot"
            self.build_authenticated_snapshot(
                service_dir,
                snapshot_dir,
                campaign_id=campaign_id,
                purpose="root_fallback",
                authorization_path=authorization_path,
                authorization=authorization,
            )
            summary_path = snapshot_dir / "packet-summary.json"
            generator.validate_snapshot_build_receipt(
                summary_path,
                service_dir=service_dir,
                campaign_id=campaign_id,
                purpose="root_fallback",
            )
            receipt_path = (
                snapshot_dir
                / generator.build_sol_idea_packet.SNAPSHOT_BUILD_RECEIPT_NAME
            )
            forged = json.loads(receipt_path.read_text(encoding="utf-8"))
            forged["invocation"]["max_inline_bytes"] = 2048
            generator.atomic_json(receipt_path, forged)
            with self.assertRaisesRegex(
                generator.ServiceError, "not reproduced by the current builder"
            ):
                generator.validate_snapshot_build_receipt(
                    summary_path,
                    service_dir=service_dir,
                    campaign_id=campaign_id,
                    purpose="root_fallback",
                )

    def test_v3_inventory_rejects_partial_result_receipt(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            self.configured_authorization(service_dir)
            seed_path = self.authenticated_seed_batch(
                service_dir, "partial-result", 1
            )
            batch = json.loads(seed_path.read_text(encoding="utf-8"))
            batch["requested_seed_count"] = 1
            batch["terminal"] = "SEED-BATCH-COMPLETE"
            generator.atomic_json(seed_path, batch)
            generator.atomic_json(
                seed_path.parent / "result-receipt.json",
                {"receipts": {"seed_batch": generator.file_receipt(seed_path)}},
            )
            with self.assertRaisesRegex(
                generator.ServiceError, "unexpected closed contract"
            ):
                generator.seed_inventory(service_dir)

    def test_campaign_identity_cannot_escape_service_tree(self) -> None:
        for value in ("../escape-root-seeds-x", "/tmp/root-seeds-x", "a/b"):
            with self.assertRaises(generator.ServiceError):
                generator.safe_leaf_id(value, "campaign_id")

    def test_deficit_bound_dedup_uses_frozen_request(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            payload = json.loads(
                (generator.ROOT / "templates/research-seed-batch.json").read_text(
                    encoding="utf-8"
                )
            )
            payload["campaign_id"] = "deficit-two"
            payload["requested_seed_count"] = 1
            payload["terminal"] = "SEED-BATCH-COMPLETE"
            source_path = service_dir / "deficit-two-source.json"
            generator.atomic_json(source_path, payload)
            filtered, report = generator.deduplicate_provider_batch(
                service_dir,
                payload,
                1,
                known_memory={},
                source_receipt=generator.file_receipt(source_path),
            )
            self.assertEqual(filtered["terminal"], "SEED-BATCH-COMPLETE")
            self.assertEqual(report["requested_seed_count"], 1)
            self.assertEqual(report["prior_fingerprint_count"], 0)
            self.assertEqual(
                report["prior_fingerprint_memory_sha256"],
                generator.canonical_json_sha256([]),
            )
            self.assertEqual(report["source"], generator.file_receipt(source_path))
            self.assertEqual(
                report["accepted"],
                [
                    {
                        "seed_id": payload["seeds"][0]["seed_id"],
                        "fingerprint": generator.seed_fingerprint(
                            payload["seeds"][0]
                        ),
                    }
                ],
            )
            with self.assertRaises(generator.ServiceError):
                generator.deduplicate_provider_batch(
                    service_dir,
                    payload,
                    2,
                    known_memory={},
                    source_receipt=generator.file_receipt(source_path),
                )

    def test_generation_gate_requests_only_exact_deficit(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization_path, authorization = self.configured_authorization(
                service_dir
            )
            for campaign_id, count in (("ready-five", 5), ("ready-three", 3)):
                self.completed_provider_attempt(
                    service_dir,
                    authorization_path=authorization_path,
                    authorization=authorization,
                    campaign_id=campaign_id,
                    terminal="SEED-BATCH-COMPLETE",
                    seed_count=count,
                )
            gate = generator.generation_gate(service_dir, authorization)
            self.assertTrue(gate["ready"])
            self.assertEqual(gate["unreconciled_seeds"], 8)
            self.assertEqual(gate["seed_deficit"], 2)

    def test_nine_ready_requests_one_and_ten_ready_quiesces(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization_path, authorization = self.configured_authorization(
                service_dir
            )
            for campaign_id, count in (("ready-five", 5), ("ready-four", 4)):
                self.completed_provider_attempt(
                    service_dir,
                    authorization_path=authorization_path,
                    authorization=authorization,
                    campaign_id=campaign_id,
                    terminal="SEED-BATCH-COMPLETE",
                    seed_count=count,
                )
            gate = generator.generation_gate(service_dir, authorization)
            self.assertTrue(gate["ready"])
            self.assertEqual(gate["seed_deficit"], 1)
            self.completed_provider_attempt(
                service_dir,
                authorization_path=authorization_path,
                authorization=authorization,
                campaign_id="ready-one",
                terminal="SEED-BATCH-COMPLETE",
                seed_count=1,
            )
            full = generator.generation_gate(service_dir, authorization)
            self.assertFalse(full["ready"])
            self.assertEqual(full["seed_deficit"], 0)
            self.assertEqual(full["reason"], "ready-seed-target-met")

    def test_ready_seed_deficit_drives_v3_refill(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization_path, authorization = self.configured_authorization(
                service_dir
            )
            self.completed_provider_attempt(
                service_dir,
                authorization_path=authorization_path,
                authorization=authorization,
                campaign_id="one-unreconciled",
                terminal="SEED-BATCH-COMPLETE",
                seed_count=1,
            )
            gate = generator.generation_gate(service_dir, authorization)
            self.assertTrue(gate["ready"])
            self.assertEqual(gate["unreconciled_batches"], 1)
            self.assertEqual(gate["unreconciled_seeds"], 1)
            self.assertEqual(gate["seed_deficit"], 9)

    def test_recent_calls_are_telemetry_not_a_daily_gate(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization_path, authorization = self.configured_authorization(
                service_dir
            )
            for ordinal in range(2):
                self.completed_provider_attempt(
                    service_dir,
                    authorization_path=authorization_path,
                    authorization=authorization,
                    campaign_id=f"cycle-{ordinal}",
                    terminal="SEED-BATCH-COMPLETE",
                    seed_count=1,
                )
            gate = generator.generation_gate(service_dir, authorization)
            self.assertTrue(gate["ready"])
            self.assertEqual(gate["reason"], "ready-seed-deficit")
            self.assertEqual(gate["calls_last_24h"], 2)

    def test_two_provider_stops_open_circuit(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization_path, authorization = self.configured_authorization(
                service_dir
            )
            for ordinal in range(2):
                self.completed_provider_attempt(
                    service_dir,
                    authorization_path=authorization_path,
                    authorization=authorization,
                    campaign_id=f"stop-{ordinal}",
                    terminal="SEED-BATCH-PROVIDER-STOP",
                    seed_count=0,
                )
            gate = generator.generation_gate(service_dir, authorization)
            self.assertFalse(gate["ready"])
            self.assertEqual(gate["reason"], "provider-stop-circuit-open")

    def test_two_zero_seed_batches_open_circuit(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization_path, authorization = self.configured_authorization(
                service_dir
            )
            for ordinal in range(2):
                self.completed_provider_attempt(
                    service_dir,
                    authorization_path=authorization_path,
                    authorization=authorization,
                    campaign_id=f"zero-{ordinal}",
                    terminal="SEED-BATCH-NOVELTY-STOP",
                    seed_count=0,
                )
            gate = generator.generation_gate(service_dir, authorization)
            self.assertFalse(gate["ready"])
            self.assertEqual(gate["reason"], "zero-seed-circuit-open")

    def test_packet_mismatch_cannot_reset_either_failure_circuit(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        cases = (
            (
                "SEED-BATCH-PROVIDER-STOP",
                "provider-stop-circuit-open",
                "consecutive_provider_stops",
            ),
            (
                "SEED-BATCH-NOVELTY-STOP",
                "zero-seed-circuit-open",
                "consecutive_zero_seed_batches",
            ),
        )
        for repeated_terminal, expected_reason, counter in cases:
            with self.subTest(terminal=repeated_terminal):
                with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
                    service_dir = Path(raw)
                    terminals = [
                        repeated_terminal,
                        "SEED-BATCH-PACKET-MISMATCH",
                        repeated_terminal,
                    ]
                    records = [
                        {
                            "campaign_id": f"circuit-{ordinal}",
                            "provider_invoked": True,
                            "result": {"terminal": terminal, "seed_count": 0},
                        }
                        for ordinal, terminal in enumerate(terminals)
                    ]
                    authorization = {
                        "limits": {
                            "ready_seed_target": 10,
                            "max_total_invocations": 100,
                            "max_consecutive_provider_stops": 2,
                            "max_consecutive_zero_seed_batches": 2,
                        }
                    }
                    with (
                        mock.patch.object(
                            generator,
                            "validate_accounting_chain",
                            return_value={"charged_count": len(records)},
                        ),
                        mock.patch.object(
                            generator,
                            "authorized_cycle_records",
                            return_value=records,
                        ),
                    ):
                        safety = generator.provider_safety_status(
                            service_dir, authorization
                        )
                    self.assertFalse(safety["allowed"])
                    self.assertEqual(safety["reason"], expected_reason)
                    self.assertEqual(safety[counter], 2)

    def test_pending_packet_cannot_launch_after_lifetime_gate_closes(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization_path, authorization = self.configured_authorization(
                service_dir
            )
            entry_path, packet_path, _packet = self.frozen_queue(
                service_dir,
                authorization_path=authorization_path,
                authorization=authorization,
                campaign_id="pending-cap",
            )
            batch_dir = packet_path.parent
            stopped = {
                "terminal": "SEED-BATCH-PACKET-MISMATCH",
                "campaign_id": "pending-cap",
            }
            with (
                mock.patch.object(
                    generator,
                    "provider_safety_status",
                    return_value={
                        "allowed": False,
                        "reason": "standing-total-invocation-cap",
                        "total_invocations": 100,
                    },
                ),
                mock.patch.object(
                    generator, "finalize_provider", return_value=stopped
                ) as finalize,
                mock.patch.object(
                    generator,
                    "codex_version",
                    return_value=authorization["provider"]["cli_version"],
                ),
                mock.patch.object(generator.subprocess, "Popen") as popen,
            ):
                result = generator.run_provider(
                    service_dir, entry_path, {}, {"stop": False}
                )
            self.assertEqual(result, stopped)
            self.assertIn(
                "standing-total-invocation-cap", finalize.call_args.args[4]
            )
            popen.assert_not_called()
            self.assertFalse((batch_dir / "attempt.json").exists())

    def test_pending_packet_cannot_use_inactive_authorization(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            batch_dir = service_dir / "batches" / "inactive-auth"
            batch_dir.mkdir(parents=True)
            packet_path = batch_dir / "packet.json"
            entry_path = service_dir / "queue" / "inactive-auth.json"
            old_auth = service_dir / "old-authorization.json"
            active_auth = service_dir / "active-authorization-v3.json"
            for path, label in (
                (packet_path, "packet"),
                (entry_path, "entry"),
                (old_auth, "old"),
                (active_auth, "active"),
            ):
                generator.atomic_json(path, {"fixture": label})
            packet = {
                "campaign_id": "inactive-auth",
                "requested_seed_count": 1,
                "standing_authorization": generator.file_receipt(old_auth),
                "feedback_epoch_sha256": "e" * 64,
                "limits": {"wall_minutes": 1, "memory_gib": 1, "output_gib": 0.01},
            }
            authorization = {"limits": {"ready_seed_target": 10}}
            stopped = {
                "terminal": "SEED-BATCH-PACKET-MISMATCH",
                "campaign_id": "inactive-auth",
            }
            with (
                mock.patch.object(
                    generator,
                    "authenticate_queue",
                    return_value=({}, packet_path, packet),
                ),
                mock.patch.object(
                    generator,
                    "active_standing_authorization",
                    return_value=(active_auth, authorization),
                ),
                mock.patch.object(
                    generator, "finalize_provider", return_value=stopped
                ),
                mock.patch.object(generator.subprocess, "Popen") as popen,
            ):
                result = generator.run_provider(
                    service_dir, entry_path, {}, {"stop": False}
                )
            self.assertEqual(result, stopped)
            popen.assert_not_called()
            self.assertFalse((batch_dir / "attempt.json").exists())

    def test_attempted_provider_output_is_suppressed_after_learning_drift(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            campaign_id = "attempted-stale"
            _authorization_path, _authorization, packet_path, _queue_path = (
                self.ledgered_attempt(service_dir, campaign_id=campaign_id)
            )
            packet = generator.verify_packet(packet_path, mode="historical")
            batch_dir = packet_path.parent
            raw_response = json.loads(
                (generator.ROOT / "templates/research-seed-batch.json").read_text(
                    encoding="utf-8"
                )
            )
            raw_response.update(
                {
                    "campaign_id": campaign_id,
                    "generation_mode": "context_rich",
                    "requested_seed_count": 1,
                    "snapshot": packet["snapshot"],
                    "terminal": "SEED-BATCH-COMPLETE",
                }
            )
            generator.atomic_json(batch_dir / "raw-response.json", raw_response)
            with (
                mock.patch.object(generator, "complete_invocation_event"),
                mock.patch.object(
                    generator,
                    "snapshot_currency",
                    return_value=(False, ["learning_epoch_changed"]),
                ),
            ):
                started_at = json.loads(
                    (batch_dir / "attempt.json").read_text(encoding="utf-8")
                )["started_at"]
                result = generator.finalize_provider(
                    batch_dir,
                    packet_path,
                    packet,
                    0,
                    None,
                    started_at,
                )
                self.assertEqual(result["terminal"], "SEED-BATCH-PACKET-MISMATCH")
                admitted = json.loads(
                    (batch_dir / "seed-batch.json").read_text(encoding="utf-8")
                )
                self.assertEqual(admitted["seeds"], [])
                self.assertEqual(generator.active_reserve(service_dir), [])

    def test_invocation_history_corruption_fails_closed(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            batch_dir = service_dir / "batches" / "missing-attempt"
            batch_dir.mkdir(parents=True)
            generator.atomic_json(
                batch_dir / "packet.json",
                {
                    "protocol": "continuous-idea-generator-v2.1",
                    "campaign_id": "missing-attempt",
                },
            )
            generator.atomic_json(
                batch_dir / "result-receipt.json",
                {
                    "campaign_id": "missing-attempt",
                    "terminal": "SEED-BATCH-PROVIDER-STOP",
                    "provider_exit_code": 1,
                },
            )
            with self.assertRaisesRegex(
                generator.ServiceError, "missing an attempt receipt"
            ):
                generator.authorized_cycle_records(service_dir, {"limits": {}})

    def test_unresolved_ledger_attempt_blocks_fresh_provider_spending(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            _path, authorization, _packet, _queue = self.ledgered_attempt(
                service_dir
            )
            safety = generator.provider_safety_status(service_dir, authorization)
            self.assertFalse(safety["allowed"])
            self.assertEqual(safety["reason"], "unresolved-attempt-circuit-open")
            self.assertEqual(safety["total_invocations"], 1)
            self.assertEqual(safety["unresolved_attempts"], 1)

    def test_operator_closes_exact_charged_prelaunch_stop_without_provider_evidence(
        self,
    ) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            _path, authorization, packet_path, queue_path = self.ledgered_attempt(
                service_dir, campaign_id="operator-prelaunch-stop"
            )
            with (
                mock.patch.object(generator, "daemon_receipt", return_value=None),
                mock.patch.object(generator, "systemd_main_pid", return_value=None),
            ):
                resolved = generator.resolve_charged_prelaunch_stop(
                    service_dir,
                    campaign_id="operator-prelaunch-stop",
                    approval_ref="test-standing-approval",
                    reason="ledger transition failed before provider acknowledgement",
                )

            accounting = generator.validate_accounting_chain(
                service_dir, authorization
            )
            record = accounting["closed_v3_by_campaign"][
                "operator-prelaunch-stop"
            ]
            outcome_path = generator.authenticate_receipt(
                record["outcome_event"], "test prelaunch-stop outcome"
            )
            outcome = json.loads(outcome_path.read_text(encoding="utf-8"))
            self.assertEqual(resolved["charged_ordinal"], 1)
            self.assertEqual(accounting["charged_count"], 1)
            self.assertIsNone(accounting["unresolved_attempt_ordinal"])
            self.assertFalse(record["provider_invoked"])
            self.assertEqual(outcome["outcome_class"], "charged_prelaunch_stop")
            self.assertEqual(record["result"]["seed_count"], 0)
            self.assertFalse((packet_path.parent / "provider-start.json").exists())
            self.assertEqual(generator.pending_queue(service_dir), [])
            self.assertFalse(queue_path in generator.pending_queue(service_dir))

    def test_operator_prelaunch_stop_rejects_any_provider_execution_trace(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            _path, _authorization, packet_path, _queue = self.ledgered_attempt(
                service_dir, campaign_id="traced-prelaunch-stop"
            )
            (packet_path.parent / "provider.log").write_text(
                "provider boundary may have been crossed\n", encoding="utf-8"
            )
            with (
                mock.patch.object(generator, "daemon_receipt", return_value=None),
                mock.patch.object(generator, "systemd_main_pid", return_value=None),
                self.assertRaisesRegex(
                    generator.ServiceError, "provider execution artifacts"
                ),
            ):
                generator.resolve_charged_prelaunch_stop(
                    service_dir,
                    campaign_id="traced-prelaunch-stop",
                    approval_ref="test-standing-approval",
                    reason="must fail closed",
                )

    def test_migrated_charged_count_controls_safety_and_generation_gate(self) -> None:
        """The fixed 30-call baseline is lifetime spend, not zero v3 records."""
        service_dir = generator.RUNS_ROOT / "offline-migrated-count-fixture"
        authorization = {
            "limits": {
                "ready_seed_target": 10,
                "max_total_invocations": 30,
                "max_consecutive_provider_stops": 2,
                "max_consecutive_zero_seed_batches": 2,
            }
        }
        migrated_accounting = {
            "charged_count": 30,
            "records": [],
            "baseline": {"legacy_charged_count": 30},
        }
        with (
            mock.patch.object(
                generator,
                "validate_accounting_chain",
                return_value=migrated_accounting,
            ),
            mock.patch.object(generator, "authorized_cycle_records", return_value=[]),
            mock.patch.object(generator, "active_reserve", return_value=[]),
            mock.patch.object(
                generator, "pending_reserved_capacity", return_value=0
            ),
        ):
            safety = generator.provider_safety_status(
                service_dir, authorization
            )
            gate = generator.generation_gate(service_dir, authorization)
        self.assertEqual(safety["records"], [])
        self.assertEqual(safety["total_invocations"], 30)
        self.assertFalse(safety["allowed"])
        self.assertEqual(safety["reason"], "standing-total-invocation-cap")
        self.assertEqual(gate["total_invocations"], 30)
        self.assertFalse(gate["ready"])
        self.assertEqual(gate["reason"], "standing-total-invocation-cap")

    def test_partial_seed_batch_remains_pending_and_never_ready(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            _path, _authorization, _packet, queue_path = self.ledgered_attempt(
                service_dir, campaign_id="partial-finalization"
            )
            seed_path = self.authenticated_seed_batch(
                service_dir, "partial-finalization", 1
            )
            batch = json.loads(seed_path.read_text(encoding="utf-8"))
            batch["requested_seed_count"] = 1
            batch["terminal"] = "SEED-BATCH-COMPLETE"
            generator.atomic_json(seed_path, batch)
            self.assertEqual(generator.pending_queue(service_dir), [queue_path])
            self.assertEqual(generator.active_reserve(service_dir), [])

    def test_legacy_shaped_batch_outside_migration_partition_is_rejected(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            self.configured_authorization(service_dir)
            self.authenticated_seed_batch(
                service_dir, "outside-immutable-migration", 1
            )
            with self.assertRaisesRegex(
                generator.ServiceError,
                "legacy/v3 identity differs from the immutable migration partition",
            ):
                generator.seed_inventory(service_dir)

    def test_lost_batch_attempt_is_detected_by_service_ledger(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            _path, authorization, packet_path, _queue = self.ledgered_attempt(
                service_dir, campaign_id="lost-attempt"
            )
            (packet_path.parent / "attempt.json").unlink()
            with self.assertRaisesRegex(
                generator.ServiceError, "no batch attempt receipt"
            ):
                generator.validate_accounting_chain(service_dir, authorization)

    def test_missing_ledger_event_fails_closed_against_head(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            _path, authorization, _packet, _queue = self.ledgered_attempt(
                service_dir, campaign_id="lost-event"
            )
            event = next(generator.accounting_event_directory(service_dir).glob("*.json"))
            event.unlink()
            with self.assertRaisesRegex(generator.ServiceError, "head/event count"):
                generator.validate_accounting_chain(service_dir, authorization)

    def test_outcome_cannot_close_another_campaigns_attempt(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            _path, _authorization, _packet, _queue = self.ledgered_attempt(
                service_dir, campaign_id="held-attempt"
            )
            other_seed = self.authenticated_seed_batch(
                service_dir, "other-campaign", 1
            )
            other_batch = json.loads(other_seed.read_text(encoding="utf-8"))
            other_result = other_seed.parent / "result-receipt.json"
            generator.atomic_json(
                other_result,
                {
                    "campaign_id": "other-campaign",
                    "terminal": other_batch["terminal"],
                    "seed_count": len(other_batch["seeds"]),
                    "finished_at": datetime.now(timezone.utc).isoformat(),
                },
            )
            head = json.loads(
                generator.accounting_head_path(service_dir).read_text(
                    encoding="utf-8"
                )
            )
            with self.assertRaisesRegex(
                generator.ServiceError, "unresolved attempt"
            ):
                generator.make_invocation_outcome(
                    service_dir,
                    head=head,
                    campaign_id="other-campaign",
                    result_path=other_result,
                    seed_path=other_seed,
                )

    def test_provider_start_rejects_malformed_process_identity(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            _path, _authorization, _packet, _queue = self.ledgered_attempt(
                service_dir, campaign_id="bad-provider-identity"
            )
            batch_dir = service_dir / "batches" / "bad-provider-identity"
            attempt = json.loads(
                (batch_dir / "attempt.json").read_text(encoding="utf-8")
            )
            prompt_path = batch_dir / "prompt.md"
            prompt_path.write_text("test prompt\n", encoding="utf-8")
            generator.atomic_json(
                batch_dir / "provider-start.json",
                {
                    "schema_version": 1,
                    "protocol": generator.PROTOCOL_VERSION,
                    "campaign_id": "bad-provider-identity",
                    "pid": 1,
                    "process_identity": {"pid": 1},
                    "started_at": datetime.now(timezone.utc).isoformat(),
                    "attempt_event": attempt["ledger_event"],
                    "prompt": generator.file_receipt(prompt_path),
                    "meaning": (
                        "durable process acknowledgement committed before prompt delivery"
                    ),
                },
            )
            with self.assertRaisesRegex(
                generator.ServiceError, "process identity is malformed"
            ):
                generator.validate_provider_start(
                    service_dir,
                    "bad-provider-identity",
                    expected_attempt_event=attempt["ledger_event"],
                )

    def test_baseline_hash_drift_fails_closed(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            _path, authorization = self.configured_authorization(service_dir)
            baseline_path = generator.authenticate_receipt(
                authorization["accounting_baseline"], "test baseline"
            )
            baseline = json.loads(baseline_path.read_text(encoding="utf-8"))
            baseline["meaning"] = "tampered"
            generator.atomic_json(baseline_path, baseline)
            with self.assertRaisesRegex(generator.ServiceError, "hash mismatch"):
                generator.provider_safety_status(service_dir, authorization)

    def test_malformed_v3_result_cannot_reset_circuit_history(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            batch_dir = service_dir / "batches" / "forged-result"
            batch_dir.mkdir(parents=True)
            generator.atomic_json(
                batch_dir / "packet.json",
                {
                    "protocol": generator.PROTOCOL_VERSION,
                    "campaign_id": "forged-result",
                },
            )
            generator.atomic_json(
                batch_dir / "attempt.json",
                {
                    "campaign_id": "forged-result",
                    "started_at": datetime.now(timezone.utc).isoformat(),
                },
            )
            seed_path = self.authenticated_seed_batch(
                service_dir, "forged-result", 1
            )
            batch = json.loads(seed_path.read_text(encoding="utf-8"))
            batch["requested_seed_count"] = 1
            batch["terminal"] = "SEED-BATCH-COMPLETE"
            generator.atomic_json(seed_path, batch)
            generator.atomic_json(
                batch_dir / "result-receipt.json",
                {
                    "campaign_id": "forged-result",
                    "terminal": "SEED-BATCH-COMPLETE",
                    "seed_count": 1,
                },
            )
            with self.assertRaisesRegex(
                generator.ServiceError, "unexpected closed contract"
            ):
                generator.authorized_cycle_records(
                    service_dir,
                    {
                        "limits": {
                            "max_total_invocations": 100,
                            "max_consecutive_provider_stops": 2,
                            "max_consecutive_zero_seed_batches": 2,
                        }
                    },
                )

    def test_frozen_cycle_is_bound_to_standing_authorization(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization_path, authorization = self.configured_authorization(
                service_dir
            )

            frozen = generator.freeze_campaign_packet(
                service_dir,
                "standing-cycle-test",
                "context_rich",
                authorization_path,
                authorization,
            )
            packet_path = generator.ROOT / frozen["packet"]["path"]
            packet = generator.verify_packet(packet_path)
            self.assertEqual(
                packet["standing_authorization"]["sha256"],
                generator.sha256(authorization_path),
            )
            self.assertFalse(packet["authority"]["may_retry_attempted_packet"])

    def test_write_once_refuses_immutable_drift(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            path = Path(raw) / "receipt.json"
            generator.write_once(path, {"value": 1})
            generator.write_once(path, {"value": 1})
            with self.assertRaises(generator.ServiceError):
                generator.write_once(path, {"value": 2})

    def test_atomic_json_fsyncs_file_before_replace_and_directory_after(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            events: list[str] = []
            original_fsync = generator.os.fsync
            original_replace = generator.os.replace

            def recording_fsync(descriptor: int) -> None:
                mode = os.fstat(descriptor).st_mode
                events.append("fsync-directory" if stat.S_ISDIR(mode) else "fsync-file")
                original_fsync(descriptor)

            def recording_replace(source, destination) -> None:
                events.append("replace")
                original_replace(source, destination)

            with (
                mock.patch.object(generator.os, "fsync", side_effect=recording_fsync),
                mock.patch.object(
                    generator.os, "replace", side_effect=recording_replace
                ),
            ):
                generator.atomic_json(Path(raw) / "durable.json", {"value": 1})
            self.assertLess(events.index("fsync-file"), events.index("replace"))
            self.assertLess(events.index("replace"), len(events) - 1)
            self.assertEqual(events[-1], "fsync-directory")

    def test_atomic_json_replace_failure_leaves_no_partial_target(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            target = Path(raw) / "fault.json"
            with mock.patch.object(
                generator.os, "replace", side_effect=OSError("injected replace fault")
            ):
                with self.assertRaisesRegex(OSError, "injected replace fault"):
                    generator.atomic_json(target, {"value": 1})
            self.assertFalse(target.exists())
            self.assertEqual(list(Path(raw).glob(".fault.json.tmp-*")), [])

    def test_standing_authorization_binds_helpers_and_schema(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization = generator.make_standing_authorization(
                service_dir, self.authorization_args()
            )
            authorization_path = generator.authorization_file_path(
                service_dir, authorization
            )
            generator.atomic_json(authorization_path, authorization)
            generator.verify_standing_authorization(
                authorization_path, service_dir=service_dir
            )
            bound_paths = {
                item["path"] for item in authorization["supporting_implementation"]
            }
            self.assertTrue(
                {
                    "docs/agents/schemas/research-development-receipt.schema.json",
                    "docs/agents/schemas/research-event-verification.schema.json",
                    "docs/agents/continuous-idea-generator-v3-migration-root.json",
                    "docs/wayfinder/tickets/0119-adopt-self-refilling-investigation-loop.md",
                    "AGENTS.md",
                }
                <= bound_paths
            )
            tampered = copy.deepcopy(authorization)
            tampered["supporting_implementation"][0]["sha256"] = "0" * 64
            tampered_path = service_dir / "authorizations" / "tampered.json"
            generator.atomic_json(tampered_path, tampered)
            with self.assertRaisesRegex(
                generator.ServiceError,
                r"(?i)(helper or schema|supporting implementation .* hash mismatch)",
            ):
                generator.verify_standing_authorization(
                    tampered_path, service_dir=service_dir
                )

    def test_standing_authorization_cannot_weaken_call_limits(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            with self.assertRaisesRegex(generator.ServiceError, "wall_minutes"):
                generator.make_standing_authorization(
                    service_dir, self.authorization_args(wall_minutes=91)
                )
            with self.assertRaisesRegex(generator.ServiceError, "exactly ten"):
                generator.make_standing_authorization(
                    service_dir,
                    self.authorization_args(ready_seed_target=9),
                )

    def test_active_pointer_rotation_preserves_prior_authorization(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            first = generator.make_standing_authorization(
                service_dir, self.authorization_args()
            )
            first_path = generator.authorization_file_path(service_dir, first)
            generator.write_once(first_path, first)
            first_hash = generator.sha256(first_path)
            pointer_path = generator.active_authorization_pointer_path(service_dir)
            first_activation = generator.append_authorization_activation(
                service_dir, first_path, first
            )
            self.assertEqual(
                generator.active_standing_authorization(service_dir)[0], first_path
            )

            second = copy.deepcopy(first)
            second["created_at"] = datetime.now(timezone.utc).isoformat()
            second["approval_ref"] = "second-test-standing-approval"
            second_path = generator.authorization_file_path(service_dir, second)
            generator.write_once(second_path, second)
            generator.append_authorization_activation(
                service_dir, second_path, second
            )
            self.assertNotEqual(first_path, second_path)
            self.assertEqual(generator.sha256(first_path), first_hash)
            self.assertEqual(
                generator.active_standing_authorization(service_dir)[0], second_path
            )
            generator.atomic_json(
                pointer_path,
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

    def test_process_identity_rejects_pid_reuse_shape(self) -> None:
        identity = generator.process_identity(os.getpid())
        self.assertIsNotNone(identity)
        assert identity is not None
        self.assertTrue(generator.process_identity_matches(identity))
        reused = dict(identity)
        reused["start_ticks"] += 1
        self.assertFalse(generator.process_identity_matches(reused))

    def test_start_rejects_stale_daemon_under_standing_authorization(self) -> None:
        args = SimpleNamespace(
            service_dir=Path("runs/agents/test-service"),
            authorization=Path(
                "runs/agents/test-service/authorizations/current.json"
            ),
            authorization_sha256="a" * 64,
        )
        service_dir = generator.ROOT / args.service_dir
        authorization_path = generator.ROOT / args.authorization
        with (
            mock.patch.object(generator, "service_directory", return_value=service_dir),
            mock.patch.object(
                generator, "packet_path_argument", return_value=authorization_path
            ),
            mock.patch.object(generator, "sha256", return_value="a" * 64),
            mock.patch.object(
                generator,
                "active_standing_authorization",
                return_value=(authorization_path, {}),
            ),
            mock.patch.object(
                generator,
                "validate_accounting_chain",
                return_value={"charged_count": 0},
            ),
            mock.patch.object(
                generator,
                "launch_daemon",
                side_effect=generator.ServiceError("stale implementation"),
            ),
        ):
            with self.assertRaisesRegex(generator.ServiceError, "stale"):
                generator.command_start(args)

    def test_start_rejects_daemon_receipt_bound_to_rotated_authorization(self) -> None:
        args = SimpleNamespace(
            service_dir=Path("runs/agents/test-service"),
            authorization=Path(
                "runs/agents/test-service/authorizations/current.json"
            ),
            authorization_sha256="a" * 64,
        )
        service_dir = generator.ROOT / args.service_dir
        authorization_path = generator.ROOT / args.authorization
        authorization_receipt = {
            "path": generator.repo_relative(authorization_path),
            "sha256": "a" * 64,
        }
        with (
            mock.patch.object(generator, "service_directory", return_value=service_dir),
            mock.patch.object(
                generator, "packet_path_argument", return_value=authorization_path
            ),
            mock.patch.object(generator, "sha256", return_value="a" * 64),
            mock.patch.object(
                generator,
                "active_standing_authorization",
                return_value=(authorization_path, {}),
            ),
            mock.patch.object(
                generator,
                "validate_accounting_chain",
                return_value={"charged_count": 0},
            ),
            mock.patch.object(
                generator,
                "launch_daemon",
                return_value={
                    "standing_authorization": {
                        "path": authorization_receipt["path"],
                        "sha256": "b" * 64,
                    }
                },
            ),
        ):
            with self.assertRaisesRegex(
                generator.ServiceError, "did not bind the requested authorization"
            ):
                generator.command_start(args)

    def test_stop_disables_failed_unit_without_live_daemon_receipt(self) -> None:
        args = SimpleNamespace(
            service_dir=Path("runs/agents/test-service"), reason="test-stop"
        )
        service_dir = generator.ROOT / args.service_dir
        completed = SimpleNamespace(returncode=0)
        with (
            mock.patch.object(generator, "service_directory", return_value=service_dir),
            mock.patch.object(generator, "daemon_receipt", return_value=None),
            mock.patch.object(generator.subprocess, "run", return_value=completed) as run,
            mock.patch("builtins.print"),
        ):
            self.assertEqual(generator.command_stop(args), 0)
        self.assertEqual(
            run.call_args.args[0],
            [
                "systemctl",
                "--user",
                "disable",
                "--now",
                generator.SYSTEMD_UNIT_NAME,
            ],
        )

    def test_service_directory_cannot_escape_run_root(self) -> None:
        with self.assertRaises(generator.ServiceError):
            generator.service_directory(Path("/tmp/not-a-project-service"))


if __name__ == "__main__":
    unittest.main()
