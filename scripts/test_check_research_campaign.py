#!/usr/bin/env python3
"""Regression tests for the evidence-first research-campaign contracts."""

from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

from scripts import check_research_campaign as campaign


def template(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


class ResearchCampaignContractTests(unittest.TestCase):
    def setUp(self) -> None:
        self.seed_batch = template(campaign.SEED_TEMPLATE)
        self.brief = template(campaign.BRIEF_TEMPLATE)
        self.receipt = template(campaign.RECEIPT_TEMPLATE)
        self.replay_outputs: dict[tuple[str, ...], dict] = {}

    def assert_campaign_error(self, function, *args, **kwargs) -> None:
        with self.assertRaises(campaign.CampaignError):
            function(*args, **kwargs)

    def test_standing_first_test_schema_is_separate_from_generic_tasks(self) -> None:
        generic_path = (
            campaign.ROOT / "docs/agents/schemas/task-packet.schema.json"
        )
        generic = template(generic_path)
        first_test = template(campaign.TASK_SCHEMA)

        self.assertEqual(campaign.TASK_SCHEMA.name, "research-first-test-task.schema.json")
        self.assertEqual(generic["properties"]["schema_version"], {"const": 1})
        self.assertEqual(first_test["properties"]["schema_version"], {"const": 2})
        self.assertNotIn("standing_first_test", generic["required"])
        self.assertNotIn("first_test_execution", generic["required"])
        self.assertIn("standing_first_test", first_test["required"])
        self.assertIn("first_test_execution", first_test["required"])

    @staticmethod
    def file_receipt(path: Path) -> dict[str, str]:
        return {
            "path": str(path.relative_to(campaign.ROOT)),
            "sha256": campaign.digest(path),
        }

    @staticmethod
    def recompute_execution_contract(task: dict) -> None:
        execution = task["first_test_execution"]
        execution["contract_id"] = campaign.canonical_sha256(
            {key: value for key, value in execution.items() if key != "contract_id"}
        )

    @classmethod
    def add_task_output(cls, task: dict, path: Path) -> None:
        relative = str(path.relative_to(campaign.ROOT))
        if relative not in task["ownership"]["write_paths"]:
            task["ownership"]["write_paths"].append(relative)
        if relative not in task["deliverables"]:
            task["deliverables"].append(relative)
        execution = task.get("first_test_execution")
        if isinstance(execution, dict) and not any(
            output.get("path") == relative for output in execution["outputs"]
        ):
            role = f"output_{len(execution['outputs']) + 1}"
            execution["outputs"].append(
                {"role": role, "path": relative, "media_type": "application/json"}
            )
            execution["argv_template"].extend(
                [f"--{role}-fd", f"{{output_fd:{role}}}"]
            )
            cls.recompute_execution_contract(task)

    @staticmethod
    def recompute_evidence_contract(brief: dict) -> None:
        contract = brief["evidence_contract"]
        scope = contract["scope"]
        scope["scope_contract_id"] = campaign.canonical_sha256(
            {key: value for key, value in scope.items() if key != "scope_contract_id"}
        )
        contract["contract_id"] = campaign.canonical_sha256(
            {key: value for key, value in contract.items() if key != "contract_id"}
        )

    def successful_replay(
        self, argv: list[str], *, timeout_seconds: int
    ) -> subprocess.CompletedProcess[str]:
        del timeout_seconds
        normalized = self.replay_outputs.get(tuple(argv))
        stdout = "PASS\n" if normalized is None else json.dumps(normalized)
        return subprocess.CompletedProcess(argv, 0, stdout=stdout, stderr="")

    def rewrite_event_verification(
        self,
        event: dict,
        verification_path: Path,
        verification: dict,
    ) -> None:
        verification_path.write_text(
            json.dumps(verification, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        event["verification_receipt"] = self.file_receipt(verification_path)
        event["event_id"] = campaign.canonical_sha256(
            {
                key: value
                for key, value in event.items()
                if key not in {"event_id", "verification_receipt"}
            }
        )

    def make_checked_event(
        self,
        directory: Path,
        *,
        brief: dict,
        task: dict,
        engine: str = "python_exact",
        kind: str = "checked_computation",
        gate_branch: str = "live",
        polarity: str = "supports",
        stem: str = "checked",
    ) -> tuple[dict, Path, dict]:
        artifact_path = directory / f"{stem}-artifact.json"
        artifact_path.write_text('{"checked": true}\n', encoding="utf-8")
        self.add_task_output(task, artifact_path)
        contract = brief["evidence_contract"]
        scope = contract["scope"]
        claim_contract_id = contract["contract_id"]
        event = {
            "event_id": "0" * 64,
            "kind": kind,
            "claim_level": "computational_evidence",
            "gate_branch": gate_branch,
            "binding": {
                "primary_contract_id": claim_contract_id,
                "subject": "primary_claim",
                "subject_contract_id": claim_contract_id,
                "model_contract_id": contract["model_contract_id"],
                "scope_contract_id": scope["scope_contract_id"],
                "polarity": polarity,
                "damage_scope_reached": "candidate-local",
            },
            "artifact": self.file_receipt(artifact_path),
            "verification_receipt": None,
            "observation": "The frozen checker returned the declared observation.",
        }
        verified_core = {
            key: value
            for key, value in event.items()
            if key not in {"event_id", "verification_receipt"}
        }
        execution = task["first_test_execution"]
        verifier_text = execution["argv_template"][2]
        verifier_receipt = next(
            copy.deepcopy(item)
            for item in execution["input_receipts"]
            if item["path"] == verifier_text
        )
        raw_inputs = [
            copy.deepcopy(item)
            for item in execution["input_receipts"]
            if item != verifier_receipt
        ]
        event_core_sha256 = campaign.canonical_sha256(verified_core)
        event["event_id"] = event_core_sha256
        verified_learning = {
            "failing_feature": None,
            "strongest_supported_statement": None,
        }
        if (
            kind in {"exact_falsifier", "claim_refuted"}
            and gate_branch == "kill"
            and polarity == "refutes"
        ):
            for role, text_value in (
                ("failing_feature", "The frozen predicate fails on the checked artifact."),
                (
                    "strongest_supported_statement",
                    "The checked artifact refutes the predicate at candidate-local scope.",
                ),
            ):
                learning_core = {
                    "role": role,
                    "text": text_value,
                    "subject_contract_id": claim_contract_id,
                    "model_contract_id": contract["model_contract_id"],
                    "scope_contract_id": scope["scope_contract_id"],
                    "verified_event_core_sha256": event_core_sha256,
                }
                verified_learning[role] = {
                    "learning_claim_id": campaign.canonical_sha256(learning_core),
                    "text": text_value,
                    "subject_contract_id": claim_contract_id,
                }
        normalized = {
            "schema_version": 1,
            "protocol": "research-event-normalized-result-v1",
            "verified_event_core_sha256": event_core_sha256,
            "event_artifact": copy.deepcopy(event["artifact"]),
            "claim_contract_id": claim_contract_id,
            "primary_contract_id": claim_contract_id,
            "subject_contract_id": claim_contract_id,
            "model_contract_id": contract["model_contract_id"],
            "scope_contract_id": scope["scope_contract_id"],
            "kind": kind,
            "gate_branch": gate_branch,
            "polarity": polarity,
            "damage_scope_reached": "candidate-local",
            "observation_sha256": hashlib.sha256(
                event["observation"].encode("utf-8")
            ).hexdigest(),
            "checked_predicate": brief["probe"]["question"],
            "result": polarity,
            "verified_learning": verified_learning,
        }
        argv = [
            "/usr/bin/python3",
            "-B",
            verifier_text,
            "--verify-event",
            event["artifact"]["path"],
            "--normalized-result-stdout",
        ]
        for item in raw_inputs:
            argv.extend(["--input", item["path"]])
        verifier_contract_core = {
            "verifier_component": verifier_receipt,
            "claim_contract_id": claim_contract_id,
            "primary_contract_id": claim_contract_id,
            "subject_contract_id": claim_contract_id,
            "model_contract_id": contract["model_contract_id"],
            "scope_contract_id": scope["scope_contract_id"],
            "verified_event_core_sha256": event_core_sha256,
            "event_artifact": copy.deepcopy(event["artifact"]),
            "engine": engine,
            "invocation": {"argv": argv, "cwd": "."},
            "input_receipts": [copy.deepcopy(event["artifact"]), *raw_inputs],
        }
        verifier_contract_id = campaign.canonical_sha256(verifier_contract_core)
        brief_path = directory / "development-brief.json"
        task_path = directory / "task.json"
        task_path.write_text(json.dumps(task, sort_keys=True), encoding="utf-8")
        candidate = scope["candidate"]
        claim_id = f"{candidate['campaign_id']}:{candidate['seed_id']}"
        claim_path = directory / "seed-claim.json"
        claim_path.write_text(
            json.dumps(
                {
                    "claim_id": claim_id,
                    "development_brief": self.file_receipt(brief_path),
                    "task_packet": self.file_receipt(task_path),
                },
                sort_keys=True,
            ),
            encoding="utf-8",
        )
        root_receipts = directory / "root-receipts"
        root_receipts.mkdir(exist_ok=True)
        request = {
            "schema_version": 1,
            "protocol": "ticket-0119-event-verifier-request-v1",
            "verifier_contract_id": verifier_contract_id,
            "guard_component": copy.deepcopy(execution["guard_component"]),
            "seed_claim": self.file_receipt(claim_path),
            "task_packet": self.file_receipt(task_path),
            "claim_id": claim_id,
            "task_id": task["task_id"],
            "event": {
                "event_id": event["event_id"],
                "event_core_sha256": event_core_sha256,
                "subject_contract_id": claim_contract_id,
                "model_contract_id": contract["model_contract_id"],
                "scope_contract_id": scope["scope_contract_id"],
                "artifact": copy.deepcopy(event["artifact"]),
            },
            "checker": verifier_receipt,
            "argv_template": argv,
            "input_receipts": [
                verifier_receipt,
                copy.deepcopy(event["artifact"]),
                *raw_inputs,
            ],
            "expected_normalized_result": normalized,
            "budget": copy.deepcopy(task["budget"]),
            "process_model": campaign.FIRST_TEST_PROCESS_MODEL,
        }
        request_path = root_receipts / f"{event['event_id']}.verification-request.json"
        request_path.write_text(
            json.dumps(request, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        normalized_bytes = campaign.canonical_bytes(normalized) + b"\n"
        empty_sha = hashlib.sha256(b"").hexdigest()
        verifier_envelope = {
            "schema_version": 1,
            "protocol": "research-event-verifier-execution-envelope-v1",
            "envelope_id": "0" * 64,
            "guard_component": copy.deepcopy(execution["guard_component"]),
            "identity": {
                "verifier_request": self.file_receipt(request_path),
                "verifier_contract_id": verifier_contract_id,
                "seed_claim": self.file_receipt(claim_path),
                "claim_id": claim_id,
                "task_packet": self.file_receipt(task_path),
                "task_id": task["task_id"],
                "event_id": event["event_id"],
                "event_core_sha256": event_core_sha256,
                "subject_contract_id": claim_contract_id,
                "model_contract_id": contract["model_contract_id"],
                "scope_contract_id": scope["scope_contract_id"],
                "event_artifact": copy.deepcopy(event["artifact"]),
            },
            "launch": {
                "started_at": "2026-08-31T12:00:00Z",
                "finished_at": "2026-08-31T12:00:01Z",
                "boot_id": "test-boot",
                "outer_pid": 200,
                "sandbox_pid": 201,
                "sandbox_start_ticks": 2000,
                "process_group": 201,
                "argv": argv,
                "cwd": "/work",
            },
            "enforced_policy": {
                "wall_seconds": task["budget"]["wall_minutes"] * 60,
                "cpu_affinity": list(range(task["budget"]["cpu_cores"])),
                "memory_bytes": task["budget"]["memory_gib"] * (1024**3),
                "output_bytes": int(task["budget"]["output_gib"] * (1024**3)),
                "process_model": campaign.FIRST_TEST_PROCESS_MODEL,
                "network": "new-net-namespace-plus-seccomp-kill",
                "repository": "sparse-authenticated-inputs-read-only",
                "persistent_writes": [],
                "seccomp_policy_sha256": "b" * 64,
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
                "wall_seconds": 1.0,
                "cpu_seconds": 0.1,
                "peak_aggregate_rss_bytes": 1024 * 1024,
                "worker_output_bytes": len(normalized_bytes),
                "writes": [],
                "stdout": {
                    "sha256": hashlib.sha256(normalized_bytes).hexdigest(),
                    "bytes": len(normalized_bytes),
                },
                "stderr": {"sha256": empty_sha, "bytes": 0},
                "forbidden_attempts": "none",
                "violations": [],
            },
            "normalized_result": {
                "sha256": hashlib.sha256(normalized_bytes).hexdigest(),
                "bytes": len(normalized_bytes),
                "value": normalized,
                "matches_expected": True,
            },
            "terminal": "PASS",
        }
        verifier_envelope["envelope_id"] = campaign.canonical_sha256(
            {
                key: value
                for key, value in verifier_envelope.items()
                if key != "envelope_id"
            }
        )
        verifier_envelope_path = (
            root_receipts / f"{event['event_id']}.verification-envelope.json"
        )
        verifier_envelope_path.write_text(
            json.dumps(verifier_envelope, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        verification = {
            "schema_version": 3,
            "protocol": "research-event-verification-v3",
            "verifier_contract_id": verifier_contract_id,
            "verification_request": self.file_receipt(request_path),
            "verification_envelope": self.file_receipt(verifier_envelope_path),
            "verifier_component": verifier_receipt,
            "claim_contract_id": claim_contract_id,
            "primary_contract_id": claim_contract_id,
            "subject_contract_id": claim_contract_id,
            "model_contract_id": contract["model_contract_id"],
            "scope_contract_id": scope["scope_contract_id"],
            "verified_event_core_sha256": event_core_sha256,
            "event_artifact": copy.deepcopy(event["artifact"]),
            "engine": engine,
            "invocation": {"argv": argv, "cwd": "."},
            "input_receipts": [copy.deepcopy(event["artifact"]), *raw_inputs],
            "normalized_result": normalized,
            "guarded_runner": None,
            "makefile": None,
            "theorem_audit": None,
            "exit_code": 0,
            "terminal": "PASS",
        }
        verification_path = root_receipts / f"{stem}-event-verification.json"
        verification_path.write_text(
            json.dumps(verification, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        event["verification_receipt"] = {
            "path": str(verification_path.relative_to(campaign.ROOT)),
            "sha256": campaign.digest(verification_path),
        }
        guard_argv = [
            "python3",
            campaign.FIRST_TEST_GUARD_PATH,
            "verify",
            "--service-dir",
            str(directory.relative_to(campaign.ROOT)),
            "--request",
            str(request_path.relative_to(campaign.ROOT)),
            "--request-sha256",
            campaign.digest(request_path),
            "--envelope",
            str(verifier_envelope_path.relative_to(campaign.ROOT)),
        ]
        self.replay_outputs[tuple(guard_argv)] = verifier_envelope
        return event, verification_path, verification

    def make_proposal_event(
        self,
        directory: Path,
        *,
        brief: dict,
        task: dict,
        gate_branch: str,
        polarity: str,
        stem: str,
    ) -> dict:
        artifact_path = directory / f"{stem}-proposal.md"
        artifact_path.write_text("proposal observation\n", encoding="utf-8")
        self.add_task_output(task, artifact_path)
        contract = brief["evidence_contract"]
        event = {
            "event_id": "0" * 64,
            "kind": "proposal_only",
            "claim_level": "proposal",
            "gate_branch": gate_branch,
            "binding": {
                "primary_contract_id": contract["contract_id"],
                "subject": "primary_claim",
                "subject_contract_id": contract["contract_id"],
                "model_contract_id": contract["model_contract_id"],
                "scope_contract_id": contract["scope"]["scope_contract_id"],
                "polarity": polarity,
                "damage_scope_reached": "candidate-local",
            },
            "artifact": self.file_receipt(artifact_path),
            "verification_receipt": None,
            "observation": "The worker recorded a proposal-level observation.",
        }
        event["event_id"] = campaign.canonical_sha256(
            {
                key: value
                for key, value in event.items()
                if key not in {"event_id", "verification_receipt"}
            }
        )
        return event

    def make_development_receipt(
        self,
        *,
        brief_path: Path,
        brief: dict,
        task: dict,
        terminal: str,
        events: list[dict],
        envelope_terminal: str = "PASS",
    ) -> dict:
        directory = brief_path.parent
        for output in task["first_test_execution"]["outputs"]:
            output_path = campaign.ROOT / output["path"]
            output_path.parent.mkdir(parents=True, exist_ok=True)
            if not output_path.exists():
                output_path.write_text("{}\n", encoding="utf-8")
        task_path = directory / "task.json"
        task_path.write_text(json.dumps(task, sort_keys=True), encoding="utf-8")
        brief_receipt = self.file_receipt(brief_path)
        task_receipt = self.file_receipt(task_path)
        candidate = brief["evidence_contract"]["scope"]["candidate"]
        claim_id = f"{candidate['campaign_id']}:{candidate['seed_id']}"
        claim = {
            "claim_id": claim_id,
            "development_brief": brief_receipt,
            "task_packet": task_receipt,
        }
        claim_path = directory / "seed-claim.json"
        claim_path.write_text(json.dumps(claim, sort_keys=True), encoding="utf-8")
        manifest = []
        for output in task["first_test_execution"]["outputs"]:
            output_path = campaign.ROOT / output["path"]
            manifest.append(
                {
                    "role": output["role"],
                    "path": output["path"],
                    "sha256": campaign.digest(output_path),
                    "bytes": output_path.stat().st_size,
                    "materialized": envelope_terminal == "PASS",
                }
            )
        empty_sha = hashlib.sha256(b"").hexdigest()
        output_bytes = sum(item["bytes"] for item in manifest)
        execution = task["first_test_execution"]
        resolved_argv = []
        next_fd = 20
        for item in execution["argv_template"]:
            if item.startswith("{output_fd:"):
                resolved_argv.append(str(next_fd))
                next_fd += 1
            else:
                resolved_argv.append(item)
        envelope = {
            "schema_version": 1,
            "protocol": "research-first-test-execution-envelope-v1",
            "envelope_id": "0" * 64,
            "guard_component": copy.deepcopy(execution["guard_component"]),
            "identity": {
                "seed_claim": self.file_receipt(claim_path),
                "claim_id": claim_id,
                "development_brief": brief_receipt,
                "brief_id": brief["brief_id"],
                "task_packet": task_receipt,
                "task_id": task["task_id"],
                "execution_contract_id": execution["contract_id"],
            },
            "launch": {
                "started_at": "2026-08-31T12:00:00Z",
                "finished_at": "2026-08-31T12:01:00Z",
                "boot_id": "test-boot",
                "outer_pid": 100,
                "sandbox_pid": 101 if envelope_terminal == "PASS" else None,
                "sandbox_start_ticks": 1000 if envelope_terminal == "PASS" else None,
                "process_group": 101 if envelope_terminal == "PASS" else None,
                "argv": resolved_argv,
                "cwd": "/work",
            },
            "enforced_policy": {
                "wall_seconds": task["budget"]["wall_minutes"] * 60,
                "cpu_affinity": list(range(task["budget"]["cpu_cores"])),
                "memory_bytes": task["budget"]["memory_gib"] * (1024**3),
                "output_bytes": int(task["budget"]["output_gib"] * (1024**3)),
                "process_model": campaign.FIRST_TEST_PROCESS_MODEL,
                "network": (
                    "new-net-namespace-plus-seccomp-kill"
                    if envelope_terminal == "PASS"
                    else "not-observed"
                ),
                "repository": (
                    "sparse-authenticated-inputs-read-only"
                    if envelope_terminal == "PASS"
                    else "not-observed"
                ),
                "persistent_writes": [item["path"] for item in execution["outputs"]],
                "seccomp_policy_sha256": "a" * 64,
                "namespace_inodes": {
                    "user": 1 if envelope_terminal == "PASS" else None,
                    "mount": 2 if envelope_terminal == "PASS" else None,
                    "pid": 3 if envelope_terminal == "PASS" else None,
                    "net": 4 if envelope_terminal == "PASS" else None,
                    "ipc": 5 if envelope_terminal == "PASS" else None,
                    "uts": 6 if envelope_terminal == "PASS" else None,
                    "cgroup": 7 if envelope_terminal == "PASS" else None,
                },
            },
            "observation": {
                "exit_code": 0 if envelope_terminal == "PASS" else 1,
                "signal": None,
                "wall_seconds": 60.0,
                "cpu_seconds": 1.0,
                "peak_aggregate_rss_bytes": 32 * (1024**2),
                "worker_output_bytes": output_bytes,
                "writes": manifest,
                "stdout": {"sha256": empty_sha, "bytes": 0},
                "stderr": {"sha256": empty_sha, "bytes": 0},
                "forbidden_attempts": (
                    "none" if envelope_terminal == "PASS" else "not-observed"
                ),
                "violations": [] if envelope_terminal == "PASS" else ["launch stopped"],
            },
            "terminal": envelope_terminal,
        }
        envelope["envelope_id"] = campaign.canonical_sha256(
            {key: value for key, value in envelope.items() if key != "envelope_id"}
        )
        envelope_path = (
            directory
            / "root-receipts"
            / f"{task['task_id']}.execution-envelope.json"
        )
        envelope_path.parent.mkdir(exist_ok=True)
        envelope_path.write_text(
            json.dumps(envelope, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        receipt = {
            "schema_version": 3,
            "brief_id": brief["brief_id"],
            "brief_sha256": campaign.digest(brief_path),
            "execution_envelope": self.file_receipt(envelope_path),
            "terminal": terminal,
            "assigned_gate_outcome": "The exact frozen gate reached its declared branch.",
            "evidence_events": events,
            "resource_use": {
                "wall_minutes": 1,
                "active_minutes": 1,
                "cpu_seconds": 1,
                "peak_memory_mib": 32,
                "artifact_bytes": output_bytes,
                "input_tokens": 0,
                "output_tokens": 0,
                "tool_calls": 1,
                "source_requests": 0,
                "experiment_runs": 1,
                "checker_runs": 1,
            },
            "claim_candidate": None,
            "serendipity": None,
            "route_action": "none",
            "admission_status": "unadmitted",
        }
        return receipt

    def test_templates_and_historical_control_validate(self) -> None:
        campaign.validate_templates()

    def test_seed_complete_requires_five_honest_seeds(self) -> None:
        self.seed_batch["terminal"] = "SEED-BATCH-COMPLETE"
        self.assert_campaign_error(
            campaign.validate_seed_batch, self.seed_batch, authenticate=False
        )

    def test_deficit_bound_seed_batch_uses_requested_count(self) -> None:
        self.seed_batch["requested_seed_count"] = 1
        self.seed_batch["terminal"] = "SEED-BATCH-COMPLETE"
        campaign.validate_seed_batch(self.seed_batch, authenticate=False)

        too_few = copy.deepcopy(self.seed_batch)
        too_few["requested_seed_count"] = 2
        self.assert_campaign_error(
            campaign.validate_seed_batch, too_few, authenticate=False
        )

        padded_novelty = copy.deepcopy(self.seed_batch)
        padded_novelty["terminal"] = "SEED-BATCH-NOVELTY-STOP"
        self.assert_campaign_error(
            campaign.validate_seed_batch, padded_novelty, authenticate=False
        )

    def test_seed_lineage_arity_is_enforced(self) -> None:
        self.seed_batch["seeds"][0]["lineage"]["kind"] = "mutation"
        self.assert_campaign_error(
            campaign.validate_seed_batch, self.seed_batch, authenticate=False
        )

    def test_seed_outcome_branches_must_discriminate(self) -> None:
        first_test = self.seed_batch["seeds"][0]["first_test"]
        first_test["information_if_no_signal"] = first_test["information_if_killed"]
        self.assert_campaign_error(
            campaign.validate_seed_batch, self.seed_batch, authenticate=False
        )

    def test_brief_rejects_more_than_five_context_artifacts(self) -> None:
        context = self.brief["selected_context"][0]
        self.brief["selected_context"] = [copy.deepcopy(context) for _ in range(6)]
        self.assert_campaign_error(
            campaign.validate_brief, self.brief, authenticate=False
        )

    def test_hostile_control_must_have_different_predictions(self) -> None:
        control = self.brief["hostile_controls"][0]
        control["expected_if_artifact"] = control["expected_if_mechanism_is_real"]
        self.assert_campaign_error(
            campaign.validate_brief, self.brief, authenticate=False
        )

    def test_lean_cannot_be_enabled_without_a_fixed_contract(self) -> None:
        self.brief["allowed_methods"].append("local_lean")
        self.assert_campaign_error(
            campaign.validate_brief, self.brief, authenticate=False
        )

    def test_persistence_instruction_cannot_be_tilted(self) -> None:
        self.brief["persistence_instruction"] += " Assume the conjecture is true."
        self.assert_campaign_error(
            campaign.validate_brief, self.brief, authenticate=False
        )

    def make_authenticated_brief(self, directory: Path) -> tuple[Path, dict, dict]:
        source_rel = "docs/agents/research-campaign.md"
        source_path = campaign.ROOT / source_rel

        batch = copy.deepcopy(self.seed_batch)
        batch["campaign_id"] = "test-campaign"
        batch["snapshot"] = {
            "path": source_rel,
            "sha256": campaign.digest(source_path),
        }
        batch_path = directory / "seed-batch.json"
        batch_path.write_text(json.dumps(batch), encoding="utf-8")
        batch_rel = str(batch_path.relative_to(campaign.ROOT))

        brief = copy.deepcopy(self.brief)
        brief["brief_id"] = "test-campaign-S01-probe"
        brief["task_id"] = "test-campaign-S01-probe"
        brief["seed"] = {
            "batch_path": batch_rel,
            "batch_sha256": campaign.digest(batch_path),
            "seed_id": "S01",
        }
        selected_seed = batch["seeds"][0]
        first_test = selected_seed["first_test"]
        brief["target_ref"] = selected_seed["target_ref"]
        brief["probe"]["question"] = first_test["question"]
        brief["probe"]["live_signal"] = first_test["live_signal"]
        brief["probe"]["kill_signal"] = first_test["kill_signal"]
        evidence_contract = brief["evidence_contract"]
        evidence_contract["statement"] = brief["probe"]["question"]
        evidence_contract["target_ref"] = brief["target_ref"]
        evidence_contract["model"] = copy.deepcopy(selected_seed["model"])
        evidence_contract["model_contract_id"] = campaign.canonical_sha256(
            evidence_contract["model"]
        )
        evidence_contract["scope"]["candidate"] = {
            "campaign_id": batch["campaign_id"],
            "seed_id": "S01",
            "seed_batch_sha256": campaign.digest(batch_path),
        }
        scope_core = {
            key: value
            for key, value in evidence_contract["scope"].items()
            if key != "scope_contract_id"
        }
        evidence_contract["scope"]["scope_contract_id"] = (
            campaign.canonical_sha256(scope_core)
        )
        contract_core = {
            key: value
            for key, value in evidence_contract.items()
            if key != "contract_id"
        }
        evidence_contract["contract_id"] = campaign.canonical_sha256(contract_core)
        brief["selected_context"] = [
            {
                "path": source_rel,
                "sha256": campaign.digest(source_path),
                "purpose": "Authenticate the campaign boundary under test.",
            }
        ]
        brief_path = directory / "development-brief.json"
        brief_path.write_text(json.dumps(brief), encoding="utf-8")
        brief_rel = str(brief_path.relative_to(campaign.ROOT))

        run_id = directory.name
        result_rel = str(
            (directory / "first-test-result.json").relative_to(campaign.ROOT)
        )
        checker_path = campaign.ROOT / "scripts" / "check_research_campaign.py"
        checker_rel = str(checker_path.relative_to(campaign.ROOT))
        input_receipts = [
            self.file_receipt(checker_path),
            {"path": batch_rel, "sha256": campaign.digest(batch_path)},
            {"path": source_rel, "sha256": campaign.digest(source_path)},
            {"path": brief_rel, "sha256": campaign.digest(brief_path)},
        ]
        guard_path = campaign.ROOT / campaign.FIRST_TEST_GUARD_PATH
        execution = {
            "protocol": campaign.FIRST_TEST_EXECUTION_PROTOCOL,
            "contract_id": "0" * 64,
            "guard_component": self.file_receipt(guard_path),
            "engine": "python_exact",
            "argv_template": [
                "/usr/bin/python3",
                "-B",
                checker_rel,
                "--input",
                batch_rel,
                "--input",
                source_rel,
                "--input",
                brief_rel,
                "--result-fd",
                "{output_fd:terminal_artifact}",
            ],
            "cwd": ".",
            "input_receipts": copy.deepcopy(input_receipts),
            "outputs": [
                {
                    "role": "terminal_artifact",
                    "path": result_rel,
                    "media_type": "application/json",
                }
            ],
            "normalized_result_role": "terminal_artifact",
            "process_model": campaign.FIRST_TEST_PROCESS_MODEL,
        }
        execution["contract_id"] = campaign.canonical_sha256(
            {key: value for key, value in execution.items() if key != "contract_id"}
        )
        task = {
            "schema_version": 2,
            "run_id": run_id,
            "task_id": brief["task_id"],
            "wayfinder_ticket": campaign.TICKET_0119,
            "profile": "test-first-investigator",
            "base_revision": "test-revision",
            "workspace_fingerprint": "test-workspace",
            "objective": "Execute the one frozen standing-authority first test.",
            "inputs": input_receipts,
            "ownership": {
                "read_paths": [checker_rel, batch_rel, source_rel, brief_rel],
                "write_paths": [result_rel],
            },
            "claims_allowed": ["proposal", "computational_evidence"],
            "theorem_contract": None,
            "budget": {
                "wall_minutes": 30,
                "cpu_cores": 1,
                "memory_gib": 1,
                "output_gib": 0.01,
            },
            "required_checks": ["Authenticate every frozen input."],
            "success": ["Return one pre-admission terminal."],
            "stop": ["Stop within the standing first-test envelope."],
            "deliverables": [result_rel],
            "standing_first_test": copy.deepcopy(brief["authority"]),
            "first_test_execution": execution,
        }
        return brief_path, brief, task

    def make_lean_brief(self, directory: Path) -> tuple[Path, dict, dict]:
        brief_path, brief, task = self.make_authenticated_brief(directory)
        batch_path = campaign.ROOT / brief["seed"]["batch_path"]
        batch = json.loads(batch_path.read_text(encoding="utf-8"))
        batch["seeds"][0]["first_test"]["question"] = "True"
        batch_path.write_text(json.dumps(batch), encoding="utf-8")
        batch_sha = campaign.digest(batch_path)

        theorem_contract = {
            "name": "FrozenLeanCheck",
            "statement": "True",
            "statement_may_change": False,
        }
        brief["seed"]["batch_sha256"] = batch_sha
        brief["probe"]["question"] = theorem_contract["statement"]
        brief["allowed_methods"].append("local_lean")
        brief["lean_policy"] = {
            "mode": "fixed_statement_in_loop",
            "theorem_contract_ref": theorem_contract["name"],
            "rationale": "Exercise the exact frozen Lean verifier contract.",
        }
        contract = brief["evidence_contract"]
        contract["statement"] = theorem_contract["statement"]
        contract["scope"]["candidate"]["seed_batch_sha256"] = batch_sha
        contract["theorem"] = {
            "name": theorem_contract["name"],
            "statement": theorem_contract["statement"],
            "task_contract_sha256": campaign.canonical_sha256(theorem_contract),
        }
        self.recompute_evidence_contract(brief)
        brief_path.write_text(json.dumps(brief), encoding="utf-8")

        task["theorem_contract"] = theorem_contract
        task["claims_allowed"] = [
            "proposal",
            "computational_evidence",
            "file_compiles",
        ]
        for item in task["inputs"]:
            if item["path"] == brief["seed"]["batch_path"]:
                item["sha256"] = batch_sha
            elif item["path"] == str(brief_path.relative_to(campaign.ROOT)):
                item["sha256"] = campaign.digest(brief_path)
        task["standing_first_test"] = None
        return brief_path, brief, task

    def make_lean_event(
        self,
        directory: Path,
        *,
        brief: dict,
        task: dict,
        proof_mode: str,
        claim_level: str | None = None,
        kind: str | None = None,
    ) -> tuple[dict, Path, dict, Path, dict]:
        if proof_mode not in {"native_decide", "kernel"}:
            raise ValueError("unknown Lean proof mode")
        source_path = directory / "CheckedEvidence.lean"
        proof = "native_decide" if proof_mode == "native_decide" else "trivial"
        source_path.write_text(
            "import Mathlib\n\n"
            f"theorem FrozenLeanCheck : True := by\n  {proof}\n",
            encoding="utf-8",
        )
        self.add_task_output(task, source_path)
        contract = brief["evidence_contract"]
        level = claim_level or (
            "computational_evidence"
            if proof_mode == "native_decide"
            else "file_compiles"
        )
        event_kind = kind or (
            "checked_computation"
            if proof_mode == "native_decide"
            else "compiling_fixed_statement"
        )
        event = {
            "event_id": "0" * 64,
            "kind": event_kind,
            "claim_level": level,
            "gate_branch": "live",
            "binding": {
                "primary_contract_id": contract["contract_id"],
                "subject": "primary_claim",
                "subject_contract_id": contract["contract_id"],
                "model_contract_id": contract["model_contract_id"],
                "scope_contract_id": contract["scope"]["scope_contract_id"],
                "polarity": "supports",
                "damage_scope_reached": "candidate-local",
            },
            "artifact": self.file_receipt(source_path),
            "verification_receipt": None,
            "observation": "The frozen Lean declaration passed its declared gate.",
        }
        verified_core = {
            key: value
            for key, value in event.items()
            if key not in {"event_id", "verification_receipt"}
        }
        axiom_path: Path | None = None
        axiom_receipt = None
        if proof_mode == "kernel":
            axiom_path = directory / "CheckedEvidence-axioms.txt"
            axiom_path.write_text("FrozenLeanCheck\n", encoding="utf-8")
            axiom_receipt = self.file_receipt(axiom_path)
        audit = {
            "schema_version": 1,
            "protocol": "research-lean-declaration-audit-v1",
            "claim_contract_id": contract["contract_id"],
            "verified_event_core_sha256": campaign.canonical_sha256(verified_core),
            "source": copy.deepcopy(event["artifact"]),
            "declaration_name": "FrozenLeanCheck",
            "statement_sha256": hashlib.sha256(b"True").hexdigest(),
            "proof_mode": proof_mode,
            "axiom_report": axiom_receipt,
            "terminal": "PASS",
        }
        audit_path = directory / "lean-declaration-audit.json"
        audit_path.write_text(
            json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        guard = self.file_receipt(campaign.ROOT / "scripts/run_lean_guarded.py")
        event_core_sha256 = campaign.canonical_sha256(verified_core)
        normalized = {
            "schema_version": 1,
            "protocol": "research-event-normalized-result-v1",
            "verified_event_core_sha256": event_core_sha256,
            "event_artifact": copy.deepcopy(event["artifact"]),
            "claim_contract_id": contract["contract_id"],
            "primary_contract_id": contract["contract_id"],
            "subject_contract_id": contract["contract_id"],
            "model_contract_id": contract["model_contract_id"],
            "scope_contract_id": contract["scope"]["scope_contract_id"],
            "kind": event_kind,
            "gate_branch": "live",
            "polarity": "supports",
            "damage_scope_reached": "candidate-local",
            "observation_sha256": hashlib.sha256(
                event["observation"].encode("utf-8")
            ).hexdigest(),
            "checked_predicate": brief["probe"]["question"],
            "result": "supports",
            "verified_learning": {
                "failing_feature": None,
                "strongest_supported_statement": None,
            },
        }
        verification = {
            "schema_version": 3,
            "protocol": "research-event-verification-v3",
            "verifier_contract_id": "0" * 64,
            "verification_request": None,
            "verification_envelope": None,
            "verifier_component": guard,
            "claim_contract_id": contract["contract_id"],
            "primary_contract_id": contract["contract_id"],
            "subject_contract_id": contract["contract_id"],
            "model_contract_id": contract["model_contract_id"],
            "scope_contract_id": contract["scope"]["scope_contract_id"],
            "verified_event_core_sha256": event_core_sha256,
            "event_artifact": copy.deepcopy(event["artifact"]),
            "engine": (
                "lean_native_decide"
                if proof_mode == "native_decide"
                else "lean_kernel"
            ),
            "invocation": {"argv": ["make", "test"], "cwd": "."},
            "input_receipts": [copy.deepcopy(event["artifact"])],
            "normalized_result": normalized,
            "guarded_runner": copy.deepcopy(guard),
            "makefile": self.file_receipt(campaign.ROOT / "Makefile"),
            "theorem_audit": self.file_receipt(audit_path),
            "exit_code": 0,
            "terminal": "PASS",
        }
        verification["verifier_contract_id"] = campaign.canonical_sha256(
            {
                key: verification[key]
                for key in (
                    "verifier_component",
                    "claim_contract_id",
                    "primary_contract_id",
                    "subject_contract_id",
                    "model_contract_id",
                    "scope_contract_id",
                    "verified_event_core_sha256",
                    "event_artifact",
                    "engine",
                    "invocation",
                    "input_receipts",
                )
            }
        )
        root_receipts = directory / "root-receipts"
        root_receipts.mkdir(exist_ok=True)
        verification_path = root_receipts / "lean-event-verification.json"
        verification_path.write_text(
            json.dumps(verification, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        event["verification_receipt"] = self.file_receipt(verification_path)
        event["event_id"] = campaign.canonical_sha256(
            {
                key: value
                for key, value in event.items()
                if key not in {"event_id", "verification_receipt"}
            }
        )
        return event, verification_path, verification, audit_path, audit

    def test_authenticated_brief_and_task_packet_validate(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            brief_path, brief, task = self.make_authenticated_brief(Path(raw_directory))
            campaign.validate_brief(
                brief,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )

    def test_context_must_be_frozen_by_task_packet(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            brief_path, brief, task = self.make_authenticated_brief(Path(raw_directory))
            context_path = brief["selected_context"][0]["path"]
            task["inputs"] = [
                entry for entry in task["inputs"] if entry["path"] != context_path
            ]
            self.assert_campaign_error(
                campaign.validate_brief,
                brief,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )

    def test_development_cannot_expand_seed_test_ceiling(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            brief_path, brief, task = self.make_authenticated_brief(Path(raw_directory))
            brief["probe"]["ceiling_minutes"] = 21
            brief_path.write_text(json.dumps(brief), encoding="utf-8")
            brief_rel = str(brief_path.relative_to(campaign.ROOT))
            for entry in task["inputs"]:
                if entry["path"] == brief_rel:
                    entry["sha256"] = campaign.digest(brief_path)
            self.assert_campaign_error(
                campaign.validate_brief,
                brief,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )

    def test_standing_first_test_rejects_oversized_task_budget(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            brief_path, brief, task = self.make_authenticated_brief(Path(raw_directory))
            task["budget"]["cpu_cores"] = 3
            self.assert_campaign_error(
                campaign.validate_brief,
                brief,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )

    def test_standing_first_test_rejects_output_outside_owned_run(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            brief_path, brief, task = self.make_authenticated_brief(Path(raw_directory))
            task["ownership"]["write_paths"] = [
                "runs/agents/different-run/result.json"
            ]
            task["deliverables"] = list(task["ownership"]["write_paths"])
            self.assert_campaign_error(
                campaign.validate_brief,
                brief,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )

    def test_standing_first_test_rejects_network_method(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            brief_path, brief, task = self.make_authenticated_brief(Path(raw_directory))
            brief["allowed_methods"].append("read_only_sources")
            brief_path.write_text(json.dumps(brief), encoding="utf-8")
            brief_rel = str(brief_path.relative_to(campaign.ROOT))
            for item in task["inputs"]:
                if item["path"] == brief_rel:
                    item["sha256"] = campaign.digest(brief_path)
            self.assert_campaign_error(
                campaign.validate_brief,
                brief,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )

    def test_standing_first_test_rejects_manual_source_and_lean_contracts(self) -> None:
        for method in ("manual_reasoning", "read_only_sources", "local_lean"):
            with self.subTest(method=method):
                candidate = copy.deepcopy(self.brief)
                candidate["allowed_methods"].append(method)
                self.assert_campaign_error(
                    campaign.validate_brief, candidate, authenticate=False
                )
        fixed = copy.deepcopy(self.brief)
        fixed["lean_policy"]["mode"] = "fixed_statement_in_loop"
        fixed["lean_policy"]["theorem_contract_ref"] = "Forbidden"
        self.assert_campaign_error(campaign.validate_brief, fixed, authenticate=False)
        theorem = copy.deepcopy(self.brief)
        theorem["evidence_contract"]["theorem"] = {
            "name": "Forbidden",
            "statement": theorem["evidence_contract"]["statement"],
            "task_contract_sha256": "0" * 64,
        }
        self.assert_campaign_error(campaign.validate_brief, theorem, authenticate=False)

    def test_shared_premise_digest_is_model_aware(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            brief_path, brief, task = self.make_authenticated_brief(Path(raw_directory))
            contract = brief["evidence_contract"]
            premise = {
                "subfamily_ref": "TEST-SUBFAMILY",
                "shared_premise": "Every member uses the same frozen overlap law.",
            }
            premise["shared_premise_contract_id"] = campaign.canonical_sha256(
                {
                    "target_ref": brief["target_ref"],
                    "model_contract_id": contract["model_contract_id"],
                    **premise,
                }
            )
            contract["scope"]["ceiling"] = "subfamily"
            contract["scope"]["subfamily"] = premise
            self.recompute_evidence_contract(brief)
            brief_path.write_text(json.dumps(brief), encoding="utf-8")
            brief_rel = str(brief_path.relative_to(campaign.ROOT))
            for item in task["inputs"]:
                if item["path"] == brief_rel:
                    item["sha256"] = campaign.digest(brief_path)
            for item in task["first_test_execution"]["input_receipts"]:
                if item["path"] == brief_rel:
                    item["sha256"] = campaign.digest(brief_path)
            self.recompute_execution_contract(task)
            campaign.validate_brief(
                brief,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )

            stale = copy.deepcopy(brief)
            stale_premise = stale["evidence_contract"]["scope"]["subfamily"]
            stale_premise["shared_premise_contract_id"] = (
                campaign.canonical_sha256(
                    {
                        "target_ref": stale["target_ref"],
                        "subfamily_ref": stale_premise["subfamily_ref"],
                        "shared_premise": stale_premise["shared_premise"],
                    }
                )
            )
            self.recompute_evidence_contract(stale)
            brief_path.write_text(json.dumps(stale), encoding="utf-8")
            for item in task["inputs"]:
                if item["path"] == brief_rel:
                    item["sha256"] = campaign.digest(brief_path)
            self.assert_campaign_error(
                campaign.validate_brief,
                stale,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )

    def test_complete_task_envelope_is_closed_and_bounded(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            brief_path, brief, task = self.make_authenticated_brief(Path(raw_directory))

            def remove_budget_field(candidate: dict) -> None:
                candidate["budget"].pop("output_gib")

            generated_checker_path = Path(raw_directory) / "generated_checker.py"
            generated_checker_path.write_text("raise SystemExit(0)\n", encoding="utf-8")
            generated_checker = self.file_receipt(generated_checker_path)

            def replace_with_generated_checker(candidate: dict) -> None:
                execution = candidate["first_test_execution"]
                old_path = execution["argv_template"][2]
                execution["argv_template"][2] = generated_checker["path"]
                for collection in (candidate["inputs"], execution["input_receipts"]):
                    for index, receipt in enumerate(collection):
                        if receipt["path"] == old_path:
                            collection[index] = copy.deepcopy(generated_checker)
                candidate["ownership"]["read_paths"] = [
                    generated_checker["path"] if path == old_path else path
                    for path in candidate["ownership"]["read_paths"]
                ]

            cases = {
                "unknown field": lambda candidate: candidate.__setitem__(
                    "unapproved", True
                ),
                "null profile": lambda candidate: candidate.__setitem__(
                    "profile", None
                ),
                "empty required checks": lambda candidate: candidate.__setitem__(
                    "required_checks", []
                ),
                "empty success": lambda candidate: candidate.__setitem__(
                    "success", []
                ),
                "empty stop": lambda candidate: candidate.__setitem__("stop", []),
                "empty deliverables": lambda candidate: candidate.__setitem__(
                    "deliverables", []
                ),
                "wrong ticket": lambda candidate: candidate.__setitem__(
                    "wayfinder_ticket", "wrong-ticket"
                ),
                "unapproved claim": lambda candidate: candidate.__setitem__(
                    "claims_allowed", ["proposal", "claim_proved"]
                ),
                "standing compilation claim": lambda candidate: candidate.__setitem__(
                    "claims_allowed", ["proposal", "file_compiles"]
                ),
                "altered authority": lambda candidate: candidate[
                    "standing_first_test"
                ].__setitem__("provider_calls", 1),
                "incomplete budget": remove_budget_field,
                "wall ceiling": lambda candidate: candidate["budget"].__setitem__(
                    "wall_minutes", 31
                ),
                "cpu ceiling": lambda candidate: candidate["budget"].__setitem__(
                    "cpu_cores", 3
                ),
                "memory ceiling": lambda candidate: candidate["budget"].__setitem__(
                    "memory_gib", 5
                ),
                "output ceiling": lambda candidate: candidate["budget"].__setitem__(
                    "output_gib", 0.11
                ),
                "missing execution contract": lambda candidate: candidate.pop(
                    "first_test_execution"
                ),
                "shell execution": lambda candidate: candidate[
                    "first_test_execution"
                ]["argv_template"].__setitem__(0, "/bin/sh"),
                "generated runs checker": replace_with_generated_checker,
                "unknown execution placeholder": lambda candidate: candidate[
                    "first_test_execution"
                ]["argv_template"].append("{unfrozen}"),
                "unfrozen execution operand": lambda candidate: candidate[
                    "first_test_execution"
                ]["argv_template"].append("runs/agents/unfrozen.json"),
                "non-JSON normalized result": lambda candidate: candidate[
                    "first_test_execution"
                ]["outputs"][0].__setitem__("media_type", "text/plain"),
                "execution output mismatch": lambda candidate: candidate[
                    "first_test_execution"
                ]["outputs"].clear(),
            }
            for label, mutate in cases.items():
                with self.subTest(label=label):
                    candidate = copy.deepcopy(task)
                    mutate(candidate)
                    execution = candidate.get("first_test_execution")
                    if isinstance(execution, dict):
                        execution["contract_id"] = campaign.canonical_sha256(
                            {
                                key: value
                                for key, value in execution.items()
                                if key != "contract_id"
                            }
                        )
                    self.assert_campaign_error(
                        campaign.validate_brief,
                        brief,
                        brief_path=brief_path,
                        task_packet=candidate,
                        authenticate=True,
                    )

    def test_authenticated_development_receipt_requires_exact_task_packet(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            brief_path, brief, task = self.make_authenticated_brief(directory)
            event = self.make_proposal_event(
                directory,
                brief=brief,
                task=task,
                gate_branch="no_signal",
                polarity="observes",
                stem="no-signal",
            )
            receipt = self.make_development_receipt(
                brief_path=brief_path,
                brief=brief,
                task=task,
                terminal="NO_DISCRIMINATING_SIGNAL",
                events=[event],
            )
            campaign.validate_development_receipt(
                receipt,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )
            self.assert_campaign_error(
                campaign.validate_development_receipt,
                receipt,
                brief_path=brief_path,
                authenticate=True,
            )

    def test_python_v3_verifier_replays_through_exact_guard_request(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            _brief_path, brief, task = self.make_authenticated_brief(directory)
            event, _verification_path, verification = self.make_checked_event(
                directory,
                brief=brief,
                task=task,
            )
            with mock.patch.object(
                campaign,
                "run_event_verifier",
                side_effect=self.successful_replay,
            ) as replay:
                campaign.validate_event_verification(
                    event["verification_receipt"],
                    event=event,
                    claim_contract_id=brief["evidence_contract"]["contract_id"],
                    brief=brief,
                    task=task,
                    authenticate=True,
                )
            request = verification["verification_request"]
            envelope = verification["verification_envelope"]
            replay.assert_called_once_with(
                [
                    "python3",
                    campaign.FIRST_TEST_GUARD_PATH,
                    "verify",
                    "--service-dir",
                    str(directory.relative_to(campaign.ROOT)),
                    "--request",
                    request["path"],
                    "--request-sha256",
                    request["sha256"],
                    "--envelope",
                    envelope["path"],
                ],
                timeout_seconds=1800,
            )

    def test_verification_receipt_cannot_be_rebound_to_another_event(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            _brief_path, brief, task = self.make_authenticated_brief(directory)
            event, _path, _receipt = self.make_checked_event(
                directory,
                brief=brief,
                task=task,
            )
            rebound = copy.deepcopy(event)
            rebound["binding"]["polarity"] = "refutes"
            with mock.patch.object(campaign, "run_event_verifier") as replay:
                self.assert_campaign_error(
                    campaign.validate_event_verification,
                    rebound["verification_receipt"],
                    event=rebound,
                    claim_contract_id=brief["evidence_contract"]["contract_id"],
                    brief=brief,
                    task=task,
                    authenticate=True,
                )
            replay.assert_not_called()

    def test_malformed_v1_verifier_receipt_is_rejected_before_replay(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            _brief_path, brief, task = self.make_authenticated_brief(directory)
            event, verification_path, verification = self.make_checked_event(
                directory,
                brief=brief,
                task=task,
            )
            verification["schema_version"] = 1
            verification["protocol"] = "research-event-verification-v1"
            self.rewrite_event_verification(event, verification_path, verification)
            with mock.patch.object(campaign, "run_event_verifier") as replay:
                self.assert_campaign_error(
                    campaign.validate_event_verification,
                    event["verification_receipt"],
                    event=event,
                    claim_contract_id=brief["evidence_contract"]["contract_id"],
                    brief=brief,
                    task=task,
                    authenticate=True,
                )
            replay.assert_not_called()

    def test_arbitrary_authenticated_verifier_is_rejected_before_replay(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            _brief_path, brief, task = self.make_authenticated_brief(directory)
            event, verification_path, verification = self.make_checked_event(
                directory,
                brief=brief,
                task=task,
            )
            verification["verifier_component"] = self.file_receipt(
                campaign.ROOT / "Makefile"
            )
            verification["invocation"]["argv"] = [
                "python3",
                "Makefile",
                task["inputs"][0]["path"],
            ]
            self.rewrite_event_verification(event, verification_path, verification)
            with mock.patch.object(campaign, "run_event_verifier") as replay:
                self.assert_campaign_error(
                    campaign.validate_event_verification,
                    event["verification_receipt"],
                    event=event,
                    claim_contract_id=brief["evidence_contract"]["contract_id"],
                    brief=brief,
                    task=task,
                    authenticate=True,
                )
            replay.assert_not_called()

    def test_falsifier_terminal_cannot_split_semantics_across_events(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            brief_path, brief, task = self.make_authenticated_brief(directory)
            kill_event = self.make_proposal_event(
                directory,
                brief=brief,
                task=task,
                gate_branch="kill",
                polarity="refutes",
                stem="kill-branch",
            )
            checked_kind, _path, _verification = self.make_checked_event(
                directory,
                brief=brief,
                task=task,
                kind="exact_falsifier",
                gate_branch="sidecar",
                polarity="supports",
                stem="checked-kind",
            )
            receipt = self.make_development_receipt(
                brief_path=brief_path,
                brief=brief,
                task=task,
                terminal="GATE_FALSIFIER",
                events=[kill_event, checked_kind],
            )
            with mock.patch.object(
                campaign,
                "run_event_verifier",
                side_effect=self.successful_replay,
            ):
                self.assert_campaign_error(
                    campaign.validate_development_receipt,
                    receipt,
                    brief_path=brief_path,
                    task_packet=task,
                    authenticate=True,
                )

    def test_refuting_event_cannot_be_selected_as_claim_candidate(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            brief_path, brief, task = self.make_authenticated_brief(directory)
            event, _path, _verification = self.make_checked_event(
                directory,
                brief=brief,
                task=task,
                kind="exact_falsifier",
                gate_branch="kill",
                polarity="refutes",
                stem="refutation",
            )
            receipt = self.make_development_receipt(
                brief_path=brief_path,
                brief=brief,
                task=task,
                terminal="GATE_FALSIFIER",
                events=[event],
            )
            contract = brief["evidence_contract"]
            receipt["claim_candidate"] = {
                "contract_id": contract["contract_id"],
                "model_contract_id": contract["model_contract_id"],
                "scope_contract_id": contract["scope"]["scope_contract_id"],
                "evidence_event_ids": [event["event_id"]],
                "downstream": "verification_funnel_required",
            }
            with mock.patch.object(
                campaign,
                "run_event_verifier",
                side_effect=self.successful_replay,
            ):
                self.assert_campaign_error(
                    campaign.validate_development_receipt,
                    receipt,
                    brief_path=brief_path,
                    task_packet=task,
                    authenticate=True,
                )

    def test_event_artifact_must_be_exact_task_owned_output(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            brief_path, brief, task = self.make_authenticated_brief(directory)
            event, _path, _verification = self.make_checked_event(
                directory,
                brief=brief,
                task=task,
            )
            receipt = self.make_development_receipt(
                brief_path=brief_path,
                brief=brief,
                task=task,
                terminal="GATE_POSITIVE_SIGNAL",
                events=[event],
            )
            artifact_path = event["artifact"]["path"]
            task["ownership"]["write_paths"].remove(artifact_path)
            task["deliverables"].remove(artifact_path)
            with mock.patch.object(campaign, "run_event_verifier") as replay:
                self.assert_campaign_error(
                    campaign.validate_development_receipt,
                    receipt,
                    brief_path=brief_path,
                    task_packet=task,
                    authenticate=True,
                )
            replay.assert_not_called()

    def test_authenticated_resource_observations_are_complete_and_bounded(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            brief_path, brief, task = self.make_authenticated_brief(directory)
            event, _path, _verification = self.make_checked_event(
                directory,
                brief=brief,
                task=task,
            )
            receipt = self.make_development_receipt(
                brief_path=brief_path,
                brief=brief,
                task=task,
                terminal="GATE_POSITIVE_SIGNAL",
                events=[event],
            )
            resource_cases = {
                **{
                    f"missing {key}": (key, None)
                    for key in (
                        "wall_minutes",
                        "active_minutes",
                        "cpu_seconds",
                        "peak_memory_mib",
                        "artifact_bytes",
                        "source_requests",
                    )
                },
                "wall overrun": ("wall_minutes", 31),
                "active-time overrun": ("active_minutes", 31),
                "cpu overrun": ("cpu_seconds", 1801),
                "memory overrun": ("peak_memory_mib", 1025),
                "output overrun": (
                    "artifact_bytes",
                    int(float(task["budget"]["output_gib"]) * (1024**3)) + 1,
                ),
                "source access": ("source_requests", 1),
                "understated artifacts": ("artifact_bytes", 0),
            }
            with mock.patch.object(
                campaign,
                "run_event_verifier",
                side_effect=self.successful_replay,
            ):
                for label, (key, value) in resource_cases.items():
                    with self.subTest(label=label):
                        candidate = copy.deepcopy(receipt)
                        candidate["resource_use"][key] = value
                        self.assert_campaign_error(
                            campaign.validate_development_receipt,
                            candidate,
                            brief_path=brief_path,
                            task_packet=task,
                            authenticate=True,
                        )

    def test_execution_envelope_is_required_and_nonpass_is_pure_operational(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            brief_path, brief, task = self.make_authenticated_brief(directory)
            operational = self.make_development_receipt(
                brief_path=brief_path,
                brief=brief,
                task=task,
                terminal="OPERATIONAL_STOP",
                events=[],
                envelope_terminal="LAUNCH_STOP",
            )
            campaign.validate_development_receipt(
                operational,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )
            missing = copy.deepcopy(operational)
            missing["execution_envelope"] = None
            self.assert_campaign_error(
                campaign.validate_development_receipt,
                missing,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )
            proposal = self.make_proposal_event(
                directory,
                brief=brief,
                task=task,
                gate_branch="no_signal",
                polarity="observes",
                stem="forbidden-stop-event",
            )
            contaminated = copy.deepcopy(operational)
            contaminated["evidence_events"] = [proposal]
            self.assert_campaign_error(
                campaign.validate_development_receipt,
                contaminated,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )

    def test_guarded_python_replay_mismatch_and_exact_solver_are_rejected(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            _brief_path, brief, task = self.make_authenticated_brief(directory)
            event, _verification_path, verification = self.make_checked_event(
                directory, brief=brief, task=task
            )
            replayed_envelope = json.loads(
                (campaign.ROOT / verification["verification_envelope"]["path"]).read_text(
                    encoding="utf-8"
                )
            )
            replayed_envelope["normalized_result"]["matches_expected"] = False
            with mock.patch.object(
                campaign,
                "run_event_verifier",
                return_value=subprocess.CompletedProcess(
                    [], 0, stdout=json.dumps(replayed_envelope), stderr=""
                ),
            ):
                self.assert_campaign_error(
                    campaign.validate_event_verification,
                    event["verification_receipt"],
                    event=event,
                    claim_contract_id=brief["evidence_contract"]["contract_id"],
                    brief=brief,
                    task=task,
                    authenticate=True,
                )

        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            _brief_path, brief, task = self.make_authenticated_brief(directory)
            event, _verification_path, _verification = self.make_checked_event(
                directory, brief=brief, task=task, engine="exact_solver"
            )
            with mock.patch.object(campaign, "run_event_verifier") as replay:
                self.assert_campaign_error(
                    campaign.validate_event_verification,
                    event["verification_receipt"],
                    event=event,
                    claim_contract_id=brief["evidence_contract"]["contract_id"],
                    brief=brief,
                    task=task,
                    authenticate=True,
                )
            replay.assert_not_called()

    def test_falsifier_verified_learning_is_exactly_event_bound(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            _brief_path, brief, task = self.make_authenticated_brief(directory)
            event, verification_path, verification = self.make_checked_event(
                directory,
                brief=brief,
                task=task,
                kind="exact_falsifier",
                gate_branch="kill",
                polarity="refutes",
            )
            with mock.patch.object(
                campaign,
                "run_event_verifier",
                side_effect=self.successful_replay,
            ):
                campaign.validate_event_verification(
                    event["verification_receipt"],
                    event=event,
                    claim_contract_id=brief["evidence_contract"]["contract_id"],
                    brief=brief,
                    task=task,
                    authenticate=True,
                )
            mutated = copy.deepcopy(verification)
            mutated["normalized_result"]["verified_learning"]["failing_feature"][
                "text"
            ] += " altered"
            self.rewrite_event_verification(
                event, verification_path, mutated
            )
            with mock.patch.object(campaign, "run_event_verifier") as replay:
                self.assert_campaign_error(
                    campaign.validate_event_verification,
                    event["verification_receipt"],
                    event=event,
                    claim_contract_id=brief["evidence_contract"]["contract_id"],
                    brief=brief,
                    task=task,
                    authenticate=True,
                )
            replay.assert_not_called()

    def test_native_decide_stays_computational_and_guarded(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            _brief_path, brief, task = self.make_lean_brief(directory)
            event, verification_path, verification, _audit_path, _audit = (
                self.make_lean_event(
                    directory,
                    brief=brief,
                    task=task,
                    proof_mode="native_decide",
                )
            )
            with mock.patch.object(
                campaign,
                "run_event_verifier",
                side_effect=self.successful_replay,
            ) as replay:
                campaign.validate_event_verification(
                    event["verification_receipt"],
                    event=event,
                    claim_contract_id=brief["evidence_contract"]["contract_id"],
                    brief=brief,
                    task=task,
                    authenticate=True,
                )
            replay.assert_called_once_with(["make", "test"], timeout_seconds=1800)

            unguarded = copy.deepcopy(verification)
            unguarded["guarded_runner"] = None
            self.rewrite_event_verification(event, verification_path, unguarded)
            with mock.patch.object(campaign, "run_event_verifier") as replay:
                self.assert_campaign_error(
                    campaign.validate_event_verification,
                    event["verification_receipt"],
                    event=event,
                    claim_contract_id=brief["evidence_contract"]["contract_id"],
                    brief=brief,
                    task=task,
                    authenticate=True,
                )
            replay.assert_not_called()

            relabeled, _path, _verification, _audit_path, _audit = (
                self.make_lean_event(
                    directory,
                    brief=brief,
                    task=task,
                    proof_mode="native_decide",
                    claim_level="file_compiles",
                    kind="compiling_fixed_statement",
                )
            )
            with mock.patch.object(campaign, "run_event_verifier") as replay:
                self.assert_campaign_error(
                    campaign.validate_event_verification,
                    relabeled["verification_receipt"],
                    event=relabeled,
                    claim_contract_id=brief["evidence_contract"]["contract_id"],
                    brief=brief,
                    task=task,
                    authenticate=True,
                )
            replay.assert_not_called()

    def test_kernel_theorem_requires_guarded_clean_declaration_audit(self) -> None:
        runs = campaign.ROOT / "runs" / "agents"
        runs.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            directory = Path(raw_directory)
            _brief_path, brief, task = self.make_lean_brief(directory)
            event, verification_path, verification, audit_path, audit = (
                self.make_lean_event(
                    directory,
                    brief=brief,
                    task=task,
                    proof_mode="kernel",
                )
            )
            with mock.patch.object(
                campaign,
                "run_event_verifier",
                side_effect=self.successful_replay,
            ) as replay:
                campaign.validate_event_verification(
                    event["verification_receipt"],
                    event=event,
                    claim_contract_id=brief["evidence_contract"]["contract_id"],
                    brief=brief,
                    task=task,
                    authenticate=True,
                )
            replay.assert_called_once_with(["make", "test"], timeout_seconds=1800)

            axiom_path = campaign.ROOT / audit["axiom_report"]["path"]
            axiom_path.write_text("FrozenLeanCheck\nsorryAx\n", encoding="utf-8")
            audit["axiom_report"] = self.file_receipt(axiom_path)
            audit_path.write_text(
                json.dumps(audit, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            verification["theorem_audit"] = self.file_receipt(audit_path)
            self.rewrite_event_verification(event, verification_path, verification)
            with mock.patch.object(campaign, "run_event_verifier") as replay:
                self.assert_campaign_error(
                    campaign.validate_event_verification,
                    event["verification_receipt"],
                    event=event,
                    claim_contract_id=brief["evidence_contract"]["contract_id"],
                    brief=brief,
                    task=task,
                    authenticate=True,
                )
            replay.assert_not_called()

    def test_serendipity_must_reference_real_evidence(self) -> None:
        self.receipt["serendipity"] = {
            "statement_or_observation": "An unrelated pattern appeared.",
            "model_tier": "the frozen finite control",
            "scope_ceiling": "one control",
            "relation_to_assigned_probe": "Not needed for its primary terminal.",
            "evidence_event_ids": ["f" * 64],
            "contains_claim_candidate": False,
            "downstream": "root_audit_required",
        }
        self.assert_campaign_error(
            campaign.validate_development_receipt,
            self.receipt,
            authenticate=False,
        )

    def test_claim_candidate_must_reference_frozen_evidence(self) -> None:
        event = self.receipt["evidence_events"][0]
        self.receipt["claim_candidate"] = {
            "contract_id": event["binding"]["primary_contract_id"],
            "model_contract_id": event["binding"]["model_contract_id"],
            "scope_contract_id": event["binding"]["scope_contract_id"],
            "evidence_event_ids": ["f" * 64],
            "downstream": "verification_funnel_required",
        }
        self.assert_campaign_error(
            campaign.validate_development_receipt,
            self.receipt,
            authenticate=False,
        )

    def test_event_kind_cannot_launder_proposal_into_compiling_evidence(self) -> None:
        self.receipt["evidence_events"][0]["claim_level"] = "file_compiles"
        self.assert_campaign_error(
            campaign.validate_development_receipt,
            self.receipt,
            authenticate=False,
        )

    def test_claim_candidate_cannot_rest_only_on_proposal_event(self) -> None:
        event = self.receipt["evidence_events"][0]
        self.receipt["claim_candidate"] = {
            "contract_id": event["binding"]["primary_contract_id"],
            "model_contract_id": event["binding"]["model_contract_id"],
            "scope_contract_id": event["binding"]["scope_contract_id"],
            "evidence_event_ids": [event["event_id"]],
            "downstream": "verification_funnel_required",
        }
        self.assert_campaign_error(
            campaign.validate_development_receipt,
            self.receipt,
            authenticate=False,
        )

    def test_worker_receipt_cannot_take_route_action(self) -> None:
        self.receipt["route_action"] = "promote"
        self.assert_campaign_error(
            campaign.validate_development_receipt,
            self.receipt,
            authenticate=False,
        )


if __name__ == "__main__":
    unittest.main()
