#!/usr/bin/env python3
"""Synthetic contract tests for the Orchard-XOR first-test builder."""

from __future__ import annotations

from contextlib import ExitStack, contextmanager
import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest import mock

try:
    from scripts import build_orchard_xor_first_test as builder
except ModuleNotFoundError:
    import build_orchard_xor_first_test as builder


ROOT = Path(__file__).resolve().parents[1]
SEMANTIC_CONTRACT = (
    ROOT
    / "runs/agents/20260831-self-refilling-loop/orchard-xor-author-v2/semantic-contract.md"
)


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(builder.encoded_json(value))


def read_json(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def synthetic_seed() -> dict:
    return {
        "seed_id": builder.SEED_ID,
        "target_ref": "D-HALF / synthetic StrongPredecessorBicoloringAt target",
        "title": "Synthetic Orchard-XOR contract fixture",
        "model": {
            "working_tier": "Synthetic realizable actuals and relaxed controls.",
            "target_tier": "Synthetic uniform planar target tier.",
            "transfer_status": "conjectural",
            "bridge_ref": "Synthetic unproved producer bridge.",
            "information_at_risk": "Finite controls do not prove the uniform bridge.",
        },
        "mechanism": {
            "family_hint": "synthetic predecessor-half Orchard XOR",
            "objects": "Synthetic two-anchor deletion partitions.",
            "operation": "Enumerate the synthetic two-deletion XOR palette.",
            "retained_information": "Both synthetic anchors and predecessor edges.",
        },
        "lineage": {
            "kind": "recombination",
            "parent_refs": ["synthetic-parent-a", "synthetic-parent-b"],
            "genuinely_new_step": "Retain both synthetic deletion identities.",
        },
        "nearest_controls": [
            {
                "ref": "synthetic-relaxed-control",
                "material_difference": "The control is nongeometric and exact-strong.",
            }
        ],
        "first_test": {
            "question": builder.orchard.EXPECTED_CHECKED_PREDICATE,
            "live_signal": "All synthetic actuals pass and a relaxed control fails.",
            "kill_signal": "A synthetic target-free actual has no passing cut.",
            "ceiling_minutes": 30,
            "information_if_live": "Synthetic discriminator signal only.",
            "information_if_killed": "Synthetic candidate-local falsifier only.",
            "information_if_no_signal": "Synthetic panel does not discriminate.",
        },
        "closest_source_lead": "Synthetic source lead with no theorem claim.",
        "claim_level": "proposal",
    }


class OrchardBuilderTests(unittest.TestCase):
    def setUp(self) -> None:
        builder.RUNS_AGENTS.mkdir(parents=True, exist_ok=True)
        self.run_dir = Path(
            tempfile.mkdtemp(prefix="orchard-builder-test-", dir=builder.RUNS_AGENTS)
        )
        self.addCleanup(shutil.rmtree, self.run_dir, True)
        self.service_dir = self.run_dir / "service"
        self.batch_path = self.service_dir / "batches" / "SYNTHETIC-ORCHARD" / "seed-batch.json"
        self.snapshot_path = self.run_dir / "synthetic-snapshot.json"
        self.panel_path = self.run_dir / "synthetic-panel.json"
        write_json(self.snapshot_path, {"synthetic": True, "role": "snapshot"})
        write_json(self.panel_path, {"synthetic": True, "role": "panel-fixture"})
        self.seed = synthetic_seed()
        self.batch = {
            "schema_version": 1,
            "campaign_id": "SYNTHETIC-ORCHARD",
            "generation_mode": "recombination",
            "requested_seed_count": 1,
            "snapshot": builder.guard.file_receipt(self.snapshot_path),
            "terminal": "SEED-BATCH-COMPLETE",
            "claim_level": "proposal",
            "seeds": [copy.deepcopy(self.seed)],
            "generation_metrics": {
                "private_seed_count": 1,
                "literal_duplicates_removed": 0,
                "target_equivalent_removed": 0,
                "malformed_removed": 0,
                "tool_calls": 0,
                "source_requests": 0,
                "input_tokens": 0,
                "output_tokens": 0,
                "provider_cost_usd": 0,
            },
        }
        write_json(self.batch_path, self.batch)
        self.output_dir = self.run_dir.parent / f"{self.run_dir.name}-execution"
        self.addCleanup(shutil.rmtree, self.output_dir, True)

    @property
    def batch_receipt(self) -> dict[str, str]:
        return builder.guard.file_receipt(self.batch_path)

    @contextmanager
    def inventory(self, state: str, *, claim: dict[str, str] | None = None):
        item = {
            "campaign_id": self.batch["campaign_id"],
            "seed_id": builder.SEED_ID,
            "ordinal": 0,
            "state": state,
            "seed_batch": self.batch_receipt,
            "claim": claim,
            "feedback": None,
        }
        with ExitStack() as stack:
            stack.enter_context(
                mock.patch.object(
                    builder.generator,
                    "active_standing_authorization",
                    return_value=(self.run_dir / "synthetic-authorization.json", {}),
                )
            )
            stack.enter_context(
                mock.patch.object(
                    builder.generator, "validate_accounting_chain", return_value={}
                )
            )
            stack.enter_context(
                mock.patch.object(builder.generator, "seed_inventory", return_value=[item])
            )
            yield

    def freeze(self) -> dict:
        with self.inventory("ready"):
            return builder.freeze(
                service_dir=self.service_dir,
                seed_batch=self.batch_path,
                seed_batch_sha256=builder.digest(self.batch_path),
                panel=self.panel_path,
                panel_sha256=builder.digest(self.panel_path),
                semantic_contract_path=SEMANTIC_CONTRACT,
                semantic_contract_sha256=builder.digest(SEMANTIC_CONTRACT),
                worker=builder.orchard.__file__,
                worker_sha256=builder.digest(Path(builder.orchard.__file__)),
                guard_path=builder.guard.__file__,
                guard_sha256=builder.digest(Path(builder.guard.__file__)),
                output_run_dir=self.output_dir,
                base_revision="synthetic-base-revision",
                workspace_fingerprint="synthetic-workspace-fingerprint",
            )

    def test_freeze_builds_closed_contract_without_fixed_point(self) -> None:
        result = self.freeze()
        self.assertEqual(result["terminal"], "BUILDER-READY")
        template = read_json(self.output_dir / builder.EVENT_TEMPLATE_NAME)
        brief = read_json(self.output_dir / builder.BRIEF_NAME)
        task = read_json(self.output_dir / builder.TASK_NAME)

        self.assertEqual(template["protocol"], "orchard-xor-event-template-v2")
        self.assertEqual(
            template["template_core_sha256"],
            builder.canonical_sha256(
                {key: value for key, value in template.items() if key != "template_core_sha256"}
            ),
        )
        forbidden = {"artifact", "event_id", "event_core_sha256", "artifact_receipt"}

        def keys(value: object) -> set[str]:
            if isinstance(value, dict):
                return set(value) | set().union(*(keys(item) for item in value.values()))
            if isinstance(value, list):
                return set().union(*(keys(item) for item in value))
            return set()

        self.assertTrue(forbidden.isdisjoint(keys(template)))
        contract = brief["evidence_contract"]
        self.assertEqual(
            contract["model_contract_id"], builder.canonical_sha256(contract["model"])
        )
        self.assertEqual(
            contract["scope"]["scope_contract_id"],
            builder.canonical_sha256(
                {
                    key: value
                    for key, value in contract["scope"].items()
                    if key != "scope_contract_id"
                }
            ),
        )
        self.assertEqual(
            contract["contract_id"],
            builder.canonical_sha256(
                {key: value for key, value in contract.items() if key != "contract_id"}
            ),
        )
        self.assertEqual(brief["probe"]["question"], self.seed["first_test"]["question"])
        self.assertEqual(brief["probe"]["live_signal"], self.seed["first_test"]["live_signal"])
        self.assertEqual(brief["probe"]["kill_signal"], self.seed["first_test"]["kill_signal"])
        self.assertEqual(brief["evidence_contract"]["model"], self.seed["model"])
        self.assertEqual(brief["target_ref"], self.seed["target_ref"])
        self.assertEqual(brief["evidence_contract"]["scope"]["ceiling"], "candidate-local")
        self.assertEqual(brief["lean_policy"]["mode"], "not_yet")

        execution = task["first_test_execution"]
        expected_inputs = [
            "scripts/check_orchard_xor_palette.py",
            builder.guard.file_receipt(self.panel_path)["path"],
            builder.guard.file_receipt(self.output_dir / builder.EVENT_TEMPLATE_NAME)["path"],
        ]
        self.assertEqual([item["path"] for item in execution["input_receipts"]], expected_inputs)
        self.assertEqual(
            execution["argv_template"],
            [
                "/usr/bin/python3",
                "-B",
                expected_inputs[0],
                "--input",
                expected_inputs[1],
                "--input",
                expected_inputs[2],
                "--result-fd",
                "{output_fd:terminal_artifact}",
            ],
        )
        self.assertEqual(
            execution["contract_id"],
            builder.canonical_sha256(
                {key: value for key, value in execution.items() if key != "contract_id"}
            ),
        )
        self.assertEqual(len(task["inputs"]), 7)
        self.assertEqual(task["budget"], builder.standing_authority()["limits"])

    def test_hash_drift_stops_before_publication(self) -> None:
        with self.inventory("ready"):
            with self.assertRaises(builder.BuilderError):
                builder.freeze(
                    service_dir=self.service_dir,
                    seed_batch=self.batch_path,
                    seed_batch_sha256=builder.digest(self.batch_path),
                    panel=self.panel_path,
                    panel_sha256="0" * 64,
                    semantic_contract_path=SEMANTIC_CONTRACT,
                    semantic_contract_sha256=builder.digest(SEMANTIC_CONTRACT),
                    worker=builder.orchard.__file__,
                    worker_sha256=builder.digest(Path(builder.orchard.__file__)),
                    guard_path=builder.guard.__file__,
                    guard_sha256=builder.digest(Path(builder.guard.__file__)),
                    output_run_dir=self.output_dir,
                    base_revision="synthetic-base",
                    workspace_fingerprint="synthetic-workspace",
                )
        self.assertFalse((self.output_dir / builder.EVENT_TEMPLATE_NAME).exists())

    def test_ready_identity_is_required(self) -> None:
        with self.inventory("investigated"):
            with self.assertRaisesRegex(builder.BuilderError, "authenticated ready"):
                builder.authenticate_ready_seed(
                    self.service_dir,
                    batch_receipt=self.batch_receipt,
                    campaign_id=self.batch["campaign_id"],
                )

    def test_freeze_is_write_once(self) -> None:
        self.freeze()
        before = {
            name: builder.digest(self.output_dir / name)
            for name in (builder.EVENT_TEMPLATE_NAME, builder.BRIEF_NAME, builder.TASK_NAME)
        }
        with self.assertRaisesRegex(builder.BuilderError, "write-once output"):
            self.freeze()
        self.assertEqual(
            before,
            {
                name: builder.digest(self.output_dir / name)
                for name in (builder.EVENT_TEMPLATE_NAME, builder.BRIEF_NAME, builder.TASK_NAME)
            },
        )

    def build_claim_and_pass_artifact(self) -> tuple[Path, Path]:
        self.freeze()
        brief_path = self.output_dir / builder.BRIEF_NAME
        task_path = self.output_dir / builder.TASK_NAME
        brief = read_json(brief_path)
        task = read_json(task_path)
        execution = task["first_test_execution"]
        claim = {
            "schema_version": 3,
            "protocol": builder.generator.CLAIM_PROTOCOL,
            "claim_id": f"{self.batch['campaign_id']}:{builder.SEED_ID}",
            "claimed_at": "2026-08-31T12:00:00+00:00",
            "seed": {
                "campaign_id": self.batch["campaign_id"],
                "seed_id": builder.SEED_ID,
                "seed_batch": self.batch_receipt,
            },
            "development_brief": builder.guard.file_receipt(brief_path),
            "task_packet": builder.guard.file_receipt(task_path),
            "first_test_validation": {
                "protocol": "ticket-0119-first-test-validation-v1",
                "approval_ref": builder.campaign.FIRST_TEST_APPROVAL_REF,
                "task_packet": builder.guard.file_receipt(task_path),
                "execution_contract_id": execution["contract_id"],
                "guard_component": execution["guard_component"],
                "budget": task["budget"],
                "write_paths": task["ownership"]["write_paths"],
                "claims_allowed": task["claims_allowed"],
                "decision": "pass",
            },
            "meaning": "Synthetic claim fixture; no service mutation or evidence admission.",
        }
        claim_path = self.service_dir / "claims" / self.batch["campaign_id"] / f"{builder.SEED_ID}.json"
        write_json(claim_path, claim)

        template_path = self.output_dir / builder.EVENT_TEMPLATE_NAME
        template = read_json(template_path)
        observation = {
            "panel_sha256": "1" * 64,
            "case_count": 2,
            "classification": {"terminal": "ORCHARD-XOR-NO-SIGNAL"},
            "producer_report_sha256": "2" * 64,
            "checker_verification_sha256": "3" * 64,
        }
        binding = {
            "blueprint_sha256": builder.orchard.digest(template["blueprint"]),
            "template_core_sha256": template["template_core_sha256"],
            "selected_terminal": "ORCHARD-XOR-NO-SIGNAL",
            "selected_branch_sha256": builder.orchard.digest(
                template["branches"]["ORCHARD-XOR-NO-SIGNAL"]
            ),
        }
        artifact_core = {
            "schema_version": 1,
            "protocol": builder.orchard.ARTIFACT_PROTOCOL,
            "worker_contract_id": builder.orchard.WORKER_CONTRACT_ID,
            "task_id": builder.orchard.TASK_ID,
            "semantic_contract_id": builder.orchard.SEMANTIC_CONTRACT_ID,
            "producer_engine": builder.orchard.PRODUCER_ID,
            "checker_engine": builder.orchard.CHECKER_ID,
            "synthetic_test_only": False,
            "panel_receipt": copy.deepcopy(execution["input_receipts"][1]),
            "event_template_receipt": copy.deepcopy(execution["input_receipts"][2]),
            "event_blueprint_binding": binding,
            "case_reports": [],
            "observation": observation,
            "observation_sha256": builder.orchard.digest(observation),
            "evidence_level": "synthetic_contract_fixture_only",
        }
        artifact = {
            **artifact_core,
            "artifact_core_sha256": builder.orchard.digest(artifact_core),
        }
        artifact_path = self.output_dir / builder.ARTIFACT_NAME
        write_json(artifact_path, artifact)
        artifact_raw = artifact_path.read_bytes()
        contract = builder.guard.validate_execution_contract(task, authenticate=True)
        resources = builder.guard.resource_policy(task)
        resolved_argv = [
            "9" if token == "{output_fd:terminal_artifact}" else token
            for token in execution["argv_template"]
        ]
        outcome = {
            "started_at": "2026-08-31T12:00:00+00:00",
            "finished_at": "2026-08-31T12:00:01+00:00",
            "outer_pid": 100,
            "sandbox_pid": 101,
            "sandbox_start_ticks": 1000,
            "process_group": 101,
            "resolved_argv": resolved_argv,
            "resources": resources,
            "policy_hash": builder.guard.seccomp_policy_sha256(),
            "namespace_inodes": {
                "user": 1,
                "mount": 2,
                "pid": 3,
                "net": 4,
                "ipc": 5,
                "uts": 6,
                "cgroup": 7,
            },
            "exit_code": 0,
            "signal": None,
            "wall_seconds": 0.01,
            "cpu_seconds": 0.01,
            "peak_rss": 4096,
            "streams": {
                "terminal_artifact": artifact_raw,
                "__stdout__": b"",
                "__stderr__": b"",
            },
            "worker_output_bytes": len(artifact_raw),
            "forbidden_attempts": "none",
            "violations": [],
            "terminal": "PASS",
            "stderr": b"",
        }
        writes = [
            {
                "role": "terminal_artifact",
                "path": builder.guard.file_receipt(artifact_path)["path"],
                "sha256": builder.digest(artifact_path),
                "bytes": len(artifact_raw),
                "materialized": True,
            }
        ]
        envelope = builder.guard.build_envelope(
            outcome=outcome,
            claim_path=claim_path,
            claim=claim,
            brief_path=brief_path,
            brief=brief,
            task_path=task_path,
            task=task,
            contract=contract,
            writes=writes,
        )
        envelope_path = (
            self.output_dir
            / "root-receipts"
            / f"{task['task_id']}.execution-envelope.json"
        )
        write_json(envelope_path, envelope)
        return claim_path, artifact_path

    def test_verifier_request_is_pure_derived_write_once_contract(self) -> None:
        claim_path, artifact_path = self.build_claim_and_pass_artifact()
        claim_receipt = builder.guard.file_receipt(claim_path)
        with self.inventory("investigating", claim=claim_receipt):
            result = builder.freeze_verifier_request(
                service_dir=self.service_dir,
                claim_path_value=claim_path,
                claim_sha256=builder.digest(claim_path),
                artifact_path_value=artifact_path,
                artifact_sha256=builder.digest(artifact_path),
            )
        self.assertEqual(result["terminal"], "BUILDER-READY")
        request_path = ROOT / result["verification_request"]["path"]
        request = read_json(request_path)
        self.assertEqual(
            request_path,
            self.output_dir
            / "root-receipts"
            / f"{request['event']['event_id']}.verification-request.json",
        )
        self.assertEqual(request["event"]["event_id"], request["event"]["event_core_sha256"])
        self.assertEqual(
            request["argv_template"],
            [
                "/usr/bin/python3",
                "-B",
                "scripts/check_orchard_xor_palette.py",
                "--verify-event",
                builder.guard.file_receipt(artifact_path)["path"],
                "--normalized-result-stdout",
                "--input",
                builder.guard.file_receipt(self.panel_path)["path"],
                "--input",
                builder.guard.file_receipt(self.output_dir / builder.EVENT_TEMPLATE_NAME)["path"],
            ],
        )
        normalized = request["expected_normalized_result"]
        verifier_core = {
            "verifier_component": request["checker"],
            "claim_contract_id": normalized["claim_contract_id"],
            "primary_contract_id": normalized["primary_contract_id"],
            "subject_contract_id": normalized["subject_contract_id"],
            "model_contract_id": normalized["model_contract_id"],
            "scope_contract_id": normalized["scope_contract_id"],
            "verified_event_core_sha256": normalized["verified_event_core_sha256"],
            "event_artifact": normalized["event_artifact"],
            "engine": "python_exact",
            "invocation": {"argv": request["argv_template"], "cwd": "."},
            "input_receipts": [request["event"]["artifact"], *request["input_receipts"][2:]],
        }
        self.assertEqual(
            request["verifier_contract_id"], builder.canonical_sha256(verifier_core)
        )
        with self.inventory("investigating", claim=claim_receipt):
            with self.assertRaisesRegex(builder.BuilderError, "write-once verifier"):
                builder.freeze_verifier_request(
                    service_dir=self.service_dir,
                    claim_path_value=claim_path,
                    claim_sha256=builder.digest(claim_path),
                    artifact_path_value=artifact_path,
                    artifact_sha256=builder.digest(artifact_path),
                )

    def test_verifier_request_requires_existing_pass_envelope(self) -> None:
        claim_path, artifact_path = self.build_claim_and_pass_artifact()
        task = read_json(self.output_dir / builder.TASK_NAME)
        envelope_path = (
            self.output_dir
            / "root-receipts"
            / f"{task['task_id']}.execution-envelope.json"
        )
        envelope_path.unlink()
        claim_receipt = builder.guard.file_receipt(claim_path)
        with self.inventory("investigating", claim=claim_receipt):
            with self.assertRaisesRegex(builder.BuilderError, "PASS execution envelope is absent"):
                builder.freeze_verifier_request(
                    service_dir=self.service_dir,
                    claim_path_value=claim_path,
                    claim_sha256=builder.digest(claim_path),
                    artifact_path_value=artifact_path,
                    artifact_sha256=builder.digest(artifact_path),
                )


if __name__ == "__main__":
    unittest.main()
