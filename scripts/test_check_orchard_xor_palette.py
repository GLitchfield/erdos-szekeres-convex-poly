#!/usr/bin/env python3
"""Canonical synthetic regressions for ``check_orchard_xor_palette.py``."""

from __future__ import annotations

import ast
import copy
import hashlib
import importlib.util
import itertools
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
WORKER_PATH = ROOT / "scripts/check_orchard_xor_palette.py"


def load_worker():
    spec = importlib.util.spec_from_file_location("check_orchard_xor_palette", WORKER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load Orchard-XOR worker")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


worker = load_worker()

SYNTHETIC_POINTS = [[0, 0], [7, 0], [0, 8], [1, 2]]
PROPOSAL_QUESTION = (
    "On the frozen Orchard-XOR v2 panel, do all four target-free realizable "
    "actuals have a passing two-deletion palette cut while at least one "
    "eligible exact-strong relaxed control has none?"
)


def increasing_signs(points: list[list[int]]) -> list[int]:
    return [worker.producer_orientation(points, *triple) for triple in itertools.combinations(range(len(points)), 3)]


def synthetic_panel() -> dict:
    return {
        "schema_version": 1,
        "protocol": worker.SYNTHETIC_PANEL_PROTOCOL,
        "input_role": "panel",
        "synthetic_only": True,
        "task_id": worker.TASK_ID,
        "cases": [
            {
                "case_id": "synthetic-interior-four",
                "role": "actual",
                "model_tier": "realizable_coordinates",
                "target_k": 4,
                "points": copy.deepcopy(SYNTHETIC_POINTS),
            },
            {
                "case_id": "synthetic-interior-four-control",
                "role": "control",
                "model_tier": "relaxed_nongeometric_sign_table",
                "eligible": True,
                "parent_case_id": "synthetic-interior-four",
                "target_k": 4,
                "point_count": 4,
                "increasing_signs": increasing_signs(SYNTHETIC_POINTS),
            },
        ],
    }


def event_template() -> dict:
    blueprint = {
        "claim_contract_id": "2" * 64,
        "primary_contract_id": "2" * 64,
        "subject": "primary_claim",
        "subject_contract_id": "2" * 64,
        "model_contract_id": "5" * 64,
        "scope_contract_id": "6" * 64,
        "checked_predicate": worker.EXPECTED_CHECKED_PREDICATE,
    }
    branches = {}
    for terminal, semantics in worker.BRANCH_SEMANTICS.items():
        kind, gate, polarity, damage = semantics
        learning_texts = {"failing_feature": None, "strongest_supported_statement": None}
        if terminal == "ORCHARD-XOR-KILL":
            learning_texts = {
                role: worker.KILL_LEARNING_TEXT[role]
                for role in ("failing_feature", "strongest_supported_statement")
            }
        branches[terminal] = {
            "kind": kind,
            "gate_branch": gate,
            "polarity": polarity,
            "damage_scope_reached": damage,
            "verified_learning_texts": learning_texts,
        }
    template = {
        "schema_version": 1,
        "protocol": worker.EVENT_TEMPLATE_PROTOCOL,
        "input_role": "event_template",
        "synthetic_only": True,
        "task_id": worker.TASK_ID,
        "semantic_contract_id": worker.SEMANTIC_CONTRACT_ID,
        "blueprint": blueprint,
        "branches": branches,
    }
    template["template_core_sha256"] = worker.digest(template)
    return template


def canonical_write(path: Path, value: object) -> None:
    path.write_bytes(worker.canonical_bytes(value) + b"\n")


def independent_sha256(value: object) -> str:
    raw = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def synthetic_artifact_for_terminal(terminal: str) -> tuple[dict, bytes, dict]:
    panel = synthetic_panel()
    template = event_template()
    panel_raw = worker.canonical_bytes(panel) + b"\n"
    template_raw = worker.canonical_bytes(template) + b"\n"
    artifact = worker.build_artifact(
        panel,
        worker.file_receipt("synthetic-panel.json", panel_raw),
        template,
        worker.file_receipt("synthetic-event-template.json", template_raw),
        synthetic_test_only=True,
    )
    artifact["observation"]["classification"]["terminal"] = terminal
    artifact["observation_sha256"] = worker.digest(artifact["observation"])
    artifact["event_blueprint_binding"]["selected_terminal"] = terminal
    artifact["event_blueprint_binding"]["selected_branch_sha256"] = worker.digest(
        template["branches"][terminal]
    )
    artifact.pop("artifact_core_sha256")
    artifact["artifact_core_sha256"] = worker.digest(artifact)
    return artifact, worker.canonical_bytes(artifact) + b"\n", template


class OrchardXorWorkerTests(unittest.TestCase):
    maxDiff = None

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="orchard-xor-worker-")
        self.directory = Path(self.temporary.name)
        self.panel_path = self.directory / "panel.json"
        self.template_path = self.directory / "event-template.json"
        self.artifact_path = self.directory / "artifact.json"
        canonical_write(self.panel_path, synthetic_panel())
        canonical_write(self.template_path, event_template())

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def command(self, *arguments: str, pass_fds: tuple[int, ...] = ()) -> subprocess.CompletedProcess[bytes]:
        return subprocess.run(
            ["/usr/bin/python3", "-B", str(WORKER_PATH), *arguments],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            pass_fds=pass_fds,
            check=False,
        )

    def first_run(self) -> tuple[subprocess.CompletedProcess[bytes], bytes]:
        read_fd, write_fd = os.pipe()
        try:
            completed = self.command(
                "--synthetic-test-only",
                "--result-fd", str(write_fd),
                "--input", str(self.panel_path),
                "--input", str(self.template_path),
                pass_fds=(write_fd,),
            )
        finally:
            os.close(write_fd)
        try:
            artifact = b""
            while True:
                chunk = os.read(read_fd, 65536)
                if not chunk:
                    break
                artifact += chunk
        finally:
            os.close(read_fd)
        return completed, artifact

    def materialize_artifact(self) -> dict:
        completed, raw = self.first_run()
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(completed.stdout, b"")
        self.assertEqual(completed.stderr, b"")
        self.artifact_path.write_bytes(raw)
        return json.loads(raw)

    def test_worker_is_self_contained_and_avoids_forbidden_modules(self) -> None:
        source = WORKER_PATH.read_text(encoding="utf-8")
        tree = ast.parse(source)
        imported = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported.update(alias.name.split(".")[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".")[0])
        self.assertTrue(imported <= {"__future__", "hashlib", "itertools", "json", "os", "pathlib", "sys", "typing"})
        self.assertTrue(imported.isdisjoint({"subprocess", "socket", "threading", "multiprocessing", "random", "time"}))
        self.assertNotIn("getenv", source)
        self.assertNotIn("environ", source)

    def test_first_run_round_trip_uses_fd_and_has_empty_streams(self) -> None:
        completed, raw = self.first_run()
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(completed.stdout, b"")
        self.assertEqual(completed.stderr, b"")
        self.assertTrue(raw.endswith(b"\n"))
        artifact = json.loads(raw)
        self.assertEqual(raw, worker.canonical_bytes(artifact) + b"\n")
        self.assertTrue(artifact["synthetic_test_only"])
        self.assertEqual(artifact["evidence_level"], "implementation_test")
        self.assertEqual(artifact["observation"]["classification"]["terminal"], "ORCHARD-XOR-NO-SIGNAL")

    def test_replay_round_trip_emits_only_normalized_stdout(self) -> None:
        artifact = self.materialize_artifact()
        completed = self.command(
            "--synthetic-test-only",
            "--verify-event", str(self.artifact_path),
            "--normalized-result-stdout",
            "--input", str(self.panel_path),
            "--input", str(self.template_path),
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(completed.stderr, b"")
        normalized = json.loads(completed.stdout)
        self.assertEqual(completed.stdout, worker.canonical_bytes(normalized) + b"\n")
        self.assertEqual(normalized["protocol"], worker.NORMALIZED_PROTOCOL)
        self.assertEqual(normalized["gate_branch"], "no_signal")
        self.assertEqual(normalized["polarity"], "observes")
        self.assertEqual(normalized["result"], "observes")
        self.assertEqual(normalized["observation_sha256"], artifact["observation_sha256"])
        self.assertEqual(normalized["checked_predicate"], PROPOSAL_QUESTION)
        self.assertEqual(normalized["event_artifact"]["path"], str(self.artifact_path))
        self.assertEqual(set(normalized), {
            "schema_version", "protocol", "verified_event_core_sha256",
            "event_artifact", "claim_contract_id", "primary_contract_id",
            "subject_contract_id", "model_contract_id", "scope_contract_id",
            "kind", "gate_branch", "polarity", "damage_scope_reached",
            "observation_sha256", "checked_predicate", "result",
            "verified_learning",
        })

    def test_template_has_no_post_run_event_hash_or_fixed_point_field(self) -> None:
        template = event_template()
        serialized = worker.canonical_bytes(template)
        self.assertNotIn(b"verified_event_core_sha256", serialized)
        self.assertNotIn(b"event_id", serialized)
        self.assertNotIn(b"artifact", serialized)
        self.assertEqual(template["blueprint"]["checked_predicate"], PROPOSAL_QUESTION)
        self.assertEqual(worker.EXPECTED_CHECKED_PREDICATE, PROPOSAL_QUESTION)

    def test_event_record_matches_independent_campaign_core_hash(self) -> None:
        artifact = self.materialize_artifact()
        artifact_raw = self.artifact_path.read_bytes()
        template = event_template()
        event = worker.event_record(
            str(self.artifact_path), artifact_raw, artifact, template
        )
        independent_core = {
            key: event[key]
            for key in event
            if key not in {"event_id", "verification_receipt"}
        }
        expected_hash = independent_sha256(independent_core)
        self.assertEqual(event["event_id"], expected_hash)
        self.assertIsNone(event["verification_receipt"])
        normalized = worker.normalized_result(event, template)
        self.assertEqual(normalized["verified_event_core_sha256"], expected_hash)
        self.assertEqual(normalized["event_artifact"], event["artifact"])

    def test_one_checked_predicate_is_used_for_every_terminal(self) -> None:
        for terminal in worker.TERMINALS:
            with self.subTest(terminal=terminal):
                artifact, raw, template = synthetic_artifact_for_terminal(terminal)
                event = worker.event_record("synthetic-artifact.json", raw, artifact, template)
                normalized = worker.normalized_result(event, template)
                self.assertEqual(normalized["checked_predicate"], PROPOSAL_QUESTION)

    def test_kill_learning_ids_match_independent_guard_formula(self) -> None:
        artifact, raw, template = synthetic_artifact_for_terminal("ORCHARD-XOR-KILL")
        event = worker.event_record("synthetic-kill-artifact.json", raw, artifact, template)
        normalized = worker.normalized_result(event, template)
        self.assertEqual(normalized["kind"], "exact_falsifier")
        self.assertEqual(normalized["gate_branch"], "kill")
        self.assertEqual(normalized["polarity"], "refutes")
        for role in ("failing_feature", "strongest_supported_statement"):
            claim = normalized["verified_learning"][role]
            independent_core = {
                "role": role,
                "text": claim["text"],
                "subject_contract_id": normalized["subject_contract_id"],
                "model_contract_id": normalized["model_contract_id"],
                "scope_contract_id": normalized["scope_contract_id"],
                "verified_event_core_sha256": normalized["verified_event_core_sha256"],
            }
            self.assertEqual(claim["learning_claim_id"], independent_sha256(independent_core))

    def test_observation_string_and_digest_match_campaign_formula(self) -> None:
        artifact, raw, template = synthetic_artifact_for_terminal("ORCHARD-XOR-NO-SIGNAL")
        event = worker.event_record("synthetic-artifact.json", raw, artifact, template)
        expected_text = worker.canonical_bytes(artifact["observation"]).decode("utf-8")
        self.assertEqual(event["observation"], expected_text)
        expected_digest = hashlib.sha256(expected_text.encode("utf-8")).hexdigest()
        self.assertEqual(expected_digest, artifact["observation_sha256"])
        self.assertEqual(
            worker.normalized_result(event, template)["observation_sha256"],
            expected_digest,
        )

    def test_event_record_rejects_observation_digest_corruption(self) -> None:
        artifact, _raw, template = synthetic_artifact_for_terminal("ORCHARD-XOR-NO-SIGNAL")
        artifact["observation"]["case_count"] += 1
        artifact.pop("artifact_core_sha256")
        artifact["artifact_core_sha256"] = worker.digest(artifact)
        raw = worker.canonical_bytes(artifact) + b"\n"
        with self.assertRaisesRegex(worker.WorkerError, "observation digest"):
            worker.event_record("synthetic-artifact.json", raw, artifact, template)

    def test_replay_rejects_canonical_rehashed_artifact_corruption(self) -> None:
        artifact = self.materialize_artifact()
        artifact["observation"]["case_count"] += 1
        artifact["observation_sha256"] = worker.digest(artifact["observation"])
        artifact.pop("artifact_core_sha256")
        artifact["artifact_core_sha256"] = worker.digest(artifact)
        canonical_write(self.artifact_path, artifact)
        completed = self.command(
            "--synthetic-test-only",
            "--verify-event", str(self.artifact_path),
            "--normalized-result-stdout",
            "--input", str(self.panel_path),
            "--input", str(self.template_path),
        )
        self.assertEqual(completed.returncode, 2)
        self.assertEqual(completed.stdout, b"")
        self.assertIn(b"cold reconstruction", completed.stderr)

    def test_replay_rejects_noncanonical_artifact_bytes(self) -> None:
        artifact = self.materialize_artifact()
        self.artifact_path.write_text(json.dumps(artifact, indent=2) + "\n", encoding="utf-8")
        completed = self.command(
            "--synthetic-test-only",
            "--verify-event", str(self.artifact_path),
            "--normalized-result-stdout",
            "--input", str(self.panel_path),
            "--input", str(self.template_path),
        )
        self.assertEqual(completed.returncode, 2)
        self.assertIn(b"not canonical", completed.stderr)

    def test_wrong_event_template_is_rejected_even_after_rehash(self) -> None:
        template = event_template()
        template["task_id"] = "wrong-task"
        template.pop("template_core_sha256")
        template["template_core_sha256"] = worker.digest(template)
        canonical_write(self.template_path, template)
        completed, raw = self.first_run()
        self.assertEqual(completed.returncode, 2)
        self.assertEqual(completed.stdout, b"")
        self.assertEqual(raw, b"")
        self.assertIn(b"template identity", completed.stderr)

    def test_wrong_branch_semantics_is_rejected_even_after_rehash(self) -> None:
        template = event_template()
        template["branches"]["ORCHARD-XOR-LIVE"]["polarity"] = "observes"
        template.pop("template_core_sha256")
        template["template_core_sha256"] = worker.digest(template)
        canonical_write(self.template_path, template)
        completed, raw = self.first_run()
        self.assertEqual(completed.returncode, 2)
        self.assertEqual(raw, b"")
        self.assertIn(b"branch ORCHARD-XOR-LIVE semantics", completed.stderr)

    def test_undeclared_input_role_is_rejected(self) -> None:
        panel = synthetic_panel()
        panel["input_role"] = "undeclared"
        canonical_write(self.panel_path, panel)
        completed, raw = self.first_run()
        self.assertEqual(completed.returncode, 2)
        self.assertEqual(raw, b"")
        self.assertIn(b"undeclared role", completed.stderr)

    def test_duplicate_input_role_is_rejected(self) -> None:
        second_panel_path = self.directory / "second-panel.json"
        canonical_write(second_panel_path, synthetic_panel())
        read_fd, write_fd = os.pipe()
        try:
            completed = self.command(
                "--synthetic-test-only",
                "--result-fd", str(write_fd),
                "--input", str(self.panel_path),
                "--input", str(second_panel_path),
                pass_fds=(write_fd,),
            )
        finally:
            os.close(write_fd)
        try:
            raw = os.read(read_fd, 1024)
        finally:
            os.close(read_fd)
        self.assertEqual(completed.returncode, 2)
        self.assertEqual(raw, b"")
        self.assertIn(b"duplicate raw input role", completed.stderr)

    def test_strict_mode_rejects_synthetic_panel(self) -> None:
        read_fd, write_fd = os.pipe()
        try:
            completed = self.command(
                "--result-fd", str(write_fd),
                "--input", str(self.panel_path),
                "--input", str(self.template_path),
                pass_fds=(write_fd,),
            )
        finally:
            os.close(write_fd)
        try:
            raw = os.read(read_fd, 1024)
        finally:
            os.close(read_fd)
        self.assertEqual(completed.returncode, 2)
        self.assertEqual(raw, b"")
        self.assertIn(b"strict panel", completed.stderr)

    def test_synthetic_identity_cannot_impersonate_strict_case(self) -> None:
        panel = synthetic_panel()
        panel["cases"][0]["case_id"] = next(iter(worker.EXPECTED_ACTUAL))
        canonical_write(self.panel_path, panel)
        completed, raw = self.first_run()
        self.assertEqual(completed.returncode, 2)
        self.assertEqual(raw, b"")
        self.assertIn(b"synthetic- prefix", completed.stderr)

    def test_exact_strong_engines_and_orchard_agree_on_all_1024_tables(self) -> None:
        triples = list(itertools.combinations(range(5), 3))
        for mask in range(1 << len(triples)):
            case = {
                "case_id": f"synthetic-table-{mask}",
                "role": "control",
                "model_tier": "relaxed_nongeometric_sign_table",
                "eligible": True,
                "parent_case_id": "synthetic-none",
                "target_k": 5,
                "point_count": 5,
                "increasing_signs": [1 if (mask >> index) & 1 else -1 for index in range(len(triples))],
            }
            n_producer, chi_producer = worker.producer_sign_access(case)
            n_checker, chi_checker = worker.checker_sign_access(case)
            for size in (4, 5):
                self.assertEqual(
                    worker.producer_edges(case, size, n_producer, chi_producer),
                    worker.checker_edges(case, size, n_checker, chi_checker),
                )
            for deleted in range(5):
                labels = [label for label in range(5) if label != deleted]
                self.assertEqual(
                    worker.producer_orchard_bits(labels, chi_producer),
                    worker.checker_orchard_bits(labels, chi_checker),
                )

    def test_circuit_balanced_hostile_is_not_strong(self) -> None:
        case = {
            "case_id": "synthetic-circuit-hostile",
            "role": "control",
            "model_tier": "relaxed_nongeometric_sign_table",
            "eligible": True,
            "parent_case_id": "synthetic-none",
            "target_k": 4,
            "point_count": 4,
            "increasing_signs": [1, -1, -1, 1],
        }
        _, pchi = worker.producer_sign_access(case)
        _, cchi = worker.checker_sign_access(case)
        a, b, c, d = range(4)
        circuit = (pchi(b, c, d), -pchi(a, c, d), pchi(a, b, d), -pchi(a, b, c))
        self.assertEqual(sum(value > 0 for value in circuit), 2)
        self.assertFalse(worker.producer_strong_literal(pchi, range(4)))
        self.assertFalse(worker.checker_middle_determined(cchi, range(4)))

    def test_coordinate_engines_remain_independently_equivalent(self) -> None:
        case = synthetic_panel()["cases"][0]
        pn, pchi = worker.producer_sign_access(case)
        cn, cchi = worker.checker_sign_access(case)
        self.assertEqual(pn, cn)
        for size in range(3, pn + 1):
            self.assertEqual(
                worker.producer_edges(case, size, pn, pchi),
                worker.checker_edges(case, size, cn, cchi),
            )

    def test_palette_has_four_extensions_per_anchor_and_complement_invariance(self) -> None:
        case = synthetic_panel()["cases"][0]
        n, chi = worker.producer_sign_access(case)
        rows, invariant, _ = worker.producer_palette(n, chi)
        checker_rows, checker_invariant, _ = worker.checker_palette(n, worker.checker_sign_access(case)[1])
        self.assertEqual(len(rows), 4 * (n * (n - 1) // 2))
        self.assertTrue(invariant)
        self.assertTrue(checker_invariant)
        self.assertEqual(rows, checker_rows)

    def test_orchard_threshold_parity_is_present(self) -> None:
        case = synthetic_panel()["cases"][0]
        _, chi = worker.producer_sign_access(case)
        labels = tuple(range(4))
        correct = worker.producer_orchard_bits(labels, chi)
        reference = labels[0]
        without_threshold = {reference: 0}
        for vertex in labels[1:]:
            parity = 0
            others = [label for label in labels if label not in (reference, vertex)]
            for a, b in itertools.combinations(others, 2):
                parity ^= chi(a, b, reference) != chi(a, b, vertex)
            without_threshold[vertex] = int(parity)
        self.assertNotEqual(correct, without_threshold)

    def test_learning_claims_bind_every_guard_identity(self) -> None:
        arguments = {
            "subject_contract_id": "a" * 64,
            "model_contract_id": "b" * 64,
            "scope_contract_id": "c" * 64,
            "verified_event_core_sha256": "d" * 64,
        }
        claim = worker.learning_claim(
            "failing_feature", worker.KILL_LEARNING_TEXT["failing_feature"],
            **arguments,
        )
        for key, replacement in (
            ("subject_contract_id", "e" * 64),
            ("model_contract_id", "f" * 64),
            ("scope_contract_id", "1" * 64),
            ("verified_event_core_sha256", "2" * 64),
        ):
            changed_arguments = dict(arguments)
            changed_arguments[key] = replacement
            changed = worker.learning_claim(
                "failing_feature", worker.KILL_LEARNING_TEXT["failing_feature"],
                **changed_arguments,
            )
            self.assertNotEqual(claim["learning_claim_id"], changed["learning_claim_id"])
        self.assertEqual(claim["subject_contract_id"], "a" * 64)

    def test_mixed_or_incomplete_cli_modes_are_rejected(self) -> None:
        completed = self.command(
            "--synthetic-test-only",
            "--normalized-result-stdout",
            "--input", str(self.panel_path),
            "--input", str(self.template_path),
        )
        self.assertEqual(completed.returncode, 2)
        self.assertEqual(completed.stdout, b"")
        self.assertIn(b"neither exact", completed.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
