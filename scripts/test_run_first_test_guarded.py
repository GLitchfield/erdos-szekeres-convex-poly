#!/usr/bin/env python3
"""Focused regressions for the Ticket-0119 local execution guard."""

from __future__ import annotations

import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from scripts import run_first_test_guarded as guard


class GuardContractTests(unittest.TestCase):
    def make_task(self) -> dict:
        checker = {
            "path": "scripts/check_guard_fixture.py",
            "sha256": "1" * 64,
        }
        raw = {
            "path": "runs/agents/guard-contract-fixture/input.json",
            "sha256": "2" * 64,
        }
        output = "runs/agents/guard-contract-fixture/terminal.json"
        task = {
            "run_id": "guard-contract-fixture",
            "task_id": "guard-contract-task",
            "inputs": [copy.deepcopy(checker), copy.deepcopy(raw)],
            "ownership": {
                "read_paths": [checker["path"], raw["path"]],
                "write_paths": [output],
            },
            "budget": {
                "wall_minutes": 30,
                "cpu_cores": 2,
                "memory_gib": 4,
                "output_gib": 0.1,
            },
            "deliverables": [output],
            "claims_allowed": ["proposal", "computational_evidence"],
            "theorem_contract": None,
            "standing_first_test": {
                "limits": {
                    "wall_minutes": 30,
                    "cpu_cores": 2,
                    "memory_gib": 4,
                    "output_gib": 0.1,
                }
            },
        }
        execution = {
            "protocol": guard.GUARD_PROTOCOL,
            "contract_id": "0" * 64,
            "guard_component": {
                "path": "scripts/run_first_test_guarded.py",
                "sha256": "3" * 64,
            },
            "engine": "python_exact",
            "argv_template": [
                "/usr/bin/python3",
                "-B",
                checker["path"],
                "--input",
                raw["path"],
                "--result-fd",
                "{output_fd:terminal_artifact}",
            ],
            "cwd": ".",
            "input_receipts": [copy.deepcopy(checker), copy.deepcopy(raw)],
            "outputs": [
                {
                    "role": "terminal_artifact",
                    "path": output,
                    "media_type": "application/json",
                }
            ],
            "normalized_result_role": "terminal_artifact",
            "process_model": guard.PROCESS_MODEL,
        }
        execution["contract_id"] = guard.canonical_sha256(
            {key: value for key, value in execution.items() if key != "contract_id"}
        )
        task["first_test_execution"] = execution
        return task

    def test_closed_contract_accepts_exact_python_checker(self) -> None:
        task = self.make_task()
        self.assertEqual(
            guard.validate_execution_contract(task, authenticate=False),
            task["first_test_execution"],
        )

    def test_contract_id_and_unknown_key_fail_closed(self) -> None:
        task = self.make_task()
        task["first_test_execution"]["contract_id"] = "f" * 64
        with self.assertRaisesRegex(guard.GuardError, "contract_id"):
            guard.validate_execution_contract(task, authenticate=False)
        task = self.make_task()
        task["first_test_execution"]["shell"] = True
        with self.assertRaisesRegex(guard.GuardError, "keys differ"):
            guard.validate_execution_contract(task, authenticate=False)

    def test_shell_lean_and_compilation_claims_are_rejected(self) -> None:
        task = self.make_task()
        execution = task["first_test_execution"]
        execution["argv_template"][0] = "/bin/sh"
        execution["contract_id"] = guard.canonical_sha256(
            {key: value for key, value in execution.items() if key != "contract_id"}
        )
        with self.assertRaisesRegex(guard.GuardError, "python3 -B"):
            guard.validate_execution_contract(task, authenticate=False)

        task = self.make_task()
        task["claims_allowed"].append("file_compiles")
        with self.assertRaisesRegex(guard.GuardError, "cannot claim compilation"):
            guard.validate_execution_contract(task, authenticate=False)

        task = self.make_task()
        task["theorem_contract"] = {
            "name": "forbidden",
            "statement": "False",
            "statement_may_change": False,
        }
        with self.assertRaisesRegex(guard.GuardError, "theorem contract"):
            guard.validate_execution_contract(task, authenticate=False)

    def test_every_input_and_output_is_exact(self) -> None:
        task = self.make_task()
        execution = task["first_test_execution"]
        execution["argv_template"].remove(
            "runs/agents/guard-contract-fixture/input.json"
        )
        execution["contract_id"] = guard.canonical_sha256(
            {key: value for key, value in execution.items() if key != "contract_id"}
        )
        with self.assertRaisesRegex(guard.GuardError, "not exact argv operands"):
            guard.validate_execution_contract(task, authenticate=False)

        task = self.make_task()
        task["ownership"]["write_paths"] = [
            "runs/agents/guard-contract-fixture/other.json"
        ]
        with self.assertRaisesRegex(guard.GuardError, "exactly equal"):
            guard.validate_execution_contract(task, authenticate=False)

    def test_worker_argv_substitution_is_role_only(self) -> None:
        contract = self.make_task()["first_test_execution"]
        resolved = guard.resolve_worker_argv(contract, {"terminal_artifact": 17})
        self.assertEqual(resolved[-1], "17")
        contract = copy.deepcopy(contract)
        contract["argv_template"].append("{not-supported}")
        with self.assertRaisesRegex(guard.GuardError, "unsupported placeholder"):
            guard.resolve_worker_argv(contract, {"terminal_artifact": 17})

    def test_command_builder_contains_frozen_controls_and_no_shell(self) -> None:
        argv = guard.build_bwrap_argv(
            work_root=Path("/tmp/work"),
            empty_shm=Path("/tmp/empty"),
            cpu_affinity=[3, 7],
            output_bytes=guard.MAX_OUTPUT_BYTES,
            contract_fd=11,
            result_fd=12,
            status_fd=13,
        )
        self.assertEqual(argv[:3], ["/usr/bin/taskset", "--cpu-list", "3,7"])
        for token in (
            "--unshare-all",
            "--unshare-user",
            "--disable-userns",
            "--assert-userns-disabled",
            "--die-with-parent",
            "--clearenv",
            "--ro-bind",
            "--tmpfs",
            "--json-status-fd",
        ):
            self.assertIn(token, argv)
        self.assertIn(str(guard.MAX_OUTPUT_BYTES), argv)
        self.assertNotIn("sh", argv)
        self.assertNotIn("-c", argv)

    def test_schema_has_both_root_envelope_protocols(self) -> None:
        schema_path = (
            guard.ROOT
            / "docs/agents/schemas/research-first-test-execution-envelope.schema.json"
        )
        schema = json.loads(schema_path.read_text(encoding="utf-8"))
        self.assertEqual(len(schema["oneOf"]), 2)
        serialized = json.dumps(schema, sort_keys=True)
        self.assertIn(guard.ENVELOPE_PROTOCOL, serialized)
        self.assertIn(guard.VERIFIER_ENVELOPE_PROTOCOL, serialized)
        self.assertIn("not-observed", serialized)

    def test_root_receipt_write_is_exactly_idempotent(self) -> None:
        guard.RUNS_AGENTS.mkdir(parents=True, exist_ok=True)
        directory = Path(
            tempfile.mkdtemp(prefix="guard-idempotence-", dir=guard.RUNS_AGENTS)
        )
        self.addCleanup(shutil.rmtree, directory, True)
        path = directory / "root-receipts" / "envelope.json"
        guard._write_envelope_once(path, {"frozen": 1})
        first = path.read_bytes()
        guard._write_envelope_once(path, {"frozen": 1})
        self.assertEqual(path.read_bytes(), first)
        with self.assertRaisesRegex(guard.GuardError, "other bytes"):
            guard._write_envelope_once(path, {"frozen": 2})

    def test_built_pass_envelopes_validate_their_complete_identity(self) -> None:
        guard.RUNS_AGENTS.mkdir(parents=True, exist_ok=True)
        directory = Path(
            tempfile.mkdtemp(prefix="guard-envelope-", dir=guard.RUNS_AGENTS)
        )
        self.addCleanup(shutil.rmtree, directory, True)
        claim_path = directory / "claim.json"
        brief_path = directory / "brief.json"
        task_path = directory / "task.json"
        artifact_path = directory / "artifact.json"
        claim = {"claim_id": "campaign:seed"}
        brief = {"brief_id": "brief"}
        task = {"task_id": "task"}
        artifact = b'{"checked":true}\n'
        for path, value in (
            (claim_path, claim), (brief_path, brief), (task_path, task)
        ):
            path.write_text(json.dumps(value) + "\n", encoding="utf-8")
        artifact_path.write_bytes(artifact)
        contract = {
            "contract_id": "4" * 64,
            "outputs": [{
                "role": "terminal_artifact",
                "path": artifact_path.relative_to(guard.ROOT).as_posix(),
                "media_type": "application/json",
            }],
        }
        policy_hash = guard.seccomp_policy_sha256()
        outcome = {
            "started_at": "2026-08-31T00:00:00+00:00",
            "finished_at": "2026-08-31T00:00:01+00:00",
            "outer_pid": 10,
            "sandbox_pid": 11,
            "sandbox_start_ticks": 12,
            "process_group": 13,
            "resolved_argv": ["/usr/bin/python3", "-B", "scripts/check.py", "17"],
            "resources": {
                "wall_seconds": 60,
                "cpu_affinity": [0],
                "memory_bytes": 1024**3,
                "output_bytes": 1024**2,
            },
            "policy_hash": policy_hash,
            "namespace_inodes": {
                "user": 1, "mount": 2, "pid": 3, "net": 4,
                "ipc": 5, "uts": 6, "cgroup": 7,
            },
            "exit_code": 0,
            "signal": None,
            "wall_seconds": 0.1,
            "cpu_seconds": 0.01,
            "peak_rss": 4096,
            "streams": {
                "terminal_artifact": artifact,
                "__stdout__": b"",
                "__stderr__": b"",
            },
            "worker_output_bytes": len(artifact),
            "forbidden_attempts": "none",
            "violations": [],
            "terminal": "PASS",
            "stderr": b"",
        }
        writes = [{
            "role": "terminal_artifact",
            "path": artifact_path.relative_to(guard.ROOT).as_posix(),
            "sha256": guard.digest_bytes(artifact),
            "bytes": len(artifact),
            "materialized": True,
        }]
        envelope = guard.build_envelope(
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
        expected_identity = envelope["identity"]
        self.assertEqual(
            guard.validate_envelope(
                envelope,
                expected_identity=expected_identity,
                authenticate_outputs=True,
            )["terminal"],
            "PASS",
        )

        expected = {"decision": "verified"}
        request = {
            "guard_component": guard.file_receipt(guard.GUARD_PATH),
            "verifier_contract_id": "5" * 64,
            "claim_id": claim["claim_id"],
            "task_id": task["task_id"],
            "event": {
                "event_id": "event",
                "event_core_sha256": "6" * 64,
                "subject_contract_id": "7" * 64,
                "model_contract_id": "8" * 64,
                "scope_contract_id": "9" * 64,
                "artifact": guard.file_receipt(artifact_path),
            },
            "argv_template": [
                "/usr/bin/python3", "-B", "scripts/check.py",
                "--verify-event", guard.file_receipt(artifact_path)["path"],
                "--normalized-result-stdout",
            ],
            "expected_normalized_result": expected,
            "budget": {
                "wall_minutes": 1,
                "cpu_cores": 1,
                "memory_gib": 1,
                "output_gib": 1 / 1024,
            },
        }
        request_path = directory / "event.verification-request.json"
        request_path.write_text(json.dumps(request) + "\n", encoding="utf-8")
        normalized = guard.canonical_bytes(expected) + b"\n"
        verifier_outcome = copy.deepcopy(outcome)
        verifier_outcome["resolved_argv"] = [
            "/usr/bin/python3", "-B", "scripts/check.py",
            "--verify-event", request["event"]["artifact"]["path"],
            "--normalized-result-stdout",
        ]
        verifier_outcome["streams"] = {
            "__stdout__": normalized, "__stderr__": b""
        }
        verifier_outcome["worker_output_bytes"] = len(normalized)
        verifier_envelope = guard.build_verifier_envelope(
            outcome=verifier_outcome,
            request_path=request_path,
            request=request,
            claim_path=claim_path,
            task_path=task_path,
        )
        self.assertEqual(
            guard.validate_verifier_envelope(
                verifier_envelope,
                request_path=request_path,
                request=request,
                claim_path=claim_path,
                task_path=task_path,
            )["terminal"],
            "PASS",
        )


class GuardIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.capability = guard.capability_report("network")

    def setUp(self) -> None:
        if self.capability["terminal"] != "PASS":
            self.skipTest(
                "guard capability operational stop: "
                + json.dumps(self.capability, sort_keys=True)
            )
        guard.RUNS_AGENTS.mkdir(parents=True, exist_ok=True)
        self.directory = Path(
            tempfile.mkdtemp(prefix="guard-integration-", dir=guard.RUNS_AGENTS)
        )
        self.addCleanup(shutil.rmtree, self.directory, True)
        self.claim = self.directory / "claim.json"
        self.brief = self.directory / "brief.json"
        self.task_path = self.directory / "task.json"
        for path in (self.claim, self.brief, self.task_path):
            path.write_text("{}\n", encoding="utf-8")
        self.task = {
            "budget": {
                "wall_minutes": 1,
                "cpu_cores": 1,
                "memory_gib": 1,
                "output_gib": 0.001,
            }
        }

    def receipt(self, path: Path) -> dict[str, str]:
        return {
            "path": path.relative_to(guard.ROOT).as_posix(),
            "sha256": guard.digest(path),
        }

    def execute(self, checker_source: str, *, with_output: bool) -> dict:
        checker = self.directory / "checker.py"
        checker.write_text(checker_source, encoding="utf-8")
        checker_receipt = self.receipt(checker)
        inputs = [checker_receipt]
        argv = ["/usr/bin/python3", "-B", checker_receipt["path"]]
        outputs: list[dict[str, str]] = []
        if with_output:
            raw = self.directory / "input.json"
            raw.write_text('{"value":7}\n', encoding="utf-8")
            raw_receipt = self.receipt(raw)
            inputs.append(raw_receipt)
            argv.extend(
                [
                    "--input",
                    raw_receipt["path"],
                    "--result-fd",
                    "{output_fd:terminal_artifact}",
                ]
            )
            outputs.append(
                {
                    "role": "terminal_artifact",
                    "path": (self.directory / "terminal.json")
                    .relative_to(guard.ROOT)
                    .as_posix(),
                    "media_type": "application/json",
                }
            )
        return guard._execute(
            contract={
                "argv_template": argv,
                "input_receipts": inputs,
                "outputs": outputs,
            },
            task=self.task,
            claim_path=self.claim,
            brief_path=self.brief,
            task_path=self.task_path,
        )

    def test_capability_observes_filter_and_network_sigsys(self) -> None:
        self.assertEqual(self.capability["positive"]["terminal"], "PASS")
        self.assertEqual(self.capability["negative"]["terminal"], "PASS")
        self.assertEqual(self.capability["negative"]["signal"], 31)
        self.assertTrue(self.capability["positive"]["observed"])

    def test_capability_kills_write_open_and_spawn(self) -> None:
        for attempt in ("write", "spawn"):
            with self.subTest(attempt=attempt):
                result = guard.run_capability_probe(attempt)
                self.assertEqual(result["terminal"], "PASS", result)
                self.assertEqual(result["signal"], 31)

    def test_tiny_checker_passes_with_exact_framed_output(self) -> None:
        outcome = self.execute(
            """import json, os, sys
path = sys.argv[sys.argv.index("--input") + 1]
descriptor = int(sys.argv[sys.argv.index("--result-fd") + 1])
value = json.load(open(path, encoding="utf-8"))
data = json.dumps({"value": value["value"]}, sort_keys=True, separators=(",", ":")) + "\\n"
os.write(descriptor, data.encode("utf-8"))
""",
            with_output=True,
        )
        self.assertEqual(outcome["terminal"], "PASS", outcome["violations"])
        self.assertEqual(outcome["forbidden_attempts"], "none")
        self.assertEqual(
            outcome["streams"]["terminal_artifact"], b'{"value":7}\n'
        )
        self.assertTrue(all(outcome["namespace_inodes"].values()))

    def test_socket_attempt_is_sigsys_and_never_passes(self) -> None:
        outcome = self.execute(
            """import socket
socket.socket()
""",
            with_output=False,
        )
        self.assertEqual(outcome["terminal"], "VIOLATION")
        self.assertEqual(outcome["signal"], 31)
        self.assertEqual(outcome["forbidden_attempts"], "at-least-one")
        self.assertNotEqual(outcome["terminal"], "PASS")

    def test_tiny_event_replay_emits_only_canonical_stdout(self) -> None:
        checker = self.directory / "verifier.py"
        artifact = self.directory / "artifact.json"
        raw = self.directory / "raw.json"
        checker.write_text(
            """import hashlib, json, sys
artifact_path = sys.argv[sys.argv.index("--verify-event") + 1]
raw_path = sys.argv[sys.argv.index("--input") + 1]
artifact = json.load(open(artifact_path, encoding="utf-8"))
raw = json.load(open(raw_path, encoding="utf-8"))
value = {"artifact": artifact["value"], "raw": raw["control"]}
print(json.dumps(value, sort_keys=True, separators=(",", ":")))
""",
            encoding="utf-8",
        )
        artifact.write_text('{"value":11}\n', encoding="utf-8")
        raw.write_text('{"control":13}\n', encoding="utf-8")
        checker_receipt = self.receipt(checker)
        artifact_receipt = self.receipt(artifact)
        raw_receipt = self.receipt(raw)
        outcome = guard._execute(
            contract={
                "argv_template": [
                    "/usr/bin/python3", "-B", checker_receipt["path"],
                    "--verify-event", artifact_receipt["path"],
                    "--normalized-result-stdout",
                    "--input", raw_receipt["path"],
                ],
                "input_receipts": [
                    checker_receipt, artifact_receipt, raw_receipt
                ],
                "outputs": [],
            },
            task=self.task,
            claim_path=self.claim,
            brief_path=self.brief,
            task_path=self.task_path,
        )
        self.assertEqual(outcome["terminal"], "PASS", outcome["violations"])
        self.assertEqual(outcome["streams"]["__stdout__"], b'{"artifact":11,"raw":13}\n')
        self.assertEqual(outcome["streams"]["__stderr__"], b"")


if __name__ == "__main__":
    unittest.main()
