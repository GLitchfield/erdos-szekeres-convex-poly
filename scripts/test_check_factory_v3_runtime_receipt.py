from __future__ import annotations

import base64
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_factory_v3_runtime_receipt import (  # noqa: E402
    RuntimeReceiptError,
    validate_runtime_receipt,
)


# These literals and digest equations deliberately do not import implementation
# constants or helpers.  The suite is an independent oracle for the frozen
# successor receipt contract.
APPROVAL_POLICY = "never"
CHAIN_DOMAIN = b"factory-v3-event-chain-v2"
COMPLETION_DOMAIN = b"factory-v3-completion-v2"
RUN_DOMAIN = b"factory-v3-run-v2"
COMPLETION_VERSION = "factory-v3-completion-v2"
CODEX_VERSION = "codex-cli 0.149.0"
CONTRACT_ID = "factory-v3-one-call-telemetry-v1"
CREDENTIAL_MECHANISM = "codex-home-auth-json-outer-only"
DESCRIPTOR_VERSION = "factory-v3-runtime-descriptor-v6"
LAUNCH_VERSION = "factory-v3-launch-receipt-v6"
PERMISSION_PROFILE = "factory-v3-two-layer-exact-v1"
PROCESS_VERSION = "factory-v3-process-receipt-v6"
PROVIDER_POLICY = "gpt-5.6-sol:max"
SANDBOX_POLICY = "outer-control-plus-inner-tool-profile"
INNER_PROFILE_NAME = "factory_v3_tool_v1"
EXPECTED_RESOURCE_LIMITS = {
    "wall_seconds": 900,
    "cpu_cores": 1,
    "memory_bytes": 2 * 1024**3,
    "output_bytes": 21_474_836,
    "kill_grace_seconds": 5,
}


def canonical_bytes(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def compact_hash(value: object) -> str:
    return sha256(canonical_bytes(value))


def expected_agent_argv(root: Path, executable_path: str) -> list[str]:
    input_path = (root / "work/input.json").as_posix()
    schema_path = (root / "control/output-schema.json").as_posix()
    work_path = (root / "work").as_posix()
    filesystem_value = "{" + ",".join(
        f'{json.dumps(path)}="read"'
        for path in (":minimal", executable_path, input_path)
    ) + "}"
    return [
        executable_path,
        "exec",
        "--json",
        "--ephemeral",
        "--ignore-user-config",
        "--ignore-rules",
        "--strict-config",
        "--skip-git-repo-check",
        "--model",
        "gpt-5.6-sol",
        "-c",
        'model_reasoning_effort="max"',
        "-c",
        f'default_permissions="{INNER_PROFILE_NAME}"',
        "-c",
        f"permissions.{INNER_PROFILE_NAME}.filesystem={filesystem_value}",
        "-c",
        f"permissions.{INNER_PROFILE_NAME}.network.enabled=false",
        "--output-schema",
        schema_path,
        "--ask-for-approval",
        "never",
        "-C",
        work_path,
        "-",
    ]


def write_bytes(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def write_json(path: Path, value: object) -> None:
    write_bytes(path, canonical_bytes(value) + b"\n")


class RuntimeFixture:
    def __init__(self, root: Path) -> None:
        self.root = root
        (root / "control").mkdir(parents=True)
        (root / "work").mkdir()
        (root / "evidence").mkdir()

        self.input_bytes = b'{"canary":"input"}\n'
        self.prompt_bytes = b"nonresearch runtime canary\n"
        self.schema_bytes = b'{"type":"object"}\n'
        write_bytes(root / "work/input.json", self.input_bytes)
        write_bytes(root / "control/prompt.txt", self.prompt_bytes)
        write_bytes(root / "control/output-schema.json", self.schema_bytes)

        self.executable = Path(sys.executable).resolve()
        self.expected_output = {
            "canary_id": CONTRACT_ID,
            "input_sha256": sha256(self.input_bytes),
            "schema_version": 1,
            "status": "ok",
        }
        self.expected_command = "sha256sum input.json"
        self.expected_command_output = f"{sha256(self.input_bytes)}  input.json\n"
        self.argv = expected_agent_argv(root, str(self.executable))
        self.input_manifest = [
            {"path": "control/output-schema.json", "sha256": sha256(self.schema_bytes)},
            {"path": "control/prompt.txt", "sha256": sha256(self.prompt_bytes)},
            {"path": "work/input.json", "sha256": sha256(self.input_bytes)},
        ]
        self.descriptor = {
            "schema_version": 1,
            "descriptor_version": DESCRIPTOR_VERSION,
            "contract_id": CONTRACT_ID,
            "evidence_mode": "live-runtime",
            "call_id": "telemetry-canary-1",
            "stage": "canary",
            "provider_policy": PROVIDER_POLICY,
            "codex_version": CODEX_VERSION,
            "executable_path": str(self.executable),
            "executable_sha256": sha256(self.executable.read_bytes()),
            "argv": self.argv,
            "argv_sha256": compact_hash(self.argv),
            "task_path": "control/prompt.txt",
            "task_sha256": sha256(self.prompt_bytes),
            "input_manifest": self.input_manifest,
            "input_fingerprint": compact_hash(self.input_manifest),
            "cwd": "work",
            "permission_profile": PERMISSION_PROFILE,
            "sandbox_policy": SANDBOX_POLICY,
            "approval_policy": APPROVAL_POLICY,
            "credential_mechanism": CREDENTIAL_MECHANISM,
            "expected_command": self.expected_command,
            "expected_command_output": self.expected_command_output,
            "expected_output": self.expected_output,
            "expected_output_canonical_sha256": compact_hash(self.expected_output),
            "allowed_item_types": ["agent_message", "command_execution", "reasoning"],
            "required_lifecycle_types": ["agent_message", "command_execution"],
            "expected_command_count": 1,
            "expected_source_count": 0,
            "skeleton_policy": "none",
            "resource_limits": dict(EXPECTED_RESOURCE_LIMITS),
            "artifacts": {
                "launch_receipt": "evidence/launch-receipt.json",
                "event_receipts": "evidence/event-receipts.jsonl",
                "raw_event_log": "evidence/events.raw.jsonl",
                "stderr": "evidence/stderr.log",
                "final_output": "evidence/final-output.json",
                "process_receipt": "evidence/process-receipt.json",
            },
        }
        self.save_descriptor()
        self.launch = {
            "schema_version": 1,
            "receipt_version": LAUNCH_VERSION,
            "contract_id": self.descriptor["contract_id"],
            "invocation_id": "invocation-fixture-1",
            "launch_descriptor_sha256": sha256(self.descriptor_path.read_bytes()),
            "executable_path": self.descriptor["executable_path"],
            "executable_sha256": self.descriptor["executable_sha256"],
            "codex_version": self.descriptor["codex_version"],
            "argv": self.descriptor["argv"],
            "argv_sha256": self.descriptor["argv_sha256"],
            "provider_policy": self.descriptor["provider_policy"],
            "cwd": self.descriptor["cwd"],
            "permission_profile": self.descriptor["permission_profile"],
            "sandbox_policy": self.descriptor["sandbox_policy"],
            "approval_policy": self.descriptor["approval_policy"],
            "credential_mechanism": self.descriptor["credential_mechanism"],
            "task_sha256": self.descriptor["task_sha256"],
            "input_fingerprint": self.descriptor["input_fingerprint"],
            "limiter": {
                "implementation": "factory-v3-local-launcher-v1",
                **EXPECTED_RESOURCE_LIMITS,
                "process_group": True,
                "stdout_line_envelope": True,
            },
            "child_pid": 4242,
            "child_pgid": 4242,
            "pre_spawn_realtime_ns": 1_000_000_000,
            "pre_spawn_monotonic_ns": 1_000_000_000,
            "post_spawn_realtime_ns": 1_010_000_000,
            "post_spawn_monotonic_ns": 1_010_000_000,
            "retry_count": 0,
        }
        self.save_launch()
        self.events = self.base_events()
        write_bytes(root / "evidence/stderr.log", b"")
        write_json(root / "evidence/final-output.json", self.expected_output)
        self.write_events(self.events)
        self.expected_descriptor_sha256 = sha256(self.descriptor_path.read_bytes())

    @property
    def descriptor_path(self) -> Path:
        return self.root / "control/launch-descriptor.json"

    @property
    def launch_path(self) -> Path:
        return self.root / "evidence/launch-receipt.json"

    @property
    def process_path(self) -> Path:
        return self.root / "evidence/process-receipt.json"

    def base_events(self) -> list[dict]:
        final_text = canonical_bytes(self.expected_output).decode("utf-8")
        return [
            {"type": "thread.started", "thread_id": "thread-1"},
            {"type": "turn.started", "thread_id": "thread-1", "turn_id": "turn-1"},
            {
                "type": "item.started",
                "thread_id": "thread-1",
                "turn_id": "turn-1",
                "item": {"id": "command-1", "type": "command_execution", "command": self.expected_command},
            },
            {
                "type": "item.completed",
                "thread_id": "thread-1",
                "turn_id": "turn-1",
                "item": {
                    "id": "command-1",
                    "type": "command_execution",
                    "command": self.expected_command,
                    "aggregated_output": self.expected_command_output,
                    "exit_code": 0,
                    "status": "completed",
                },
            },
            {
                "type": "item.completed",
                "thread_id": "thread-1",
                "turn_id": "turn-1",
                "item": {"id": "reasoning-1", "type": "reasoning", "text": "private"},
            },
            {
                "type": "item.started",
                "thread_id": "thread-1",
                "turn_id": "turn-1",
                "item": {"id": "message-1", "type": "agent_message"},
            },
            {
                "type": "item.completed",
                "thread_id": "thread-1",
                "turn_id": "turn-1",
                "item": {"id": "message-1", "type": "agent_message", "text": final_text},
            },
            {
                "type": "turn.completed",
                "thread_id": "thread-1",
                "turn_id": "turn-1",
                "usage": {"input_tokens": 10, "cached_input_tokens": 0, "output_tokens": 5},
            },
        ]

    def save_descriptor(self) -> None:
        write_json(self.descriptor_path, self.descriptor)

    def save_launch(self) -> None:
        write_json(self.launch_path, self.launch)

    def rebind_descriptor(self) -> None:
        self.save_descriptor()
        for field in (
            "contract_id",
            "executable_path",
            "executable_sha256",
            "codex_version",
            "argv",
            "argv_sha256",
            "provider_policy",
            "cwd",
            "permission_profile",
            "sandbox_policy",
            "approval_policy",
            "credential_mechanism",
            "task_sha256",
            "input_fingerprint",
        ):
            self.launch[field] = self.descriptor[field]
        self.launch["launch_descriptor_sha256"] = sha256(self.descriptor_path.read_bytes())
        self.save_launch()
        self.write_events(self.events)

    def write_events(self, events: list[dict]) -> None:
        self.write_raw_lines([canonical_bytes(event) + b"\n" for event in events])

    def write_raw_lines(self, lines: list[bytes]) -> None:
        raw = b"".join(lines)
        write_bytes(self.root / "evidence/events.raw.jsonl", raw)
        chain = hashlib.sha256(
            CHAIN_DOMAIN
            + b"\0"
            + bytes.fromhex(sha256(self.descriptor_path.read_bytes()))
            + bytes.fromhex(sha256(self.launch_path.read_bytes()))
        ).digest()
        rows = []
        for sequence, line in enumerate(lines, start=1):
            mono = self.launch["post_spawn_monotonic_ns"] + sequence * 10_000_000
            real = self.launch["post_spawn_realtime_ns"] + sequence * 10_000_000
            line_hash = sha256(line)
            previous = chain.hex()
            chain = hashlib.sha256(
                chain
                + sequence.to_bytes(8, "big")
                + mono.to_bytes(8, "big")
                + bytes.fromhex(line_hash)
            ).digest()
            rows.append({
                "schema_version": 1,
                "sequence": sequence,
                "received_monotonic_ns": mono,
                "received_realtime_ns": real,
                "raw_line_base64": base64.b64encode(line).decode("ascii"),
                "raw_line_sha256": line_hash,
                "previous_chain_sha256": previous,
                "chain_sha256": chain.hex(),
            })
        envelope = b"".join(canonical_bytes(row) + b"\n" for row in rows)
        write_bytes(self.root / "evidence/event-receipts.jsonl", envelope)
        launch_bytes = self.launch_path.read_bytes()
        final_output_bytes = (self.root / "evidence/final-output.json").read_bytes()
        stderr_bytes = (self.root / "evidence/stderr.log").read_bytes()
        end_monotonic_ns = self.launch["post_spawn_monotonic_ns"] + (len(lines) + 1) * 10_000_000
        self.process = {
            "schema_version": 1,
            "receipt_version": PROCESS_VERSION,
            "contract_id": self.descriptor["contract_id"],
            "invocation_id": self.launch["invocation_id"],
            "launch_descriptor_sha256": sha256(self.descriptor_path.read_bytes()),
            "launch_receipt_sha256": sha256(launch_bytes),
            "final_chain_sha256": chain.hex(),
            "event_count": len(lines),
            "raw_event_log_sha256": sha256(raw),
            "event_receipts_sha256": sha256(envelope),
            "stderr_sha256": sha256(stderr_bytes),
            "final_output_sha256": sha256(final_output_bytes),
            "output_canonical_sha256": compact_hash(self.expected_output),
            "exit_status": 0,
            "signal": None,
            "timed_out": False,
            "interrupted": False,
            "retry_count": 0,
            "end_realtime_ns": self.launch["post_spawn_realtime_ns"] + (len(lines) + 1) * 10_000_000,
            "end_monotonic_ns": end_monotonic_ns,
            "elapsed_ns": end_monotonic_ns - self.launch["pre_spawn_monotonic_ns"],
            "peak_rss_bytes": 1024,
            "aggregate_output_bytes": len(launch_bytes) + len(raw) + len(envelope) + len(stderr_bytes) + len(final_output_bytes),
            "thread_id": "thread-1",
            "turn_id": "turn-1",
            "terminal": "turn.completed",
            "usage": {"input_tokens": 10, "cached_input_tokens": 0, "output_tokens": 5},
            "verdict_codes": ["V3_RUNTIME_RECEIPT_OK"],
        }
        self.save_process()

    def save_process(self) -> None:
        write_json(self.process_path, self.process)

    def refresh_process_hashes(self) -> None:
        for field, path in (
            ("raw_event_log_sha256", "events.raw.jsonl"),
            ("event_receipts_sha256", "event-receipts.jsonl"),
            ("stderr_sha256", "stderr.log"),
            ("final_output_sha256", "final-output.json"),
        ):
            self.process[field] = sha256((self.root / "evidence" / path).read_bytes())
        self.process["output_canonical_sha256"] = compact_hash(
            json.loads((self.root / "evidence/final-output.json").read_text())
        )
        self.process["aggregate_output_bytes"] = sum(
            (self.root / "evidence" / path).stat().st_size
            for path in (
                "launch-receipt.json",
                "events.raw.jsonl",
                "event-receipts.jsonl",
                "stderr.log",
                "final-output.json",
            )
        )
        self.save_process()

    def independently_derived_digests(self) -> tuple[str, str, str]:
        descriptor_bytes = self.descriptor_path.read_bytes()
        launch_bytes = self.launch_path.read_bytes()
        envelope_bytes = (self.root / "evidence/event-receipts.jsonl").read_bytes()
        raw_bytes = (self.root / "evidence/events.raw.jsonl").read_bytes()
        stderr_bytes = (self.root / "evidence/stderr.log").read_bytes()
        output_bytes = (self.root / "evidence/final-output.json").read_bytes()
        process_bytes = self.process_path.read_bytes()
        descriptor_sha = sha256(descriptor_bytes)
        launch_sha = sha256(launch_bytes)
        first_chain = sha256(
            CHAIN_DOMAIN
            + b"\0"
            + bytes.fromhex(descriptor_sha)
            + bytes.fromhex(launch_sha)
        )
        envelope_rows = [json.loads(line) for line in envelope_bytes.splitlines()]
        closure = []
        for path in sorted(
            (
                "control/launch-descriptor.json",
                "control/output-schema.json",
                "control/prompt.txt",
                "evidence/event-receipts.jsonl",
                "evidence/events.raw.jsonl",
                "evidence/final-output.json",
                "evidence/launch-receipt.json",
                "evidence/process-receipt.json",
                "evidence/stderr.log",
                "work/input.json",
            )
        ):
            full = self.root / path
            data = full.read_bytes()
            info = os.lstat(full)
            closure.append(
                {
                    "path": path,
                    "raw_size": len(data),
                    "raw_sha256": sha256(data),
                    "st_dev": info.st_dev,
                    "st_ino": info.st_ino,
                    "st_mode": info.st_mode,
                    "st_nlink": info.st_nlink,
                }
            )
        artifact_closure_sha = compact_hash(closure)
        total_root_bytes = sum(row["raw_size"] for row in closure)
        output_canonical_sha = sha256(canonical_bytes(self.expected_output))
        derived = {
            "call_id": "telemetry-canary-1",
            "stage": "canary",
            "invocation_id": self.launch["invocation_id"],
            "thread_id": "thread-1",
            "turn_id": "turn-1",
            "event_count": len(self.events),
            "start_event_ordinal": 2,
            "end_event_ordinal": len(self.events),
            "first_event_monotonic_ns": envelope_rows[0]["received_monotonic_ns"],
            "last_event_monotonic_ns": envelope_rows[-1]["received_monotonic_ns"],
            "pre_spawn_monotonic_ns": self.launch["pre_spawn_monotonic_ns"],
            "end_monotonic_ns": self.process["end_monotonic_ns"],
            "elapsed_ns": self.process["elapsed_ns"],
            "payload_output_bytes": self.process["aggregate_output_bytes"],
            "total_root_bytes": total_root_bytes,
            "peak_rss_bytes": self.process["peak_rss_bytes"],
            "usage": self.process["usage"],
            "retry_count": self.process["retry_count"],
            "interrupted": self.process["interrupted"],
            "timed_out": self.process["timed_out"],
            "exit_status": self.process["exit_status"],
            "signal": self.process["signal"],
            "final_chain_sha256": self.process["final_chain_sha256"],
            "output_canonical_sha256": output_canonical_sha,
        }
        derived_sha = compact_hash(derived)
        raw_digests = {
            "launch_descriptor_sha256": descriptor_sha,
            "launch_receipt_sha256": launch_sha,
            "event_receipts_sha256": sha256(envelope_bytes),
            "raw_event_log_sha256": sha256(raw_bytes),
            "stderr_sha256": sha256(stderr_bytes),
            "final_output_sha256": sha256(output_bytes),
            "process_receipt_sha256": sha256(process_bytes),
        }
        completion_core = {
            "schema_version": 1,
            "completion_version": COMPLETION_VERSION,
            **raw_digests,
            "artifact_closure_sha256": artifact_closure_sha,
            "derived_quantities_sha256": derived_sha,
            "final_chain_sha256": self.process["final_chain_sha256"],
            "output_canonical_sha256": output_canonical_sha,
        }
        completion_sha = sha256(
            COMPLETION_DOMAIN + b"\0" + canonical_bytes(completion_core)
        )
        run_digest = sha256(
            RUN_DOMAIN
            + b"\0"
            + b"".join(
                bytes.fromhex(raw_digests[key])
                for key in (
                    "launch_descriptor_sha256",
                    "launch_receipt_sha256",
                    "event_receipts_sha256",
                    "raw_event_log_sha256",
                    "stderr_sha256",
                    "final_output_sha256",
                    "process_receipt_sha256",
                )
            )
            + bytes.fromhex(artifact_closure_sha)
            + bytes.fromhex(derived_sha)
            + bytes.fromhex(completion_sha)
        )
        return first_chain, completion_sha, run_digest


class RuntimeReceiptTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.fixture = RuntimeFixture(self.root)

    def tearDown(self) -> None:
        self.temp.cleanup()

    def assert_code(self, code: str, *, descriptor_sha256: str | None = None) -> None:
        with self.assertRaises(RuntimeReceiptError) as caught:
            validate_runtime_receipt(
                self.root,
                descriptor_sha256 or self.fixture.expected_descriptor_sha256,
            )
        self.assertEqual(caught.exception.code, code)

    def test_valid_runtime_receipt_is_derived(self) -> None:
        receipt = validate_runtime_receipt(self.root, self.fixture.expected_descriptor_sha256)
        first_chain, completion_sha, run_digest = self.fixture.independently_derived_digests()
        first_envelope = json.loads(
            (self.root / "evidence/event-receipts.jsonl").read_text().splitlines()[0]
        )
        self.assertEqual(receipt["receipt_kind"], "runtime")
        self.assertEqual(receipt["thread_id"], "thread-1")
        self.assertEqual(receipt["turn_id"], "turn-1")
        self.assertEqual(receipt["source_events"], [])
        self.assertIsNone(receipt["skeleton_seal"])
        self.assertEqual(first_envelope["previous_chain_sha256"], first_chain)
        self.assertEqual(receipt["completion_sha256"], completion_sha)
        self.assertEqual(receipt["run_digest"], run_digest)

    def test_raw_event_log_digest_drift_fails(self) -> None:
        path = self.root / "evidence/events.raw.jsonl"
        path.write_bytes(path.read_bytes() + b" ")
        self.fixture.refresh_process_hashes()
        self.assert_code("V3E_INVOCATION_PROVENANCE_INVALID")

    def test_event_envelope_chain_drift_fails(self) -> None:
        path = self.root / "evidence/event-receipts.jsonl"
        rows = [json.loads(line) for line in path.read_text().splitlines()]
        rows[2]["received_monotonic_ns"] += 1
        write_bytes(path, b"".join(canonical_bytes(row) + b"\n" for row in rows))
        self.fixture.refresh_process_hashes()
        self.assert_code("V3E_INVOCATION_PROVENANCE_INVALID")

    def test_independently_wrong_chain_anchor_fails(self) -> None:
        path = self.root / "evidence/event-receipts.jsonl"
        rows = [json.loads(line) for line in path.read_text().splitlines()]
        chain = hashlib.sha256(
            b"factory-v3-one-call-receipt-v1"
            + b"\0"
            + canonical_bytes(self.fixture.launch)
        ).digest()
        for row in rows:
            row["previous_chain_sha256"] = chain.hex()
            chain = hashlib.sha256(
                chain
                + row["sequence"].to_bytes(8, "big")
                + row["received_monotonic_ns"].to_bytes(8, "big")
                + bytes.fromhex(row["raw_line_sha256"])
            ).digest()
            row["chain_sha256"] = chain.hex()
        write_bytes(path, b"".join(canonical_bytes(row) + b"\n" for row in rows))
        self.fixture.process["final_chain_sha256"] = chain.hex()
        self.fixture.refresh_process_hashes()
        self.assert_code("V3E_INVOCATION_PROVENANCE_INVALID")

    def test_descriptor_boolean_schema_version_fails_schema(self) -> None:
        self.fixture.descriptor["schema_version"] = True
        self.fixture.rebind_descriptor()
        self.assert_code(
            "V3E_RUNTIME_RECEIPT_SCHEMA_INVALID",
            descriptor_sha256=sha256(self.fixture.descriptor_path.read_bytes()),
        )

    def test_output_boolean_schema_version_fails_schema(self) -> None:
        changed = dict(self.fixture.expected_output)
        changed["schema_version"] = True
        self.fixture.descriptor["expected_output"] = changed
        self.fixture.descriptor["expected_output_canonical_sha256"] = compact_hash(changed)
        self.fixture.rebind_descriptor()
        self.assert_code(
            "V3E_RUNTIME_RECEIPT_SCHEMA_INVALID",
            descriptor_sha256=sha256(self.fixture.descriptor_path.read_bytes()),
        )

    def test_process_boolean_alias_fails_schema(self) -> None:
        self.fixture.process["timed_out"] = 0
        self.fixture.save_process()
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_limiter_integer_boolean_alias_fails_schema(self) -> None:
        self.fixture.launch["limiter"]["cpu_cores"] = True
        self.fixture.save_launch()
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_limiter_integer_float_alias_fails_schema(self) -> None:
        self.fixture.launch["limiter"]["wall_seconds"] = 900.0
        self.fixture.save_launch()
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_process_usage_boolean_alias_fails_schema(self) -> None:
        self.fixture.process["usage"]["cached_input_tokens"] = False
        self.fixture.save_process()
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_process_usage_float_alias_fails_schema(self) -> None:
        self.fixture.process["usage"] = {
            "input_tokens": 10.0,
            "cached_input_tokens": 0.0,
            "output_tokens": 5.0,
        }
        self.fixture.save_process()
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_equal_pre_and_post_spawn_monotonic_clocks_fail(self) -> None:
        self.fixture.launch["post_spawn_monotonic_ns"] = self.fixture.launch[
            "pre_spawn_monotonic_ns"
        ]
        self.fixture.save_launch()
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_INVOCATION_PROVENANCE_INVALID")

    def test_process_end_realtime_before_last_event_fails_resource_receipt(self) -> None:
        self.fixture.process["end_realtime_ns"] = self.fixture.launch["post_spawn_realtime_ns"]
        self.fixture.save_process()
        self.assert_code("V3E_RESOURCE_RECEIPT_INVALID")

    def test_extra_reasoning_event_fails_lifecycle(self) -> None:
        self.fixture.events.insert(
            5,
            {
                "type": "item.completed",
                "thread_id": "thread-1",
                "turn_id": "turn-1",
                "item": {"id": "reasoning-2", "type": "reasoning", "text": "private-2"},
            },
        )
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_LIFECYCLE_INVALID")

    def test_missing_message_completion_fails_lifecycle(self) -> None:
        del self.fixture.events[6]
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_LIFECYCLE_INVALID")

    def test_missing_complete_message_lifecycle_fails_lifecycle(self) -> None:
        del self.fixture.events[5:7]
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_LIFECYCLE_INVALID")

    def test_outer_envelope_without_item_lifecycles_fails_lifecycle(self) -> None:
        self.fixture.events = [
            self.fixture.events[0],
            self.fixture.events[1],
            self.fixture.events[-1],
        ]
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_LIFECYCLE_INVALID")

    def test_outer_only_bad_usage_keys_fail_schema_before_lifecycle(self) -> None:
        self.fixture.events = [
            self.fixture.events[0],
            self.fixture.events[1],
            self.fixture.events[-1],
        ]
        self.fixture.events[-1]["usage"] = {"arbitrary_counter": 0}
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_missing_message_with_boolean_usage_fails_schema_before_lifecycle(self) -> None:
        del self.fixture.events[6]
        self.fixture.events[-1]["usage"]["input_tokens"] = True
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_missing_outer_terminal_event_remains_field_gap(self) -> None:
        self.fixture.events = self.fixture.events[:2]
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_FIELD_GAP")

    def test_reasoning_before_command_fails_lifecycle(self) -> None:
        reasoning = self.fixture.events.pop(4)
        self.fixture.events.insert(2, reasoning)
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_LIFECYCLE_INVALID")

    def test_reasoning_reusing_command_id_fails_lifecycle(self) -> None:
        self.fixture.events[4]["item"]["id"] = "command-1"
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_LIFECYCLE_INVALID")

    def test_noncanonical_raw_event_line_fails_schema(self) -> None:
        lines = [canonical_bytes(event) + b"\n" for event in self.fixture.events]
        lines[0] = b'{"thread_id": "thread-1", "type": "thread.started"}\n'
        self.fixture.write_raw_lines(lines)
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_root_symlink_component_fails_closure(self) -> None:
        with tempfile.TemporaryDirectory(dir="/tmp") as alias_parent:
            alias = Path(alias_parent) / "root-alias"
            os.symlink(self.root, alias)
            with self.assertRaises(RuntimeReceiptError) as caught:
                validate_runtime_receipt(alias, self.fixture.expected_descriptor_sha256)
            self.assertEqual(caught.exception.code, "V3E_ARTIFACT_CLOSURE_INVALID")

    def test_executable_symlink_component_fails_provenance(self) -> None:
        with tempfile.TemporaryDirectory(dir="/tmp") as executable_parent:
            parent = Path(executable_parent)
            real = parent / "real"
            real.mkdir()
            executable = real / "runner"
            executable.write_bytes(b"inert executable fixture\n")
            alias = parent / "alias"
            os.symlink(real, alias)
            aliased_executable = alias / "runner"
            self.fixture.descriptor["executable_path"] = str(aliased_executable)
            self.fixture.descriptor["executable_sha256"] = sha256(executable.read_bytes())
            self.fixture.descriptor["argv"] = expected_agent_argv(
                self.root,
                str(aliased_executable),
            )
            self.fixture.descriptor["argv_sha256"] = compact_hash(
                self.fixture.descriptor["argv"]
            )
            self.fixture.rebind_descriptor()
            self.assert_code(
                "V3E_INVOCATION_PROVENANCE_INVALID",
                descriptor_sha256=sha256(self.fixture.descriptor_path.read_bytes()),
            )

    def test_duplicate_json_key_in_event_fails(self) -> None:
        lines = [canonical_bytes(event) + b"\n" for event in self.fixture.events]
        lines[0] = b'{"type":"thread.started","type":"thread.started","thread_id":"thread-1"}\n'
        self.fixture.write_raw_lines(lines)
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_missing_turn_identity_is_runtime_field_gap(self) -> None:
        del self.fixture.events[1]["turn_id"]
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_mismatched_turn_identity_fails(self) -> None:
        self.fixture.events[3]["turn_id"] = "turn-elsewhere"
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_INVOCATION_PROVENANCE_INVALID")

    def test_required_item_without_start_fails_lifecycle(self) -> None:
        del self.fixture.events[2]
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_LIFECYCLE_INVALID")

    def test_reused_item_id_fails(self) -> None:
        self.fixture.events[5]["item"]["id"] = "command-1"
        self.fixture.events[6]["item"]["id"] = "command-1"
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_LIFECYCLE_INVALID")

    def test_hosted_search_is_unexpected_authority(self) -> None:
        self.fixture.events.insert(5, {
            "type": "item.completed",
            "thread_id": "thread-1",
            "turn_id": "turn-1",
            "item": {"id": "search-1", "type": "web_search", "query": "forbidden"},
        })
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_UNEXPECTED_AUTHORITY")

    def test_second_command_fails(self) -> None:
        second = [json.loads(json.dumps(self.fixture.events[2])), json.loads(json.dumps(self.fixture.events[3]))]
        for event in second:
            event["item"]["id"] = "command-2"
        self.fixture.events[4:4] = second
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_LIFECYCLE_INVALID")

    def test_command_drift_fails(self) -> None:
        self.fixture.events[2]["item"]["command"] = "cat input.json"
        self.fixture.events[3]["item"]["command"] = "cat input.json"
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_OUTPUT_INVALID")

    def test_output_drift_fails_without_semantic_fallback(self) -> None:
        changed = dict(self.fixture.expected_output)
        changed["status"] = "provider-says-ok"
        write_json(self.root / "evidence/final-output.json", changed)
        self.fixture.refresh_process_hashes()
        self.assert_code("V3E_OUTPUT_INVALID")

    def test_duplicate_json_key_in_output_fails(self) -> None:
        write_bytes(self.root / "evidence/final-output.json", b'{"status":"ok","status":"ok"}\n')
        self.fixture.refresh_process_hashes()
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_retry_cannot_count_as_valid_receipt(self) -> None:
        self.fixture.process["retry_count"] = 1
        self.fixture.save_process()
        self.assert_code("V3E_INVOCATION_PROVENANCE_INVALID")

    def test_interruption_cannot_count_as_valid_receipt(self) -> None:
        self.fixture.process["interrupted"] = True
        self.fixture.save_process()
        self.assert_code("V3E_INVOCATION_PROVENANCE_INVALID")

    def test_descriptor_rejects_model_authored_invocation_fallback(self) -> None:
        self.fixture.descriptor["invocation"] = {"thread_id": "self-authored"}
        self.fixture.save_descriptor()
        self.assert_code(
            "V3E_RUNTIME_RECEIPT_SCHEMA_INVALID",
            descriptor_sha256=sha256(self.fixture.descriptor_path.read_bytes()),
        )

    def test_resource_breach_fails(self) -> None:
        self.fixture.process["peak_rss_bytes"] = self.fixture.descriptor["resource_limits"]["memory_bytes"] + 1
        self.fixture.save_process()
        self.assert_code("V3E_RESOURCE_RECEIPT_INVALID")

    def test_rc01_missing_item_identities_fails_exact_schema(self) -> None:
        for event in self.fixture.events:
            if event["type"].startswith("item."):
                del event["thread_id"]
                del event["turn_id"]
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_rc02_message_before_command_fails_lifecycle(self) -> None:
        self.fixture.events = (
            self.fixture.events[:2]
            + self.fixture.events[5:7]
            + self.fixture.events[2:5]
            + self.fixture.events[7:]
        )
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_LIFECYCLE_INVALID")

    def test_rc03_message_output_divergence_fails(self) -> None:
        self.fixture.events[6]["item"]["text"] = "semantically different final answer"
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_OUTPUT_INVALID")

    def test_rc04_command_shaped_reasoning_fails_exact_schema(self) -> None:
        self.fixture.events[4]["item"]["command"] = self.fixture.expected_command
        self.fixture.events[4]["item"]["aggregated_output"] = self.fixture.expected_command_output
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_rc05_arbitrary_usage_fails_exact_schema(self) -> None:
        self.fixture.events[-1]["usage"] = {"arbitrary_counter": 0}
        self.fixture.write_events(self.fixture.events)
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_rc06_dangerous_argv_fails_anchor_and_inner_authority(self) -> None:
        self.fixture.descriptor["argv"].append("--dangerously-bypass-approvals-and-sandbox")
        self.fixture.descriptor["argv_sha256"] = compact_hash(self.fixture.descriptor["argv"])
        self.fixture.rebind_descriptor()
        self.assert_code("V3E_DESCRIPTOR_ANCHOR_MISMATCH")
        self.assert_code(
            "V3E_UNEXPECTED_AUTHORITY",
            descriptor_sha256=sha256(self.fixture.descriptor_path.read_bytes()),
        )

    def test_rc07_surplus_input_fails_anchor_and_inner_input_set(self) -> None:
        self.fixture.descriptor["input_manifest"].append(dict(self.fixture.descriptor["input_manifest"][-1]))
        self.fixture.descriptor["input_fingerprint"] = compact_hash(self.fixture.descriptor["input_manifest"])
        self.fixture.rebind_descriptor()
        self.assert_code("V3E_DESCRIPTOR_ANCHOR_MISMATCH")
        self.assert_code(
            "V3E_STAGE_INPUT_SET_MISMATCH",
            descriptor_sha256=sha256(self.fixture.descriptor_path.read_bytes()),
        )

    def test_rc08_symlink_artifact_alias_fails_closure(self) -> None:
        stderr_path = self.root / "evidence/stderr.log"
        stderr_path.unlink()
        os.symlink(self.root / "work/input.json", stderr_path)
        self.assert_code("V3E_ARTIFACT_CLOSURE_INVALID")

    def test_hard_link_artifact_alias_fails_closure(self) -> None:
        stderr_path = self.root / "evidence/stderr.log"
        stderr_path.unlink()
        os.link(self.root / "evidence/final-output.json", stderr_path)
        self.assert_code("V3E_ARTIFACT_CLOSURE_INVALID")

    def test_rc09_noncanonical_launch_receipt_fails_schema(self) -> None:
        self.fixture.launch_path.write_text(json.dumps(self.fixture.launch, indent=2) + "\n")
        self.assert_code("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    def test_rc10_inconsistent_elapsed_clocks_fail_resource_receipt(self) -> None:
        self.fixture.process["end_monotonic_ns"] = (
            self.fixture.launch["pre_spawn_monotonic_ns"] + 901 * 1_000_000_000
        )
        self.fixture.process["end_realtime_ns"] = (
            self.fixture.launch["pre_spawn_realtime_ns"] + 901 * 1_000_000_000
        )
        self.fixture.process["elapsed_ns"] = 1
        self.fixture.save_process()
        self.assert_code("V3E_RESOURCE_RECEIPT_INVALID")

    def test_rc11_false_aggregate_bytes_fail_resource_receipt(self) -> None:
        self.fixture.process["aggregate_output_bytes"] = 1
        self.fixture.save_process()
        self.assert_code("V3E_RESOURCE_RECEIPT_INVALID")

    def test_rc12_policy_drift_fails_anchor_and_inner_policy(self) -> None:
        self.fixture.descriptor["provider_policy"] = "drifted-provider:max"
        self.fixture.descriptor["codex_version"] = "codex-cli 999.0.0"
        self.fixture.descriptor["sandbox_policy"] = "broadened"
        self.fixture.descriptor["approval_policy"] = "on-request"
        self.fixture.rebind_descriptor()
        self.assert_code("V3E_DESCRIPTOR_ANCHOR_MISMATCH")
        self.assert_code(
            "V3E_DESCRIPTOR_POLICY_INVALID",
            descriptor_sha256=sha256(self.fixture.descriptor_path.read_bytes()),
        )

    def test_rc13_resource_expansion_fails_anchor_and_inner_contract(self) -> None:
        self.fixture.descriptor["resource_limits"] = {
            key: value * 2 for key, value in self.fixture.descriptor["resource_limits"].items()
        }
        self.fixture.rebind_descriptor()
        self.assert_code("V3E_DESCRIPTOR_ANCHOR_MISMATCH")
        self.assert_code(
            "V3E_RESOURCE_CONTRACT_INVALID",
            descriptor_sha256=sha256(self.fixture.descriptor_path.read_bytes()),
        )

    def test_cli_permission_error_is_safe_and_nonreflecting(self) -> None:
        sentinel = "PRIVATE-RUNTIME-SENTINEL-EXECUTABLE-8841"
        with tempfile.TemporaryDirectory(prefix=sentinel, dir="/tmp") as executable_root:
            executable = Path(executable_root) / "inert-executable"
            executable.write_bytes(b"synthetic executable bytes\n")
            self.fixture.descriptor["executable_path"] = str(executable)
            self.fixture.descriptor["executable_sha256"] = sha256(executable.read_bytes())
            self.fixture.descriptor["argv"][0] = str(executable)
            self.fixture.descriptor["argv_sha256"] = compact_hash(self.fixture.descriptor["argv"])
            self.fixture.rebind_descriptor()
            descriptor_sha = sha256(self.fixture.descriptor_path.read_bytes())
            executable.chmod(0)
            completed = subprocess.run(
                [
                    sys.executable,
                    str(Path(__file__).resolve().parent / "check_factory_v3_runtime_receipt.py"),
                    "--root",
                    str(self.root),
                    "--expected-descriptor-sha256",
                    descriptor_sha,
                ],
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(completed.returncode, 1)
            self.assertEqual(completed.stdout, "V3E_RUNTIME_RECEIPT_IO_INVALID\n")
            self.assertEqual(completed.stderr, "")
            self.assertNotIn(sentinel, completed.stdout + completed.stderr)

    def test_cli_error_does_not_reflect_protected_text(self) -> None:
        sentinel = "PRIVATE-RUNTIME-SENTINEL-7719"
        self.fixture.descriptor[sentinel] = sentinel
        self.fixture.save_descriptor()
        completed = subprocess.run(
            [
                sys.executable,
                str(Path(__file__).resolve().parent / "check_factory_v3_runtime_receipt.py"),
                "--root",
                str(self.root),
                "--expected-descriptor-sha256",
                sha256(self.fixture.descriptor_path.read_bytes()),
            ],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(completed.returncode, 1)
        self.assertEqual(completed.stderr, "")
        self.assertEqual(completed.stdout.strip(), "V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
        self.assertNotIn(sentinel, completed.stdout + completed.stderr)


if __name__ == "__main__":
    unittest.main()
