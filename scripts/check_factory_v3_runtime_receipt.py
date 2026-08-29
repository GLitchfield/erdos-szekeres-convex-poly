#!/usr/bin/env python3
"""Replay and validate a Factory-v3 Codex runtime receipt.

This checker is intentionally narrower than ``check_factory_v3_pilot.py``.
It validates the dormant, nonresearch one-call telemetry canary.  In
particular, it derives the public receipt from a raw Codex JSONL stream and a
root-owned line envelope; it never accepts an invocation record written by the
evaluated worker as a fallback.
"""

from __future__ import annotations

import argparse
import base64
import binascii
from dataclasses import dataclass, field
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
from typing import Any, Iterable


class RuntimeReceiptError(ValueError):
    """A safe, non-reflecting runtime-receipt failure."""

    def __init__(self, code: str) -> None:
        if not code.startswith("V3E_"):
            code = "V3E_RUNTIME_RECEIPT_INVALID"
        self.code = code
        super().__init__(code)


HEX = set("0123456789abcdef")
DESCRIPTOR_VERSION = "factory-v3-runtime-descriptor-v6"
LAUNCH_VERSION = "factory-v3-launch-receipt-v6"
PROCESS_VERSION = "factory-v3-process-receipt-v6"
RECEIPT_VERSION = "factory-v3-runtime-receipt-v6"
CHAIN_DOMAIN = b"factory-v3-event-chain-v2"
COMPLETION_DOMAIN = b"factory-v3-completion-v2"
RUN_DOMAIN = b"factory-v3-run-v2"
COMPLETION_VERSION = "factory-v3-completion-v2"

CONTRACT_ID = "factory-v3-one-call-telemetry-v1"
CALL_ID = "telemetry-canary-1"
PROVIDER_POLICY = "gpt-5.6-sol:max"
CODEX_VERSION = "codex-cli 0.149.0"
PERMISSION_PROFILE = "factory-v3-two-layer-exact-v1"
SANDBOX_POLICY = "outer-control-plus-inner-tool-profile"
APPROVAL_POLICY = "never"
CREDENTIAL_MECHANISM = "codex-home-auth-json-outer-only"
INNER_PROFILE_NAME = "factory_v3_tool_v1"
EXPECTED_COMMAND = "sha256sum input.json"
EXPECTED_RESOURCE_LIMITS = {
    "wall_seconds": 900,
    "cpu_cores": 1,
    "memory_bytes": 2 * 1024**3,
    "output_bytes": 21_474_836,
    "kill_grace_seconds": 5,
}
EXPECTED_ARTIFACTS = {
    "launch_receipt": "evidence/launch-receipt.json",
    "event_receipts": "evidence/event-receipts.jsonl",
    "raw_event_log": "evidence/events.raw.jsonl",
    "stderr": "evidence/stderr.log",
    "final_output": "evidence/final-output.json",
    "process_receipt": "evidence/process-receipt.json",
}
EXPECTED_INPUT_PATHS = (
    "control/output-schema.json",
    "control/prompt.txt",
    "work/input.json",
)
EXPECTED_ROOT_LAYOUT = {
    ".": {"control", "evidence", "work"},
    "control": {"launch-descriptor.json", "output-schema.json", "prompt.txt"},
    "work": {"input.json"},
    "evidence": {
        "event-receipts.jsonl",
        "events.raw.jsonl",
        "final-output.json",
        "launch-receipt.json",
        "process-receipt.json",
        "stderr.log",
    },
}
BANNED_ARGV = {
    "--add-dir",
    "--approve-for-me",
    "--dangerously-bypass-approvals-and-sandbox",
    "--dangerously-bypass-hook-trust",
    "--local-provider",
    "--oss",
    "--search",
    "danger-full-access",
    "fork",
    "resume",
    "review",
}


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

DESCRIPTOR_KEYS = {
    "schema_version",
    "descriptor_version",
    "contract_id",
    "evidence_mode",
    "call_id",
    "stage",
    "provider_policy",
    "codex_version",
    "executable_path",
    "executable_sha256",
    "argv",
    "argv_sha256",
    "task_path",
    "task_sha256",
    "input_manifest",
    "input_fingerprint",
    "cwd",
    "permission_profile",
    "sandbox_policy",
    "approval_policy",
    "credential_mechanism",
    "expected_command",
    "expected_command_output",
    "expected_output",
    "expected_output_canonical_sha256",
    "allowed_item_types",
    "required_lifecycle_types",
    "expected_command_count",
    "expected_source_count",
    "skeleton_policy",
    "resource_limits",
    "artifacts",
}
ARTIFACT_KEYS = {
    "launch_receipt",
    "event_receipts",
    "raw_event_log",
    "stderr",
    "final_output",
    "process_receipt",
}
RESOURCE_KEYS = {
    "wall_seconds",
    "cpu_cores",
    "memory_bytes",
    "output_bytes",
    "kill_grace_seconds",
}
INPUT_KEYS = {"path", "sha256"}
LAUNCH_KEYS = {
    "schema_version",
    "receipt_version",
    "contract_id",
    "invocation_id",
    "launch_descriptor_sha256",
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
    "limiter",
    "child_pid",
    "child_pgid",
    "pre_spawn_realtime_ns",
    "pre_spawn_monotonic_ns",
    "post_spawn_realtime_ns",
    "post_spawn_monotonic_ns",
    "retry_count",
}
LIMITER_KEYS = {
    "implementation",
    "wall_seconds",
    "cpu_cores",
    "memory_bytes",
    "output_bytes",
    "kill_grace_seconds",
    "process_group",
    "stdout_line_envelope",
}
EVENT_RECEIPT_KEYS = {
    "schema_version",
    "sequence",
    "received_monotonic_ns",
    "received_realtime_ns",
    "raw_line_base64",
    "raw_line_sha256",
    "previous_chain_sha256",
    "chain_sha256",
}
PROCESS_KEYS = {
    "schema_version",
    "receipt_version",
    "contract_id",
    "invocation_id",
    "launch_descriptor_sha256",
    "launch_receipt_sha256",
    "final_chain_sha256",
    "event_count",
    "raw_event_log_sha256",
    "event_receipts_sha256",
    "stderr_sha256",
    "final_output_sha256",
    "output_canonical_sha256",
    "exit_status",
    "signal",
    "timed_out",
    "interrupted",
    "retry_count",
    "end_realtime_ns",
    "end_monotonic_ns",
    "elapsed_ns",
    "peak_rss_bytes",
    "aggregate_output_bytes",
    "thread_id",
    "turn_id",
    "terminal",
    "usage",
    "verdict_codes",
}

USAGE_KEYS = {"input_tokens", "cached_input_tokens", "output_tokens"}
THREAD_STARTED_KEYS = {"type", "thread_id"}
TURN_STARTED_KEYS = {"type", "thread_id", "turn_id"}
TURN_COMPLETED_KEYS = {"type", "thread_id", "turn_id", "usage"}
ITEM_EVENT_KEYS = {"type", "thread_id", "turn_id", "item"}
COMMAND_STARTED_KEYS = {"id", "type", "command"}
COMMAND_COMPLETED_KEYS = {
    "id",
    "type",
    "command",
    "aggregated_output",
    "exit_code",
    "status",
}
REASONING_COMPLETED_KEYS = {"id", "type", "text"}
MESSAGE_STARTED_KEYS = {"id", "type"}
MESSAGE_COMPLETED_KEYS = {"id", "type", "text"}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def compact_hash(value: Any) -> str:
    return sha256(canonical_bytes(value))


def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
        result[key] = value
    return result


def decode_object(data: bytes) -> dict[str, Any]:
    try:
        value = json.loads(
            data.decode("utf-8"),
            object_pairs_hook=unique_object,
            parse_constant=lambda _value: (_ for _ in ()).throw(ValueError()),
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID") from exc
    if not isinstance(value, dict):
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    return value


def load_object_bytes(data: bytes, *, canonical_file: bool = False) -> tuple[dict[str, Any], bytes]:
    value = decode_object(data)
    if canonical_file and data != canonical_bytes(value) + b"\n":
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    return value, data


def load_jsonl_bytes(data: bytes, *, canonical_lines: bool) -> tuple[list[dict[str, Any]], bytes]:
    if not data or not data.endswith(b"\n"):
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    rows: list[dict[str, Any]] = []
    for line in data.splitlines(keepends=True):
        if not line.endswith(b"\n") or line == b"\n":
            raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
        row = decode_object(line[:-1])
        if canonical_lines and line != canonical_bytes(row) + b"\n":
            raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
        rows.append(row)
    return rows, data


def require_exact_keys(value: Any, keys: set[str]) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != keys:
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    return value


def require_string(value: Any) -> str:
    if not isinstance(value, str) or not value:
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    return value


def require_hash(value: Any) -> str:
    text = require_string(value)
    if len(text) != 64 or any(char not in HEX for char in text):
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    return text


def require_int(value: Any, *, minimum: int = 0) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < minimum:
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    return value


def require_string_list(value: Any) -> list[str]:
    if (
        not isinstance(value, list)
        or not value
        or not all(isinstance(item, str) and item for item in value)
        or len(set(value)) != len(value)
    ):
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    return value


def relative_name(value: Any) -> str:
    text = require_string(value)
    pure = PurePosixPath(text)
    if pure.is_absolute() or not pure.parts or any(part in {"", ".", ".."} for part in pure.parts):
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    return pure.as_posix()


def read_fd(fd: int) -> bytes:
    try:
        os.lseek(fd, 0, os.SEEK_SET)
        chunks: list[bytes] = []
        while True:
            chunk = os.read(fd, 1024 * 1024)
            if not chunk:
                return b"".join(chunks)
            chunks.append(chunk)
    except OSError as exc:
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_IO_INVALID") from exc


def read_stable_fd(fd: int, *, error_code: str) -> tuple[bytes, os.stat_result]:
    try:
        before = os.fstat(fd)
        data = read_fd(fd)
        after = os.fstat(fd)
    except OSError as exc:
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_IO_INVALID") from exc
    fields = (
        "st_dev",
        "st_ino",
        "st_mode",
        "st_nlink",
        "st_uid",
        "st_gid",
        "st_size",
        "st_mtime_ns",
        "st_ctime_ns",
    )
    if any(getattr(before, name) != getattr(after, name) for name in fields) or len(data) != after.st_size:
        raise RuntimeReceiptError(error_code)
    return data, after


def _open_dir_at(parent_fd: int, name: str) -> int:
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
    try:
        return os.open(name, flags, dir_fd=parent_fd)
    except OSError as exc:
        raise RuntimeReceiptError("V3E_ARTIFACT_CLOSURE_INVALID") from exc


def _open_absolute_dir(path: Path) -> list[int]:
    if not path.is_absolute() or any(part in {"", ".", ".."} for part in path.parts[1:]):
        raise RuntimeReceiptError("V3E_ARTIFACT_CLOSURE_INVALID")
    descriptors: list[int] = []
    try:
        current = os.open("/", os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        descriptors.append(current)
        for part in path.parts[1:]:
            current = _open_dir_at(current, part)
            descriptors.append(current)
        return descriptors
    except Exception:
        for fd in reversed(descriptors):
            try:
                os.close(fd)
            except OSError:
                pass
        raise


@dataclass
class SnapshotFile:
    path: str
    fd: int
    data: bytes
    info: os.stat_result


@dataclass
class ArtifactSnapshot:
    root: Path
    root_info: os.stat_result
    directory_fds: dict[str, int]
    files: dict[str, SnapshotFile]
    retained_fds: list[int] = field(default_factory=list)

    def close(self) -> None:
        while self.retained_fds:
            fd = self.retained_fds.pop()
            try:
                os.close(fd)
            except OSError:
                pass

    def __enter__(self) -> "ArtifactSnapshot":
        return self

    def __exit__(self, _type: object, _value: object, _traceback: object) -> None:
        self.close()

    def bytes(self, path: str) -> bytes:
        try:
            return self.files[path].data
        except KeyError as exc:
            raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID") from exc

    def closure_rows(self) -> list[dict[str, Any]]:
        return [
            {
                "path": path,
                "raw_size": len(snapshot.data),
                "raw_sha256": sha256(snapshot.data),
                "st_dev": snapshot.info.st_dev,
                "st_ino": snapshot.info.st_ino,
                "st_mode": snapshot.info.st_mode,
                "st_nlink": snapshot.info.st_nlink,
            }
            for path, snapshot in sorted(self.files.items())
        ]

    def total_file_bytes(self) -> int:
        return sum(len(snapshot.data) for snapshot in self.files.values())


def _check_metadata(info: os.stat_result, owner: os.stat_result, *, kind: str) -> None:
    if kind == "dir":
        valid_kind = stat.S_ISDIR(info.st_mode)
    elif kind == "file":
        valid_kind = stat.S_ISREG(info.st_mode) and info.st_nlink == 1
    else:
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    if (
        not valid_kind
        or info.st_dev != owner.st_dev
        or info.st_uid != owner.st_uid
        or info.st_gid != owner.st_gid
        or info.st_mode & 0o022
    ):
        raise RuntimeReceiptError("V3E_ARTIFACT_CLOSURE_INVALID")


def snapshot_closed_layout(root: Path, expected_descriptor_sha: str) -> ArtifactSnapshot:
    retained = _open_absolute_dir(root)
    try:
        root_fd = retained[-1]
        root_info = os.fstat(root_fd)
        _check_metadata(root_info, root_info, kind="dir")
        directory_fds = {".": root_fd}

        # The descriptor anchor is checked before any descendant content is trusted.
        control_fd = _open_dir_at(root_fd, "control")
        retained.append(control_fd)
        directory_fds["control"] = control_fd
        try:
            descriptor_fd = os.open(
                "launch-descriptor.json",
                os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC,
                dir_fd=control_fd,
            )
        except OSError as exc:
            raise RuntimeReceiptError("V3E_ARTIFACT_CLOSURE_INVALID") from exc
        retained.append(descriptor_fd)
        descriptor_info = os.fstat(descriptor_fd)
        _check_metadata(descriptor_info, root_info, kind="file")
        descriptor_data, descriptor_info = read_stable_fd(
            descriptor_fd,
            error_code="V3E_ARTIFACT_CLOSURE_INVALID",
        )
        if sha256(descriptor_data) != expected_descriptor_sha:
            raise RuntimeReceiptError("V3E_DESCRIPTOR_ANCHOR_MISMATCH")

        for name in ("evidence", "work"):
            fd = _open_dir_at(root_fd, name)
            retained.append(fd)
            directory_fds[name] = fd

        files: dict[str, SnapshotFile] = {
            "control/launch-descriptor.json": SnapshotFile(
                "control/launch-descriptor.json", descriptor_fd, descriptor_data, descriptor_info
            )
        }
        identities = {(descriptor_info.st_dev, descriptor_info.st_ino)}
        for relative, expected_names in EXPECTED_ROOT_LAYOUT.items():
            directory_fd = directory_fds[relative]
            directory_info = os.fstat(directory_fd)
            _check_metadata(directory_info, root_info, kind="dir")
            try:
                names = set(os.listdir(directory_fd))
            except OSError as exc:
                raise RuntimeReceiptError("V3E_ARTIFACT_CLOSURE_INVALID") from exc
            if names != expected_names:
                raise RuntimeReceiptError("V3E_ARTIFACT_CLOSURE_INVALID")
            if relative == ".":
                continue
            for name in sorted(expected_names):
                path = f"{relative}/{name}"
                if path in files:
                    continue
                try:
                    fd = os.open(
                        name,
                        os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC,
                        dir_fd=directory_fd,
                    )
                except OSError as exc:
                    raise RuntimeReceiptError("V3E_ARTIFACT_CLOSURE_INVALID") from exc
                retained.append(fd)
                info = os.fstat(fd)
                _check_metadata(info, root_info, kind="file")
                identity = (info.st_dev, info.st_ino)
                if identity in identities:
                    raise RuntimeReceiptError("V3E_ARTIFACT_CLOSURE_INVALID")
                identities.add(identity)
                data, info = read_stable_fd(fd, error_code="V3E_ARTIFACT_CLOSURE_INVALID")
                files[path] = SnapshotFile(path, fd, data, info)
        return ArtifactSnapshot(root, root_info, directory_fds, files, retained)
    except Exception:
        for fd in reversed(retained):
            try:
                os.close(fd)
            except OSError:
                pass
        raise


def read_absolute_regular_file(path: Path) -> bytes:
    if not path.is_absolute() or any(part in {"", ".", ".."} for part in path.parts[1:]):
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    try:
        parent_fds = _open_absolute_dir(path.parent)
    except RuntimeReceiptError as exc:
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID") from exc
    file_fd = -1
    try:
        file_fd = os.open(
            path.name,
            os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC,
            dir_fd=parent_fds[-1],
        )
        info = os.fstat(file_fd)
        if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
            raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
        data, _ = read_stable_fd(
            file_fd,
            error_code="V3E_INVOCATION_PROVENANCE_INVALID",
        )
        return data
    except RuntimeReceiptError:
        raise
    except OSError as exc:
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_IO_INVALID") from exc
    finally:
        if file_fd >= 0:
            try:
                os.close(file_fd)
            except OSError:
                pass
        for fd in reversed(parent_fds):
            try:
                os.close(fd)
            except OSError:
                pass


def u64(value: int) -> bytes:
    try:
        return value.to_bytes(8, "big", signed=False)
    except OverflowError as exc:
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID") from exc


def equal_fields(left: dict[str, Any], right: dict[str, Any], keys: Iterable[str]) -> None:
    if any(left.get(key) != right.get(key) for key in keys):
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")


def validate_descriptor(snapshot: ArtifactSnapshot, descriptor: dict[str, Any]) -> dict[str, str]:
    require_exact_keys(descriptor, DESCRIPTOR_KEYS)
    require_int(descriptor["schema_version"], minimum=1)
    require_int(descriptor["expected_command_count"], minimum=1)
    require_int(descriptor["expected_source_count"])
    if (
        descriptor["schema_version"] != 1
        or descriptor["descriptor_version"] != DESCRIPTOR_VERSION
        or descriptor["contract_id"] != CONTRACT_ID
        or descriptor["evidence_mode"] != "live-runtime"
        or descriptor["call_id"] != CALL_ID
        or descriptor["stage"] != "canary"
        or descriptor["expected_command_count"] != 1
        or descriptor["expected_source_count"] != 0
        or descriptor["skeleton_policy"] != "none"
    ):
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    if (
        descriptor["provider_policy"] != PROVIDER_POLICY
        or descriptor["codex_version"] != CODEX_VERSION
        or descriptor["permission_profile"] != PERMISSION_PROFILE
        or descriptor["sandbox_policy"] != SANDBOX_POLICY
        or descriptor["approval_policy"] != APPROVAL_POLICY
        or descriptor["credential_mechanism"] != CREDENTIAL_MECHANISM
        or descriptor["expected_command"] != EXPECTED_COMMAND
    ):
        raise RuntimeReceiptError("V3E_DESCRIPTOR_POLICY_INVALID")
    for key in (
        "contract_id",
        "call_id",
        "provider_policy",
        "codex_version",
        "permission_profile",
        "sandbox_policy",
        "approval_policy",
        "credential_mechanism",
        "expected_command",
        "expected_command_output",
    ):
        require_string(descriptor[key])

    executable = Path(require_string(descriptor["executable_path"]))
    if not executable.is_absolute():
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    if sha256(read_absolute_regular_file(executable)) != require_hash(descriptor["executable_sha256"]):
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")

    argv = descriptor["argv"]
    if not isinstance(argv, list) or not argv or not all(isinstance(x, str) for x in argv):
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    if compact_hash(argv) != require_hash(descriptor["argv_sha256"]):
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    argv_bases = {token.split("=", 1)[0] for token in argv}
    if (
        argv_bases & BANNED_ARGV
        or "--sandbox" in argv_bases
        or "-s" in argv_bases
        or argv != expected_agent_argv(snapshot.root, descriptor["executable_path"])
    ):
        raise RuntimeReceiptError("V3E_UNEXPECTED_AUTHORITY")

    manifest = descriptor["input_manifest"]
    if not isinstance(manifest, list) or len(manifest) != len(EXPECTED_INPUT_PATHS):
        raise RuntimeReceiptError("V3E_STAGE_INPUT_SET_MISMATCH")
    seen: set[str] = set()
    input_paths: dict[str, str] = {}
    for expected_name, item in zip(EXPECTED_INPUT_PATHS, manifest, strict=True):
        require_exact_keys(item, INPUT_KEYS)
        name = relative_name(item["path"])
        if name != expected_name or name in seen:
            raise RuntimeReceiptError("V3E_STAGE_INPUT_SET_MISMATCH")
        if name not in snapshot.files or sha256(snapshot.bytes(name)) != require_hash(item["sha256"]):
            raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
        seen.add(name)
        input_paths[name] = name
    if compact_hash(manifest) != require_hash(descriptor["input_fingerprint"]):
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    task_name = relative_name(descriptor["task_path"])
    if (
        task_name != "control/prompt.txt"
        or task_name not in snapshot.files
        or sha256(snapshot.bytes(task_name)) != require_hash(descriptor["task_sha256"])
    ):
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    cwd_name = relative_name(descriptor["cwd"])
    if cwd_name != "work" or cwd_name not in snapshot.directory_fds:
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")

    input_digest = sha256(snapshot.bytes(input_paths["work/input.json"]))
    expected_command_output = f"{input_digest}  input.json\n"
    expected_output = {
        "canary_id": CONTRACT_ID,
        "input_sha256": input_digest,
        "schema_version": 1,
        "status": "ok",
    }
    if descriptor["expected_command_output"] != expected_command_output:
        raise RuntimeReceiptError("V3E_OUTPUT_INVALID")

    expected = require_exact_keys(
        descriptor["expected_output"],
        {"canary_id", "input_sha256", "schema_version", "status"},
    )
    if (
        type(expected["schema_version"]) is not int
        or expected["schema_version"] != 1
        or not isinstance(expected["canary_id"], str)
        or not isinstance(expected["input_sha256"], str)
        or not isinstance(expected["status"], str)
    ):
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    if canonical_bytes(expected) != canonical_bytes(expected_output):
        raise RuntimeReceiptError("V3E_OUTPUT_INVALID")
    if compact_hash(expected) != require_hash(descriptor["expected_output_canonical_sha256"]):
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")

    allowed = set(require_string_list(descriptor["allowed_item_types"]))
    required = set(require_string_list(descriptor["required_lifecycle_types"]))
    if allowed != {"agent_message", "command_execution", "reasoning"}:
        raise RuntimeReceiptError("V3E_UNEXPECTED_AUTHORITY")
    if required != {"agent_message", "command_execution"} or not required <= allowed:
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    limits = require_exact_keys(descriptor["resource_limits"], RESOURCE_KEYS)
    if limits != EXPECTED_RESOURCE_LIMITS or any(require_int(limits[key], minimum=1) < 1 for key in RESOURCE_KEYS):
        raise RuntimeReceiptError("V3E_RESOURCE_CONTRACT_INVALID")

    artifacts = require_exact_keys(descriptor["artifacts"], ARTIFACT_KEYS)
    if artifacts != EXPECTED_ARTIFACTS:
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    resolved: dict[str, str] = {}
    for key, value in artifacts.items():
        name = relative_name(value)
        if name in seen or name not in snapshot.files:
            raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
        resolved[key] = name
    return resolved


def validate_launch(
    descriptor: dict[str, Any], launch: dict[str, Any], descriptor_sha: str, launch_bytes: bytes
) -> str:
    require_exact_keys(launch, LAUNCH_KEYS)
    require_int(launch["schema_version"], minimum=1)
    require_int(launch["retry_count"])
    if (
        launch["schema_version"] != 1
        or launch["receipt_version"] != LAUNCH_VERSION
        or launch["launch_descriptor_sha256"] != descriptor_sha
        or launch["retry_count"] != 0
    ):
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    equal_fields(
        launch,
        descriptor,
        (
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
        ),
    )
    require_string(launch["invocation_id"])
    require_int(launch["child_pid"], minimum=2)
    require_int(launch["child_pgid"], minimum=2)
    pre_real = require_int(launch["pre_spawn_realtime_ns"], minimum=1)
    post_real = require_int(launch["post_spawn_realtime_ns"], minimum=pre_real)
    pre_mono = require_int(launch["pre_spawn_monotonic_ns"], minimum=1)
    post_mono = require_int(launch["post_spawn_monotonic_ns"], minimum=pre_mono)
    if post_real < pre_real or post_mono <= pre_mono:
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    limiter = require_exact_keys(launch["limiter"], LIMITER_KEYS)
    require_string(limiter["implementation"])
    for key in RESOURCE_KEYS:
        require_int(limiter[key], minimum=1)
    if type(limiter["process_group"]) is not bool or type(limiter["stdout_line_envelope"]) is not bool:
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    expected_limiter = {
        "implementation": "factory-v3-local-launcher-v1",
        **EXPECTED_RESOURCE_LIMITS,
        "process_group": True,
        "stdout_line_envelope": True,
    }
    if limiter != expected_limiter:
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    if launch_bytes != canonical_bytes(launch) + b"\n":
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    return sha256(launch_bytes)


def replay_envelope(
    launch: dict[str, Any],
    rows: list[dict[str, Any]],
    descriptor_sha: str,
    launch_sha: str,
) -> tuple[list[dict[str, Any]], bytes, str, list[int], list[int]]:
    chain = hashlib.sha256(
        CHAIN_DOMAIN
        + b"\0"
        + bytes.fromhex(descriptor_sha)
        + bytes.fromhex(launch_sha)
    ).digest()
    raw = bytearray()
    events: list[dict[str, Any]] = []
    times: list[int] = []
    realtime_values: list[int] = []
    previous_mono = require_int(launch["post_spawn_monotonic_ns"], minimum=1)
    previous_real = require_int(launch["post_spawn_realtime_ns"], minimum=1)
    for index, row in enumerate(rows, start=1):
        require_exact_keys(row, EVENT_RECEIPT_KEYS)
        require_int(row["schema_version"], minimum=1)
        require_int(row["sequence"], minimum=1)
        if row["schema_version"] != 1 or row["sequence"] != index:
            raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
        mono = require_int(row["received_monotonic_ns"], minimum=1)
        real = require_int(row["received_realtime_ns"], minimum=1)
        if mono <= previous_mono or real < previous_real:
            raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
        try:
            encoded_line = require_string(row["raw_line_base64"])
            line = base64.b64decode(encoded_line, validate=True)
        except (binascii.Error, ValueError) as exc:
            raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID") from exc
        if base64.b64encode(line).decode("ascii") != encoded_line:
            raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
        if not line.endswith(b"\n") or line.count(b"\n") != 1:
            raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
        line_hash = sha256(line)
        if line_hash != require_hash(row["raw_line_sha256"]):
            raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
        if row["previous_chain_sha256"] != chain.hex():
            raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
        chain = hashlib.sha256(chain + u64(index) + u64(mono) + bytes.fromhex(line_hash)).digest()
        if row["chain_sha256"] != chain.hex():
            raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
        event = decode_object(line[:-1])
        if line != canonical_bytes(event) + b"\n":
            raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
        raw.extend(line)
        events.append(event)
        times.append(mono)
        realtime_values.append(real)
        previous_mono = mono
        previous_real = real
    return events, bytes(raw), chain.hex(), times, realtime_values


def event_identity(event: dict[str, Any], thread_id: str, turn_id: str) -> None:
    if event.get("thread_id") != thread_id or event.get("turn_id") != turn_id:
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")


def validate_events(
    descriptor: dict[str, Any], events: list[dict[str, Any]], times: list[int]
) -> tuple[str, str, int, int, dict[str, Any], str]:
    if len(events) < 3:
        raise RuntimeReceiptError("V3E_RUNTIME_FIELD_GAP")
    types = [event.get("type") for event in events]
    if types[0] != "thread.started" or types[1] != "turn.started" or types[-1] != "turn.completed":
        raise RuntimeReceiptError("V3E_RUNTIME_FIELD_GAP")
    if types.count("thread.started") != 1 or types.count("turn.started") != 1 or types.count("turn.completed") != 1:
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    if any(kind in {"turn.failed", "error"} for kind in types):
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    if any(kind not in {"thread.started", "turn.started", "item.started", "item.completed", "turn.completed"} for kind in types):
        raise RuntimeReceiptError("V3E_UNEXPECTED_AUTHORITY")

    require_exact_keys(events[0], THREAD_STARTED_KEYS)
    require_exact_keys(events[1], TURN_STARTED_KEYS)
    require_exact_keys(events[-1], TURN_COMPLETED_KEYS)
    if not isinstance(events[0].get("thread_id"), str) or not events[0]["thread_id"]:
        raise RuntimeReceiptError("V3E_RUNTIME_FIELD_GAP")
    if not isinstance(events[1].get("turn_id"), str) or not events[1]["turn_id"]:
        raise RuntimeReceiptError("V3E_RUNTIME_FIELD_GAP")
    thread_id = events[0]["thread_id"]
    turn_id = events[1]["turn_id"]
    if events[1].get("thread_id") != thread_id:
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    if events[-1].get("thread_id") != thread_id or events[-1].get("turn_id") != turn_id:
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")

    usage = require_exact_keys(events[-1].get("usage"), USAGE_KEYS)
    for value in usage.values():
        require_int(value)
    if usage["cached_input_tokens"] > usage["input_tokens"]:
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    allowed = set(descriptor["allowed_item_types"])
    seen_item_ids: set[str] = set()
    command_started: tuple[str, int] | None = None
    command_completed: tuple[str, int] | None = None
    message_started: tuple[str, int] | None = None
    message_completed: tuple[str, int] | None = None
    final_message_text: str | None = None
    command_count = 0
    message_count = 0
    reasoning_count = 0
    for event_index, event in enumerate(events[2:-1], start=2):
        require_exact_keys(event, ITEM_EVENT_KEYS)
        event_identity(event, thread_id, turn_id)
        item = event.get("item")
        if not isinstance(item, dict):
            raise RuntimeReceiptError("V3E_RUNTIME_FIELD_GAP")
        item_id = require_string(item.get("id"))
        item_type = require_string(item.get("type"))
        if item_type not in allowed:
            raise RuntimeReceiptError("V3E_UNEXPECTED_AUTHORITY")
        if item_type == "reasoning":
            if event["type"] != "item.completed":
                raise RuntimeReceiptError("V3E_RUNTIME_FIELD_GAP")
            require_exact_keys(item, REASONING_COMPLETED_KEYS)
            require_string(item["text"])
            if (
                item_id in seen_item_ids
                or command_completed is None
                or message_started is not None
                or event_index != 4
            ):
                raise RuntimeReceiptError("V3E_RUNTIME_LIFECYCLE_INVALID")
            seen_item_ids.add(item_id)
            reasoning_count += 1
            continue

        if item_type == "command_execution":
            if event["type"] == "item.started":
                require_exact_keys(item, COMMAND_STARTED_KEYS)
                if (
                    item_id in seen_item_ids
                    or command_started is not None
                    or command_completed is not None
                    or message_started is not None
                ):
                    raise RuntimeReceiptError("V3E_RUNTIME_LIFECYCLE_INVALID")
                if item["command"] != descriptor["expected_command"]:
                    raise RuntimeReceiptError("V3E_OUTPUT_INVALID")
                command_started = (item_id, event_index)
                seen_item_ids.add(item_id)
                continue
            require_exact_keys(item, COMMAND_COMPLETED_KEYS)
            require_int(item["exit_code"])
            if (
                command_started is None
                or command_completed is not None
                or command_started[0] != item_id
                or message_started is not None
            ):
                raise RuntimeReceiptError("V3E_RUNTIME_LIFECYCLE_INVALID")
            if times[command_started[1]] >= times[event_index]:
                raise RuntimeReceiptError("V3E_RUNTIME_LIFECYCLE_INVALID")
            command_count += 1
            if (
                item.get("command") != descriptor["expected_command"]
                or item.get("aggregated_output") != descriptor["expected_command_output"]
                or item.get("exit_code") != 0
                or item.get("status") != "completed"
            ):
                raise RuntimeReceiptError("V3E_OUTPUT_INVALID")
            command_completed = (item_id, event_index)
            continue

        if item_type != "agent_message":
            raise RuntimeReceiptError("V3E_UNEXPECTED_AUTHORITY")
        if event["type"] == "item.started":
            require_exact_keys(item, MESSAGE_STARTED_KEYS)
            if (
                command_completed is None
                or message_started is not None
                or message_completed is not None
                or item_id in seen_item_ids
            ):
                raise RuntimeReceiptError("V3E_RUNTIME_LIFECYCLE_INVALID")
            message_started = (item_id, event_index)
            seen_item_ids.add(item_id)
            continue
        require_exact_keys(item, MESSAGE_COMPLETED_KEYS)
        if (
            message_started is None
            or message_completed is not None
            or message_started[0] != item_id
            or times[message_started[1]] >= times[event_index]
        ):
            raise RuntimeReceiptError("V3E_RUNTIME_LIFECYCLE_INVALID")
        final_message_text = require_string(item["text"])
        message_completed = (item_id, event_index)
        message_count += 1

    if command_started is None or command_completed is None or message_started is None or message_completed is None:
        raise RuntimeReceiptError("V3E_RUNTIME_LIFECYCLE_INVALID")
    if command_count != descriptor["expected_command_count"] or message_count != 1:
        raise RuntimeReceiptError("V3E_OUTPUT_INVALID")
    if reasoning_count != 1 or types != [
        "thread.started",
        "turn.started",
        "item.started",
        "item.completed",
        "item.completed",
        "item.started",
        "item.completed",
        "turn.completed",
    ]:
        raise RuntimeReceiptError("V3E_RUNTIME_LIFECYCLE_INVALID")
    if descriptor["expected_source_count"] != 0:
        raise RuntimeReceiptError("V3E_SOURCE_TELEMETRY_INVALID")

    if final_message_text is None:
        raise RuntimeReceiptError("V3E_RUNTIME_FIELD_GAP")
    return thread_id, turn_id, 2, len(events), usage, final_message_text


def validate_process(
    descriptor: dict[str, Any],
    launch: dict[str, Any],
    process: dict[str, Any],
    descriptor_sha: str,
    launch_sha: str,
    final_chain: str,
    event_count: int,
    artifact_bytes: dict[str, bytes],
    last_event_time: int,
    last_event_realtime: int,
    thread_id: str,
    turn_id: str,
    usage: dict[str, Any],
    canonical_output_sha: str,
) -> dict[str, Any]:
    require_exact_keys(process, PROCESS_KEYS)
    require_int(process["schema_version"], minimum=1)
    require_int(process["event_count"], minimum=1)
    require_int(process["retry_count"])
    require_int(process["exit_status"])
    if type(process["timed_out"]) is not bool or type(process["interrupted"]) is not bool:
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    process_usage = require_exact_keys(process["usage"], USAGE_KEYS)
    for value in process_usage.values():
        require_int(value)
    if process_usage["cached_input_tokens"] > process_usage["input_tokens"]:
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")
    if (
        process["schema_version"] != 1
        or process["receipt_version"] != PROCESS_VERSION
        or process["contract_id"] != descriptor["contract_id"]
        or process["invocation_id"] != launch["invocation_id"]
        or process["launch_descriptor_sha256"] != descriptor_sha
        or process["launch_receipt_sha256"] != launch_sha
        or process["final_chain_sha256"] != final_chain
        or process["event_count"] != event_count
        or process["retry_count"] != 0
        or process["output_canonical_sha256"] != canonical_output_sha
        or process["thread_id"] != thread_id
        or process["turn_id"] != turn_id
        or process["terminal"] != "turn.completed"
        or canonical_bytes(process_usage) != canonical_bytes(usage)
        or process["verdict_codes"] != ["V3_RUNTIME_RECEIPT_OK"]
    ):
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    expected_hashes = {
        "raw_event_log_sha256": sha256(artifact_bytes["raw_event_log"]),
        "event_receipts_sha256": sha256(artifact_bytes["event_receipts"]),
        "stderr_sha256": sha256(artifact_bytes["stderr"]),
        "final_output_sha256": sha256(artifact_bytes["final_output"]),
    }
    if any(process[key] != value for key, value in expected_hashes.items()):
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    if (
        process["exit_status"] != 0
        or process["signal"] is not None
        or process["timed_out"] is not False
        or process["interrupted"] is not False
    ):
        raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
    end_mono = require_int(process["end_monotonic_ns"], minimum=1)
    end_real = require_int(process["end_realtime_ns"], minimum=1)
    elapsed = require_int(process["elapsed_ns"], minimum=1)
    peak = require_int(process["peak_rss_bytes"], minimum=1)
    aggregate = require_int(process["aggregate_output_bytes"], minimum=1)
    expected_elapsed = end_mono - launch["pre_spawn_monotonic_ns"]
    expected_aggregate = sum(len(value) for value in artifact_bytes.values())
    limits = descriptor["resource_limits"]
    if (
        elapsed != expected_elapsed
        or aggregate != expected_aggregate
        or elapsed > limits["wall_seconds"] * 1_000_000_000
        or peak > limits["memory_bytes"]
        or aggregate > limits["output_bytes"]
        or end_mono < last_event_time
        or end_real < last_event_realtime
    ):
        raise RuntimeReceiptError("V3E_RESOURCE_RECEIPT_INVALID")
    return {
        "end_realtime_ns": process["end_realtime_ns"],
        "end_monotonic_ns": end_mono,
        "elapsed_ns": elapsed,
        "peak_rss_bytes": peak,
        "payload_output_bytes": aggregate,
        "retry_count": process["retry_count"],
        "interrupted": process["interrupted"],
        "timed_out": process["timed_out"],
        "exit_status": process["exit_status"],
        "signal": process["signal"],
    }


def validate_runtime_receipt(
    root: Path,
    expected_descriptor_sha256: str,
    descriptor_path: str = "control/launch-descriptor.json",
) -> dict[str, Any]:
    expected_descriptor_sha = require_hash(expected_descriptor_sha256)
    root = Path(root)
    if relative_name(descriptor_path) != "control/launch-descriptor.json":
        raise RuntimeReceiptError("V3E_RUNTIME_RECEIPT_SCHEMA_INVALID")

    with snapshot_closed_layout(root, expected_descriptor_sha) as snapshot:
        descriptor_bytes = snapshot.bytes("control/launch-descriptor.json")
        descriptor_sha = sha256(descriptor_bytes)
        descriptor = decode_object(descriptor_bytes)
        if descriptor_bytes != canonical_bytes(descriptor) + b"\n":
            raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
        artifacts = validate_descriptor(snapshot, descriptor)

        launch_bytes = snapshot.bytes(artifacts["launch_receipt"])
        launch, _ = load_object_bytes(launch_bytes, canonical_file=True)
        launch_sha = validate_launch(descriptor, launch, descriptor_sha, launch_bytes)
        envelope_bytes = snapshot.bytes(artifacts["event_receipts"])
        envelope_rows, _ = load_jsonl_bytes(envelope_bytes, canonical_lines=True)
        events, reconstructed, final_chain, times, realtime_values = replay_envelope(
            launch,
            envelope_rows,
            descriptor_sha,
            launch_sha,
        )
        raw_bytes = snapshot.bytes(artifacts["raw_event_log"])
        if reconstructed != raw_bytes:
            raise RuntimeReceiptError("V3E_INVOCATION_PROVENANCE_INVALID")
        thread_id, turn_id, start_ordinal, end_ordinal, usage, message_text = validate_events(
            descriptor, events, times
        )

        output_bytes = snapshot.bytes(artifacts["final_output"])
        output, _ = load_object_bytes(output_bytes, canonical_file=True)
        try:
            message_raw = message_text.encode("utf-8")
        except UnicodeEncodeError as exc:
            raise RuntimeReceiptError("V3E_OUTPUT_INVALID") from exc
        if (
            b"\0" in message_raw
            or b"\r" in message_raw
            or message_text != message_text.strip()
        ):
            raise RuntimeReceiptError("V3E_OUTPUT_INVALID")
        try:
            message_output = decode_object(message_raw)
        except RuntimeReceiptError as exc:
            raise RuntimeReceiptError("V3E_OUTPUT_INVALID") from exc
        canonical_output = canonical_bytes(output)
        if (
            output_bytes != canonical_output + b"\n"
            or message_raw != canonical_output
            or message_output != output
            or canonical_output != canonical_bytes(descriptor["expected_output"])
        ):
            raise RuntimeReceiptError("V3E_OUTPUT_INVALID")
        canonical_output_sha = sha256(canonical_output)
        if canonical_output_sha != descriptor["expected_output_canonical_sha256"]:
            raise RuntimeReceiptError("V3E_OUTPUT_INVALID")

        stderr_bytes = snapshot.bytes(artifacts["stderr"])
        process_bytes = snapshot.bytes(artifacts["process_receipt"])
        process, _ = load_object_bytes(process_bytes, canonical_file=True)
        artifact_bytes = {
            "launch_receipt": launch_bytes,
            "raw_event_log": raw_bytes,
            "event_receipts": envelope_bytes,
            "stderr": stderr_bytes,
            "final_output": output_bytes,
        }
        process_derived = validate_process(
            descriptor,
            launch,
            process,
            descriptor_sha,
            launch_sha,
            final_chain,
            len(events),
            artifact_bytes,
            times[-1],
            realtime_values[-1],
            thread_id,
            turn_id,
            usage,
            canonical_output_sha,
        )
        total_root_bytes = snapshot.total_file_bytes()
        if total_root_bytes > descriptor["resource_limits"]["output_bytes"]:
            raise RuntimeReceiptError("V3E_RESOURCE_RECEIPT_INVALID")

        artifact_closure_sha = compact_hash(snapshot.closure_rows())
        derived_quantities = {
            "call_id": descriptor["call_id"],
            "stage": descriptor["stage"],
            "invocation_id": launch["invocation_id"],
            "thread_id": thread_id,
            "turn_id": turn_id,
            "event_count": len(events),
            "start_event_ordinal": start_ordinal,
            "end_event_ordinal": end_ordinal,
            "first_event_monotonic_ns": times[0],
            "last_event_monotonic_ns": times[-1],
            "pre_spawn_monotonic_ns": launch["pre_spawn_monotonic_ns"],
            "end_monotonic_ns": process_derived["end_monotonic_ns"],
            "elapsed_ns": process_derived["elapsed_ns"],
            "payload_output_bytes": process_derived["payload_output_bytes"],
            "total_root_bytes": total_root_bytes,
            "peak_rss_bytes": process_derived["peak_rss_bytes"],
            "usage": usage,
            "retry_count": process_derived["retry_count"],
            "interrupted": process_derived["interrupted"],
            "timed_out": process_derived["timed_out"],
            "exit_status": process_derived["exit_status"],
            "signal": process_derived["signal"],
            "final_chain_sha256": final_chain,
            "output_canonical_sha256": canonical_output_sha,
        }
        derived_quantities_sha = compact_hash(derived_quantities)
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
            "derived_quantities_sha256": derived_quantities_sha,
            "final_chain_sha256": final_chain,
            "output_canonical_sha256": canonical_output_sha,
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
            + bytes.fromhex(derived_quantities_sha)
            + bytes.fromhex(completion_sha)
        )

        return {
            "schema_version": 1,
            "receipt_version": RECEIPT_VERSION,
            "receipt_kind": "runtime",
            "call_id": descriptor["call_id"],
            "stage": descriptor["stage"],
            "provider_policy": descriptor["provider_policy"],
            "thread_id": thread_id,
            "turn_id": turn_id,
            "launch_descriptor_sha256": descriptor_sha,
            "launch_receipt_sha256": launch_sha,
            "completion_sha256": completion_sha,
            "task_sha256": descriptor["task_sha256"],
            "input_fingerprint": descriptor["input_fingerprint"],
            "output_sha256": sha256(output_bytes),
            "output_canonical_sha256": canonical_output_sha,
            "raw_event_log_path": descriptor["artifacts"]["raw_event_log"],
            "raw_event_log_sha256": sha256(raw_bytes),
            "start_event_ordinal": start_ordinal,
            "end_event_ordinal": end_ordinal,
            "terminal": "turn.completed",
            "usage": usage,
            "source_events": [],
            "skeleton_seal": None,
            "retry_count": 0,
            "interrupted": False,
            "run_digest": run_digest,
        }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--descriptor", default="control/launch-descriptor.json")
    parser.add_argument("--expected-descriptor-sha256", required=True)
    args = parser.parse_args()
    try:
        receipt = validate_runtime_receipt(
            args.root,
            args.expected_descriptor_sha256,
            args.descriptor,
        )
    except RuntimeReceiptError as exc:
        print(exc.code)
        return 1
    except Exception:
        print("V3E_RUNTIME_RECEIPT_IO_INVALID")
        return 1
    print(json.dumps(receipt, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
