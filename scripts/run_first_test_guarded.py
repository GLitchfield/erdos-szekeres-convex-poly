#!/usr/bin/env python3
"""Execute one Ticket-0119 first test in a narrow local sandbox.

The public ``run`` command accepts identity receipts only.  It never accepts a
trailing command or invokes a shell.  The worker command is reconstructed from
the frozen task packet, and only a root-owned execution envelope can attest the
result.

This is deliberately not a general agent sandbox.  The only supported worker
is a self-contained, frozen Python checker using the standard library (or an
in-process exact solver imported by that checker).  Bubblewrap supplies sparse
read-only mounts and a new network namespace; a libseccomp filter kills the
worker on process creation, sockets, write-capable opens, and other authority-
expanding system calls.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import ctypes
import datetime as _datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import runpy
import select
import signal
import struct
import subprocess
import sys
import tempfile
import time
import traceback
from typing import Any, Iterable

try:
    from scripts import check_research_campaign as campaign
    from scripts import continuous_idea_generator as generator
except ModuleNotFoundError:  # Direct ``python3 scripts/...`` execution.
    try:
        import check_research_campaign as campaign
        import continuous_idea_generator as generator
    except ModuleNotFoundError:
        # The sparse inner namespace intentionally mounts this guard without
        # the campaign/service implementations.  Inner modes do not need them.
        campaign = None  # type: ignore[assignment]
        generator = None  # type: ignore[assignment]


_THIS_FILE = Path(__file__).resolve()
# Inner modes are mounted either at /guard.py or /guard/<name>.  They need no
# host-repository view; relative worker paths live below /work.
ROOT = Path("/work") if _THIS_FILE.as_posix().startswith("/guard") else _THIS_FILE.parents[1]
RUNS_AGENTS = (ROOT / "runs" / "agents").resolve()
GUARD_PATH = _THIS_FILE
GUARD_PROTOCOL = "ticket-0119-first-test-execution-v1"
ENVELOPE_PROTOCOL = "research-first-test-execution-envelope-v1"
VERIFIER_REQUEST_PROTOCOL = "ticket-0119-event-verifier-request-v1"
VERIFIER_ENVELOPE_PROTOCOL = "research-event-verifier-execution-envelope-v1"
CAPABILITY_PROTOCOL = "research-first-test-guard-capability-v1"
PROCESS_MODEL = "one-filtered-process-no-children-v1"
NETWORK_POLICY = "new-net-namespace-plus-seccomp-kill"
REPOSITORY_POLICY = "sparse-authenticated-inputs-read-only"

MAX_WALL_SECONDS = 30 * 60
MAX_CPU_CORES = 2
MAX_MEMORY_BYTES = 4 * 1024**3
MAX_OUTPUT_BYTES = int(0.1 * 1024**3)
SUPERVISOR_MEMORY_RESERVE = 64 * 1024**2
MAX_FRAME_OVERHEAD = 1024 * 1024
FRAME_MAGIC = b"ESFTG1\0\0"
HEX64 = re.compile(r"^[0-9a-f]{64}$")
SAFE_ROLE = re.compile(r"^[a-z][a-z0-9_]{0,63}$")
SAFE_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")

BWRAP = Path("/usr/bin/bwrap")
TASKSET = Path("/usr/bin/taskset")
PRLIMIT = Path("/usr/bin/prlimit")
PYTHON = Path("/usr/bin/python3")


class GuardError(ValueError):
    """A frozen contract, identity, or execution observation failed."""


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def digest_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def digest(path: Path) -> str:
    return digest_bytes(path.read_bytes())


def utc_now() -> str:
    return _datetime.datetime.now(_datetime.timezone.utc).isoformat()


def exact_keys(value: Any, expected: set[str], label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise GuardError(f"{label} must be an object")
    if set(value) != expected:
        raise GuardError(
            f"{label} keys differ; missing={sorted(expected - set(value))}, "
            f"extra={sorted(set(value) - expected)}"
        )
    return value


def repo_path(value: Any, label: str) -> tuple[str, Path]:
    if not isinstance(value, str) or not value:
        raise GuardError(f"{label} must be a nonempty repository-relative path")
    path = Path(value)
    if path.is_absolute() or ".." in path.parts or value != path.as_posix():
        raise GuardError(f"{label} must be a normalized repository-relative path")
    resolved = (ROOT / path).resolve()
    try:
        resolved.relative_to(ROOT.resolve())
    except ValueError as exc:
        raise GuardError(f"{label} resolves outside the repository") from exc
    return value, resolved


def argument_path(value: str, label: str) -> Path:
    path = Path(value)
    resolved = path.resolve() if path.is_absolute() else (ROOT / path).resolve()
    try:
        resolved.relative_to(ROOT.resolve())
    except ValueError as exc:
        raise GuardError(f"{label} is outside the repository") from exc
    return resolved


def receipt(value: Any, label: str, *, authenticate: bool = True) -> tuple[str, Path]:
    item = exact_keys(value, {"path", "sha256"}, label)
    path_text, path = repo_path(item["path"], f"{label}.path")
    claimed = item["sha256"]
    if not isinstance(claimed, str) or HEX64.fullmatch(claimed) is None:
        raise GuardError(f"{label}.sha256 must be 64 lowercase hexadecimal characters")
    if authenticate:
        if not path.is_file():
            raise GuardError(f"{label} is absent: {path_text}")
        if digest(path) != claimed:
            raise GuardError(f"{label} hash differs: {path_text}")
    return path_text, path


def file_receipt(path: Path) -> dict[str, str]:
    resolved = path.resolve()
    try:
        relative = resolved.relative_to(ROOT.resolve()).as_posix()
    except ValueError as exc:
        raise GuardError(f"receipt path is outside the repository: {path}") from exc
    return {"path": relative, "sha256": digest(resolved)}


def load_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise GuardError(f"cannot parse {label} {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise GuardError(f"{label} must be a JSON object")
    return value


def _ignored(path_text: str) -> bool:
    command = ["git"]
    if (ROOT / ".git-data").is_dir():
        command.extend(["--git-dir=.git-data", "--work-tree=."])
    completed = subprocess.run(
        [*command, "check-ignore", "--no-index", "--quiet", path_text],
        cwd=ROOT,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return completed.returncode == 0


def validate_execution_contract(
    task: dict[str, Any], *, authenticate: bool = True
) -> dict[str, Any]:
    """Validate and return the closed Ticket-0119 execution contract."""
    contract = exact_keys(
        task.get("first_test_execution"),
        {
            "protocol",
            "contract_id",
            "guard_component",
            "engine",
            "argv_template",
            "cwd",
            "input_receipts",
            "outputs",
            "normalized_result_role",
            "process_model",
        },
        "first_test_execution",
    )
    if contract["protocol"] != GUARD_PROTOCOL:
        raise GuardError("first-test execution protocol differs")
    core = {key: value for key, value in contract.items() if key != "contract_id"}
    if contract["contract_id"] != canonical_sha256(core):
        raise GuardError("first-test execution contract_id differs")

    guard_path_text, guard_path = receipt(
        contract["guard_component"], "first-test guard component", authenticate=authenticate
    )
    if guard_path_text != "scripts/run_first_test_guarded.py":
        raise GuardError("first-test guard component path differs")
    if authenticate and guard_path != GUARD_PATH:
        raise GuardError("first-test guard component resolves to another file")

    if contract["engine"] not in {"python_exact", "exact_solver_in_process"}:
        raise GuardError("first-test execution engine is not locally guardable")
    if contract["cwd"] != ".":
        raise GuardError("first-test execution cwd must be '.'")
    if contract["process_model"] != PROCESS_MODEL:
        raise GuardError("first-test execution process model differs")

    task_inputs_value = task.get("inputs")
    if not isinstance(task_inputs_value, list):
        raise GuardError("task inputs must be an array")
    task_inputs: dict[str, str] = {}
    for index, item in enumerate(task_inputs_value):
        path_text, _ = receipt(item, f"task input {index}", authenticate=authenticate)
        if path_text in task_inputs:
            raise GuardError("task input paths must be unique")
        task_inputs[path_text] = item["sha256"]

    execution_inputs = contract["input_receipts"]
    if not isinstance(execution_inputs, list) or not execution_inputs:
        raise GuardError("first-test execution requires frozen checker/input receipts")
    input_map: dict[str, str] = {}
    for index, item in enumerate(execution_inputs):
        path_text, _ = receipt(
            item, f"execution input {index}", authenticate=authenticate
        )
        if path_text in input_map:
            raise GuardError("execution input paths must be unique")
        if task_inputs.get(path_text) != item["sha256"]:
            raise GuardError(f"execution input is not exactly frozen by task: {path_text}")
        if path_text == ".guard" or path_text.startswith(".guard/"):
            raise GuardError("execution inputs may not occupy the reserved .guard view")
        input_map[path_text] = item["sha256"]

    argv = contract["argv_template"]
    if (
        not isinstance(argv, list)
        or len(argv) < 3
        or not all(isinstance(item, str) and item for item in argv)
    ):
        raise GuardError("argv_template must be an array of nonempty strings")
    if argv[:2] != [str(PYTHON), "-B"]:
        raise GuardError("argv_template must begin exactly /usr/bin/python3 -B")
    checker = argv[2]
    if checker not in input_map or not checker.startswith("scripts/"):
        raise GuardError("the worker checker is not an exact frozen scripts/ input")
    if not checker.endswith(".py"):
        raise GuardError("the worker checker must be a Python source file")

    placeholder = re.compile(r"^\{output_fd:([a-z][a-z0-9_]{0,63})\}$")
    output_roles_in_argv: list[str] = []
    input_operands: list[str] = [checker]
    for token in argv[3:]:
        match = placeholder.fullmatch(token)
        if match is not None:
            output_roles_in_argv.append(match.group(1))
            continue
        if "{" in token or "}" in token:
            raise GuardError("argv_template contains an unsupported placeholder")
        if token in input_map:
            input_operands.append(token)
            continue
        if token.startswith("-"):
            continue
        # A value without a slash may be a frozen scalar option.  Anything
        # path-shaped must be an authenticated input operand.
        if "/" in token or token.endswith((".json", ".txt", ".csv", ".bin", ".py")):
            raise GuardError(f"argv path operand is not a frozen input: {token}")
    if set(input_operands) != set(input_map):
        missing = sorted(set(input_map) - set(input_operands))
        raise GuardError(f"frozen execution inputs are not exact argv operands: {missing}")

    ownership = exact_keys(
        task.get("ownership"), {"read_paths", "write_paths"}, "task ownership"
    )
    write_paths = ownership["write_paths"]
    deliverables = task.get("deliverables")
    if (
        not isinstance(write_paths, list)
        or not write_paths
        or not isinstance(deliverables, list)
        or not deliverables
        or any(not isinstance(path, str) for path in [*write_paths, *deliverables])
    ):
        raise GuardError("task outputs and deliverables must be nonempty path arrays")
    outputs = contract["outputs"]
    if not isinstance(outputs, list) or not outputs:
        raise GuardError("first-test execution requires at least one output")
    role_map: dict[str, dict[str, str]] = {}
    output_paths: list[str] = []
    run_id = task.get("run_id")
    if not isinstance(run_id, str) or SAFE_ID.fullmatch(run_id) is None:
        raise GuardError("task run_id is unsafe")
    run_root = Path("runs") / "agents" / run_id
    for index, value in enumerate(outputs):
        item = exact_keys(value, {"role", "path", "media_type"}, f"output {index}")
        role = item["role"]
        if not isinstance(role, str) or SAFE_ROLE.fullmatch(role) is None:
            raise GuardError(f"output {index} has an unsafe role")
        if role in role_map:
            raise GuardError("output roles must be unique")
        path_text, _path = repo_path(item["path"], f"output {index}.path")
        path_value = Path(path_text)
        if path_value == run_root or run_root not in path_value.parents:
            raise GuardError("execution output is not a strict descendant of its run")
        if any(character in path_text for character in "*?[]"):
            raise GuardError("execution output paths must be exact, not patterns")
        if authenticate and not _ignored(path_text):
            raise GuardError(f"execution output is not ignored: {path_text}")
        media_type = item["media_type"]
        if not isinstance(media_type, str) or not media_type:
            raise GuardError("execution output media_type must be nonempty")
        role_map[role] = item
        output_paths.append(path_text)
    if len(set(output_paths)) != len(output_paths):
        raise GuardError("execution output paths must be unique")
    if set(output_paths) != set(write_paths) or set(output_paths) != set(deliverables):
        raise GuardError(
            "execution outputs must exactly equal owned write paths and deliverables"
        )
    if set(output_roles_in_argv) != set(role_map) or len(output_roles_in_argv) != len(role_map):
        raise GuardError("argv_template must name every output role exactly once")
    normalized_role = contract["normalized_result_role"]
    if normalized_role not in role_map:
        raise GuardError("normalized_result_role is not a declared output")
    if role_map[normalized_role]["media_type"] != "application/json":
        raise GuardError("normalized_result_role must use application/json")

    budget = task.get("budget")
    if not isinstance(budget, dict) or set(budget) != {
        "wall_minutes", "cpu_cores", "memory_gib", "output_gib"
    }:
        raise GuardError("task budget has an unexpected contract")
    wall = budget["wall_minutes"]
    cores = budget["cpu_cores"]
    memory = budget["memory_gib"]
    output = budget["output_gib"]
    if not isinstance(wall, int) or isinstance(wall, bool) or not 1 <= wall <= 30:
        raise GuardError("task wall budget exceeds 30 minutes")
    if not isinstance(cores, int) or isinstance(cores, bool) or not 1 <= cores <= 2:
        raise GuardError("task CPU budget exceeds two cores")
    if not isinstance(memory, int) or isinstance(memory, bool) or not 1 <= memory <= 4:
        raise GuardError("task memory budget exceeds 4 GiB")
    if (
        not isinstance(output, (int, float))
        or isinstance(output, bool)
        or not 0 < float(output) <= 0.1
    ):
        raise GuardError("task output budget exceeds 0.1 GiB")

    standing = task.get("standing_first_test")
    if not isinstance(standing, dict):
        raise GuardError("task lacks standing first-test authority")
    limits = standing.get("limits")
    if not isinstance(limits, dict) or limits != {
        "wall_minutes": 30,
        "cpu_cores": 2,
        "memory_gib": 4,
        "output_gib": 0.1,
    }:
        raise GuardError("standing first-test limits differ from Ticket 0119")
    if task.get("theorem_contract") is not None:
        raise GuardError("standing guarded first tests cannot carry a theorem contract")
    claims = task.get("claims_allowed")
    if not isinstance(claims, list) or not set(claims) <= {
        "proposal", "computational_evidence"
    }:
        raise GuardError("standing guarded first tests cannot claim compilation")
    return contract


def resolve_worker_argv(contract: dict[str, Any], output_fds: dict[str, int]) -> list[str]:
    placeholder = re.compile(r"^\{output_fd:([a-z][a-z0-9_]{0,63})\}$")
    resolved: list[str] = []
    for token in contract["argv_template"]:
        match = placeholder.fullmatch(token)
        if match is None:
            if "{" in token or "}" in token:
                raise GuardError("worker argv contains an unsupported placeholder")
            resolved.append(token)
        else:
            role = match.group(1)
            if role not in output_fds:
                raise GuardError(f"worker argv names undeclared output role: {role}")
            resolved.append(str(output_fds[role]))
    return resolved


def resource_policy(task: dict[str, Any]) -> dict[str, int | list[int]]:
    budget = task["budget"]
    available = sorted(os.sched_getaffinity(0))
    count = min(int(budget["cpu_cores"]), MAX_CPU_CORES, len(available))
    if count < 1:
        raise GuardError("no CPU is available to the first-test guard")
    policy = {
        "wall_seconds": min(int(budget["wall_minutes"]) * 60, MAX_WALL_SECONDS),
        "cpu_affinity": available[:count],
        "memory_bytes": min(int(budget["memory_gib"]) * 1024**3, MAX_MEMORY_BYTES),
        "output_bytes": min(int(float(budget["output_gib"]) * 1024**3), MAX_OUTPUT_BYTES),
    }
    if int(policy["output_bytes"]) < 1:
        raise GuardError("task output budget rounds below one byte")
    return policy


# The filter is default-allow so the pinned stdlib interpreter can run, but all
# authority-expanding calls relevant to this narrow worker are kill actions.
FORBIDDEN_SYSCALLS = (
    "fork", "vfork", "clone", "clone3", "execve", "execveat",
    "socket", "socketpair", "connect", "bind", "listen", "accept", "accept4",
    "sendto", "sendmsg", "sendmmsg", "recvfrom", "recvmsg", "recvmmsg",
    "shutdown", "setsockopt", "getsockopt",
    "creat", "openat2", "unlink", "unlinkat", "mkdir", "mkdirat", "rmdir",
    "rename", "renameat", "renameat2", "link", "linkat", "symlink", "symlinkat",
    "mknod", "mknodat", "chmod", "fchmod", "fchmodat", "chown", "fchown",
    "lchown", "fchownat", "truncate", "ftruncate", "utime", "utimes",
    "futimesat", "utimensat", "setxattr", "lsetxattr", "fsetxattr",
    "removexattr", "lremovexattr", "fremovexattr",
    "mount", "umount", "umount2", "pivot_root", "chroot", "unshare", "setns",
    "ptrace", "process_vm_readv", "process_vm_writev", "pidfd_open",
    "pidfd_getfd", "pidfd_send_signal", "kill", "tkill", "tgkill",
    "add_key", "request_key", "keyctl", "bpf", "perf_event_open",
    "init_module", "finit_module", "delete_module", "reboot", "iopl", "ioperm",
    "io_uring_setup", "io_uring_enter", "io_uring_register",
)
WRITE_OPEN_FLAGS = tuple(
    sorted(
        {
            os.O_WRONLY,
            os.O_RDWR,
            os.O_CREAT,
            os.O_TRUNC,
            os.O_APPEND,
            getattr(os, "O_TMPFILE", 0),
        }
        - {0}
    )
)


class _ScmpArgCmp(ctypes.Structure):
    _fields_ = [
        ("arg", ctypes.c_uint),
        ("op", ctypes.c_int),
        ("datum_a", ctypes.c_uint64),
        ("datum_b", ctypes.c_uint64),
    ]


def _seccomp_library() -> ctypes.CDLL:
    try:
        library = ctypes.CDLL("libseccomp.so.2", use_errno=True)
    except OSError as exc:
        raise GuardError(f"libseccomp.so.2 is unavailable: {exc}") from exc
    library.seccomp_init.argtypes = [ctypes.c_uint32]
    library.seccomp_init.restype = ctypes.c_void_p
    library.seccomp_release.argtypes = [ctypes.c_void_p]
    library.seccomp_release.restype = None
    library.seccomp_syscall_resolve_name.argtypes = [ctypes.c_char_p]
    library.seccomp_syscall_resolve_name.restype = ctypes.c_int
    library.seccomp_rule_add_array.argtypes = [
        ctypes.c_void_p,
        ctypes.c_uint32,
        ctypes.c_int,
        ctypes.c_uint,
        ctypes.POINTER(_ScmpArgCmp),
    ]
    library.seccomp_rule_add_array.restype = ctypes.c_int
    library.seccomp_load.argtypes = [ctypes.c_void_p]
    library.seccomp_load.restype = ctypes.c_int
    return library


def seccomp_policy() -> dict[str, Any]:
    library = _seccomp_library()
    resolved: list[str] = []
    missing: list[str] = []
    for name in FORBIDDEN_SYSCALLS:
        if library.seccomp_syscall_resolve_name(name.encode("ascii")) >= 0:
            resolved.append(name)
        else:
            missing.append(name)
    critical = {"clone", "execve", "socket", "openat"}
    if any(name in missing for name in critical - {"openat"}):
        raise GuardError(f"critical seccomp syscalls cannot be resolved: {missing}")
    if library.seccomp_syscall_resolve_name(b"openat") < 0:
        raise GuardError("critical seccomp syscall cannot be resolved: openat")
    if library.seccomp_syscall_resolve_name(b"open") < 0:
        raise GuardError("critical seccomp syscall cannot be resolved: open")
    return {
        "version": "ticket-0119-libseccomp-kill-v1",
        "default_action": "allow",
        "kill_action": "kill_process",
        "forbidden_syscalls": resolved,
        "unavailable_syscalls": missing,
        "write_open_flags": list(WRITE_OPEN_FLAGS),
        "write_open_rule": "masked-equal-any-bit",
    }


def seccomp_policy_sha256() -> str:
    return canonical_sha256(seccomp_policy())


def _check_rc(code: int, label: str) -> None:
    if code != 0:
        raise GuardError(f"libseccomp {label} failed with {-code if code < 0 else code}")


def install_seccomp_filter() -> str:
    """Install the exact worker filter and return its policy digest."""
    policy = seccomp_policy()
    library = _seccomp_library()
    SCMP_ACT_ALLOW = 0x7FFF0000
    SCMP_ACT_KILL_PROCESS = 0x80000000
    SCMP_CMP_MASKED_EQ = 7
    context = library.seccomp_init(SCMP_ACT_ALLOW)
    if not context:
        raise GuardError("libseccomp could not allocate a filter")
    try:
        for name in policy["forbidden_syscalls"]:
            number = library.seccomp_syscall_resolve_name(name.encode("ascii"))
            _check_rc(
                library.seccomp_rule_add_array(
                    context, SCMP_ACT_KILL_PROCESS, number, 0, None
                ),
                f"rule {name}",
            )
        for name, argument in (("open", 1), ("openat", 2)):
            number = library.seccomp_syscall_resolve_name(name.encode("ascii"))
            for flag in WRITE_OPEN_FLAGS:
                comparison = _ScmpArgCmp(
                    arg=argument,
                    op=SCMP_CMP_MASKED_EQ,
                    datum_a=flag,
                    datum_b=flag,
                )
                _check_rc(
                    library.seccomp_rule_add_array(
                        context,
                        SCMP_ACT_KILL_PROCESS,
                        number,
                        1,
                        ctypes.pointer(comparison),
                    ),
                    f"write-open rule {name}/{flag}",
                )
        _check_rc(library.seccomp_load(context), "load")
    finally:
        library.seccomp_release(context)
    return canonical_sha256(policy)


def set_no_new_privileges() -> None:
    libc = ctypes.CDLL(None, use_errno=True)
    libc.prctl.argtypes = [
        ctypes.c_int,
        ctypes.c_ulong,
        ctypes.c_ulong,
        ctypes.c_ulong,
        ctypes.c_ulong,
    ]
    libc.prctl.restype = ctypes.c_int
    if libc.prctl(38, 1, 0, 0, 0) != 0:  # PR_SET_NO_NEW_PRIVS
        error = ctypes.get_errno()
        raise GuardError(f"PR_SET_NO_NEW_PRIVS failed: {os.strerror(error)}")


def _close_fds_except(kept: set[int]) -> None:
    try:
        candidates = [int(name) for name in os.listdir("/proc/self/fd") if name.isdigit()]
    except OSError:
        soft, _hard = resource.getrlimit(resource.RLIMIT_NOFILE)
        candidates = list(range(3, min(int(soft), 4096)))
    for descriptor in candidates:
        if descriptor > 2 and descriptor not in kept:
            try:
                os.close(descriptor)
            except OSError:
                pass


def _write_all(descriptor: int, data: bytes) -> None:
    view = memoryview(data)
    while view:
        written = os.write(descriptor, view)
        view = view[written:]


def _inner_worker(config: dict[str, Any], result_fd: int) -> int:
    outputs = config["outputs"]
    output_descriptors: dict[str, int] = {}
    output_files: dict[str, Path] = {}
    for index, item in enumerate(outputs):
        role = item["role"]
        path = Path("/out") / f"output-{index:03d}"
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        os.set_inheritable(descriptor, True)
        output_descriptors[role] = descriptor
        output_files[role] = path
    stdout_path = Path("/out/.guard-stdout")
    stderr_path = Path("/out/.guard-stderr")
    stdout_fd = os.open(stdout_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    stderr_fd = os.open(stderr_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    os.chmod("/out", 0o555)

    resolved_argv = resolve_worker_argv(config["contract"], output_descriptors)
    ack_read, ack_write = os.pipe()
    started = time.monotonic()
    child = os.fork()
    if child == 0:
        try:
            os.close(ack_read)
            os.close(result_fd)
            null_fd = os.open("/dev/null", os.O_RDONLY)
            os.dup2(null_fd, 0)
            os.dup2(stdout_fd, 1)
            os.dup2(stderr_fd, 2)
            kept = {0, 1, 2, ack_write, *output_descriptors.values()}
            _close_fds_except(kept)
            resources = config["resources"]
            os.sched_setaffinity(0, set(resources["cpu_affinity"]))
            memory_limit = max(
                64 * 1024**2,
                int(resources["memory_bytes"]) - SUPERVISOR_MEMORY_RESERVE,
            )
            resource.setrlimit(resource.RLIMIT_AS, (memory_limit, memory_limit))
            cpu_limit = max(
                1,
                int(resources["wall_seconds"]) * len(resources["cpu_affinity"]),
            )
            resource.setrlimit(resource.RLIMIT_CPU, (cpu_limit, cpu_limit))
            resource.setrlimit(
                resource.RLIMIT_FSIZE,
                (int(resources["output_bytes"]), int(resources["output_bytes"])),
            )
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
            set_no_new_privileges()
            installed = install_seccomp_filter()
            if installed != config["seccomp_policy_sha256"]:
                raise GuardError("inner seccomp policy digest differs")
            _write_all(ack_write, b"1")
            os.close(ack_write)
            checker = resolved_argv[2]
            sys.argv = [checker, *resolved_argv[3:]]
            try:
                runpy.run_path(checker, run_name="__main__")
            except SystemExit as exc:
                code = exc.code
                if code is None:
                    code = 0
                if not isinstance(code, int):
                    print(code, file=sys.stderr)
                    code = 1
                sys.stdout.flush()
                sys.stderr.flush()
                os._exit(code & 0xFF)
            sys.stdout.flush()
            sys.stderr.flush()
            os._exit(0)
        except BaseException:  # This is the worker's bounded diagnostic stream.
            traceback.print_exc()
            try:
                sys.stdout.flush()
                sys.stderr.flush()
            except BaseException:
                pass
            os._exit(70)

    os.close(ack_write)
    for descriptor in [*output_descriptors.values(), stdout_fd, stderr_fd]:
        os.close(descriptor)
    waited, status, usage = os.wait4(child, 0)
    if waited != child:
        raise GuardError("inner supervisor waited for an unexpected worker")
    try:
        ack = os.read(ack_read, 2)
    finally:
        os.close(ack_read)
    filter_loaded = ack == b"1"
    exit_code: int | None
    worker_signal: int | None
    if os.WIFEXITED(status):
        exit_code = os.WEXITSTATUS(status)
        worker_signal = None
    elif os.WIFSIGNALED(status):
        exit_code = None
        worker_signal = os.WTERMSIG(status)
    else:
        exit_code = None
        worker_signal = None

    streams: list[dict[str, Any]] = []
    payload = bytearray()
    for role, path in [*(output_files.items()), ("__stdout__", stdout_path), ("__stderr__", stderr_path)]:
        data = path.read_bytes()
        streams.append({
            "role": role,
            "bytes": len(data),
            "sha256": digest_bytes(data),
        })
        payload.extend(data)
    header = {
        "protocol": "research-first-test-inner-result-v1",
        "filter_loaded": filter_loaded,
        "seccomp_policy_sha256": config["seccomp_policy_sha256"],
        "exit_code": exit_code,
        "signal": worker_signal,
        "cpu_seconds": float(usage.ru_utime + usage.ru_stime),
        "wall_seconds": time.monotonic() - started,
        "maxrss_kib": int(usage.ru_maxrss),
        "resolved_argv": resolved_argv,
        "streams": streams,
    }
    encoded = canonical_bytes(header)
    frame = FRAME_MAGIC + struct.pack(">Q", len(encoded)) + encoded + bytes(payload)
    _write_all(result_fd, frame)
    return 0


def _inner_capability(result_fd: int, attempt: str) -> int:
    set_no_new_privileges()
    installed = install_seccomp_filter()
    if attempt == "none":
        _write_all(result_fd, canonical_bytes({"policy": installed, "status": "filtered"}))
        return 0
    if attempt == "network":
        import socket

        socket.socket()
    elif attempt == "write":
        with open("/out/forbidden", "wb") as handle:
            handle.write(b"forbidden")
    elif attempt == "spawn":
        os.fork()
    else:
        raise GuardError(f"unknown capability attempt: {attempt}")
    return 71


def build_bwrap_argv(
    *,
    work_root: Path,
    empty_shm: Path,
    cpu_affinity: list[int],
    output_bytes: int,
    contract_fd: int,
    result_fd: int,
    status_fd: int,
) -> list[str]:
    cpu_list = ",".join(str(item) for item in cpu_affinity)
    return [
        str(TASKSET), "--cpu-list", cpu_list,
        str(PRLIMIT), "--core=0:0", "--nofile=64:64",
        f"--fsize={output_bytes}:{output_bytes}", "--",
        str(BWRAP),
        "--unshare-all", "--unshare-user", "--disable-userns",
        "--assert-userns-disabled", "--die-with-parent", "--new-session",
        "--clearenv",
        "--setenv", "PATH", "/usr/bin:/bin",
        "--setenv", "HOME", "/nonexistent",
        "--setenv", "TMPDIR", "/nonexistent",
        "--setenv", "PYTHONDONTWRITEBYTECODE", "1",
        "--setenv", "PYTHONHASHSEED", "0",
        "--setenv", "LC_ALL", "C.UTF-8",
        "--dir", "/guard",
        "--ro-bind", str(GUARD_PATH), "/guard/run_first_test_guarded.py",
        "--ro-bind", str(work_root), "/work",
        "--ro-bind", "/usr", "/usr",
        "--ro-bind-try", "/lib", "/lib",
        "--ro-bind-try", "/lib64", "/lib64",
        "--proc", "/proc", "--dev", "/dev",
        "--ro-bind", str(empty_shm), "/dev/shm",
        "--size", str(output_bytes), "--tmpfs", "/out",
        "--chdir", "/work",
        "--json-status-fd", str(status_fd),
        "--",
        str(PYTHON), "-B", "/guard/run_first_test_guarded.py", "inner",
        "--contract-fd", str(contract_fd), "--result-fd", str(result_fd),
    ]


def _capability_bwrap_argv(*, result_fd: int, status_fd: int, attempt: str) -> list[str]:
    return [
        str(BWRAP),
        "--unshare-all", "--unshare-user", "--disable-userns",
        "--assert-userns-disabled", "--die-with-parent", "--new-session",
        "--clearenv",
        "--setenv", "PYTHONDONTWRITEBYTECODE", "1",
        "--setenv", "PYTHONHASHSEED", "0",
        "--ro-bind", str(GUARD_PATH), "/guard.py",
        "--ro-bind", "/usr", "/usr",
        "--ro-bind-try", "/lib", "/lib",
        "--ro-bind-try", "/lib64", "/lib64",
        "--proc", "/proc", "--dev", "/dev",
        "--size", "1048576", "--tmpfs", "/out",
        "--json-status-fd", str(status_fd),
        "--",
        str(PYTHON), "-B", "/guard.py", "inner-capability",
        "--result-fd", str(result_fd), "--attempt", attempt,
    ]


def _parse_status_documents(data: bytes) -> list[dict[str, Any]]:
    documents: list[dict[str, Any]] = []
    for line in data.splitlines():
        if not line.strip():
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError as exc:
            raise GuardError(f"Bubblewrap status is malformed: {exc}") from exc
        if not isinstance(value, dict):
            raise GuardError("Bubblewrap status document is not an object")
        documents.append(value)
    return documents


def run_capability_probe(attempt: str) -> dict[str, Any]:
    """Run a no-external-state Bubblewrap/seccomp smoke probe."""
    if attempt not in {"none", "network", "write", "spawn"}:
        raise GuardError("capability attempt is invalid")
    required = [BWRAP, PYTHON]
    missing = [str(path) for path in required if not path.is_file()]
    if missing:
        return {
            "attempt": attempt,
            "terminal": "LAUNCH_STOP",
            "observed": False,
            "exit_code": None,
            "signal": None,
            "status": [],
            "detail": f"required components are absent: {missing}",
        }
    try:
        expected_policy = seccomp_policy_sha256()
    except GuardError as exc:
        return {
            "attempt": attempt, "terminal": "LAUNCH_STOP", "observed": False,
            "exit_code": None, "signal": None, "status": [], "detail": str(exc),
        }
    result_read, result_write = os.pipe()
    status_read, status_write = os.pipe()
    command = _capability_bwrap_argv(
        result_fd=result_write, status_fd=status_write, attempt=attempt
    )
    try:
        process = subprocess.Popen(
            command,
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            pass_fds=(result_write, status_write),
            start_new_session=True,
        )
    except OSError as exc:
        os.close(result_read); os.close(result_write)
        os.close(status_read); os.close(status_write)
        return {
            "attempt": attempt, "terminal": "LAUNCH_STOP", "observed": False,
            "exit_code": None, "signal": None, "status": [], "detail": str(exc),
        }
    os.close(result_write)
    os.close(status_write)
    try:
        _stdout, stderr = process.communicate(timeout=10)
    except subprocess.TimeoutExpired:
        os.killpg(os.getpgid(process.pid), signal.SIGKILL)
        _stdout, stderr = process.communicate()
    result = bytearray()
    status_data = bytearray()
    for descriptor, target in ((result_read, result), (status_read, status_data)):
        while True:
            chunk = os.read(descriptor, 65536)
            if not chunk:
                break
            target.extend(chunk)
        os.close(descriptor)
    documents = _parse_status_documents(bytes(status_data)) if status_data else []
    status_exit = next(
        (item.get("exit-code") for item in documents if "exit-code" in item), None
    )
    exit_status = status_exit if isinstance(status_exit, int) else process.returncode
    observed_signal = (
        signal.SIGSYS
        if exit_status in {signal.SIGSYS, 128 + signal.SIGSYS}
        else None
    )
    if attempt == "none":
        try:
            payload = json.loads(bytes(result))
        except (UnicodeDecodeError, json.JSONDecodeError):
            payload = None
        passed = (
            process.returncode == 0
            and isinstance(payload, dict)
            and payload == {"policy": expected_policy, "status": "filtered"}
            and any("net-namespace" in item for item in documents)
        )
    else:
        passed = (
            observed_signal == signal.SIGSYS
            and not result
            and any("net-namespace" in item for item in documents)
        )
    return {
        "attempt": attempt,
        "terminal": "PASS" if passed else "LAUNCH_STOP",
        "observed": bool(documents),
        "exit_code": exit_status,
        "signal": observed_signal,
        "status": documents,
        "detail": stderr.decode("utf-8", "replace")[-2000:],
    }


def capability_report(negative: str = "network") -> dict[str, Any]:
    positive = run_capability_probe("none")
    hostile = run_capability_probe(negative) if positive["terminal"] == "PASS" else None
    passed = positive["terminal"] == "PASS" and hostile is not None and hostile["terminal"] == "PASS"
    return {
        "schema_version": 1,
        "protocol": CAPABILITY_PROTOCOL,
        "guard_component": file_receipt(GUARD_PATH),
        "positive": positive,
        "negative": hostile,
        "terminal": "PASS" if passed else "LAUNCH_STOP",
    }


def _copy_sparse_inputs(
    work_root: Path,
    contract: dict[str, Any],
    claim_path: Path,
    brief_path: Path,
    task_path: Path,
    identity_sha256: dict[str, str] | None = None,
) -> None:
    for item in contract["input_receipts"]:
        path_text, source = receipt(item, "sparse input", authenticate=True)
        data = source.read_bytes()
        if digest_bytes(data) != item["sha256"]:
            raise GuardError(f"sparse input changed while being copied: {path_text}")
        destination = work_root / path_text
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
        destination.chmod(0o444)
    metadata = work_root / ".guard"
    metadata.mkdir(parents=True, exist_ok=False)
    metadata_sources = {
        "claim.json": claim_path,
        "brief.json": brief_path,
        "task.json": task_path,
    }
    expected_identity = identity_sha256 or {
        name: digest(source) for name, source in metadata_sources.items()
    }
    if set(expected_identity) != set(metadata_sources):
        raise GuardError("sparse identity digest map differs from claim/brief/task")
    for name, source in metadata_sources.items():
        data = source.read_bytes()
        if digest_bytes(data) != expected_identity[name]:
            raise GuardError(f"sparse identity changed while being copied: {name}")
        destination = metadata / name
        destination.write_bytes(data)
        destination.chmod(0o444)
    for directory, children, _files in os.walk(work_root, topdown=False):
        del children
        Path(directory).chmod(0o555)


def validate_verifier_request(
    value: Any, *, service_dir_value: str | Path, request_path: Path | None = None
) -> tuple[
    dict[str, Any], dict[str, Any], Path, dict[str, Any], Path, dict[str, Any], Path
]:
    """Authenticate a root-frozen, artifact-consuming verifier request."""
    request = exact_keys(
        value,
        {
            "schema_version", "protocol", "verifier_contract_id",
            "guard_component", "seed_claim", "task_packet", "claim_id",
            "task_id", "event", "checker", "argv_template", "input_receipts",
            "expected_normalized_result", "budget", "process_model",
        },
        "event verifier request",
    )
    if request["schema_version"] != 1 or request["protocol"] != VERIFIER_REQUEST_PROTOCOL:
        raise GuardError("event verifier request version/protocol differs")
    if (
        not isinstance(request["verifier_contract_id"], str)
        or HEX64.fullmatch(request["verifier_contract_id"]) is None
    ):
        raise GuardError("event verifier contract ID is malformed")
    guard_text, guard_file = receipt(
        request["guard_component"], "event verifier guard", authenticate=True
    )
    if guard_text != "scripts/run_first_test_guarded.py" or guard_file != GUARD_PATH:
        raise GuardError("event verifier request binds another guard")
    if request["process_model"] != PROCESS_MODEL:
        raise GuardError("event verifier process model differs")

    claim_text, claim_path = receipt(request["seed_claim"], "verifier seed claim")
    task_text, task_path = receipt(request["task_packet"], "verifier task packet")
    claim = load_json(claim_path, "verifier seed claim")
    task = load_json(task_path, "verifier task packet")
    if request["claim_id"] != claim.get("claim_id") or request["task_id"] != task.get("task_id"):
        raise GuardError("event verifier request identity differs from claim/task")
    if claim.get("task_packet") != file_receipt(task_path):
        raise GuardError("event verifier claim does not bind its task")
    brief_text, brief_path = receipt(
        claim.get("development_brief"), "event verifier development brief"
    )
    brief = load_json(brief_path, "event verifier development brief")
    if campaign is None or generator is None:
        raise GuardError("campaign/service validators are unavailable in outer verifier mode")
    try:
        campaign.validate_brief(
            brief, brief_path=brief_path, task_packet=task, authenticate=True
        )
    except Exception as exc:
        raise GuardError(f"event verifier brief/task validation failed: {exc}") from exc
    execution = validate_execution_contract(task, authenticate=True)

    seed_identity = claim.get("seed")
    if not isinstance(seed_identity, dict):
        raise GuardError("event verifier claim seed identity is absent")
    campaign_id = seed_identity.get("campaign_id")
    seed_id = seed_identity.get("seed_id")
    _batch_text, seed_path = receipt(
        seed_identity.get("seed_batch"), "event verifier seed batch"
    )
    if not isinstance(campaign_id, str) or not isinstance(seed_id, str):
        raise GuardError("event verifier claim composite identity is invalid")
    try:
        generator.validate_seed_claim(
            claim_path, campaign_id=campaign_id, seed_id=seed_id, seed_path=seed_path
        )
        service_dir = generator.service_directory(Path(service_dir_value))
        _authorization_path, authorization = generator.active_standing_authorization(service_dir)
        accounting = generator.validate_accounting_chain(service_dir, authorization)
        inventory = generator.seed_inventory(
            service_dir, authorization=authorization, accounting=accounting
        )
    except Exception as exc:
        raise GuardError(f"event verifier current claim authentication failed: {exc}") from exc
    matching = [
        item for item in inventory
        if item.get("campaign_id") == campaign_id
        and item.get("seed_id") == seed_id
        and item.get("claim") == file_receipt(claim_path)
    ]
    if len(matching) != 1 or matching[0].get("state") != "investigating":
        raise GuardError("event verifier requires one unreconciled investigating identity")

    event = exact_keys(
        request["event"],
        {
            "event_id", "event_core_sha256", "subject_contract_id",
            "model_contract_id", "scope_contract_id", "artifact",
        },
        "event verifier event",
    )
    event_id = event["event_id"]
    if not isinstance(event_id, str) or HEX64.fullmatch(event_id) is None:
        raise GuardError("event verifier event_id must be its 64-hex event hash")
    for key in (
        "event_core_sha256", "subject_contract_id", "model_contract_id", "scope_contract_id"
    ):
        if not isinstance(event[key], str) or HEX64.fullmatch(event[key]) is None:
            raise GuardError(f"event verifier {key} is invalid")
    artifact_text, artifact_path = receipt(
        event["artifact"], "event verifier mathematical artifact"
    )
    if artifact_text not in task.get("deliverables", []):
        raise GuardError("event verifier artifact is not an exact task deliverable")

    first_envelope_path = _derived_envelope_path(task)
    if not first_envelope_path.is_file():
        raise GuardError("event verifier requires a PASS first-test execution envelope")
    first_identity = {
        "seed_claim": file_receipt(claim_path),
        "claim_id": claim["claim_id"],
        "development_brief": file_receipt(brief_path),
        "brief_id": brief["brief_id"],
        "task_packet": file_receipt(task_path),
        "task_id": task["task_id"],
        "execution_contract_id": execution["contract_id"],
    }
    first_envelope = validate_envelope(
        load_json(first_envelope_path, "first-test execution envelope"),
        expected_identity=first_identity,
        authenticate_outputs=True,
    )
    if first_envelope["terminal"] != "PASS":
        raise GuardError("event verifier cannot replay a non-PASS first test")
    artifact_writes = [
        item for item in first_envelope["observation"]["writes"]
        if item["path"] == artifact_text
        and item["sha256"] == event["artifact"]["sha256"]
        and item["materialized"] is True
    ]
    if len(artifact_writes) != 1:
        raise GuardError("event verifier artifact is absent from the first-test manifest")

    checker_text, checker_path = receipt(
        request["checker"], "event verifier checker", authenticate=True
    )
    if checker_text != execution["argv_template"][2]:
        raise GuardError("event verifier does not reuse the frozen first-test checker")
    raw_inputs = [
        item for item in execution["input_receipts"] if item["path"] != checker_text
    ]
    expected_receipts = [request["checker"], event["artifact"], *raw_inputs]
    if request["input_receipts"] != expected_receipts:
        raise GuardError("event verifier input receipts differ from checker/artifact/raw inputs")
    for index, item in enumerate(request["input_receipts"]):
        receipt(item, f"event verifier input {index}", authenticate=True)
    expected_argv = [
        str(PYTHON), "-B", checker_text,
        "--verify-event", artifact_text, "--normalized-result-stdout",
    ]
    for item in raw_inputs:
        expected_argv.extend(["--input", item["path"]])
    if request["argv_template"] != expected_argv:
        raise GuardError("event verifier argv differs from the canonical replay invocation")
    if request["budget"] != task.get("budget"):
        raise GuardError("event verifier budget differs from its frozen task")
    expected_result = request["expected_normalized_result"]
    normalized = exact_keys(
        expected_result,
        {
            "schema_version", "protocol", "verified_event_core_sha256",
            "event_artifact", "claim_contract_id", "primary_contract_id",
            "subject_contract_id", "model_contract_id", "scope_contract_id",
            "kind", "gate_branch", "polarity", "damage_scope_reached",
            "observation_sha256", "checked_predicate", "result",
            "verified_learning",
        },
        "event verifier expected normalized result",
    )
    evidence_contract = brief.get("evidence_contract") or {}
    evidence_scope = evidence_contract.get("scope") or {}
    if (
        normalized["schema_version"] != 1
        or normalized["protocol"] != "research-event-normalized-result-v1"
        or normalized["verified_event_core_sha256"] != event["event_core_sha256"]
        or normalized["event_artifact"] != event["artifact"]
        or normalized["subject_contract_id"] != event["subject_contract_id"]
        or normalized["model_contract_id"] != event["model_contract_id"]
        or normalized["scope_contract_id"] != event["scope_contract_id"]
        or normalized["checked_predicate"] != (brief.get("probe") or {}).get("question")
        or normalized["result"] != normalized["polarity"]
        or normalized["claim_contract_id"] != evidence_contract.get("contract_id")
        or normalized["primary_contract_id"] != evidence_contract.get("contract_id")
        or normalized["model_contract_id"] != evidence_contract.get("model_contract_id")
        or normalized["scope_contract_id"] != evidence_scope.get("scope_contract_id")
    ):
        raise GuardError("event verifier expected result identity differs")
    for key in (
        "claim_contract_id", "primary_contract_id", "subject_contract_id",
        "model_contract_id", "scope_contract_id", "observation_sha256",
    ):
        if not isinstance(normalized[key], str) or HEX64.fullmatch(normalized[key]) is None:
            raise GuardError(f"event verifier normalized {key} is invalid")
    if (
        not isinstance(normalized["kind"], str)
        or not normalized["kind"]
        or normalized["gate_branch"] not in {"live", "kill", "no_signal", "sidecar"}
        or normalized["polarity"] not in {"supports", "refutes", "observes"}
        or normalized["damage_scope_reached"] not in {"candidate-local", "subfamily"}
        or not isinstance(normalized["checked_predicate"], str)
        or not normalized["checked_predicate"]
    ):
        raise GuardError("event verifier normalized semantic fields are invalid")
    learning = exact_keys(
        normalized["verified_learning"],
        {"failing_feature", "strongest_supported_statement"},
        "event verifier normalized verified_learning",
    )
    falsifier = (
        normalized["kind"] in {"exact_falsifier", "claim_refuted"}
        and normalized["gate_branch"] == "kill"
        and normalized["polarity"] == "refutes"
    )
    for role in ("failing_feature", "strongest_supported_statement"):
        item = learning[role]
        if falsifier:
            claim = exact_keys(
                item,
                {"learning_claim_id", "text", "subject_contract_id"},
                f"event verifier normalized {role}",
            )
            if (
                not isinstance(claim["text"], str)
                or not claim["text"].strip()
                or len(claim["text"]) > 2000
                or claim["subject_contract_id"] != normalized["subject_contract_id"]
            ):
                raise GuardError(f"event verifier normalized {role} is invalid")
            learning_core = {
                "role": role,
                "text": claim["text"],
                "subject_contract_id": claim["subject_contract_id"],
                "model_contract_id": normalized["model_contract_id"],
                "scope_contract_id": normalized["scope_contract_id"],
                "verified_event_core_sha256": normalized["verified_event_core_sha256"],
            }
            if claim["learning_claim_id"] != canonical_sha256(learning_core):
                raise GuardError(f"event verifier normalized {role} ID differs")
        elif item is not None:
            raise GuardError("non-falsifier verifier result cannot verify negative learning")
    if len(canonical_bytes(expected_result)) > 64 * 1024:
        raise GuardError("event verifier expected normalized result exceeds 64 KiB")

    engine = (
        "python_exact" if execution["engine"] == "python_exact" else "exact_solver"
    )
    verifier_core = {
        "verifier_component": request["checker"],
        "claim_contract_id": normalized["claim_contract_id"],
        "primary_contract_id": normalized["primary_contract_id"],
        "subject_contract_id": normalized["subject_contract_id"],
        "model_contract_id": normalized["model_contract_id"],
        "scope_contract_id": normalized["scope_contract_id"],
        "verified_event_core_sha256": normalized["verified_event_core_sha256"],
        "event_artifact": normalized["event_artifact"],
        "engine": engine,
        "invocation": {"argv": expected_argv, "cwd": "."},
        "input_receipts": [event["artifact"], *raw_inputs],
    }
    if request["verifier_contract_id"] != canonical_sha256(verifier_core):
        raise GuardError("event verifier contract ID differs from verifier-v3")

    run_id = task.get("run_id")
    expected_request = (
        ROOT / "runs" / "agents" / str(run_id) / "root-receipts"
        / f"{event_id}.verification-request.json"
    ).resolve()
    if request_path is not None and request_path.resolve() != expected_request:
        raise GuardError("event verifier request path differs from its derived root receipt")
    return request, claim, claim_path, task, task_path, brief, brief_path


def _process_snapshot(root_pid: int) -> tuple[int, float, dict[int, tuple[int, int]]]:
    page_size = os.sysconf("SC_PAGE_SIZE")
    clock_ticks = os.sysconf("SC_CLK_TCK")
    records: dict[int, tuple[int, int, int, int]] = {}
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            fields = (entry / "stat").read_text(encoding="ascii").split()
            pid = int(fields[0])
            ppid = int(fields[3])
            utime = int(fields[13])
            stime = int(fields[14])
            rss_pages = int(fields[23])
        except (OSError, ValueError, IndexError):
            continue
        records[pid] = (ppid, utime + stime, max(0, rss_pages), int(fields[21]))
    descendants = {root_pid}
    changed = True
    while changed:
        changed = False
        for pid, (ppid, _cpu, _rss, _start) in records.items():
            if ppid in descendants and pid not in descendants:
                descendants.add(pid)
                changed = True
    rss = sum(records[pid][2] * page_size for pid in descendants if pid in records)
    cpu = sum(records[pid][1] for pid in descendants if pid in records) / clock_ticks
    compact = {
        pid: (records[pid][0], records[pid][3])
        for pid in descendants if pid in records
    }
    return rss, cpu, compact


def _namespace_inode(pid: int, name: str) -> int | None:
    try:
        target = os.readlink(f"/proc/{pid}/ns/{name}")
    except OSError:
        return None
    match = re.search(r"\[(\d+)\]$", target)
    return int(match.group(1)) if match else None


def _terminate_sandbox(
    process: subprocess.Popen[bytes],
    process_group: int,
    sandbox_pid: int | None,
    sandbox_start_ticks: int | None,
) -> None:
    """Terminate both the outer launcher and authenticated inner session."""
    if sandbox_pid is not None and sandbox_start_ticks is not None:
        try:
            fields = Path(f"/proc/{sandbox_pid}/stat").read_text(encoding="ascii").split()
            if int(fields[21]) == sandbox_start_ticks:
                inner_group = os.getpgid(sandbox_pid)
                if inner_group != os.getpgrp():
                    os.killpg(inner_group, signal.SIGKILL)
        except (OSError, ValueError, IndexError):
            pass
    try:
        os.killpg(process_group, signal.SIGKILL)
    except ProcessLookupError:
        pass


def _drain_nonblocking(descriptor: int, target: bytearray, limit: int) -> None:
    while len(target) <= limit:
        try:
            chunk = os.read(descriptor, min(65536, limit + 1 - len(target)))
        except BlockingIOError:
            return
        if not chunk:
            return
        target.extend(chunk)


def _decode_inner_frame(data: bytes, output_limit: int) -> tuple[dict[str, Any], dict[str, bytes]]:
    if len(data) < len(FRAME_MAGIC) + 8 or not data.startswith(FRAME_MAGIC):
        raise GuardError("inner result framing is absent or malformed")
    header_size = struct.unpack(">Q", data[len(FRAME_MAGIC):len(FRAME_MAGIC) + 8])[0]
    if header_size > MAX_FRAME_OVERHEAD:
        raise GuardError("inner result header exceeds its bound")
    start = len(FRAME_MAGIC) + 8
    end = start + header_size
    if end > len(data):
        raise GuardError("inner result header is truncated")
    try:
        header = json.loads(data[start:end])
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise GuardError(f"inner result header is malformed: {exc}") from exc
    if not isinstance(header, dict) or header.get("protocol") != "research-first-test-inner-result-v1":
        raise GuardError("inner result protocol differs")
    streams = header.get("streams")
    if not isinstance(streams, list):
        raise GuardError("inner result stream manifest is missing")
    cursor = end
    values: dict[str, bytes] = {}
    total = 0
    for item in streams:
        entry = exact_keys(item, {"role", "bytes", "sha256"}, "inner result stream")
        role = entry["role"]
        size = entry["bytes"]
        claimed = entry["sha256"]
        if not isinstance(role, str) or role in values:
            raise GuardError("inner result stream roles are invalid or duplicated")
        if not isinstance(size, int) or isinstance(size, bool) or size < 0:
            raise GuardError("inner result stream size is invalid")
        if not isinstance(claimed, str) or HEX64.fullmatch(claimed) is None:
            raise GuardError("inner result stream digest is invalid")
        segment = data[cursor:cursor + size]
        if len(segment) != size or digest_bytes(segment) != claimed:
            raise GuardError("inner result stream bytes differ from its manifest")
        values[role] = segment
        cursor += size
        total += size
    if cursor != len(data):
        raise GuardError("inner result contains undeclared trailing bytes")
    if total > output_limit:
        raise GuardError("complete worker output exceeds its bound")
    return header, values


def _parse_bwrap_status(data: bytes) -> tuple[dict[str, Any], int | None]:
    documents = _parse_status_documents(data)
    identity = next((item for item in documents if "child-pid" in item), {})
    exit_code = next(
        (item.get("exit-code") for item in documents if "exit-code" in item), None
    )
    return identity, exit_code if isinstance(exit_code, int) else None


def _execute(
    *,
    contract: dict[str, Any],
    task: dict[str, Any],
    claim_path: Path,
    brief_path: Path,
    task_path: Path,
    identity_sha256: dict[str, str] | None = None,
) -> dict[str, Any]:
    resources = resource_policy(task)
    policy_hash = seccomp_policy_sha256()
    started_at = utc_now()
    started = time.monotonic()
    result_data = bytearray()
    status_data = bytearray()
    stderr_data = bytearray()
    peak_rss = 0
    peak_cpu = 0.0
    resource_observer_samples = 0
    sandbox_pid: int | None = None
    sandbox_start_ticks: int | None = None
    namespace_inodes: dict[str, int | None] = {
        "user": None, "mount": None, "pid": None, "net": None,
        "ipc": None, "uts": None, "cgroup": None,
    }
    outer_namespace_names = {
        "user": "user", "mount": "mnt", "pid": "pid", "net": "net",
        "ipc": "ipc", "uts": "uts", "cgroup": "cgroup",
    }
    outer_namespace_inodes = {
        label: _namespace_inode(os.getpid(), proc_name)
        for label, proc_name in outer_namespace_names.items()
    }
    violations: list[str] = []
    process: subprocess.Popen[bytes] | None = None
    process_group: int | None = None
    command: list[str] = []
    inner_config = {
        "schema_version": 1,
        "contract": contract,
        "outputs": contract["outputs"],
        "resources": resources,
        "seccomp_policy_sha256": policy_hash,
    }
    with tempfile.TemporaryDirectory(prefix="ticket-0119-first-test-") as temporary:
        temp = Path(temporary)
        work = temp / "work"
        work.mkdir()
        empty_shm = temp / "empty-shm"
        empty_shm.mkdir()
        empty_shm.chmod(0o555)
        _copy_sparse_inputs(
            work,
            contract,
            claim_path,
            brief_path,
            task_path,
            identity_sha256,
        )
        contract_read, contract_write = os.pipe()
        result_read, result_write = os.pipe()
        status_read, status_write = os.pipe()
        command = build_bwrap_argv(
            work_root=work,
            empty_shm=empty_shm,
            cpu_affinity=list(resources["cpu_affinity"]),
            output_bytes=int(resources["output_bytes"]),
            contract_fd=contract_read,
            result_fd=result_write,
            status_fd=status_write,
        )
        try:
            process = subprocess.Popen(
                command,
                cwd=ROOT,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
                pass_fds=(contract_read, result_write, status_write),
                start_new_session=True,
            )
            process_group = os.getpgid(process.pid)
        except OSError as exc:
            violations.append(f"sandbox launch failed: {exc}")
            for descriptor in (contract_read, contract_write, result_read, result_write, status_read, status_write):
                try:
                    os.close(descriptor)
                except OSError:
                    pass
        else:
            os.close(contract_read)
            os.close(result_write)
            os.close(status_write)
            encoded_config = canonical_bytes(inner_config)
            try:
                _write_all(contract_write, struct.pack(">Q", len(encoded_config)) + encoded_config)
            except OSError as exc:
                violations.append(f"inner contract delivery failed: {exc}")
            finally:
                os.close(contract_write)
            for descriptor in (result_read, status_read, process.stderr.fileno()):
                os.set_blocking(descriptor, False)
            deadline = started + int(resources["wall_seconds"])
            max_result = int(resources["output_bytes"]) + MAX_FRAME_OVERHEAD
            while process.poll() is None:
                _drain_nonblocking(result_read, result_data, max_result)
                _drain_nonblocking(status_read, status_data, MAX_FRAME_OVERHEAD)
                _drain_nonblocking(process.stderr.fileno(), stderr_data, MAX_FRAME_OVERHEAD)
                if sandbox_pid is None and status_data:
                    try:
                        status_identity, _status_exit = _parse_bwrap_status(bytes(status_data))
                    except GuardError:
                        status_identity = {}
                    child_pid = status_identity.get("child-pid")
                    if isinstance(child_pid, int) and child_pid > 0:
                        sandbox_pid = child_pid
                        try:
                            fields = Path(f"/proc/{sandbox_pid}/stat").read_text(encoding="ascii").split()
                            sandbox_start_ticks = int(fields[21])
                        except (OSError, ValueError, IndexError):
                            sandbox_start_ticks = None
                        namespace_inodes["user"] = _namespace_inode(sandbox_pid, "user")
                try:
                    rss, cpu, tree = _process_snapshot(process.pid)
                except OSError:
                    rss, cpu = 0, 0.0
                else:
                    if process.pid in tree:
                        resource_observer_samples += 1
                peak_rss = max(peak_rss, rss)
                peak_cpu = max(peak_cpu, cpu)
                if rss > int(resources["memory_bytes"]):
                    violations.append("aggregate RSS exceeded the frozen memory ceiling")
                    _terminate_sandbox(
                        process, process_group, sandbox_pid, sandbox_start_ticks
                    )
                    break
                if cpu > int(resources["wall_seconds"]) * len(resources["cpu_affinity"]):
                    violations.append("aggregate CPU time exceeded the frozen ceiling")
                    _terminate_sandbox(
                        process, process_group, sandbox_pid, sandbox_start_ticks
                    )
                    break
                if time.monotonic() >= deadline:
                    violations.append("wall deadline exceeded")
                    _terminate_sandbox(
                        process, process_group, sandbox_pid, sandbox_start_ticks
                    )
                    break
                select.select([], [], [], 0.02)
            try:
                process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                violations.append("sandbox process group did not terminate promptly")
                _terminate_sandbox(
                    process, process_group, sandbox_pid, sandbox_start_ticks
                )
                process.wait(timeout=2)
            _drain_nonblocking(result_read, result_data, max_result)
            _drain_nonblocking(status_read, status_data, MAX_FRAME_OVERHEAD)
            _drain_nonblocking(process.stderr.fileno(), stderr_data, MAX_FRAME_OVERHEAD)
            os.close(result_read)
            os.close(status_read)
            process.stderr.close()

    finished_at = utc_now()
    wall_seconds = time.monotonic() - started
    status_identity: dict[str, Any] = {}
    status_exit: int | None = None
    if status_data:
        try:
            status_identity, status_exit = _parse_bwrap_status(bytes(status_data))
        except GuardError as exc:
            violations.append(str(exc))
    if sandbox_pid is None and isinstance(status_identity.get("child-pid"), int):
        sandbox_pid = status_identity["child-pid"]
    status_map = {
        "mount": "mnt-namespace", "pid": "pid-namespace", "net": "net-namespace",
        "ipc": "ipc-namespace", "uts": "uts-namespace", "cgroup": "cgroup-namespace",
    }
    for label, key in status_map.items():
        value = status_identity.get(key)
        if isinstance(value, int) and value > 0:
            namespace_inodes[label] = value

    header: dict[str, Any] | None = None
    streams: dict[str, bytes] = {}
    try:
        header, streams = _decode_inner_frame(bytes(result_data), int(resources["output_bytes"]))
    except GuardError as exc:
        violations.append(str(exc))
    if process is None:
        return {
            "started_at": started_at, "finished_at": finished_at,
            "outer_pid": os.getpid(), "sandbox_pid": None,
            "sandbox_start_ticks": None, "process_group": None,
            "resolved_argv": contract["argv_template"], "resources": resources,
            "policy_hash": policy_hash, "namespace_inodes": namespace_inodes,
            "exit_code": None, "signal": None, "wall_seconds": wall_seconds,
            "cpu_seconds": peak_cpu, "peak_rss": peak_rss,
            "streams": {}, "worker_output_bytes": 0,
            "forbidden_attempts": "not-observed", "violations": violations,
            "terminal": "LAUNCH_STOP", "stderr": bytes(stderr_data),
            "bwrap_command": command,
        }

    worker_signal = header.get("signal") if header is not None else None
    worker_exit = header.get("exit_code") if header is not None else status_exit
    filter_loaded = bool(header is not None and header.get("filter_loaded") is True)
    if header is not None:
        if header.get("seccomp_policy_sha256") != policy_hash:
            violations.append("inner seccomp policy digest differs")
        if header.get("resolved_argv") is not None:
            resolved_argv = header["resolved_argv"]
        else:
            resolved_argv = contract["argv_template"]
        peak_cpu = max(peak_cpu, float(header.get("cpu_seconds") or 0.0))
        peak_rss = max(peak_rss, int(header.get("maxrss_kib") or 0) * 1024)
    else:
        resolved_argv = contract["argv_template"]
    expected_roles = {item["role"] for item in contract["outputs"]}
    if header is not None and set(streams) != expected_roles | {"__stdout__", "__stderr__"}:
        violations.append("inner stream manifest differs from declared outputs")
    for role in sorted(expected_roles):
        if role not in streams or not streams[role]:
            violations.append(f"declared output {role} is absent or empty")
    if not filter_loaded:
        violations.append("worker seccomp-load acknowledgement is absent")
    if worker_signal == signal.SIGSYS:
        forbidden = "at-least-one"
        violations.append("worker was killed by SIGSYS")
    elif filter_loaded:
        forbidden = "none"
    else:
        forbidden = "not-observed"
    if worker_signal is not None and worker_signal != signal.SIGSYS:
        violations.append(f"worker was killed by signal {worker_signal}")
    if worker_exit != 0:
        violations.append(f"worker exit code is {worker_exit}")
    if process.returncode != 0:
        violations.append(f"sandbox launcher exit code is {process.returncode}")
    if stderr_data:
        violations.append(
            "sandbox launcher emitted stderr "
            f"sha256={digest_bytes(bytes(stderr_data))} bytes={len(stderr_data)}"
        )
    output_total = sum(len(value) for value in streams.values())
    if output_total > int(resources["output_bytes"]):
        violations.append("complete staged output exceeds its frozen ceiling")
    if peak_rss > int(resources["memory_bytes"]):
        violations.append("observed aggregate RSS exceeds its frozen ceiling")
    if peak_cpu > int(resources["wall_seconds"]) * len(resources["cpu_affinity"]):
        violations.append("observed aggregate CPU time exceeds its frozen ceiling")
    if resource_observer_samples < 1:
        violations.append("aggregate process-tree resource observer produced no sample")
    required_namespaces = ("mount", "pid", "net", "ipc", "uts", "cgroup", "user")
    if any(namespace_inodes[name] is None for name in required_namespaces):
        violations.append("one or more namespace observations are absent")
    for name in required_namespaces:
        if (
            namespace_inodes[name] is not None
            and outer_namespace_inodes[name] is not None
            and namespace_inodes[name] == outer_namespace_inodes[name]
        ):
            violations.append(f"sandbox {name} namespace was not unshared")
    terminal = "PASS" if not violations else (
        "VIOLATION" if filter_loaded or worker_signal == signal.SIGSYS else "LAUNCH_STOP"
    )
    return {
        "started_at": started_at, "finished_at": finished_at,
        "outer_pid": os.getpid(), "sandbox_pid": sandbox_pid,
        "sandbox_start_ticks": sandbox_start_ticks, "process_group": process_group,
        "resolved_argv": resolved_argv, "resources": resources,
        "policy_hash": policy_hash, "namespace_inodes": namespace_inodes,
        "exit_code": worker_exit, "signal": worker_signal,
        "wall_seconds": wall_seconds, "cpu_seconds": peak_cpu, "peak_rss": peak_rss,
        "streams": streams, "worker_output_bytes": output_total,
        "forbidden_attempts": forbidden, "violations": sorted(set(violations)),
        "terminal": terminal, "stderr": bytes(stderr_data),
        "bwrap_command": command,
    }


def _normalized_json(data: bytes) -> bool:
    try:
        value = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return False
    return data == canonical_bytes(value) + b"\n"


def _materialize_outputs(
    contract: dict[str, Any], streams: dict[str, bytes]
) -> list[dict[str, Any]]:
    created: list[Path] = []
    writes: list[dict[str, Any]] = []
    try:
        for item in contract["outputs"]:
            role = item["role"]
            data = streams[role]
            path_text, path = repo_path(item["path"], f"output {role}")
            path.parent.mkdir(parents=True, exist_ok=True)
            descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            try:
                _write_all(descriptor, data)
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
            created.append(path)
            writes.append({
                "role": role, "path": path_text, "sha256": digest_bytes(data),
                "bytes": len(data), "materialized": True,
            })
        for directory in {path.parent for path in created}:
            descriptor = os.open(directory, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
            try:
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
        return writes
    except BaseException:
        for path in reversed(created):
            try:
                path.unlink()
            except OSError:
                pass
        raise


def _unmaterialized_writes(
    contract: dict[str, Any], streams: dict[str, bytes]
) -> list[dict[str, Any]]:
    writes: list[dict[str, Any]] = []
    for item in contract["outputs"]:
        data = streams.get(item["role"], b"")
        writes.append({
            "role": item["role"], "path": item["path"],
            "sha256": digest_bytes(data), "bytes": len(data), "materialized": False,
        })
    return writes


def _boot_id() -> str:
    try:
        value = Path("/proc/sys/kernel/random/boot_id").read_text(encoding="ascii").strip()
    except OSError:
        return "not-observed"
    return value or "not-observed"


def build_envelope(
    *,
    outcome: dict[str, Any],
    claim_path: Path,
    claim: dict[str, Any],
    brief_path: Path,
    brief: dict[str, Any],
    task_path: Path,
    task: dict[str, Any],
    contract: dict[str, Any],
    writes: list[dict[str, Any]],
) -> dict[str, Any]:
    streams = outcome["streams"]
    stdout = streams.get("__stdout__", b"")
    stderr = streams.get("__stderr__", outcome.get("stderr", b""))
    namespace_observed = all(value is not None for value in outcome["namespace_inodes"].values())
    filter_observed = outcome["forbidden_attempts"] != "not-observed"
    envelope = {
        "schema_version": 1,
        "protocol": ENVELOPE_PROTOCOL,
        "envelope_id": "",
        "guard_component": file_receipt(GUARD_PATH),
        "identity": {
            "seed_claim": file_receipt(claim_path),
            "claim_id": claim["claim_id"],
            "development_brief": file_receipt(brief_path),
            "brief_id": brief["brief_id"],
            "task_packet": file_receipt(task_path),
            "task_id": task["task_id"],
            "execution_contract_id": contract["contract_id"],
        },
        "launch": {
            "started_at": outcome["started_at"],
            "finished_at": outcome["finished_at"],
            "boot_id": _boot_id(),
            "outer_pid": outcome["outer_pid"],
            "sandbox_pid": outcome["sandbox_pid"],
            "sandbox_start_ticks": outcome["sandbox_start_ticks"],
            "process_group": outcome["process_group"],
            "argv": outcome["resolved_argv"],
            "cwd": "/work",
        },
        "enforced_policy": {
            "wall_seconds": outcome["resources"]["wall_seconds"],
            "cpu_affinity": outcome["resources"]["cpu_affinity"],
            "memory_bytes": outcome["resources"]["memory_bytes"],
            "output_bytes": outcome["resources"]["output_bytes"],
            "process_model": PROCESS_MODEL,
            "network": NETWORK_POLICY if namespace_observed and filter_observed else "not-observed",
            "repository": REPOSITORY_POLICY if namespace_observed else "not-observed",
            "persistent_writes": [item["path"] for item in contract["outputs"]],
            "seccomp_policy_sha256": outcome["policy_hash"],
            "namespace_inodes": outcome["namespace_inodes"],
        },
        "observation": {
            "exit_code": outcome["exit_code"],
            "signal": outcome["signal"],
            "wall_seconds": outcome["wall_seconds"],
            "cpu_seconds": outcome["cpu_seconds"],
            "peak_aggregate_rss_bytes": outcome["peak_rss"],
            "worker_output_bytes": outcome["worker_output_bytes"],
            "writes": writes,
            "stdout": {"sha256": digest_bytes(stdout), "bytes": len(stdout)},
            "stderr": {"sha256": digest_bytes(stderr), "bytes": len(stderr)},
            "forbidden_attempts": outcome["forbidden_attempts"],
            "violations": outcome["violations"],
        },
        "terminal": outcome["terminal"],
    }
    envelope["envelope_id"] = canonical_sha256(
        {key: value for key, value in envelope.items() if key != "envelope_id"}
    )
    return envelope


def _verifier_identity(
    request_path: Path,
    request: dict[str, Any],
    claim_path: Path,
    task_path: Path,
) -> dict[str, Any]:
    event = request["event"]
    return {
        "verifier_request": file_receipt(request_path),
        "verifier_contract_id": request["verifier_contract_id"],
        "seed_claim": file_receipt(claim_path),
        "claim_id": request["claim_id"],
        "task_packet": file_receipt(task_path),
        "task_id": request["task_id"],
        "event_id": event["event_id"],
        "event_core_sha256": event["event_core_sha256"],
        "subject_contract_id": event["subject_contract_id"],
        "model_contract_id": event["model_contract_id"],
        "scope_contract_id": event["scope_contract_id"],
        "event_artifact": event["artifact"],
    }


def build_verifier_envelope(
    *,
    outcome: dict[str, Any],
    request_path: Path,
    request: dict[str, Any],
    claim_path: Path,
    task_path: Path,
) -> dict[str, Any]:
    streams = outcome["streams"]
    stdout = streams.get("__stdout__", b"")
    stderr = streams.get("__stderr__", outcome.get("stderr", b""))
    try:
        normalized_value = json.loads(stdout.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        normalized_value = None
    matches = (
        normalized_value == request["expected_normalized_result"]
        and stdout == canonical_bytes(request["expected_normalized_result"]) + b"\n"
    )
    namespace_observed = all(
        value is not None for value in outcome["namespace_inodes"].values()
    )
    filter_observed = outcome["forbidden_attempts"] != "not-observed"
    envelope = {
        "schema_version": 1,
        "protocol": VERIFIER_ENVELOPE_PROTOCOL,
        "envelope_id": "",
        "guard_component": file_receipt(GUARD_PATH),
        "identity": _verifier_identity(
            request_path, request, claim_path, task_path
        ),
        "launch": {
            "started_at": outcome["started_at"],
            "finished_at": outcome["finished_at"],
            "boot_id": _boot_id(),
            "outer_pid": outcome["outer_pid"],
            "sandbox_pid": outcome["sandbox_pid"],
            "sandbox_start_ticks": outcome["sandbox_start_ticks"],
            "process_group": outcome["process_group"],
            "argv": outcome["resolved_argv"],
            "cwd": "/work",
        },
        "enforced_policy": {
            "wall_seconds": outcome["resources"]["wall_seconds"],
            "cpu_affinity": outcome["resources"]["cpu_affinity"],
            "memory_bytes": outcome["resources"]["memory_bytes"],
            "output_bytes": outcome["resources"]["output_bytes"],
            "process_model": PROCESS_MODEL,
            "network": NETWORK_POLICY if namespace_observed and filter_observed else "not-observed",
            "repository": REPOSITORY_POLICY if namespace_observed else "not-observed",
            "persistent_writes": [],
            "seccomp_policy_sha256": outcome["policy_hash"],
            "namespace_inodes": outcome["namespace_inodes"],
        },
        "observation": {
            "exit_code": outcome["exit_code"],
            "signal": outcome["signal"],
            "wall_seconds": outcome["wall_seconds"],
            "cpu_seconds": outcome["cpu_seconds"],
            "peak_aggregate_rss_bytes": outcome["peak_rss"],
            "worker_output_bytes": outcome["worker_output_bytes"],
            "writes": [],
            "stdout": {"sha256": digest_bytes(stdout), "bytes": len(stdout)},
            "stderr": {"sha256": digest_bytes(stderr), "bytes": len(stderr)},
            "forbidden_attempts": outcome["forbidden_attempts"],
            "violations": outcome["violations"],
        },
        "normalized_result": {
            "sha256": digest_bytes(stdout),
            "bytes": len(stdout),
            "value": normalized_value,
            "matches_expected": matches,
        },
        "terminal": outcome["terminal"],
    }
    envelope["envelope_id"] = canonical_sha256(
        {key: value for key, value in envelope.items() if key != "envelope_id"}
    )
    return envelope


def validate_verifier_envelope(
    value: Any,
    *,
    request_path: Path,
    request: dict[str, Any],
    claim_path: Path,
    task_path: Path,
) -> dict[str, Any]:
    envelope = exact_keys(
        value,
        {
            "schema_version", "protocol", "envelope_id", "guard_component",
            "identity", "launch", "enforced_policy", "observation",
            "normalized_result", "terminal",
        },
        "event verifier execution envelope",
    )
    if envelope["schema_version"] != 1 or envelope["protocol"] != VERIFIER_ENVELOPE_PROTOCOL:
        raise GuardError("event verifier envelope version/protocol differs")
    if envelope["envelope_id"] != canonical_sha256(
        {key: item for key, item in envelope.items() if key != "envelope_id"}
    ):
        raise GuardError("event verifier envelope_id differs")
    receipt(envelope["guard_component"], "event verifier envelope guard", authenticate=True)
    if envelope["guard_component"] != request["guard_component"]:
        raise GuardError("event verifier envelope guard differs from its request")
    expected_identity = _verifier_identity(
        request_path, request, claim_path, task_path
    )
    if envelope["identity"] != expected_identity:
        raise GuardError("event verifier envelope identity differs from its request")
    for key in ("verifier_request", "seed_claim", "task_packet", "event_artifact"):
        receipt(
            envelope["identity"][key],
            f"event verifier envelope identity {key}",
            authenticate=True,
        )
    launch = exact_keys(
        envelope["launch"],
        {
            "started_at", "finished_at", "boot_id", "outer_pid", "sandbox_pid",
            "sandbox_start_ticks", "process_group", "argv", "cwd",
        },
        "event verifier envelope launch",
    )
    if (
        launch["argv"] != request["argv_template"]
        or launch["cwd"] != "/work"
        or not isinstance(launch["outer_pid"], int)
        or isinstance(launch["outer_pid"], bool)
        or launch["outer_pid"] < 1
    ):
        raise GuardError("event verifier envelope launch differs from its request")
    for key in ("sandbox_pid", "sandbox_start_ticks", "process_group"):
        item = launch[key]
        if item is not None and (
            not isinstance(item, int) or isinstance(item, bool) or item < 1
        ):
            raise GuardError(f"event verifier envelope launch {key} is invalid")
    policy = exact_keys(
        envelope["enforced_policy"],
        {
            "wall_seconds", "cpu_affinity", "memory_bytes", "output_bytes",
            "process_model", "network", "repository", "persistent_writes",
            "seccomp_policy_sha256", "namespace_inodes",
        },
        "event verifier envelope policy",
    )
    if policy["persistent_writes"] != [] or policy["process_model"] != PROCESS_MODEL:
        raise GuardError("event verifier envelope authorizes a persistent worker write")
    if (
        not isinstance(policy["wall_seconds"], int)
        or not 1 <= policy["wall_seconds"] <= MAX_WALL_SECONDS
        or not isinstance(policy["cpu_affinity"], list)
        or not 1 <= len(policy["cpu_affinity"]) <= MAX_CPU_CORES
        or len(set(policy["cpu_affinity"])) != len(policy["cpu_affinity"])
        or any(
            not isinstance(cpu, int) or isinstance(cpu, bool) or cpu < 0
            for cpu in policy["cpu_affinity"]
        )
        or not isinstance(policy["memory_bytes"], int)
        or not 1 <= policy["memory_bytes"] <= MAX_MEMORY_BYTES
        or not isinstance(policy["output_bytes"], int)
        or not 1 <= policy["output_bytes"] <= MAX_OUTPUT_BYTES
        or policy["network"] not in {NETWORK_POLICY, "not-observed"}
        or policy["repository"] not in {REPOSITORY_POLICY, "not-observed"}
        or policy["seccomp_policy_sha256"] != seccomp_policy_sha256()
    ):
        raise GuardError("event verifier envelope resource policy is invalid")
    namespace = exact_keys(
        policy["namespace_inodes"],
        {"user", "mount", "pid", "net", "ipc", "uts", "cgroup"},
        "event verifier namespace observations",
    )
    if any(
        item is not None
        and (not isinstance(item, int) or isinstance(item, bool) or item < 1)
        for item in namespace.values()
    ):
        raise GuardError("event verifier namespace observation is invalid")
    expected_policy = resource_policy({"budget": request["budget"]})
    for key in ("wall_seconds", "cpu_affinity", "memory_bytes", "output_bytes"):
        if policy[key] != expected_policy[key]:
            raise GuardError(f"event verifier envelope {key} differs from its request")
    observation = exact_keys(
        envelope["observation"],
        {
            "exit_code", "signal", "wall_seconds", "cpu_seconds",
            "peak_aggregate_rss_bytes", "worker_output_bytes", "writes",
            "stdout", "stderr", "forbidden_attempts", "violations",
        },
        "event verifier observation",
    )
    if observation["writes"] != []:
        raise GuardError("event verifier envelope contains a worker write")
    if observation["exit_code"] is not None and (
        not isinstance(observation["exit_code"], int)
        or isinstance(observation["exit_code"], bool)
        or not 0 <= observation["exit_code"] <= 255
    ):
        raise GuardError("event verifier exit-code observation is invalid")
    if observation["signal"] is not None and (
        not isinstance(observation["signal"], int)
        or isinstance(observation["signal"], bool)
        or observation["signal"] < 1
    ):
        raise GuardError("event verifier signal observation is invalid")
    for key in ("wall_seconds", "cpu_seconds"):
        if (
            not isinstance(observation[key], (int, float))
            or isinstance(observation[key], bool)
            or observation[key] < 0
        ):
            raise GuardError(f"event verifier {key} observation is invalid")
    for key in ("peak_aggregate_rss_bytes", "worker_output_bytes"):
        if (
            not isinstance(observation[key], int)
            or isinstance(observation[key], bool)
            or observation[key] < 0
        ):
            raise GuardError(f"event verifier {key} observation is invalid")
    for key in ("stdout", "stderr"):
        stream = exact_keys(observation[key], {"sha256", "bytes"}, f"verifier {key}")
        if not isinstance(stream["sha256"], str) or HEX64.fullmatch(stream["sha256"]) is None:
            raise GuardError(f"event verifier {key} digest is invalid")
        if not isinstance(stream["bytes"], int) or stream["bytes"] < 0:
            raise GuardError(f"event verifier {key} size is invalid")
    if observation["worker_output_bytes"] != (
        observation["stdout"]["bytes"] + observation["stderr"]["bytes"]
    ):
        raise GuardError("event verifier complete output total differs")
    if observation["worker_output_bytes"] > policy["output_bytes"]:
        raise GuardError("event verifier staged output exceeds its policy")
    if observation["forbidden_attempts"] not in {
        "none", "at-least-one", "not-observed"
    }:
        raise GuardError("event verifier forbidden-attempt observation is invalid")
    if (
        not isinstance(observation["violations"], list)
        or any(not isinstance(item, str) or not item for item in observation["violations"])
        or len(set(observation["violations"])) != len(observation["violations"])
    ):
        raise GuardError("event verifier violation observations are invalid")
    namespace_observed = all(item is not None for item in namespace.values())
    filter_observed = observation["forbidden_attempts"] != "not-observed"
    if policy["network"] != (
        NETWORK_POLICY if namespace_observed and filter_observed else "not-observed"
    ) or policy["repository"] != (
        REPOSITORY_POLICY if namespace_observed else "not-observed"
    ):
        raise GuardError("event verifier envelope claims unobserved controls")
    normalized = exact_keys(
        envelope["normalized_result"],
        {"sha256", "bytes", "value", "matches_expected"},
        "event verifier normalized result",
    )
    if (
        normalized["sha256"] != observation["stdout"]["sha256"]
        or normalized["bytes"] != observation["stdout"]["bytes"]
        or not isinstance(normalized["matches_expected"], bool)
    ):
        raise GuardError("event verifier normalized result differs from stdout")
    terminal = envelope["terminal"]
    if terminal not in {"PASS", "VIOLATION", "LAUNCH_STOP"}:
        raise GuardError("event verifier envelope terminal is invalid")
    if terminal == "PASS":
        expected_bytes = canonical_bytes(request["expected_normalized_result"]) + b"\n"
        if (
            normalized["matches_expected"] is not True
            or normalized["value"] != request["expected_normalized_result"]
            or normalized["sha256"] != digest_bytes(expected_bytes)
            or normalized["bytes"] != len(expected_bytes)
            or observation["stderr"]["bytes"] != 0
            or observation["exit_code"] != 0
            or observation["signal"] is not None
            or observation["violations"]
            or observation["forbidden_attempts"] != "none"
            or policy["network"] != NETWORK_POLICY
            or policy["repository"] != REPOSITORY_POLICY
            or any(
                not isinstance(value, int) or isinstance(value, bool) or value < 1
                for value in namespace.values()
            )
            or any(
                not isinstance(launch[key], int)
                or isinstance(launch[key], bool)
                or launch[key] < 1
                for key in ("sandbox_pid", "sandbox_start_ticks", "process_group")
            )
            or observation["wall_seconds"] > policy["wall_seconds"]
            or observation["cpu_seconds"]
            > policy["wall_seconds"] * len(policy["cpu_affinity"])
            or observation["peak_aggregate_rss_bytes"] > policy["memory_bytes"]
            or observation["worker_output_bytes"] > policy["output_bytes"]
        ):
            raise GuardError("PASS event verifier envelope lacks a clean exact replay")
    elif normalized["matches_expected"] is True:
        # A matching staged string is not admitted when execution authority
        # failed.  Retain the observation, but never call it verified.
        pass
    return envelope


def validate_envelope(
    value: Any,
    *,
    expected_identity: dict[str, Any] | None = None,
    authenticate_outputs: bool = True,
) -> dict[str, Any]:
    envelope = exact_keys(
        value,
        {
            "schema_version", "protocol", "envelope_id", "guard_component",
            "identity", "launch", "enforced_policy", "observation", "terminal",
        },
        "execution envelope",
    )
    if envelope["schema_version"] != 1 or envelope["protocol"] != ENVELOPE_PROTOCOL:
        raise GuardError("execution envelope version/protocol differs")
    if envelope["envelope_id"] != canonical_sha256(
        {key: item for key, item in envelope.items() if key != "envelope_id"}
    ):
        raise GuardError("execution envelope_id differs")
    receipt(envelope["guard_component"], "execution envelope guard", authenticate=True)
    if envelope["guard_component"] != file_receipt(GUARD_PATH):
        raise GuardError("execution envelope guard is not the current pinned component")
    identity = exact_keys(
        envelope["identity"],
        {
            "seed_claim", "claim_id", "development_brief", "brief_id",
            "task_packet", "task_id", "execution_contract_id",
        },
        "execution envelope identity",
    )
    for key in ("seed_claim", "development_brief", "task_packet"):
        receipt(identity[key], f"execution envelope {key}", authenticate=True)
    if expected_identity is not None and identity != expected_identity:
        raise GuardError("existing execution envelope identity differs from exact retry")
    launch = exact_keys(
        envelope["launch"],
        {
            "started_at", "finished_at", "boot_id", "outer_pid", "sandbox_pid",
            "sandbox_start_ticks", "process_group", "argv", "cwd",
        },
        "execution envelope launch",
    )
    if (
        not isinstance(launch["argv"], list)
        or not launch["argv"]
        or any(not isinstance(item, str) or not item for item in launch["argv"])
        or launch["cwd"] != "/work"
        or not isinstance(launch["outer_pid"], int)
        or isinstance(launch["outer_pid"], bool)
        or launch["outer_pid"] < 1
    ):
        raise GuardError("execution envelope launch observation is invalid")
    for key in ("sandbox_pid", "sandbox_start_ticks", "process_group"):
        item = launch[key]
        if item is not None and (
            not isinstance(item, int) or isinstance(item, bool) or item < 1
        ):
            raise GuardError(f"execution envelope launch {key} is invalid")
    policy = exact_keys(
        envelope["enforced_policy"],
        {
            "wall_seconds", "cpu_affinity", "memory_bytes", "output_bytes",
            "process_model", "network", "repository", "persistent_writes",
            "seccomp_policy_sha256", "namespace_inodes",
        },
        "execution envelope policy",
    )
    if (
        not isinstance(policy["wall_seconds"], int)
        or not 1 <= policy["wall_seconds"] <= MAX_WALL_SECONDS
        or not isinstance(policy["cpu_affinity"], list)
        or not 1 <= len(policy["cpu_affinity"]) <= MAX_CPU_CORES
        or len(set(policy["cpu_affinity"])) != len(policy["cpu_affinity"])
        or any(
            not isinstance(cpu, int) or isinstance(cpu, bool) or cpu < 0
            for cpu in policy["cpu_affinity"]
        )
        or not isinstance(policy["memory_bytes"], int)
        or not 1 <= policy["memory_bytes"] <= MAX_MEMORY_BYTES
        or not isinstance(policy["output_bytes"], int)
        or not 1 <= policy["output_bytes"] <= MAX_OUTPUT_BYTES
        or policy["process_model"] != PROCESS_MODEL
        or not isinstance(policy["persistent_writes"], list)
        or policy["network"] not in {NETWORK_POLICY, "not-observed"}
        or policy["repository"] not in {REPOSITORY_POLICY, "not-observed"}
        or policy["seccomp_policy_sha256"] != seccomp_policy_sha256()
    ):
        raise GuardError("execution envelope enforced policy is invalid")
    namespace = exact_keys(
        policy["namespace_inodes"],
        {"user", "mount", "pid", "net", "ipc", "uts", "cgroup"},
        "execution envelope namespace observations",
    )
    if any(
        item is not None
        and (not isinstance(item, int) or isinstance(item, bool) or item < 1)
        for item in namespace.values()
    ):
        raise GuardError("execution envelope namespace observation is invalid")
    observation = exact_keys(
        envelope["observation"],
        {
            "exit_code", "signal", "wall_seconds", "cpu_seconds",
            "peak_aggregate_rss_bytes", "worker_output_bytes", "writes",
            "stdout", "stderr", "forbidden_attempts", "violations",
        },
        "execution envelope observation",
    )
    if observation["exit_code"] is not None and (
        not isinstance(observation["exit_code"], int)
        or isinstance(observation["exit_code"], bool)
        or not 0 <= observation["exit_code"] <= 255
    ):
        raise GuardError("execution envelope exit-code observation is invalid")
    if observation["signal"] is not None and (
        not isinstance(observation["signal"], int)
        or isinstance(observation["signal"], bool)
        or observation["signal"] < 1
    ):
        raise GuardError("execution envelope signal observation is invalid")
    for key in ("wall_seconds", "cpu_seconds"):
        if (
            not isinstance(observation[key], (int, float))
            or isinstance(observation[key], bool)
            or observation[key] < 0
        ):
            raise GuardError(f"execution envelope {key} observation is invalid")
    for key in ("peak_aggregate_rss_bytes", "worker_output_bytes"):
        if (
            not isinstance(observation[key], int)
            or isinstance(observation[key], bool)
            or observation[key] < 0
        ):
            raise GuardError(f"execution envelope {key} observation is invalid")
    for key in ("stdout", "stderr"):
        stream = exact_keys(observation[key], {"sha256", "bytes"}, f"observation {key}")
        if not isinstance(stream["sha256"], str) or HEX64.fullmatch(stream["sha256"]) is None:
            raise GuardError(f"observation {key} digest is invalid")
        if not isinstance(stream["bytes"], int) or stream["bytes"] < 0:
            raise GuardError(f"observation {key} size is invalid")
    writes = observation["writes"]
    if not isinstance(writes, list) or not writes:
        raise GuardError("execution envelope write manifest is empty")
    materialized = []
    output_sum = observation["stdout"]["bytes"] + observation["stderr"]["bytes"]
    for index, item in enumerate(writes):
        entry = exact_keys(
            item, {"role", "path", "sha256", "bytes", "materialized"},
            f"execution envelope write {index}",
        )
        path_text, path = repo_path(entry["path"], f"execution envelope write {index}.path")
        if not isinstance(entry["role"], str) or SAFE_ROLE.fullmatch(entry["role"]) is None:
            raise GuardError("execution envelope write role is invalid")
        if not isinstance(entry["bytes"], int) or entry["bytes"] < 0:
            raise GuardError("execution envelope write size is invalid")
        if not isinstance(entry["sha256"], str) or HEX64.fullmatch(entry["sha256"]) is None:
            raise GuardError("execution envelope write digest is invalid")
        if not isinstance(entry["materialized"], bool):
            raise GuardError("execution envelope materialized flag is invalid")
        if entry["materialized"] and authenticate_outputs:
            if not path.is_file() or path.stat().st_size != entry["bytes"] or digest(path) != entry["sha256"]:
                raise GuardError(f"materialized output differs from envelope: {path_text}")
        materialized.append(entry["materialized"])
        output_sum += entry["bytes"]
    if len({(item["role"], item["path"]) for item in writes}) != len(writes):
        raise GuardError("execution envelope write manifest contains duplicates")
    if observation["worker_output_bytes"] != output_sum:
        raise GuardError("execution envelope complete output total differs")
    if observation["worker_output_bytes"] > policy["output_bytes"]:
        raise GuardError("execution envelope staged output exceeds its policy")
    if observation["forbidden_attempts"] not in {
        "none", "at-least-one", "not-observed"
    }:
        raise GuardError("execution envelope forbidden-attempt observation is invalid")
    if (
        not isinstance(observation["violations"], list)
        or any(not isinstance(item, str) or not item for item in observation["violations"])
        or len(set(observation["violations"])) != len(observation["violations"])
    ):
        raise GuardError("execution envelope violation observations are invalid")
    namespace_observed = all(item is not None for item in namespace.values())
    filter_observed = observation["forbidden_attempts"] != "not-observed"
    if policy["network"] != (
        NETWORK_POLICY if namespace_observed and filter_observed else "not-observed"
    ) or policy["repository"] != (
        REPOSITORY_POLICY if namespace_observed else "not-observed"
    ):
        raise GuardError("execution envelope claims unobserved controls")
    terminal = envelope["terminal"]
    if terminal not in {"PASS", "VIOLATION", "LAUNCH_STOP"}:
        raise GuardError("execution envelope terminal is invalid")
    if terminal == "PASS":
        if (
            not all(materialized)
            or observation["exit_code"] != 0
            or observation["signal"] is not None
            or observation["violations"]
            or observation["forbidden_attempts"] != "none"
            or any(
                not isinstance(launch[key], int)
                or isinstance(launch[key], bool)
                or launch[key] < 1
                for key in ("sandbox_pid", "sandbox_start_ticks", "process_group")
            )
            or any(
                not isinstance(item, int) or isinstance(item, bool) or item < 1
                for item in namespace.values()
            )
        ):
            raise GuardError("PASS envelope does not prove a clean materialization")
        if policy["network"] != NETWORK_POLICY or policy["repository"] != REPOSITORY_POLICY:
            raise GuardError("PASS envelope lacks observed namespace/filter policy")
        if (
            observation["wall_seconds"] > policy["wall_seconds"]
            or observation["cpu_seconds"]
            > policy["wall_seconds"] * len(policy["cpu_affinity"])
            or observation["peak_aggregate_rss_bytes"] > policy["memory_bytes"]
            or observation["worker_output_bytes"] > policy["output_bytes"]
        ):
            raise GuardError("PASS envelope exceeds an enforced resource ceiling")
    elif any(materialized):
        raise GuardError("non-PASS envelope materialized mathematical output")
    return envelope


def validate_first_envelope_contract(
    envelope: dict[str, Any], contract: dict[str, Any], task: dict[str, Any]
) -> None:
    """Bind a validated envelope to the exact task execution fields."""
    launch_argv = envelope["launch"]["argv"]
    template = contract["argv_template"]
    if len(launch_argv) != len(template):
        raise GuardError("execution envelope argv length differs from its contract")
    placeholder = re.compile(r"^\{output_fd:([a-z][a-z0-9_]{0,63})\}$")
    for expected, actual in zip(template, launch_argv, strict=True):
        if placeholder.fullmatch(expected):
            if re.fullmatch(r"[0-9]+", actual) is None:
                raise GuardError("execution envelope output FD was not resolved")
        elif expected != actual:
            raise GuardError("execution envelope argv differs from its contract")
    expected_policy = resource_policy(task)
    policy = envelope["enforced_policy"]
    for key in ("wall_seconds", "cpu_affinity", "memory_bytes", "output_bytes"):
        if policy[key] != expected_policy[key]:
            raise GuardError(f"execution envelope {key} differs from its task")
    expected_paths = [item["path"] for item in contract["outputs"]]
    if policy["persistent_writes"] != expected_paths:
        raise GuardError("execution envelope persistent writes differ from its task")
    manifest = envelope["observation"]["writes"]
    if [(item["role"], item["path"]) for item in manifest] != [
        (item["role"], item["path"]) for item in contract["outputs"]
    ]:
        raise GuardError("execution envelope write manifest differs from its task")
    if envelope["terminal"] == "PASS":
        normalized_role = contract["normalized_result_role"]
        normalized_path = next(
            item["path"] for item in contract["outputs"]
            if item["role"] == normalized_role
        )
        _path_text, path = repo_path(normalized_path, "normalized first-test output")
        if not _normalized_json(path.read_bytes()):
            raise GuardError("execution envelope normalized output is not canonical JSON")


def _derived_envelope_path(task: dict[str, Any]) -> Path:
    run_id = task.get("run_id")
    task_id = task.get("task_id")
    if not isinstance(run_id, str) or not isinstance(task_id, str):
        raise GuardError("task identity is missing")
    if SAFE_ID.fullmatch(run_id) is None or SAFE_ID.fullmatch(task_id) is None:
        raise GuardError("task identity is not safe for a root receipt path")
    return ROOT / "runs" / "agents" / run_id / "root-receipts" / f"{task_id}.execution-envelope.json"


def _write_envelope_once(path: Path, value: dict[str, Any]) -> None:
    encoded = json.dumps(value, indent=2, sort_keys=True) + "\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with path.open("x", encoding="utf-8") as handle:
            handle.write(encoded)
            handle.flush()
            os.fsync(handle.fileno())
    except FileExistsError as exc:
        if path.read_text(encoding="utf-8") != encoded:
            raise GuardError("immutable execution envelope appeared with other bytes") from exc
    descriptor = os.open(path.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


@contextmanager
def _root_execution_lock(target: Path):
    """Serialize exact retries without exposing a worker-visible lock file."""
    lock_root = Path(tempfile.gettempdir()) / f"erdos-first-test-guard-{os.getuid()}"
    lock_root.mkdir(mode=0o700, parents=True, exist_ok=True)
    try:
        lock_root.chmod(0o700)
    except OSError:
        pass
    lock_name = hashlib.sha256(str(target.resolve()).encode("utf-8")).hexdigest()
    lock_path = lock_root / f"{lock_name}.lock"
    descriptor = os.open(lock_path, os.O_RDWR | os.O_CREAT, 0o600)
    handle = os.fdopen(descriptor, "r+")
    try:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        yield
    finally:
        fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
        handle.close()


def _preflight(args: argparse.Namespace) -> tuple[
    Path, dict[str, Any], Path, dict[str, Any], Path, dict[str, Any], dict[str, Any], Path
]:
    claim_path = argument_path(args.claim, "claim")
    brief_path = argument_path(args.brief, "development brief")
    task_path = argument_path(args.task, "task packet")
    for path, claimed, label in (
        (claim_path, args.claim_sha256, "claim"),
        (brief_path, args.brief_sha256, "development brief"),
        (task_path, args.task_sha256, "task packet"),
    ):
        if not isinstance(claimed, str) or HEX64.fullmatch(claimed) is None:
            raise GuardError(f"{label} CLI digest is invalid")
        if not path.is_file() or digest(path) != claimed:
            raise GuardError(f"{label} CLI digest does not authenticate its file")
    claim = load_json(claim_path, "seed claim")
    brief = load_json(brief_path, "development brief")
    task = load_json(task_path, "task packet")
    try:
        campaign.validate_brief(
            brief, brief_path=brief_path, task_packet=task, authenticate=True
        )
    except Exception as exc:
        raise GuardError(f"campaign brief/task validation failed: {exc}") from exc
    contract = validate_execution_contract(task, authenticate=True)
    if claim.get("development_brief") != file_receipt(brief_path):
        raise GuardError("seed claim does not bind the supplied development brief")
    if claim.get("task_packet") != file_receipt(task_path):
        raise GuardError("seed claim does not bind the supplied task packet")
    validation = claim.get("first_test_validation")
    if not isinstance(validation, dict):
        raise GuardError("seed claim lacks first-test validation")
    if validation.get("execution_contract_id") != contract["contract_id"]:
        raise GuardError("seed claim does not bind the execution contract")
    if validation.get("guard_component") != contract["guard_component"]:
        raise GuardError("seed claim does not bind the execution guard")

    identity = claim.get("seed")
    if not isinstance(identity, dict):
        raise GuardError("seed claim identity is missing")
    campaign_id = identity.get("campaign_id")
    seed_id = identity.get("seed_id")
    _seed_path_text, seed_path = receipt(identity.get("seed_batch"), "claimed seed batch")
    if not isinstance(campaign_id, str) or not isinstance(seed_id, str):
        raise GuardError("seed claim composite identity is invalid")
    try:
        generator.validate_seed_claim(
            claim_path,
            campaign_id=campaign_id,
            seed_id=seed_id,
            seed_path=seed_path,
        )
        service_dir = generator.service_directory(Path(args.service_dir))
        _auth_path, authorization = generator.active_standing_authorization(service_dir)
        accounting = generator.validate_accounting_chain(service_dir, authorization)
        inventory = generator.seed_inventory(
            service_dir, authorization=authorization, accounting=accounting
        )
    except Exception as exc:
        raise GuardError(f"current seed/service authentication failed: {exc}") from exc
    matches = [
        item for item in inventory
        if item.get("campaign_id") == campaign_id
        and item.get("seed_id") == seed_id
        and item.get("seed_batch") == file_receipt(seed_path)
    ]
    if len(matches) != 1 or matches[0].get("state") != "investigating":
        raise GuardError("guard run requires exactly one current investigating seed")
    if matches[0].get("claim") != file_receipt(claim_path) or matches[0].get("feedback") is not None:
        raise GuardError("investigating inventory does not bind the exact unreconciled claim")

    envelope_path = argument_path(args.envelope, "execution envelope")
    expected_envelope = _derived_envelope_path(task).resolve()
    if envelope_path != expected_envelope:
        raise GuardError("execution envelope path differs from its derived root receipt")
    run_root = (ROOT / "runs" / "agents" / task["run_id"]).resolve()
    try:
        envelope_path.relative_to(run_root)
    except ValueError as exc:
        raise GuardError("execution envelope is outside its run") from exc
    worker_paths = {
        *(task.get("ownership") or {}).get("read_paths", []),
        *(task.get("ownership") or {}).get("write_paths", []),
        *task.get("deliverables", []),
    }
    envelope_relative = envelope_path.relative_to(ROOT).as_posix()
    if envelope_relative in worker_paths:
        raise GuardError("root execution envelope is worker-owned or worker-visible")
    return claim_path, claim, brief_path, brief, task_path, task, contract, envelope_path


def command_run(args: argparse.Namespace) -> int:
    initial = _preflight(args)
    envelope_path = initial[-1]
    with _root_execution_lock(envelope_path):
        # State and immutable identities are reauthenticated after waiting.
        return _command_run_locked(args)


def _command_run_locked(args: argparse.Namespace) -> int:
    (
        claim_path, claim, brief_path, brief, task_path, task, contract, envelope_path
    ) = _preflight(args)
    expected_identity = {
        "seed_claim": file_receipt(claim_path),
        "claim_id": claim["claim_id"],
        "development_brief": file_receipt(brief_path),
        "brief_id": brief["brief_id"],
        "task_packet": file_receipt(task_path),
        "task_id": task["task_id"],
        "execution_contract_id": contract["contract_id"],
    }
    if envelope_path.exists():
        existing = validate_envelope(
            load_json(envelope_path, "existing execution envelope"),
            expected_identity=expected_identity,
            authenticate_outputs=True,
        )
        validate_first_envelope_contract(existing, contract, task)
        print(json.dumps(existing, indent=2, sort_keys=True))
        return 0 if existing["terminal"] == "PASS" else 2
    for item in contract["outputs"]:
        _text, path = repo_path(item["path"], f"output {item['role']}")
        if path.exists():
            raise GuardError(f"first-test output already exists without an envelope: {item['path']}")

    capability = capability_report("network")
    if capability["terminal"] != "PASS":
        resources = resource_policy(task)
        now_value = utc_now()
        outcome = {
            "started_at": now_value, "finished_at": now_value,
            "outer_pid": os.getpid(), "sandbox_pid": None,
            "sandbox_start_ticks": None, "process_group": None,
            "resolved_argv": contract["argv_template"], "resources": resources,
            "policy_hash": seccomp_policy_sha256(),
            "namespace_inodes": {key: None for key in ("user", "mount", "pid", "net", "ipc", "uts", "cgroup")},
            "exit_code": None, "signal": None, "wall_seconds": 0.0,
            "cpu_seconds": 0.0, "peak_rss": 0, "streams": {},
            "worker_output_bytes": 0, "forbidden_attempts": "not-observed",
            "violations": ["guard capability check stopped: " + json.dumps(capability, sort_keys=True)],
            "terminal": "LAUNCH_STOP", "stderr": b"",
        }
    else:
        outcome = _execute(
            contract=contract,
            task=task,
            claim_path=claim_path,
            brief_path=brief_path,
            task_path=task_path,
            identity_sha256={
                "claim.json": args.claim_sha256,
                "brief.json": args.brief_sha256,
                "task.json": args.task_sha256,
            },
        )
    # The namespace received the CLI-authenticated identity files and exact
    # execution inputs.  Reauthenticate the complete current claim/service
    # state and all frozen inputs before any staged byte is materialized.
    _preflight(args)
    if outcome["terminal"] == "PASS":
        normalized = outcome["streams"].get(contract["normalized_result_role"], b"")
        if not _normalized_json(normalized):
            outcome["terminal"] = "VIOLATION"
            outcome["violations"].append(
                "normalized_result_role is not canonical JSON plus one newline"
            )
    if outcome["terminal"] == "PASS":
        try:
            writes = _materialize_outputs(contract, outcome["streams"])
        except BaseException as exc:
            outcome["terminal"] = "VIOLATION"
            outcome["violations"].append(f"root output materialization failed: {exc}")
            writes = _unmaterialized_writes(contract, outcome["streams"])
    else:
        writes = _unmaterialized_writes(contract, outcome["streams"])
    envelope = build_envelope(
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
    validate_envelope(envelope, expected_identity=expected_identity, authenticate_outputs=True)
    validate_first_envelope_contract(envelope, contract, task)
    _write_envelope_once(envelope_path, envelope)
    print(json.dumps(envelope, indent=2, sort_keys=True))
    return 0 if envelope["terminal"] == "PASS" else 2


def _derived_verifier_envelope_path(
    task: dict[str, Any], event_id: str
) -> Path:
    run_id = task.get("run_id")
    if (
        not isinstance(run_id, str)
        or SAFE_ID.fullmatch(run_id) is None
        or HEX64.fullmatch(event_id) is None
    ):
        raise GuardError("verifier run/event identity is unsafe")
    return (
        ROOT / "runs" / "agents" / run_id / "root-receipts"
        / f"{event_id}.verification-envelope.json"
    ).resolve()


def command_verify(args: argparse.Namespace) -> int:
    request_path = argument_path(args.request, "event verifier request")
    if (
        not request_path.is_file()
        or not isinstance(args.request_sha256, str)
        or HEX64.fullmatch(args.request_sha256) is None
        or digest(request_path) != args.request_sha256
    ):
        raise GuardError("event verifier request CLI digest does not authenticate its file")
    request = load_json(request_path, "event verifier request")
    validated = validate_verifier_request(
        request, service_dir_value=args.service_dir, request_path=request_path
    )
    task = validated[3]
    event_id = request["event"]["event_id"]
    target = _derived_verifier_envelope_path(task, event_id)
    with _root_execution_lock(target):
        # Reauthenticate the current claim and request after waiting.
        return _command_verify_locked(args)


def _command_verify_locked(args: argparse.Namespace) -> int:
    request_path = argument_path(args.request, "event verifier request")
    if (
        not isinstance(args.request_sha256, str)
        or HEX64.fullmatch(args.request_sha256) is None
        or not request_path.is_file()
        or digest(request_path) != args.request_sha256
    ):
        raise GuardError("event verifier request CLI digest does not authenticate its file")
    request_value = load_json(request_path, "event verifier request")
    (
        request, claim, claim_path, task, task_path, _brief, brief_path
    ) = validate_verifier_request(
        request_value,
        service_dir_value=args.service_dir,
        request_path=request_path,
    )
    event_id = request["event"]["event_id"]
    envelope_path = argument_path(args.envelope, "event verifier envelope")
    expected_envelope = _derived_verifier_envelope_path(task, event_id)
    if envelope_path != expected_envelope:
        raise GuardError("event verifier envelope path differs from its derived root receipt")
    if envelope_path.exists():
        existing = validate_verifier_envelope(
            load_json(envelope_path, "existing event verifier envelope"),
            request_path=request_path,
            request=request,
            claim_path=claim_path,
            task_path=task_path,
        )
        print(json.dumps(existing, indent=2, sort_keys=True))
        return 0 if existing["terminal"] == "PASS" else 2

    worker_contract = {
        "argv_template": request["argv_template"],
        "input_receipts": request["input_receipts"],
        "outputs": [],
    }
    capability = capability_report("network")
    if capability["terminal"] != "PASS":
        resources = resource_policy(task)
        now_value = utc_now()
        outcome = {
            "started_at": now_value, "finished_at": now_value,
            "outer_pid": os.getpid(), "sandbox_pid": None,
            "sandbox_start_ticks": None, "process_group": None,
            "resolved_argv": request["argv_template"], "resources": resources,
            "policy_hash": seccomp_policy_sha256(),
            "namespace_inodes": {
                key: None for key in ("user", "mount", "pid", "net", "ipc", "uts", "cgroup")
            },
            "exit_code": None, "signal": None, "wall_seconds": 0.0,
            "cpu_seconds": 0.0, "peak_rss": 0, "streams": {},
            "worker_output_bytes": 0, "forbidden_attempts": "not-observed",
            "violations": [
                "guard capability check stopped: " + json.dumps(capability, sort_keys=True)
            ],
            "terminal": "LAUNCH_STOP", "stderr": b"",
        }
    else:
        outcome = _execute(
            contract=worker_contract,
            task=task,
            claim_path=claim_path,
            brief_path=brief_path,
            task_path=task_path,
            identity_sha256={
                "claim.json": request["seed_claim"]["sha256"],
                "brief.json": claim["development_brief"]["sha256"],
                "task.json": request["task_packet"]["sha256"],
            },
        )
    if digest(request_path) != args.request_sha256:
        raise GuardError("event verifier request changed during execution")
    validate_verifier_request(
        load_json(request_path, "post-execution event verifier request"),
        service_dir_value=args.service_dir,
        request_path=request_path,
    )
    stdout = outcome["streams"].get("__stdout__", b"")
    stderr = outcome["streams"].get("__stderr__", outcome.get("stderr", b""))
    expected_stdout = canonical_bytes(request["expected_normalized_result"]) + b"\n"
    if outcome["terminal"] == "PASS" and stdout != expected_stdout:
        outcome["terminal"] = "VIOLATION"
        outcome["violations"].append(
            "event verifier stdout differs from the exact normalized result"
        )
    if outcome["terminal"] == "PASS" and stderr:
        outcome["terminal"] = "VIOLATION"
        outcome["violations"].append("event verifier wrote a nonempty stderr stream")
    envelope = build_verifier_envelope(
        outcome=outcome,
        request_path=request_path,
        request=request,
        claim_path=claim_path,
        task_path=task_path,
    )
    validate_verifier_envelope(
        envelope,
        request_path=request_path,
        request=request,
        claim_path=claim_path,
        task_path=task_path,
    )
    _write_envelope_once(envelope_path, envelope)
    print(json.dumps(envelope, indent=2, sort_keys=True))
    return 0 if envelope["terminal"] == "PASS" else 2


def command_inner(args: argparse.Namespace) -> int:
    header = os.read(args.contract_fd, 8)
    if len(header) != 8:
        raise GuardError("inner contract length is missing")
    size = struct.unpack(">Q", header)[0]
    if size > MAX_FRAME_OVERHEAD:
        raise GuardError("inner contract exceeds its bound")
    data = bytearray()
    while len(data) < size:
        chunk = os.read(args.contract_fd, size - len(data))
        if not chunk:
            raise GuardError("inner contract is truncated")
        data.extend(chunk)
    value = json.loads(bytes(data))
    if not isinstance(value, dict):
        raise GuardError("inner contract is not an object")
    return _inner_worker(value, args.result_fd)


def command_inner_capability(args: argparse.Namespace) -> int:
    return _inner_capability(args.result_fd, args.attempt)


def command_capability(args: argparse.Namespace) -> int:
    report = capability_report(args.negative)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["terminal"] == "PASS" else 2


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    capability = subparsers.add_parser(
        "capability-check", help="run an ephemeral Bubblewrap/seccomp smoke check"
    )
    capability.add_argument(
        "--negative", choices=("network", "write", "spawn"), default="network"
    )
    capability.set_defaults(func=command_capability)

    run = subparsers.add_parser("run", help="execute one authenticated first test")
    run.add_argument("--service-dir", required=True)
    run.add_argument("--claim", required=True)
    run.add_argument("--claim-sha256", required=True)
    run.add_argument("--brief", required=True)
    run.add_argument("--brief-sha256", required=True)
    run.add_argument("--task", required=True)
    run.add_argument("--task-sha256", required=True)
    run.add_argument("--envelope", required=True)
    run.set_defaults(func=command_run)

    verify = subparsers.add_parser(
        "verify", help="replay one frozen event under a separate root envelope"
    )
    verify.add_argument("--service-dir", required=True)
    verify.add_argument("--request", required=True)
    verify.add_argument("--request-sha256", required=True)
    verify.add_argument("--envelope", required=True)
    verify.set_defaults(func=command_verify)

    inner = subparsers.add_parser("inner", help=argparse.SUPPRESS)
    inner.add_argument("--contract-fd", type=int, required=True)
    inner.add_argument("--result-fd", type=int, required=True)
    inner.set_defaults(func=command_inner)
    inner_capability = subparsers.add_parser("inner-capability", help=argparse.SUPPRESS)
    inner_capability.add_argument("--result-fd", type=int, required=True)
    inner_capability.add_argument(
        "--attempt", choices=("none", "network", "write", "spawn"), required=True
    )
    inner_capability.set_defaults(func=command_inner_capability)
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)
    try:
        return int(args.func(args))
    except (GuardError, OSError, json.JSONDecodeError) as exc:
        print(f"first-test guard error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
