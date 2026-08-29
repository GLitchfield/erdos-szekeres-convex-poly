#!/usr/bin/env python3
"""One-shot supervisor for the unapproved FD014 Hankel corpus pilot v2.

Candidate mode authenticates a frozen task and run contract before it creates
any runtime state.  Synthetic mode is deliberately self-contained: it writes
and executes tiny fake sources only and never opens an accepted semantic
source.
"""

from __future__ import annotations

import argparse
import errno
import hashlib
import json
import os
from pathlib import Path
import selectors
import shutil
import signal
import stat
import subprocess
import sys
import time
from typing import Any


ROOT = Path("/home/gavin/git/erdos-szekeres-convex-poly")
SUPERVISOR = ROOT / "scripts/supervise_hankel_context_corpus_pilot_v2.py"
AUTHOR_PLAN = ROOT / (
    "runs/agents/20260827-post-fin13-slate-acquisition/planning/"
    "hankel-context-corpus-pilot-v2-author-v1"
)
CANDIDATE_TASK = AUTHOR_PLAN / "candidate-task.json"
RUN_CONTRACT = AUTHOR_PLAN / "run-contract.json"
CANDIDATE_PARENT = ROOT / "runs/agents/20260827-post-fin13-slate-acquisition/candidates"
NAMESPACE = CANDIDATE_PARENT / "hankel-context-corpus-pilot-v2"
LEDGER = CANDIDATE_PARENT / ".hankel-context-corpus-pilot-v2.spent.jsonl"
SCRATCH = NAMESPACE / ".scratch"
SYNTHETIC_ROOT = Path("/tmp/hankel-context-corpus-pilot-v2-author-v1-synthetic")

SCHEMA_TOKEN = (
    "runs/agents/20260827-post-fin13-slate-acquisition/results/"
    "hankel-context-corpus-contract-audit-v1/corpus-schema.json"
)
CONTROL_TOKEN = "data/derived/e3-context-k6-n9-singleton-collision.json"
RELATIVE_TOKENS = (SCHEMA_TOKEN, CONTROL_TOKEN)

TERMINAL_VERIFIED = "HANKEL-CORPUS-PILOT-VERIFIED"
TERMINAL_SCHEMA = "HANKEL-CORPUS-PILOT-SCHEMA-DEFECT"
TERMINAL_RESOURCE = "HANKEL-CORPUS-PILOT-RESOURCE-STOP"
TERMINAL_INPUT = "HANKEL-CORPUS-PILOT-INPUT-STOP"
TERMINALS = (
    TERMINAL_VERIFIED,
    TERMINAL_SCHEMA,
    TERMINAL_RESOURCE,
    TERMINAL_INPUT,
)

STREAM_CAP = 1_048_576
LEDGER_CAP = 65_536
OUTPUT_CAPS = {
    "corpus.json": 192_847_488,
    "checker-receipt.json": 1_000_000,
    "hostile-receipt.json": 2_000_000,
    "report.md": 2_000_000,
    "result.json": 1_000_000,
}
FINAL_RETAINED_CAP = 198_913_024
HARD_RETAINED_CAP = 200_000_000

ENVIRONMENT_KEYS = (
    "LC_ALL",
    "LANG",
    "TZ",
    "PYTHONHASHSEED",
    "PYTHONDONTWRITEBYTECODE",
    "PYTHONNOUSERSITE",
    "PYTHONSAFEPATH",
    "TMPDIR",
)

SYNTHETIC_CASES = (
    "PATH-TOKEN-REJECT",
    "ROOT-CLOSURE-REJECT",
    "ZERO-START-REJECT",
    "CWD-ENV-AFFINITY-PASS",
    "PRODUCER-OWNS-NAMESPACE-PASS",
    "TIMEOUT-TREE-RESOURCE-STOP",
    "RLIMIT-AS-4G-PASS",
    "RLIMIT-AS-2G-PASS",
    "OUTPUT-BOUND-REJECT",
    "LEDGER-ONE-SHOT-REJECT",
    "ATOMIC-SEAL-PASS",
    "INTERRUPTED-SEAL-REJECT",
)


class SupervisorError(RuntimeError):
    """A classified supervisor stop."""

    def __init__(self, terminal: str, diagnostic: str):
        super().__init__(f"{terminal}:{diagnostic}")
        self.terminal = terminal
        self.diagnostic = diagnostic


def fail_input(diagnostic: str) -> None:
    raise SupervisorError(TERMINAL_INPUT, diagnostic)


def fail_resource(diagnostic: str) -> None:
    raise SupervisorError(TERMINAL_RESOURCE, diagnostic)


def fail_schema(diagnostic: str) -> None:
    raise SupervisorError(TERMINAL_SCHEMA, diagnostic)


def canonical(value: object) -> bytes:
    return json.dumps(
        value, ensure_ascii=True, sort_keys=True, separators=(",", ":")
    ).encode("ascii")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def load_json(path: Path, *, terminal: str = TERMINAL_INPUT) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise SupervisorError(terminal, f"json:{path.name}:{type(error).__name__}") from None


def require_regular(path: Path, *, cap: int | None = None) -> os.stat_result:
    try:
        info = os.lstat(path)
    except OSError as error:
        fail_input(f"missing:{path}:{error.errno}")
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
        fail_input(f"not_regular:{path}")
    if cap is not None and info.st_size > cap:
        fail_resource(f"file_cap:{path.name}")
    return info


def exact_stat(path: Path) -> dict[str, object]:
    info = os.lstat(path)
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
        fail_input(f"root_component:{path}")
    return {
        "path": str(path),
        "device": info.st_dev,
        "inode": info.st_ino,
        "mode": format(stat.S_IMODE(info.st_mode), "04o"),
        "uid": info.st_uid,
        "gid": info.st_gid,
        "type": "directory",
        "symlink": False,
    }


def compare_root_receipt(receipt: list[dict[str, object]]) -> None:
    if ROOT.resolve(strict=True) != ROOT:
        fail_input("physical_root")
    for expected in receipt:
        path = Path(str(expected.get("path")))
        actual = exact_stat(path)
        if actual != expected:
            fail_input(f"root_receipt:{path}")


def make_environment(tmpdir: Path) -> dict[str, str]:
    return {
        "LC_ALL": "C",
        "LANG": "C",
        "TZ": "UTC",
        "PYTHONHASHSEED": "0",
        "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONNOUSERSITE": "1",
        "PYTHONSAFEPATH": "1",
        "TMPDIR": str(tmpdir),
    }


def check_token_spelling(token: str) -> tuple[str, ...]:
    if not token or token.startswith("/") or token.startswith("./"):
        fail_input("relative_token_syntax")
    if "//" in token or "\\" in token:
        fail_input("relative_token_syntax")
    parts = tuple(token.split("/"))
    if any(part in ("", ".", "..") for part in parts):
        fail_input("relative_token_component")
    return parts


def validate_token_set(tokens: list[str] | tuple[str, ...]) -> None:
    if tuple(tokens) != RELATIVE_TOKENS:
        fail_input("relative_token_set")


def validate_relative_token(
    root_fd: int,
    root: Path,
    token: str,
    expected_path: Path,
    expected_hash: str,
) -> None:
    parts = check_token_spelling(token)
    current = os.dup(root_fd)
    try:
        for part in parts[:-1]:
            next_fd = os.open(
                part,
                os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                dir_fd=current,
            )
            os.close(current)
            current = next_fd
        final_fd = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW, dir_fd=current)
        try:
            info = os.fstat(final_fd)
            if not stat.S_ISREG(info.st_mode):
                fail_input("relative_token_type")
            digest = hashlib.sha256()
            while True:
                block = os.read(final_fd, 1 << 20)
                if not block:
                    break
                digest.update(block)
        finally:
            os.close(final_fd)
    except OSError as error:
        fail_input(f"relative_token_walk:{error.errno}")
    finally:
        os.close(current)
    resolved = (root / token).resolve(strict=True)
    if resolved != expected_path or digest.hexdigest() != expected_hash:
        fail_input("relative_token_identity")


def require_absent(paths: list[Path] | tuple[Path, ...], diagnostic: str) -> None:
    if any(os.path.lexists(path) for path in paths):
        fail_input(diagnostic)


def fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def atomic_new(path: Path, payload: bytes, cap: int) -> None:
    if len(payload) > cap:
        fail_resource(f"atomic_cap:{path.name}")
    temporary = path.with_name("." + path.name + ".tmp")
    require_absent((path, temporary), f"atomic_exists:{path.name}")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW
    descriptor = os.open(path=temporary, flags=flags, mode=0o600)
    try:
        view = memoryview(payload)
        while view:
            written = os.write(descriptor, view)
            view = view[written:]
        os.fsync(descriptor)
    except BaseException:
        os.close(descriptor)
        raise
    else:
        os.close(descriptor)
    os.replace(temporary, path)
    fsync_directory(path.parent)
    require_regular(path, cap=cap)


class LedgerWriter:
    """Exclusive capped JSON-lines ledger."""

    def __init__(self, path: Path):
        self.path = path
        self.states: set[str] = set()
        flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW
        try:
            self.descriptor = os.open(path, flags, 0o600)
        except OSError as error:
            fail_input(f"ledger_create:{error.errno}")
        self.bytes = 0

    def append(self, state: str, fields: dict[str, object]) -> None:
        if state in self.states:
            fail_resource(f"ledger_duplicate:{state}")
        row = dict(fields)
        row["state"] = state
        payload = canonical(row) + b"\n"
        if self.bytes + len(payload) > LEDGER_CAP:
            fail_resource("ledger_cap")
        os.write(self.descriptor, payload)
        os.fsync(self.descriptor)
        self.bytes += len(payload)
        self.states.add(state)

    def close(self) -> None:
        if getattr(self, "descriptor", -1) >= 0:
            os.close(self.descriptor)
            self.descriptor = -1


def terminate_group(process: subprocess.Popen[bytes], grace: float = 0.25) -> None:
    if process.poll() is not None:
        process.wait()
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=grace)
        return
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=2.0)
    except subprocess.TimeoutExpired:
        fail_resource("process_group_live")


def run_bounded(
    argv: list[str],
    *,
    cwd: Path,
    env: dict[str, str],
    deadline_ns: int,
    stream_cap: int = STREAM_CAP,
) -> dict[str, object]:
    if not argv or not Path(argv[0]).is_absolute():
        fail_input("absolute_executable")
    started = time.monotonic_ns()
    process = subprocess.Popen(
        argv,
        cwd=str(cwd),
        env=env,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
        shell=False,
    )
    assert process.stdout is not None and process.stderr is not None
    selector = selectors.DefaultSelector()
    data = {"stdout": bytearray(), "stderr": bytearray()}
    digests = {"stdout": hashlib.sha256(), "stderr": hashlib.sha256()}
    counts = {"stdout": 0, "stderr": 0}
    for name, stream in (("stdout", process.stdout), ("stderr", process.stderr)):
        os.set_blocking(stream.fileno(), False)
        selector.register(stream, selectors.EVENT_READ, name)
    try:
        while selector.get_map() or process.poll() is None:
            now = time.monotonic_ns()
            if now >= deadline_ns:
                terminate_group(process)
                fail_resource("stage_timeout")
            wait = min(0.05, max(0.0, (deadline_ns - now) / 1_000_000_000))
            for key, _ in selector.select(wait):
                name = str(key.data)
                try:
                    block = os.read(key.fileobj.fileno(), 65_536)
                except BlockingIOError:
                    continue
                if not block:
                    selector.unregister(key.fileobj)
                    continue
                counts[name] += len(block)
                if counts[name] > stream_cap:
                    terminate_group(process)
                    fail_resource(f"stream_cap:{name}")
                digests[name].update(block)
                data[name].extend(block)
        status = process.wait(timeout=0)
    except BaseException:
        if process.poll() is None:
            terminate_group(process)
        raise
    finally:
        selector.close()
        process.stdout.close()
        process.stderr.close()
    ended = time.monotonic_ns()
    return {
        "argv": argv,
        "exit_status": status,
        "started_monotonic_ns": started,
        "ended_monotonic_ns": ended,
        "elapsed_ns": ended - started,
        "stdout_bytes": counts["stdout"],
        "stdout_sha256": digests["stdout"].hexdigest(),
        "stderr_bytes": counts["stderr"],
        "stderr_sha256": digests["stderr"].hexdigest(),
        "stdout_data": bytes(data["stdout"]),
        "stderr_data": bytes(data["stderr"]),
    }


def authenticate_input_vector(candidate: dict[str, object], contract: dict[str, object]) -> None:
    actual = candidate.get("inputs")
    expected = contract.get("candidate_inputs")
    if not isinstance(actual, list) or not isinstance(expected, list) or len(actual) != 24:
        fail_input("candidate_input_count")
    if len(expected) != 24:
        fail_input("contract_input_count")
    for index, (given, wanted) in enumerate(zip(actual, expected), 1):
        if not isinstance(given, dict) or not isinstance(wanted, dict):
            fail_input(f"candidate_input_shape:{index}")
        if given.get("path") != wanted.get("path"):
            fail_input(f"candidate_input_path:{index}")
        expected_hash = wanted.get("sha256")
        if expected_hash == "SELF":
            expected_hash = sha256_file(RUN_CONTRACT)
        if given.get("sha256") != expected_hash:
            fail_input(f"candidate_input_digest:{index}")
        text = str(given["path"])
        path = Path(text) if text.startswith("/") else ROOT / text
        require_regular(path)
        if sha256_file(path) != given["sha256"]:
            fail_input(f"candidate_input_bytes:{index}")


def authenticate_tools(contract: dict[str, object]) -> None:
    tools = contract.get("tool_receipt")
    if not isinstance(tools, list) or len(tools) != 5:
        fail_input("tool_receipt_count")
    for expected in tools:
        if not isinstance(expected, dict):
            fail_input("tool_receipt_shape")
        path = Path(str(expected.get("path")))
        info = require_regular(path)
        actual = {
            "path": str(path),
            "sha256": sha256_file(path),
            "bytes": info.st_size,
            "device": info.st_dev,
            "inode": info.st_ino,
            "mode": format(stat.S_IMODE(info.st_mode), "04o"),
            "uid": info.st_uid,
            "gid": info.st_gid,
            "type": "regular file",
        }
        if actual != expected:
            fail_input(f"tool_identity:{path.name}")


def no_scoped_processes(marker: bytes) -> None:
    excluded = {os.getpid(), os.getppid()}
    proc = Path("/proc")
    if not proc.is_dir():
        fail_input("proc_unavailable")
    for entry in proc.iterdir():
        if not entry.name.isdigit() or int(entry.name) in excluded:
            continue
        try:
            command = (entry / "cmdline").read_bytes()
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            continue
        if marker in command:
            fail_input("scoped_process_exists")


def enumerate_namespace(allowed: set[str], *, scratch_may_be_nonempty: bool) -> int:
    if not NAMESPACE.exists():
        fail_resource("namespace_missing")
    info = os.lstat(NAMESPACE)
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
        fail_resource("namespace_type")
    if stat.S_IMODE(info.st_mode) != 0o700:
        fail_resource("namespace_mode")
    total = os.lstat(LEDGER).st_size if LEDGER.exists() else 0
    for child in NAMESPACE.iterdir():
        if child.name == ".scratch":
            sinfo = os.lstat(child)
            if stat.S_ISLNK(sinfo.st_mode) or not stat.S_ISDIR(sinfo.st_mode):
                fail_resource("scratch_type")
            descendants = list(child.rglob("*"))
            if descendants and not scratch_may_be_nonempty:
                fail_resource("scratch_not_empty")
            for descendant in descendants:
                dinfo = os.lstat(descendant)
                if stat.S_ISLNK(dinfo.st_mode) or not (
                    stat.S_ISREG(dinfo.st_mode) or stat.S_ISDIR(dinfo.st_mode)
                ):
                    fail_resource("scratch_special")
                if stat.S_ISREG(dinfo.st_mode):
                    total += dinfo.st_size
            continue
        normalized = child.name[1:-4] if child.name.startswith(".") and child.name.endswith(".tmp") else child.name
        if normalized not in allowed:
            fail_resource(f"unknown_output:{child.name}")
        cinfo = os.lstat(child)
        if stat.S_ISLNK(cinfo.st_mode) or not stat.S_ISREG(cinfo.st_mode):
            fail_resource(f"output_type:{child.name}")
        cap = OUTPUT_CAPS[normalized]
        if cinfo.st_size > cap:
            fail_resource(f"output_cap:{child.name}")
        total += cinfo.st_size
        temporary = NAMESPACE / ("." + normalized + ".tmp")
        final = NAMESPACE / normalized
        if os.path.lexists(temporary) and os.path.lexists(final):
            fail_resource(f"output_pair:{normalized}")
    if total > HARD_RETAINED_CAP:
        fail_resource("aggregate_cap")
    for name in allowed:
        final = NAMESPACE / name
        try:
            finfo = os.lstat(final)
        except FileNotFoundError:
            fail_resource(f"output_missing:{name}")
        if stat.S_ISLNK(finfo.st_mode) or not stat.S_ISREG(finfo.st_mode):
            fail_resource(f"output_type:{name}")
    return total


def build_report(
    terminal: str,
    candidate_hash: str,
    stages: list[dict[str, object]],
    total_bytes: int,
) -> bytes:
    lines = [
        "# FD014 Hankel context-corpus pilot v2",
        "",
        f"Terminal: `{terminal}`",
        "",
        f"Candidate SHA-256: `{candidate_hash}`.",
        f"Selected CPU: `{min(os.sched_getaffinity(0))}`.",
        f"Retained bytes before final seal: `{total_bytes}`.",
        "",
        "The three stages were supervised strictly serially with authenticated",
        "fixed cwd, direct argv, a fresh whitelist environment, one-start",
        "ledger semantics, known exits, and no retry.",
        "",
        "## Stages",
        "",
    ]
    for stage in stages:
        lines.append(
            f"- `{stage['name']}`: exit `{stage['exit_status']}`, elapsed_ns "
            f"`{stage['elapsed_ns']}`, stdout `{stage['stdout_bytes']}` bytes, "
            f"stderr `{stage['stderr_bytes']}` bytes."
        )
    lines += [
        "",
        "## Scope",
        "",
        "Maximum n is exactly 6. This bounded acquisition is neutral proof",
        "movement and does not establish a theorem, rank result, route action,",
        "larger acquisition, or automatic successor.",
        "",
    ]
    return "\n".join(lines).encode("utf-8")


def build_result(
    terminal: str,
    candidate_hash: str,
    stages: list[dict[str, object]],
    output_hashes: dict[str, str],
) -> bytes:
    verified = terminal == TERMINAL_VERIFIED
    value = {
        "schema_version": 1,
        "task_id": "hankel-context-corpus-pilot-v2",
        "status": "completed" if verified else "refuted",
        "claim_level": "computational_evidence",
        "summary": (
            f"{terminal}: the immutable n<=6 Hankel context-corpus pilot completed "
            "under its one-shot supervised contract."
        ),
        "supports": [
            "The frozen candidate, all 24 inputs, five tools, physical root, and two relative semantic tokens authenticated.",
            "Three direct stages ran once, serially, with one CPU, known exits, fixed cwd/environment, address-space limits, bounded streams, output checks, and no retry.",
            "The terminal is bounded computational evidence for only the exact n<=6 acquisition contract."
        ],
        "does_not_support": [
            "No theorem, uniform result, rank/predictor claim, n=7/8 extension, route promotion, proof movement, or automatic successor follows.",
            "A resource or schema terminal is not a mechanism-wide mathematical negative."
        ],
        "changes": [
            str(NAMESPACE / "corpus.json").removeprefix(str(ROOT) + "/"),
            str(NAMESPACE / "checker-receipt.json").removeprefix(str(ROOT) + "/"),
            str(NAMESPACE / "hostile-receipt.json").removeprefix(str(ROOT) + "/"),
            str(NAMESPACE / "report.md").removeprefix(str(ROOT) + "/"),
            str(NAMESPACE / "result.json").removeprefix(str(ROOT) + "/"),
        ],
        "checks": [
            {"command": "authenticate candidate, 24 inputs, tools, root/tokens, approval, and zero start", "outcome": "passed"},
            {"command": "run producer/checker/hostile once each under frozen direct vectors and resource boundaries", "outcome": "passed" if stages else "not_run"},
            {"command": "validate output types, caps, hashes, checker replay, nine hostiles, and atomic seal", "outcome": "passed" if verified else "failed"},
        ],
        "evidence": [
            f"terminal={terminal};candidate_sha256={candidate_hash};stages={len(stages)};retry=false",
            "output_hashes=" + json.dumps(output_hashes, sort_keys=True, separators=(",", ":")),
            "net_proof_movement=neutral;damage_scope=operational-only;load_bearing_ledger=unchanged;failure_genome=none",
        ],
        "limitations": [
            "This result is bounded to HANKEL-CONTEXT-ASCII-V1 with maximum n=6.",
            "Runtime resource feasibility and semantic agreement are reported only for this immutable execution.",
            "Any further rank, prediction, larger acquisition, or route action requires a new reviewed packet."
        ],
        "blocked_by": None if verified else terminal,
    }
    return canonical(value) + b"\n"


def seal_terminal(
    terminal: str,
    candidate_hash: str,
    stages: list[dict[str, object]],
) -> None:
    allowed = {"corpus.json", "checker-receipt.json", "hostile-receipt.json"}
    total = enumerate_namespace(allowed, scratch_may_be_nonempty=False)
    report_payload = build_report(terminal, candidate_hash, stages, total)
    atomic_new(NAMESPACE / "report.md", report_payload, OUTPUT_CAPS["report.md"])
    output_hashes = {
        name: sha256_file(NAMESPACE / name)
        for name in ("corpus.json", "checker-receipt.json", "hostile-receipt.json", "report.md")
    }
    result_payload = build_result(terminal, candidate_hash, stages, output_hashes)
    atomic_new(NAMESPACE / "result.json", result_payload, OUTPUT_CAPS["result.json"])
    enumerate_namespace(set(OUTPUT_CAPS), scratch_may_be_nonempty=False)


def candidate_mode(candidate_path: Path, contract_path: Path, approved_hash: str) -> int:
    if candidate_path != CANDIDATE_TASK or contract_path != RUN_CONTRACT:
        fail_input("launch_paths")
    if len(approved_hash) != 64 or any(c not in "0123456789abcdef" for c in approved_hash):
        fail_input("approval_syntax")
    require_regular(candidate_path)
    require_regular(contract_path)
    actual_candidate_hash = sha256_file(candidate_path)
    if actual_candidate_hash != approved_hash:
        fail_input("approval_hash")
    candidate = load_json(candidate_path)
    contract = load_json(contract_path)
    if candidate.get("task_id") != "hankel-context-corpus-pilot-v2":
        fail_input("candidate_identity")
    if candidate.get("profile") != "finite_model_experimentalist":
        fail_input("candidate_profile")
    if contract.get("contract_id") != "HANKEL-CORPUS-PILOT-V2-RUN-CONTRACT-V1":
        fail_input("run_contract_identity")
    authenticate_input_vector(candidate, contract)
    authenticate_tools(contract)
    compare_root_receipt(contract.get("root_receipt", []))
    if Path.cwd().resolve(strict=True) != ROOT:
        fail_input("fixed_cwd")
    root_fd = os.open(ROOT, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        token_records = contract.get("relative_tokens")
        if not isinstance(token_records, list) or len(token_records) != 2:
            fail_input("token_records")
        validate_token_set([str(row.get("token")) for row in token_records if isinstance(row, dict)])
        for row in token_records:
            validate_relative_token(
                root_fd,
                ROOT,
                str(row["token"]),
                Path(str(row["absolute_path"])),
                str(row["sha256"]),
            )
    finally:
        os.close(root_fd)
    no_scoped_processes(b"hankel-context-corpus-pilot-v2")
    require_absent((CANDIDATE_PARENT, LEDGER, NAMESPACE), "runtime_zero_start")

    os.mkdir(CANDIDATE_PARENT, mode=0o700)
    if stat.S_IMODE(os.lstat(CANDIDATE_PARENT).st_mode) != 0o700:
        fail_resource("candidate_parent_mode")
    ledger = LedgerWriter(LEDGER)
    stages: list[dict[str, object]] = []
    try:
        allowed_cpus = os.sched_getaffinity(0)
        if not allowed_cpus:
            fail_input("cpu_affinity_empty")
        selected_cpu = min(allowed_cpus)
        os.sched_setaffinity(0, {selected_cpu})
        if os.sched_getaffinity(0) != {selected_cpu}:
            fail_resource("cpu_affinity")
        env = make_environment(SCRATCH)
        if env != contract.get("environment"):
            fail_input("environment_contract")
        vectors = contract.get("stage_vectors")
        if not isinstance(vectors, list) or len(vectors) != 3:
            fail_input("stage_vectors")
        t0 = time.monotonic_ns()
        ledger.append(
            "producer_started",
            {
                "candidate_sha256": actual_candidate_hash,
                "selected_cpu": selected_cpu,
                "t0_monotonic_ns": t0,
                "t0_wall_ns": time.time_ns(),
            },
        )
        deadlines = (t0 + 720_000_000_000, t0 + 1_320_000_000_000, t0 + 1_680_000_000_000)
        names = ("producer", "checker", "hostile")
        for index, (name, vector, deadline) in enumerate(zip(names, vectors, deadlines)):
            if index:
                ledger.append(name + "_started", {"monotonic_ns": time.monotonic_ns()})
            if name == "hostile":
                os.mkdir(SCRATCH, mode=0o700)
            if os.sched_getaffinity(0) != {selected_cpu}:
                fail_resource("cpu_affinity_drift")
            stage = run_bounded(
                [str(item) for item in vector],
                cwd=ROOT,
                env=env,
                deadline_ns=deadline,
            )
            stage["name"] = name
            stages.append(stage)
            ledger.append(name + "_exited", {"exit_status": stage["exit_status"], "monotonic_ns": time.monotonic_ns()})
            if stage["exit_status"] != 0:
                fail_schema(f"{name}_exit")
            if name == "producer":
                enumerate_namespace({"corpus.json"}, scratch_may_be_nonempty=False)
            elif name == "checker":
                enumerate_namespace({"corpus.json", "checker-receipt.json"}, scratch_may_be_nonempty=False)
            else:
                enumerate_namespace(
                    {"corpus.json", "checker-receipt.json", "hostile-receipt.json"},
                    scratch_may_be_nonempty=False,
                )
        checker = load_json(NAMESPACE / "checker-receipt.json", terminal=TERMINAL_SCHEMA)
        hostile = load_json(NAMESPACE / "hostile-receipt.json", terminal=TERMINAL_SCHEMA)
        expected_diagnostics = [
            "OMISSION",
            "DUPLICATION",
            "ID_COLLISION",
            "ROOT_INCOMPATIBLE",
            "WRONG_HOLE_TYPE",
            "STALE_PARENT",
            "OUTPUT_BIT_FLIP",
            "SPLIT_LEAKAGE",
            "EXTERNAL_CONTROL_MUTATION",
        ]
        terminal = TERMINAL_VERIFIED
        if not checker.get("ok") or not hostile.get("ok") or hostile.get("diagnostics") != expected_diagnostics:
            terminal = TERMINAL_SCHEMA
        if time.monotonic_ns() >= t0 + 1_800_000_000_000:
            fail_resource("final_seal_timeout")
        seal_terminal(terminal, actual_candidate_hash, stages)
        ledger.append("terminal_sealed", {"terminal": terminal, "monotonic_ns": time.monotonic_ns()})
        print(canonical({"terminal": terminal, "candidate_sha256": actual_candidate_hash}).decode("ascii"))
        return 0 if terminal == TERMINAL_VERIFIED else 1
    except SupervisorError as error:
        try:
            ledger.append(
                "terminal_stop",
                {"terminal": error.terminal, "diagnostic": error.diagnostic},
            )
        except SupervisorError:
            pass
        raise
    finally:
        ledger.close()


def write_fake(path: Path, source: str) -> None:
    path.write_text(source, encoding="utf-8")
    os.chmod(path, 0o600)


def expect_supervisor_error(function, terminal: str | None = None) -> None:
    try:
        function()
    except SupervisorError as error:
        if terminal is not None and error.terminal != terminal:
            raise AssertionError((terminal, error.terminal)) from error
        return
    raise AssertionError("expected SupervisorError")


def synthetic_path_token(root: Path) -> None:
    safe = root / "safe" / "input.json"
    safe.parent.mkdir()
    safe.write_bytes(b"{}\n")
    descriptor = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        validate_relative_token(descriptor, root, "safe/input.json", safe, sha256_file(safe))
        for bad in ("", "/safe/input.json", "./safe/input.json", "safe//input.json", "safe/../input.json"):
            expect_supervisor_error(
                lambda value=bad: validate_relative_token(
                    descriptor, root, value, safe, sha256_file(safe)
                ),
                TERMINAL_INPUT,
            )
        expect_supervisor_error(lambda: validate_token_set([SCHEMA_TOKEN, CONTROL_TOKEN, "third"]), TERMINAL_INPUT)
    finally:
        os.close(descriptor)


def synthetic_root_closure(root: Path) -> None:
    actual = root / "actual"
    actual.mkdir()
    link = root / "link"
    link.symlink_to(actual, target_is_directory=True)
    expected = exact_stat(actual)
    expected["inode"] = int(expected["inode"]) + 1
    expect_supervisor_error(lambda: compare_root_receipt([expected]), TERMINAL_INPUT)
    descriptor = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        expect_supervisor_error(
            lambda: validate_relative_token(descriptor, root, "link/file", actual / "file", "0" * 64),
            TERMINAL_INPUT,
        )
    finally:
        os.close(descriptor)


def synthetic_zero_start(root: Path) -> None:
    target = root / "zero"
    require_absent((target,), "synthetic_zero")
    target.write_bytes(b"x")
    expect_supervisor_error(lambda: require_absent((target,), "synthetic_zero"), TERMINAL_INPUT)


def synthetic_cwd_env_affinity(root: Path) -> None:
    script = root / "env_probe.py"
    work = root / "cwd"
    temp = root / "tmp"
    work.mkdir()
    temp.mkdir()
    write_fake(
        script,
        "import json,os\n"
        "print(json.dumps({'cwd':os.getcwd(),'env':dict(os.environ),'affinity':sorted(os.sched_getaffinity(0))},sort_keys=True))\n",
    )
    original = os.sched_getaffinity(0)
    selected = min(original)
    try:
        os.sched_setaffinity(0, {selected})
        receipt = run_bounded(
            ["/usr/bin/python3.12", "-I", "-S", "-B", str(script)],
            cwd=work,
            env=make_environment(temp),
            deadline_ns=time.monotonic_ns() + 5_000_000_000,
        )
    finally:
        os.sched_setaffinity(0, original)
    assert receipt["exit_status"] == 0
    observed = json.loads(bytes(receipt["stdout_data"]).decode("ascii"))
    assert observed["cwd"] == str(work)
    assert observed["affinity"] == [selected]
    assert observed["env"] == make_environment(temp)


def synthetic_producer_namespace(root: Path) -> None:
    script = root / "fake_producer.py"
    namespace = root / "producer-namespace"
    output = namespace / "artifact.json"
    write_fake(
        script,
        "import json,os,sys\nfrom pathlib import Path\n"
        "p=Path(sys.argv[1])\n"
        "assert not p.parent.exists()\n"
        "p.parent.mkdir(mode=0o700,parents=True,exist_ok=False)\n"
        "p.write_text('{}\\n',encoding='ascii')\n"
        "print(json.dumps({'created':True},sort_keys=True))\n",
    )
    receipt = run_bounded(
        ["/usr/bin/python3.12", "-I", "-S", "-B", str(script), str(output)],
        cwd=root,
        env=make_environment(root),
        deadline_ns=time.monotonic_ns() + 5_000_000_000,
    )
    assert receipt["exit_status"] == 0 and output.is_file()
    assert stat.S_IMODE(os.lstat(namespace).st_mode) == 0o700


def process_gone(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return True
    except PermissionError:
        return False
    stat_path = Path(f"/proc/{pid}/stat")
    try:
        fields = stat_path.read_text().split()
    except FileNotFoundError:
        return True
    return len(fields) > 2 and fields[2] == "Z"


def synthetic_timeout_tree(root: Path) -> None:
    script = root / "tree.py"
    write_fake(
        script,
        "import subprocess,sys,time\n"
        "p=subprocess.Popen([sys.executable,'-I','-S','-B','-c','import time; time.sleep(60)'])\n"
        "print(p.pid,flush=True)\n"
        "time.sleep(60)\n",
    )
    process = subprocess.Popen(
        ["/usr/bin/python3.12", "-I", "-S", "-B", str(script)],
        cwd=str(root),
        env=make_environment(root),
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    assert process.stdout is not None
    line = process.stdout.readline().strip()
    grandchild = int(line)
    terminate_group(process)
    deadline = time.monotonic() + 2.0
    while time.monotonic() < deadline and not process_gone(grandchild):
        time.sleep(0.02)
    assert process.poll() is not None and process_gone(grandchild)
    process.stdout.close()
    assert process.stderr is not None
    process.stderr.close()


def synthetic_rlimit(root: Path, limit: int) -> None:
    code = "import json,resource; print(json.dumps(resource.getrlimit(resource.RLIMIT_AS)))"
    receipt = run_bounded(
        [
            "/usr/bin/prlimit",
            f"--as={limit}:{limit}",
            "--",
            "/usr/bin/python3.12",
            "-I",
            "-S",
            "-B",
            "-c",
            code,
        ],
        cwd=root,
        env=make_environment(root),
        deadline_ns=time.monotonic_ns() + 5_000_000_000,
    )
    assert receipt["exit_status"] == 0
    assert json.loads(bytes(receipt["stdout_data"]).decode("ascii")) == [limit, limit]


def check_small_output(path: Path, cap: int) -> None:
    info = os.lstat(path)
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
        fail_resource("synthetic_output_type")
    if info.st_size > cap:
        fail_resource("synthetic_output_cap")


def check_allowed_names(directory: Path, allowed: set[str]) -> None:
    for path in directory.iterdir():
        if path.name not in allowed:
            fail_resource("synthetic_unknown_output")


def synthetic_output_bound(root: Path) -> None:
    oversized = root / "oversized"
    oversized.write_bytes(b"123456789")
    expect_supervisor_error(lambda: check_small_output(oversized, 8), TERMINAL_RESOURCE)
    link = root / "output-link"
    link.symlink_to(oversized)
    expect_supervisor_error(lambda: check_small_output(link, 100), TERMINAL_RESOURCE)
    unknown = root / "unknown"
    unknown.write_bytes(b"x")
    expect_supervisor_error(
        lambda: check_allowed_names(root, {"oversized", "output-link"}),
        TERMINAL_RESOURCE,
    )


def synthetic_ledger(root: Path) -> None:
    path = root / "spent.jsonl"
    ledger = LedgerWriter(path)
    try:
        ledger.append("stage_started", {"sequence": 1})
        expect_supervisor_error(
            lambda: ledger.append("stage_started", {"sequence": 2}), TERMINAL_RESOURCE
        )
    finally:
        ledger.close()
    expect_supervisor_error(lambda: LedgerWriter(path), TERMINAL_INPUT)


def synthetic_atomic(root: Path) -> None:
    path = root / "sealed.json"
    payload = b'{"ok":true}\n'
    atomic_new(path, payload, 1024)
    assert path.read_bytes() == payload
    assert not os.path.lexists(path.with_name(".sealed.json.tmp"))


def synthetic_interrupted(root: Path) -> None:
    final = root / "result.json"
    temporary = root / ".result.json.tmp"
    temporary.write_bytes(b"partial")
    expect_supervisor_error(
        lambda: require_absent((final, temporary), "interrupted_seal"), TERMINAL_INPUT
    )
    assert not final.exists()


def run_synthetic_suite(synthetic_root: Path) -> int:
    if synthetic_root != SYNTHETIC_ROOT or not synthetic_root.is_absolute():
        fail_input("synthetic_root")
    require_absent((synthetic_root,), "synthetic_root_exists")
    synthetic_root.mkdir(mode=0o700)
    tests = (
        synthetic_path_token,
        synthetic_root_closure,
        synthetic_zero_start,
        synthetic_cwd_env_affinity,
        synthetic_producer_namespace,
        synthetic_timeout_tree,
        lambda path: synthetic_rlimit(path, 4_294_967_296),
        lambda path: synthetic_rlimit(path, 2_147_483_648),
        synthetic_output_bound,
        synthetic_ledger,
        synthetic_atomic,
        synthetic_interrupted,
    )
    cases: list[dict[str, object]] = []
    try:
        for index, (name, test) in enumerate(zip(SYNTHETIC_CASES, tests), 1):
            case_root = synthetic_root / f"case-{index:02d}"
            case_root.mkdir(mode=0o700)
            test(case_root)
            cases.append({"case": name, "ok": True})
    finally:
        if os.path.lexists(synthetic_root):
            info = os.lstat(synthetic_root)
            if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
                raise RuntimeError("unsafe synthetic cleanup target")
            shutil.rmtree(synthetic_root)
    receipt = {
        "schema_version": 1,
        "suite": "HANKEL-V2-SUPERVISOR-SYNTHETIC-V1",
        "cases": cases,
        "diagnostics": list(SYNTHETIC_CASES),
        "ok": len(cases) == 12 and all(case["ok"] for case in cases),
    }
    print(canonical(receipt).decode("ascii"))
    return 0 if receipt["ok"] else 1


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--candidate-task", type=Path)
    modes.add_argument("--synthetic-suite", action="store_true")
    parser.add_argument("--run-contract", type=Path)
    parser.add_argument("--approved-candidate-sha256")
    parser.add_argument("--synthetic-root", type=Path)
    args = parser.parse_args()
    if args.synthetic_suite:
        if args.synthetic_root is None or args.run_contract is not None or args.approved_candidate_sha256 is not None:
            parser.error("synthetic mode accepts only --synthetic-root")
    else:
        if args.run_contract is None or args.approved_candidate_sha256 is None or args.synthetic_root is not None:
            parser.error("candidate mode requires run contract and approved hash")
    return args


def main() -> int:
    args = parse_args()
    try:
        if args.synthetic_suite:
            return run_synthetic_suite(args.synthetic_root)
        return candidate_mode(
            args.candidate_task,
            args.run_contract,
            args.approved_candidate_sha256,
        )
    except SupervisorError as error:
        print(
            canonical(
                {"terminal": error.terminal, "diagnostic": error.diagnostic, "ok": False}
            ).decode("ascii")
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
