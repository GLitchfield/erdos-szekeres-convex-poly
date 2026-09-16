"""Deterministic, sanitized evidence bundle for a completed native research run.

The review is an inventory, not an evaluator.  In particular, process exit zero
does not establish a Lean theorem; only explicit proof receipts are labelled as
such, and even those are left for a reviewer to interpret.
"""
from __future__ import annotations

import hashlib
import json
import math
import os
from pathlib import Path
import re
from typing import Any

from es import artifacts, gitutil, usage
from es.errors import UsageError
from es.jobs import check_outputs
from es.store import Store


STATE_NAME = "agent-run.json"
USAGE_FIELDS = ("input_tokens", "cached_input_tokens", "output_tokens", "reasoning_output_tokens")
PENDING_JOB_STATES = {"queued", "starting", "running"}
UNKNOWN_JOB_STATES = {"unknown_execution"}
SCRIPT_SUFFIXES = {
    ".awk", ".bash", ".c", ".cc", ".cjs", ".cpp", ".fish", ".go", ".h", ".hpp", ".ipynb",
    ".java", ".jl", ".js", ".lean", ".lua", ".mjs", ".pl", ".pm", ".py", ".r", ".rb", ".rs",
    ".sage", ".scala", ".sed", ".sh", ".ts", ".tsx", ".zsh",
}
VALIDATION_ACTIONS = {"proof_check", "proof_prove", "node_check", "node_audit", "node_extract", "node_prepare"}
PROOF_RECEIPT_ACTIONS = {"proof_check", "proof_prove", "node_check", "node_prepare"}
ASSIGNMENT_SECRET = re.compile(
    r"(?i)(\b(?:api[_-]?key|authorization|credential|passwd|password|secret|token)\b\s*[:=]\s*)([^\s,;]+|['\"][^'\"]*['\"])",
)
BEARER_SECRET = re.compile(r"(?i)(\bbearer\s+)[A-Za-z0-9._~+/=-]+")
TOKEN_SHAPES = re.compile(r"\b(?:sk-[A-Za-z0-9_-]{12,}|gh[pousr]_[A-Za-z0-9]{12,}|AKIA[A-Z0-9]{12,})\b")


def _digest_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _digest_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _safe_text(value: Any, limit: int = 240) -> str | None:
    if not isinstance(value, str):
        return None
    return _redact(value.replace("\x00", ""))[0:limit]


def _redact(text: str) -> str:
    text = ASSIGNMENT_SECRET.sub(r"\1<redacted>", text)
    text = BEARER_SECRET.sub(r"\1<redacted>", text)
    return TOKEN_SHAPES.sub("<redacted-token>", text)


def _safe_scalar(value: Any, limit: int = 160) -> str | int | float | bool | None:
    if isinstance(value, str):
        return _safe_text(value, limit)
    if isinstance(value, bool) or isinstance(value, int):
        return value
    if isinstance(value, float) and math.isfinite(value):
        return value
    return None


def _path_has_symlink(path: Path, root: Path) -> bool:
    try:
        rel = path.absolute().relative_to(root.absolute())
    except ValueError:
        return False
    current = root.absolute()
    for part in rel.parts:
        current /= part
        if current.is_symlink():
            return True
    return False


def _load_state(cfg, out: str | Path) -> tuple[Path, str, dict, dict]:
    requested = Path(out).expanduser()
    if not requested.is_absolute():
        requested = cfg.root / requested
    if _path_has_symlink(requested, cfg.root):
        raise UsageError("agent run directory and state must not pass through symlinks")
    rel = check_outputs(cfg, [str(out)])[0]
    out_path = (cfg.root / rel).resolve()
    path = out_path / STATE_NAME
    if path.is_symlink():
        raise UsageError("agent run directory and state must not be symlinks")
    try:
        raw = path.read_bytes()
        state = json.loads(raw)
    except FileNotFoundError as exc:
        raise UsageError(f"no agent run at {out_path}") from exc
    except json.JSONDecodeError as exc:
        raise UsageError(f"invalid agent run state at {path}") from exc
    if not isinstance(state, dict) or state.get("schema_version") != 1:
        raise UsageError(f"unsupported agent run state at {path}")
    if Path(str(state.get("root", ""))).resolve() != cfg.root.resolve():
        raise UsageError("agent run state belongs to a different project root")
    if Path(str(state.get("out", ""))).resolve() != out_path:
        raise UsageError("agent run state out path does not match the requested directory")
    source = {"path": str(Path(rel) / STATE_NAME), "sha256": _digest_bytes(raw), "bytes": len(raw)}
    return out_path, rel, state, source


def _select_artifact_root(cfg, out_path: Path, state: dict, explicit: str | Path | None) -> tuple[Path, dict]:
    recorded = state.get("artifact_root")
    selected = explicit if explicit is not None else recorded
    if selected is None:
        return out_path, {
            "coverage": "host_out_only",
            "root": str(out_path.relative_to(cfg.root)),
            "limitation": "agent-run state has no artifact_root; scripts in a parent run directory are not inventoried",
        }
    if not isinstance(selected, (str, Path)) or not str(selected):
        raise UsageError("artifact_root must be a nonempty path")
    requested = Path(selected).expanduser()
    if not requested.is_absolute():
        requested = cfg.root / requested
    if _path_has_symlink(requested, cfg.root):
        raise UsageError("artifact_root must not pass through symlinks")
    rel = check_outputs(cfg, [str(selected)])[0]
    root = (cfg.root / rel).resolve()
    if root != out_path and root not in out_path.parents:
        raise UsageError("artifact_root must be the host out directory or one of its ancestors")
    return root, {
        "coverage": "explicit_artifact_root",
        "root": rel,
        "source": "command_argument" if explicit is not None else "agent-run state",
    }


def _lifecycle(state: dict) -> dict:
    timing = state.get("timing") if isinstance(state.get("timing"), dict) else {}
    goal = state.get("goal") if isinstance(state.get("goal"), dict) else {}
    progress = state.get("progress") if isinstance(state.get("progress"), dict) else {}
    submissions = state.get("submissions") if isinstance(state.get("submissions"), dict) else {}
    return {
        "status": _safe_text(state.get("status"), 80),
        "phase": _safe_text(state.get("phase"), 80),
        "created_at": _safe_text(state.get("created_at"), 64),
        "updated_at": _safe_text(state.get("updated_at"), 64),
        "model": _safe_text(state.get("model"), 80),
        "effort": _safe_text(state.get("effort"), 40),
        "thread_id": _safe_text(state.get("thread_id"), 160),
        "window_id": _safe_text(state.get("window_id"), 160),
        "researcher_agent": _safe_text(state.get("researcher_agent"), 160),
        "coordinator_agent": _safe_text(state.get("coordinator_agent"), 160),
        "timing": {key: _safe_text(timing.get(key), 64) for key in (
            "started_at", "finalization_start_at", "deadline_at", "final_deadline_at"
        ) if timing.get(key) is not None},
        "goal": {key: _safe_scalar(goal.get(key)) for key in (
            "status", "createdAt", "updatedAt", "tokensUsed", "timeUsedSeconds", "tokenBudget", "objective_sha256"
        ) if _safe_scalar(goal.get(key)) is not None},
        "progress": {key: _safe_scalar(progress.get(key)) for key in (
            "turns_started", "turns_completed", "denied_requests", "last_turn_id", "last_turn_status",
            "last_turn_error_code", "thread_status", "research_turn_interrupted_at_deadline"
        ) if _safe_scalar(progress.get(key)) is not None},
        "submissions": {
            name: {key: _safe_scalar(value.get(key)) for key in ("state", "at", "thread_id", "turn_id", "objective_sha256")
                   if _safe_scalar(value.get(key)) is not None}
            for name, value in sorted(submissions.items())
            if name in {"thread_start", "goal_set", "final_turn"} and isinstance(value, dict)
        },
        "host_job_ids": sorted({_safe_text(item, 160) for item in state.get("host_job_ids", []) if isinstance(item, str)}),
        "resume_count": state.get("resume_count") if isinstance(state.get("resume_count"), int) else None,
    }


def _recorded_session(path: Path) -> str | None:
    with path.open() as handle:
        for line in handle:
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue
            if not isinstance(event, dict):
                continue
            payload = event.get("payload") if isinstance(event, dict) else None
            if event.get("type") == "session_meta" and isinstance(payload, dict):
                return payload.get("id") if isinstance(payload.get("id"), str) else None
    return None


def _usage_evidence(cfg, state: dict) -> dict:
    window_id = state.get("window_id") if isinstance(state.get("window_id"), str) else None
    thread_id = state.get("thread_id") if isinstance(state.get("thread_id"), str) else None
    source = state.get("thread_path") if isinstance(state.get("thread_path"), str) else None
    ingestion: dict[str, Any] = {"attempted": False, "coverage": "not_available"}
    if window_id and source:
        candidate = Path(source).expanduser()
        try:
            if candidate.is_symlink():
                raise UsageError("thread usage source must not be a symlink")
            if _recorded_session(candidate) != thread_id:
                raise UsageError("thread usage source session does not match agent-run thread_id")
            ingestion["attempted"] = True
            imported = usage.ingest(cfg, str(candidate), window_id)
            ingestion.update(coverage=imported.get("coverage"), records=imported.get("records", 0),
                             source_sha256=_digest_file(candidate.resolve()), source_bytes=candidate.stat().st_size)
        except (OSError, UsageError) as exc:
            ingestion.update(coverage="unavailable", error={"type": type(exc).__name__, "message": _safe_text(str(exc), 240)})

    window_report = None
    window_row = None
    if window_id:
        try:
            window_report = usage.report(cfg, window_id)
            raw_window = window_report.get("window") or {}
            window_row = {key: raw_window.get(key) for key in (
                "id", "agent", "status", "started_at", "ended_at", "output_budget", "accepted_results"
            )}
        except UsageError as exc:
            ingestion.setdefault("error", {"type": type(exc).__name__, "message": _safe_text(str(exc), 240)})

    with Store(cfg) as store:
        window_rows = [dict(row) for row in store.conn.execute(
            "SELECT * FROM usage_records WHERE window_id=? ORDER BY at,provider,session_id,response_id", (window_id,)
        )] if window_id else []
        same_thread = [dict(row) for row in store.conn.execute(
            "SELECT * FROM usage_records WHERE provider='codex' AND session_id=? ORDER BY at,response_id", (thread_id,)
        )] if thread_id else []

    ended_at = window_row.get("ended_at") if window_row else None
    late_rows = [row for row in same_thread if ended_at and row["at"] > usage.timestamp(ended_at)]
    combined: dict[tuple[str, str, str], tuple[str, dict]] = {}
    for boundary, rows in (("research_window", window_rows), ("late_same_native_thread", late_rows)):
        for row in rows:
            combined.setdefault((row["provider"], row["session_id"], row["response_id"]), (boundary, row))

    totals = dict.fromkeys(USAGE_FIELDS, 0)
    late_totals = dict.fromkeys(USAGE_FIELDS, 0)
    records = []
    for boundary, row in sorted(combined.values(), key=lambda pair: (pair[1]["at"], pair[1]["response_id"])):
        record = {
            "provider": row["provider"], "session_id": row["session_id"], "response_id": row["response_id"],
            "at": row["at"], "boundary": boundary, "model": row.get("model"), "effort": row.get("effort"),
            "association": _safe_text(row.get("association"), 240), "source_line": row.get("source_line"),
            "usage": {key: row[key] for key in USAGE_FIELDS},
        }
        records.append(record)
        for key in USAGE_FIELDS:
            totals[key] += row[key]
            if boundary == "late_same_native_thread":
                late_totals[key] += row[key]
    totals["uncached_input_tokens"] = totals["input_tokens"] - totals["cached_input_tokens"]
    late_totals["uncached_input_tokens"] = late_totals["input_tokens"] - late_totals["cached_input_tokens"]
    report_usage = (window_report or {}).get("usage") or {}
    return {
        "window": window_row,
        "ingestion": ingestion,
        "research_window_report": {
            "responses": (window_report or {}).get("responses", 0),
            "usage": {key: report_usage.get(key) for key in (*USAGE_FIELDS, "uncached_input_tokens")},
            "coverage": (window_report or {}).get("coverage", "no_window"),
        },
        "same_thread_late_boundary": {"strictly_after": ended_at, "thread_id": thread_id},
        "records": records,
        "responses": len(records),
        "late_responses": sum(boundary == "late_same_native_thread" for boundary, _row in combined.values()),
        "deduplication_key": ["provider", "session_id", "response_id"],
        "usage": totals,
        "late_usage": late_totals,
    }


def _json_list(value: Any) -> list:
    try:
        parsed = json.loads(value or "[]")
    except (TypeError, json.JSONDecodeError):
        return []
    return parsed if isinstance(parsed, list) else []


def _safe_receipt(value: Any) -> dict:
    if isinstance(value, str):
        try:
            value = json.loads(value)
        except json.JSONDecodeError:
            return {}
    if not isinstance(value, dict):
        return {}
    allowed = ("ok", "proof_accepted", "command_succeeded", "rc", "timeout", "refused",
               "termination_acknowledged", "frontier_fresh", "published", "outcome")
    result = {}
    for key in allowed:
        if key not in value:
            continue
        item = value.get(key)
        if isinstance(item, str):
            result[key] = _redact(item)[:240]
        elif isinstance(item, bool) or isinstance(item, int) or (isinstance(item, float) and math.isfinite(item)) or item is None:
            result[key] = item
    artifact = value.get("artifact")
    if isinstance(artifact, dict) and isinstance(artifact.get("id"), str):
        result["artifact"] = {
            "id": artifact["id"][:80],
            **({"bytes": artifact["bytes"]} if isinstance(artifact.get("bytes"), int) else {}),
            **({"kind": _safe_text(artifact["kind"], 80)} if isinstance(artifact.get("kind"), str) else {}),
        }
    return result


def _job_entry(row: dict) -> dict:
    why = row.get("why") if isinstance(row.get("why"), str) else ""
    argv = _json_list(row.get("argv"))
    return {
        key: row.get(key) for key in (
            "id", "kind", "node", "status", "exit_code", "created_at", "started_at", "finished_at",
            "budget_min", "agent", "memory_max", "peak_mib", "seconds", "operation_id", "stage_ordinal"
        )
    } | {
        "why": _redact(why)[:4096], "why_sha256": _digest_bytes(why.encode()),
        "outputs": [str(item)[:1024] for item in _json_list(row.get("outputs")) if isinstance(item, str)],
        "argv_sha256": _digest_bytes(str(row.get("argv") or "").encode()),
        "command_classification": _classify_recorded_command(argv),
        "result": _safe_receipt(row.get("result_json")),
        "log": {"path_recorded": bool(row.get("log_path")), "content_included": False},
    }


def _operations(store: Store, researcher: str | None, window_id: str | None) -> list[dict]:
    clauses, params = [], []
    if researcher:
        clauses.append("agent=?")
        params.append(researcher)
    if window_id:
        clauses.append("window_id=?")
        params.append(window_id)
    if not clauses:
        return []
    rows = store.conn.execute(
        "SELECT * FROM operations WHERE " + " OR ".join(clauses) + " ORDER BY created_at,id", params
    ).fetchall()
    result = []
    for raw in rows:
        row = dict(raw)
        try:
            spec = json.loads(row.get("spec_json") or "{}")
        except json.JSONDecodeError:
            spec = {}
        spec_stages = spec.get("stages") if isinstance(spec.get("stages"), list) else []
        stages = []
        for stage_row in store.conn.execute(
            "SELECT * FROM operation_stages WHERE operation_id=? ORDER BY ordinal", (row["id"],)
        ):
            stage = dict(stage_row)
            definition = spec_stages[stage["ordinal"]] if stage["ordinal"] < len(spec_stages) and isinstance(spec_stages[stage["ordinal"]], dict) else {}
            stages.append({
                "ordinal": stage["ordinal"], "name": stage["name"], "action": definition.get("action"),
                "status": stage["status"], "attempt": stage["attempt"], "job_id": stage["job_id"],
                "input_hash": stage["input_hash"], "started_at": stage["started_at"], "finished_at": stage["finished_at"],
                "receipt": _safe_receipt(stage.get("result_json")),
            })
        result.append({
            "id": row["id"], "kind": row["kind"], "agent": row["agent"], "node": row["node"],
            "window_id": row["window_id"], "status": row["status"], "created_at": row["created_at"],
            "updated_at": row["updated_at"], "result": _safe_receipt(row.get("result_json")), "stages": stages,
        })
    return result


def _validation(jobs: list[dict], operations: list[dict]) -> dict:
    evidence = []
    explicit = []
    for operation in operations:
        for stage in operation["stages"]:
            action = stage.get("action")
            if action not in VALIDATION_ACTIONS:
                continue
            receipt = stage["receipt"]
            accepted = (
                action in PROOF_RECEIPT_ACTIONS and stage.get("status") == "succeeded"
                and receipt.get("proof_accepted") is True
                and receipt.get("termination_acknowledged") is not False
            )
            item = {
                "source": "operation_stage_receipt", "operation_id": operation["id"], "stage": stage["name"],
                "action": action, "job_id": stage["job_id"], "status": stage["status"],
                "receipt": receipt, "explicit_proof_accepted": accepted,
            }
            evidence.append(item)
            if accepted:
                explicit.append({key: item[key] for key in ("operation_id", "stage", "action", "job_id")})
    for job in jobs:
        classified = job.get("command_classification")
        direct_harness_validation = job.get("kind") == "run" and isinstance(classified, dict)
        if job.get("operation_id") or (job.get("kind") not in {"build", "check", "falsify"} and not direct_harness_validation):
            continue
        item = {
            "source": "job_lifecycle", "job_id": job["id"], "kind": job["kind"], "status": job["status"],
            "exit_code": job["exit_code"], "receipt": job["result"], "explicit_proof_accepted": False,
        }
        if direct_harness_validation:
            item["recorded_command"] = classified
        evidence.append(item)
    return {
        "evidence": evidence,
        "explicit_proof_receipts": explicit,
        "theorem_credit": "not_assessed; exit status and operational receipts require theorem/frontier review",
    }


def _file_entry(cfg, path: Path, origin: str) -> dict:
    resolved = path.resolve()
    try:
        rel = resolved.relative_to(cfg.root.resolve())
    except ValueError as exc:
        raise UsageError(f"inventory path escapes project root: {path}") from exc
    if path.is_symlink():
        raise UsageError(f"inventory script must not be a symlink: {path}")
    stat = path.stat()
    return {"origin": origin, "path": str(rel), "bytes": stat.st_size, "sha256": _digest_file(path)}


def _artifact_scripts(cfg, out_path: Path) -> tuple[list[dict], list[dict]]:
    entries, excluded = [], []
    for root, dirs, files in os.walk(out_path, followlinks=False):
        base = Path(root)
        kept_dirs = []
        for name in sorted(dirs):
            path = base / name
            if path.is_symlink():
                excluded.append({"path": str(path.relative_to(cfg.root)), "reason": "symlink_not_followed"})
            else:
                kept_dirs.append(name)
        dirs[:] = kept_dirs
        for name in sorted(files):
            path = base / name
            if path.suffix.lower() not in SCRIPT_SUFFIXES:
                continue
            if path.is_symlink():
                excluded.append({"path": str(path.relative_to(cfg.root)), "reason": "symlink_not_read"})
                continue
            entries.append(_file_entry(cfg, path, "run_artifact_directory"))
    return entries, excluded


def _changed_tracked_scripts(cfg, state: dict) -> tuple[list[dict], dict]:
    baseline = state.get("baseline_commit")
    if not isinstance(baseline, str) or not re.fullmatch(r"[0-9a-fA-F]{7,64}", baseline):
        return [], {"coverage": "unavailable", "reason": "agent-run state has no trusted baseline_commit"}
    try:
        gitutil.git(cfg, "cat-file", "-e", baseline + "^{commit}")
    except (OSError, RuntimeError):
        return [], {"coverage": "unavailable", "reason": "baseline_commit is not a local commit", "baseline_commit": baseline}
    current = set(gitutil.git(cfg, "ls-files", "-z").split("\x00"))
    original = set(gitutil.git(cfg, "ls-tree", "-r", "--name-only", "-z", baseline).split("\x00"))
    tracked = current | original
    entries, excluded = [], []
    for rel in gitutil.changed_files(cfg, baseline):
        if rel not in tracked or Path(rel).suffix.lower() not in SCRIPT_SUFFIXES:
            continue
        path = cfg.root / rel
        if not path.exists():
            entries.append({"origin": "changed_tracked_script", "path": rel, "state": "deleted"})
        elif path.is_symlink():
            excluded.append({"path": rel, "reason": "symlink_not_read"})
        elif path.is_file():
            entries.append(_file_entry(cfg, path, "changed_tracked_script"))
    return entries, {
        "coverage": "baseline_to_current_worktree", "baseline_commit": baseline,
        "current_head": gitutil.head_sha(cfg), "excluded": excluded,
    }


def _inline_from_argv(argv: Any, source: dict) -> list[dict]:
    if not isinstance(argv, list) or not argv or not all(isinstance(item, str) for item in argv):
        return []
    if Path(argv[0]).name.lower() == "env":
        position = 1
        while position < len(argv) and (argv[position].startswith("-") or "=" in argv[position]):
            position += 1
        argv = argv[position:]
        if not argv:
            return []
    executable = Path(argv[0]).name.lower()
    if executable not in {"bash", "dash", "node", "perl", "python", "python3", "ruby", "sh", "zsh"} and not executable.startswith("python3."):
        return []
    entries = []
    for index, token in enumerate(argv[:-1]):
        is_shell_code = executable in {"bash", "dash", "sh", "zsh"} and token.startswith("-") and token.endswith("c")
        if token != "-c" and not is_shell_code:
            continue
        code = argv[index + 1]
        entries.append({
            **source, "interpreter": executable, "argument_index": index + 1,
            "bytes": len(code.encode()), "sha256": _digest_bytes(code.encode()),
            "sanitized_source": _redact(code), "redaction_policy": "credential assignments and bearer values",
        })
    return entries


def _classify_recorded_command(argv: Any) -> dict | None:
    """Recognize direct es validation argv without evaluating shell text."""
    if not isinstance(argv, list) or not argv or not all(isinstance(item, str) for item in argv):
        return None
    values = list(argv)
    if Path(values[0]).name.lower() == "env":
        position = 1
        while position < len(values):
            token = values[position]
            if token in {"-u", "--unset"} and position + 1 < len(values):
                position += 2
            elif token.startswith("-") or "=" in token:
                position += 1
            else:
                break
        values = values[position:]
    if not values:
        return None
    executable = Path(values[0]).name.lower()
    if executable == "es":
        args = values[1:]
    elif executable.startswith("python") and len(values) >= 3 and values[1:3] == ["-m", "es"]:
        args = values[3:]
    else:
        return None
    position = 0
    while position < len(args):
        token = args[position]
        if token in {"--json", "--full"}:
            position += 1
        elif token == "--root" and position + 1 < len(args):
            position += 2
        elif token.startswith("--root="):
            position += 1
        else:
            break
    command = args[position:position + 2]
    accepted = {
        ("audit",), ("build",), ("check",), ("doctor",), ("extract",),
        ("layers", "check"), ("node", "finish"), ("proof", "check"), ("proof", "prove"),
    }
    matched = next((candidate for candidate in accepted if tuple(command[:len(candidate)]) == candidate), None)
    if matched is None:
        return None
    return {
        "tool": "es",
        "command": " ".join(matched),
        "basis": "direct recorded argv; shell command strings are not interpreted",
    }


def _code_inventory(cfg, artifact_root: Path, artifact_boundary: dict, state: dict,
                    raw_jobs: list[dict], operations: list[dict]) -> dict:
    artifacts_found, excluded = _artifact_scripts(cfg, artifact_root)
    changed, changed_boundary = _changed_tracked_scripts(cfg, state)
    inline = []
    for job in raw_jobs:
        inline.extend(_inline_from_argv(_json_list(job.get("argv")), {"source": "job", "job_id": job["id"]}))
    for operation in operations:
        with Store(cfg) as store:
            row = store.conn.execute("SELECT spec_json FROM operations WHERE id=?", (operation["id"],)).fetchone()
        try:
            spec = json.loads(row["spec_json"] if row else "{}")
        except json.JSONDecodeError:
            spec = {}
        for ordinal, stage in enumerate(spec.get("stages", []) if isinstance(spec.get("stages"), list) else []):
            if isinstance(stage, dict):
                inline.extend(_inline_from_argv(stage.get("argv"), {
                    "source": "operation_stage", "operation_id": operation["id"], "stage_ordinal": ordinal,
                }))
    return {
        "artifact_scripts": sorted(artifacts_found, key=lambda item: item["path"]),
        "changed_tracked_scripts": sorted(changed, key=lambda item: item["path"]),
        "inline_commands": sorted(inline, key=lambda item: (
            item.get("source", ""), item.get("job_id", ""), item.get("operation_id", ""), item.get("stage_ordinal", -1), item["argument_index"]
        )),
        "excluded_paths": sorted(excluded, key=lambda item: item["path"]),
        "artifact_boundary": artifact_boundary,
        "changed_tracked_boundary": changed_boundary,
        "execution_policy": "files were hashed and command records parsed as data; no inventoried code was imported or executed",
    }


def _bounded_summary(summary: dict, limit: int) -> dict:
    if not isinstance(limit, int) or isinstance(limit, bool) or limit < 2:
        raise UsageError("compact_limit must be an integer of at least 2 bytes")
    candidates = [
        summary,
        {key: summary[key] for key in (
            "schema_version", "status", "artifact", "counts", "theorem_credit",
            "code_review_required", "final_review_required", "review_required",
        ) if key in summary},
        {"artifact": {"id": summary["artifact"]["id"]}},
        {},
    ]
    for candidate in candidates:
        if len(json.dumps(candidate, ensure_ascii=True, indent=2).encode()) <= limit:
            return candidate
    return {}


def build_review(cfg, out: str | Path, *, artifact_root: str | Path | None = None,
                 compact_limit: int = 4096) -> dict:
    """Create immutable full evidence and return a bounded, conversation-safe summary."""
    out_path, rel, state, state_source = _load_state(cfg, out)
    selected_artifact_root, artifact_boundary = _select_artifact_root(cfg, out_path, state, artifact_root)
    lifecycle = _lifecycle(state)
    usage_evidence = _usage_evidence(cfg, state)
    researcher = state.get("researcher_agent") if isinstance(state.get("researcher_agent"), str) else None
    host_ids = {item for item in state.get("host_job_ids", []) if isinstance(item, str)}
    with Store(cfg) as store:
        raw_jobs = [dict(row) for row in store.conn.execute(
            "SELECT * FROM jobs WHERE agent=? ORDER BY created_at,id", (researcher,)
        )] if researcher else []
        raw_jobs = [row for row in raw_jobs if row["id"] not in host_ids]
        claims = [dict(row) for row in store.conn.execute(
            "SELECT * FROM claims WHERE agent=? ORDER BY claimed_at,node", (researcher,)
        )] if researcher else []
        operations = _operations(store, researcher, state.get("window_id"))
    jobs = [_job_entry(row) for row in raw_jobs]
    validation = _validation(jobs, operations)
    inventory = _code_inventory(cfg, selected_artifact_root, artifact_boundary, state, raw_jobs, operations)
    resources = {
        "jobs": len(jobs),
        "worker_seconds": round(sum(row["seconds"] for row in jobs if isinstance(row.get("seconds"), (int, float))), 1),
        "maximum_job_peak_mib": max((row["peak_mib"] for row in jobs if isinstance(row.get("peak_mib"), (int, float))), default=None),
        "host_job_ids_excluded": sorted(host_ids),
        "association": "jobs submitted directly as researcher_agent; operation linkage is not required",
    }
    pending_jobs = [row["id"] for row in jobs if row.get("status") in PENDING_JOB_STATES]
    unknown_jobs = [row["id"] for row in jobs if row.get("status") in UNKNOWN_JOB_STATES]
    claim_evidence = [{
        "node": row["node"], "agent": row["agent"], "claimed_at": row["claimed_at"], "expires_at": row["expires_at"],
        "note_sha256": _digest_bytes(str(row.get("note") or "").encode()),
    } for row in claims]
    full = {
        "schema_version": 1,
        "kind": "agent-run-review",
        "run": {"out": rel, "state_source": state_source, "lifecycle": lifecycle},
        "usage": usage_evidence,
        "resources": resources,
        "jobs": jobs,
        "operations": operations,
        "unresolved": {"pending_jobs": pending_jobs, "unknown_jobs": unknown_jobs, "active_claims": claim_evidence},
        "validation": validation,
        "code_inventory": inventory,
        "review_requirements": {
            "code_review_required": bool(inventory["artifact_scripts"] or inventory["changed_tracked_scripts"] or inventory["inline_commands"]),
            "final_review_required": True,
            "interpretation": "an empty code inventory does not waive mathematical and receipt review",
        },
        "source_boundaries": {
            "state": "whitelisted lifecycle fields from the exact hashed agent-run.json",
            "usage": "research-window records plus same Codex session records strictly after the recorded window end; stable response key union",
            "resources": "jobs whose agent exactly equals researcher_agent, excluding recorded host job IDs",
            "claims": "currently active claims whose agent exactly equals researcher_agent",
            "validation": "sanitized operation-stage receipts and direct build/check/falsify lifecycle; log bodies and prose diagnostics excluded",
            "code": "non-symlink scripts under run out, baseline_commit-to-worktree tracked scripts, and recorded -c arguments",
        },
        "privacy": "no prompt, model messages, raw conversation, raw job log, or unbounded diagnostic text is included",
    }
    ref = artifacts.put_json(cfg, full, "agent-run-review-v1")
    counts = {
        "responses": usage_evidence["responses"],
        "late_responses": usage_evidence["late_responses"],
        "jobs": len(jobs), "pending_jobs": len(pending_jobs), "unknown_jobs": len(unknown_jobs),
        "active_claims": len(claims), "validation_evidence": len(validation["evidence"]),
        "explicit_proof_receipts": len(validation["explicit_proof_receipts"]),
        "artifact_scripts": len(inventory["artifact_scripts"]),
        "changed_tracked_scripts": len(inventory["changed_tracked_scripts"]),
        "inline_commands": len(inventory["inline_commands"]),
    }
    summary = {
        "schema_version": 1, "status": lifecycle.get("status"), "artifact": ref, "counts": counts,
        "usage": usage_evidence["usage"], "usage_coverage": usage_evidence["ingestion"].get("coverage"),
        "theorem_credit": "not_inferred",
        "code_review_required": bool(sum(counts[key] for key in (
            "artifact_scripts", "changed_tracked_scripts", "inline_commands"
        ))), "final_review_required": True, "review_required": True,
    }
    return _bounded_summary(summary, compact_limit)
