"""Bounded host for one durable Codex native goal.

The host owns transport and time limits.  Codex owns the research loop through the
App Server's durable thread goal; this module never manufactures a chain of turns.
"""
from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import signal
import shutil
import sys
import tempfile
import time
from typing import Any
import uuid

from es import artifacts, bundles, usage
from es.codex_client import CodexClient, ProtocolError
from es.config import Config, load_config, primary_root
from es.errors import CheckFailed, UsageError
from es.jobs import check_outputs, submit_run
from es.store import Store


STATE_NAME = "agent-run.json"
LOCK_NAME = ".agent-run.lock"
FINALIZATION_SECONDS = 30 * 60
MAX_OBJECTIVE_CHARS = 4000  # installed Codex native-goal API, Unicode scalar count
TERMINAL_GOALS = {"paused", "blocked", "usageLimited", "budgetLimited", "complete"}
LIVE_JOB_STATES = {"queued", "starting", "running", "unknown_execution"}
USAGE_KEYS = {
    "inputTokens": "input_tokens",
    "cachedInputTokens": "cached_input_tokens",
    "outputTokens": "output_tokens",
    "reasoningOutputTokens": "reasoning_output_tokens",
    "totalTokens": "total_tokens",
    "cacheWriteInputTokens": "cache_write_input_tokens",
}


class StopRequested(BaseException):
    pass


def _utc(ts: float) -> str:
    return dt.datetime.fromtimestamp(ts, dt.timezone.utc).isoformat().replace("+00:00", "Z")


def _parse_utc(value: str) -> float:
    return dt.datetime.fromisoformat(value.replace("Z", "+00:00")).timestamp()


def _atomic_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix=".agent-run-", dir=path.parent)
    try:
        with os.fdopen(fd, "w") as handle:
            json.dump(value, handle, indent=2, sort_keys=True, allow_nan=False)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(name, path)
    finally:
        Path(name).unlink(missing_ok=True)


def _read_state(out: Path) -> dict:
    path = out / STATE_NAME
    try:
        value = json.loads(path.read_text())
    except FileNotFoundError as exc:
        raise UsageError(f"no agent run at {out}") from exc
    except json.JSONDecodeError as exc:
        raise UsageError(f"invalid agent run state at {path}") from exc
    if not isinstance(value, dict) or value.get("schema_version") != 1:
        raise UsageError(f"unsupported agent run state at {path}")
    return value


def _output(cfg: Config, out: str | Path) -> tuple[Path, str]:
    rel = check_outputs(cfg, [str(out)])[0]
    return (cfg.root / rel).resolve(), rel


def _goal_summary(goal: Any) -> dict | None:
    if not isinstance(goal, dict):
        return None
    keep = ("status", "createdAt", "updatedAt", "tokensUsed", "timeUsedSeconds", "tokenBudget")
    result = {key: goal.get(key) for key in keep if key in goal}
    objective = goal.get("objective")
    if isinstance(objective, str):
        result["objective_sha256"] = hashlib.sha256(objective.encode()).hexdigest()
    return result


def _error_summary(exc: BaseException, code: str | None = None) -> dict:
    # ProtocolError messages intentionally contain only method names and numeric codes.
    text = str(exc).replace("\n", " ")[:240]
    return {"code": code or type(exc).__name__, "message": text, "at": _utc(time.time())}


def _objective(state: dict, prompt: str) -> str:
    timing = state["timing"]
    # App Server canonicalizes a goal by trimming its trailing newline.  Build the
    # same canonical value so a durable goal compares byte-for-byte after resume.
    return f"""{prompt.rstrip()}

Time and execution contract for this native goal:
- Work only in {state['root']} and use the repository's `es` automation and AGENTS.md rules.
- Use only the configured {state['model']} model at {state['effort']} effort. Do not delegate research to another model or agent.
- Lean builds, checks, extraction, falsifiers, and every command over one minute must use guarded `es` jobs. Never run a bare `lake build`.
- The research deadline is {timing['deadline_at']}. Do not mark this goal complete before that instant, even if a result appears early; use the remaining window to verify it and improve the handoff.
- Begin consolidating and checking the final result at {timing['finalization_start_at']}.
- At the research deadline the external host stops further research admission. If work is still active, it pauses this goal and permits exactly one finalization/report turn, ending no later than {timing['final_deadline_at']}.
- The user may interrupt the run. On interruption, preserve exact job, claim, commit, and proof receipts so the same thread can be resumed explicitly.
- Do not extend a deadline or reset a usage limit. Report blocked, usage-limited, incomplete, and failed outcomes honestly.
- Finish with a compact report stating what changed, exact checks and job IDs, commits, open risks, and the safest next action. Update this native goal's status truthfully."""


def _sandbox(primary: Path) -> dict:
    return {
        "type": "workspaceWrite",
        "writableRoots": [str(primary), "/tmp"],
        "networkAccess": True,
        "excludeSlashTmp": False,
        "excludeTmpdirEnvVar": False,
    }


def _thread_config(state: dict) -> dict:
    tool_path = str(Path(state["root"]) / "tools" / "es" / "bin")
    inherited_path = os.environ.get("PATH", "")
    return {
        "model_reasoning_effort": state["effort"],
        "mcp_servers": {"lean-lsp": {"enabled": False}},
        "shell_environment_policy": {
            "inherit": "all",
            "set": {
                "ES_AGENT": state["researcher_agent"],
                "ES_PROJECT_ROOT": state["root"],
                "ES_WINDOW_ID": state["window_id"],
                "PATH": tool_path + (os.pathsep + inherited_path if inherited_path else ""),
            },
        },
    }


def _host_command(cfg: Config, out: Path, resume: bool) -> list[str]:
    # A shared worker can use another checkout's virtualenv/PYTHONPATH.  Load
    # the submitting checkout's host explicitly, including with system Python.
    command = ["/usr/bin/env", f"PYTHONPATH={cfg.root / 'tools' / 'es'}",
               sys.executable, "-m", "es.agent_run", "host", "--root", str(cfg.root), "--out", str(out)]
    if resume:
        command.append("--resume")
    return command


def _live_host(cfg: Config, state: dict) -> dict | None:
    ident = state.get("current_host_job_id")
    if not ident:
        return None
    with Store(cfg) as store:
        job = store.job(ident)
    return job if job and job.get("status") in LIVE_JOB_STATES else None


def submit_agent_run(
    cfg: Config,
    *,
    agent: str,
    out: str,
    prompt: str | None = None,
    model: str | None = None,
    effort: str | None = None,
    hours: float | None = None,
    resume: bool = False,
) -> dict:
    """Freeze a run request and queue its 2 GiB host."""
    out_path, out_rel = _output(cfg, out)
    state_path = out_path / STATE_NAME
    if resume:
        state = _read_state(out_path)
        if Path(state["root"]).resolve() != cfg.root.resolve():
            raise UsageError("resume must use the run's frozen project root")
        for name, supplied in (("model", model), ("effort", effort), ("hours", hours)):
            if supplied is not None and supplied != state[name]:
                raise UsageError(f"--{name} differs from the frozen run")
        if prompt is not None:
            raise UsageError("--prompt cannot be replaced on resume")
        live = _live_host(cfg, state)
        if live:
            raise CheckFailed(f"host job {live['id']} is already {live['status']}")
        if state.get("status") == "complete":
            raise CheckFailed("agent run is already complete")
        thread_submission = (state.get("submissions") or {}).get("thread_start") or {}
        if not state.get("thread_id") and thread_submission.get("state") == "pending":
            raise CheckFailed("thread/start receipt is unknown; refusing to create a duplicate thread")
    else:
        if state_path.exists():
            raise UsageError(f"agent run already exists at {out_path}; use --resume")
        model = model or "gpt-5.6-sol"
        effort = effort or "xhigh"
        hours = 12.0 if hours is None else hours
        if not isinstance(hours, (int, float)) or isinstance(hours, bool) or not math.isfinite(hours) or hours <= 0:
            raise UsageError("--hours must be finite and positive")
        if not prompt:
            raise UsageError("--prompt is required for a new agent run")
        source = Path(prompt).expanduser().resolve()
        if not source.is_file():
            raise UsageError("--prompt must name a readable local file")
        data = source.read_bytes()
        try:
            data.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise UsageError("--prompt must be UTF-8 text") from exc
        prompt_ref = artifacts.put(cfg, data, "agent-run-prompt-v1")
        codex_executable = shutil.which("codex")
        if not codex_executable:
            raise UsageError("codex executable is not available on PATH")
        out_path.mkdir(parents=True, exist_ok=True)
        state = {
            "schema_version": 1,
            "status": "configured",
            "phase": "configured",
            "created_at": _utc(time.time()),
            "root": str(cfg.root.resolve()),
            "primary_root": str(primary_root(cfg.root).resolve()),
            "out": str(out_path),
            "model": model,
            "effort": effort,
            "hours": float(hours),
            "codex_executable": str(Path(codex_executable).resolve()),
            "researcher_agent": f"codex:agent-run-{uuid.uuid4().hex[:16]}",
            "source": {"path": str(source), "artifact": prompt_ref, "sha256": prompt_ref["id"]},
            "host_job_ids": [],
            "resume_count": 0,
            "submissions": {},
            "progress": {"turns_started": 0, "turns_completed": 0, "denied_requests": 0},
        }
        # Native goals have a smaller text limit than ordinary user messages.
        # Validate before starting any session; use full microsecond UTC lengths.
        preview = state | {"timing": {
            key: "2000-01-01T00:00:00.123456Z"
            for key in ("deadline_at", "finalization_start_at", "final_deadline_at")
        }}
        objective_chars = len(_objective(preview, data.decode("utf-8")))
        if objective_chars > MAX_OBJECTIVE_CHARS:
            raise UsageError(
                f"goal with execution contract is {objective_chars} characters; limit is {MAX_OBJECTIVE_CHARS}. "
                "Shorten the prompt or reference a reviewed instruction file. No session was started."
            )
        _atomic_json(state_path, state)

    # queue=True closes the admission race between a sandboxed CLI and the external worker.
    command = _host_command(cfg, out_path, resume)
    try:
        job = submit_run(
            cfg,
            command=command,
            why="Host one bounded durable Codex native-goal research run",
            outputs=[out_rel],
            agent=agent,
            memory_max="2G",
            budget_min=max(1, math.ceil(float(state["hours"]) * 60 + 31)),
            queue=True,
        )
    except Exception as exc:
        state["status"] = "submission_failed"
        state["last_error"] = _error_summary(exc, "host_submission_failed")
        _atomic_json(state_path, state)
        raise
    state.setdefault("host_job_ids", []).append(job["id"])
    state["current_host_job_id"] = job["id"]
    state["status"] = "queued"
    state["phase"] = "host_queued"
    if resume:
        state["resume_count"] = int(state.get("resume_count", 0)) + 1
    _atomic_json(state_path, state)
    return {"run": status_agent_run(cfg, out), "job": job}


def status_agent_run(cfg: Config, out: str | Path) -> dict:
    out_path, _ = _output(cfg, out)
    state = _read_state(out_path)
    timing = state.get("timing") or {}
    remaining = None
    if timing.get("deadline_at"):
        remaining = max(0, round(_parse_utc(timing["deadline_at"]) - time.time()))
    return {
        key: state.get(key)
        for key in (
            "status", "phase", "model", "effort", "hours", "thread_id", "window_id",
            "current_host_job_id", "goal", "usage", "progress", "last_error", "handoff",
        )
        if state.get(key) is not None
    } | {
        "out": str(out_path),
        "deadline_at": timing.get("deadline_at"),
        "final_deadline_at": timing.get("final_deadline_at"),
        "remaining_seconds": remaining,
    }


class AgentHost:
    def __init__(self, cfg: Config, out: Path, *, explicit_resume: bool = False, client_class=CodexClient) -> None:
        self.cfg = cfg
        self.out = out
        self.path = out / STATE_NAME
        self.state = _read_state(out)
        self.explicit_resume = explicit_resume
        self.client_class = client_class
        self.client: CodexClient | None = None
        self._last_save_monotonic = 0.0
        self._resumed_turn: dict | None = None

    def _record_turn(self, turn: dict) -> dict:
        """Keep lifecycle evidence only, never provider messages or turn items."""
        error = turn.get("error")
        code = error.get("codexErrorInfo") if isinstance(error, dict) else None
        if isinstance(code, dict):
            code = next(iter(code), None)
        summary = {
            "id": turn.get("id"), "status": turn.get("status"),
            "error_code": code if isinstance(code, str) else None,
            "completed_at": turn.get("completedAt"),
        }
        progress = self.state.setdefault("progress", {})
        progress["last_turn_id"] = summary["id"]
        progress["last_turn_status"] = summary["status"]
        progress.pop("last_turn_error_code", None)
        if summary["error_code"]:
            progress["last_turn_error_code"] = summary["error_code"][:80]
        if summary["status"] == "inProgress" and isinstance(summary["id"], str):
            progress["active_turn_id"] = summary["id"]
        elif summary["id"] == progress.get("active_turn_id"):
            progress.pop("active_turn_id", None)
        return summary

    def _capture_terminal_turn(self) -> None:
        # A blocked goal notification can precede turn/completed. Read the durable
        # receipt before closing the connection, so provider failure is distinguishable
        # from a mathematical blocker without retaining conversation text.
        try:
            page = self._request("thread/turns/list", {
                "threadId": self.state["thread_id"], "limit": 1,
                "sortDirection": "desc", "itemsView": "summary",
            }, 5)
            turns = page.get("data")
            if isinstance(turns, list) and turns and isinstance(turns[0], dict):
                self._record_turn(turns[0])
        except (ProtocolError, TimeoutError, OSError) as exc:
            self.state["terminal_receipt_error"] = _error_summary(exc, "turn_receipt_unavailable")

    def save(self) -> None:
        self.state["updated_at"] = _utc(time.time())
        _atomic_json(self.path, self.state)
        self._last_save_monotonic = time.monotonic()

    def on_event(self, message: dict) -> None:
        method = message.get("method")
        params = message.get("params") or {}
        if not isinstance(params, dict):
            return
        thread = self.state.get("thread_id")
        if params.get("threadId") not in (None, thread):
            return
        progress = self.state.setdefault("progress", {})
        changed = False
        if method == "client/request-denied":
            progress["denied_requests"] = int(progress.get("denied_requests", 0)) + 1
            changed = True
        elif method == "thread/goal/updated":
            self.state["goal"] = _goal_summary(params.get("goal"))
            changed = True
        elif method == "thread/tokenUsage/updated":
            raw = params.get("tokenUsage") or {}
            if isinstance(raw, dict) and isinstance(raw.get("total"), dict):
                raw = raw["total"]
            if isinstance(raw, dict):
                self.state["usage"] = {
                    target: raw[source]
                    for source, target in USAGE_KEYS.items()
                    if isinstance(raw.get(source), int) and not isinstance(raw.get(source), bool)
                }
                changed = True
        elif method == "turn/started":
            turn = params.get("turn") or {}
            if isinstance(turn, dict) and isinstance(turn.get("id"), str):
                progress["active_turn_id"] = turn["id"]
                progress["turns_started"] = int(progress.get("turns_started", 0)) + 1
                changed = True
        elif method == "turn/completed":
            turn = params.get("turn") or {}
            if isinstance(turn, dict):
                self._record_turn(turn)
                progress["turns_completed"] = int(progress.get("turns_completed", 0)) + 1
                changed = True
        elif method == "thread/status/changed":
            raw = params.get("status")
            if isinstance(raw, dict):
                progress["thread_status"] = raw.get("type")
            elif isinstance(raw, str):
                progress["thread_status"] = raw
            changed = True
        # Token counters can update frequently.  Keep their latest in memory and flush
        # at most twice a minute; lifecycle events remain immediately durable.
        if changed and (method != "thread/tokenUsage/updated" or time.monotonic() - self._last_save_monotonic >= 30):
            progress["last_event_at"] = _utc(time.time())
            self.save()

    def _request(self, method: str, params: dict, timeout: float = 30) -> dict:
        assert self.client is not None
        return self.client.request(method, params, timeout)

    def _new_thread(self) -> None:
        self.state.setdefault("submissions", {})["thread_start"] = {
            "state": "pending", "at": _utc(time.time()),
        }
        self.state.update(status="starting", phase="thread_submission_pending")
        self.save()
        primary = Path(self.state["primary_root"])
        result = self._request("thread/start", {
            "model": self.state["model"],
            "cwd": self.state["root"],
            "approvalPolicy": "never",
            "approvalsReviewer": "user",
            "sandbox": "workspace-write",
            "runtimeWorkspaceRoots": [str(primary), "/tmp"],
            # A fresh thread has no rollout to resume yet.  Install the stable
            # researcher identity here, before activating its first goal turn.
            "config": _thread_config(self.state),
            "developerInstructions": (
                "Run the user's repository research autonomously under its AGENTS.md rules. "
                f"Use only the configured {self.state['model']} model at {self.state['effort']} effort; do not delegate. "
                "All Lean/compiler and long-running work must use "
                "the repository's guarded es commands. Never request approval: the host denies it."
            ),
        })
        thread = result.get("thread") or {}
        ident = thread.get("id") if isinstance(thread, dict) else None
        if not isinstance(ident, str):
            raise ProtocolError("thread/start returned no thread receipt")
        self.state["thread_id"] = ident
        self.state.setdefault("submissions", {})["thread_start"] = {
            "state": "received", "thread_id": ident, "at": _utc(time.time()),
        }
        self.state["thread_path"] = thread.get("path")
        self.state["actual_model"] = result.get("model")
        self.state["actual_effort"] = result.get("reasoningEffort")
        started = time.time()
        deadline = started + float(self.state["hours"]) * 3600
        self.state["timing"] = {
            "started_at": _utc(started),
            "finalization_start_at": _utc(max(started, deadline - FINALIZATION_SECONDS)),
            "deadline_at": _utc(deadline),
            "final_deadline_at": _utc(deadline + FINALIZATION_SECONDS),
        }
        self.state.update(status="starting", phase="thread_received")
        self.save()  # durable receipt before any request can start a model turn
        if result.get("model") != self.state["model"] or result.get("reasoningEffort") != self.state["effort"]:
            raise ProtocolError("thread/start did not honor the frozen model and effort")

    def _ensure_window(self) -> None:
        if self.state.get("window_id"):
            return
        ident = usage.begin(
            self.cfg,
            self.state["researcher_agent"],
            f"Codex native goal: {self.out.name}",
            cohort="native-goal-research",
            arm="sol",
            pair_key=self.state["source"]["sha256"],
        )
        self.state["window_id"] = ident
        self.state["phase"] = "window_started"
        self.save()

    def _update_settings(self) -> None:
        primary = Path(self.state["primary_root"])
        self._request("thread/settings/update", {
            "threadId": self.state["thread_id"],
            "approvalPolicy": "never",
            "approvalsReviewer": "user",
            "cwd": self.state["root"],
            "model": self.state["model"],
            "effort": self.state["effort"],
            "sandboxPolicy": _sandbox(primary),
        })
        self.state["phase"] = "thread_configured"
        self.save()

    def _resume_thread(self) -> None:
        primary = Path(self.state["primary_root"])
        params = {
            "threadId": self.state["thread_id"],
            "path": self.state.get("thread_path"),
            "model": self.state["model"],
            "cwd": self.state["root"],
            "approvalPolicy": "never",
            "approvalsReviewer": "user",
            "sandbox": "workspace-write",
            "runtimeWorkspaceRoots": [str(primary), "/tmp"],
            "config": _thread_config(self.state),
            "excludeTurns": True,
            "initialTurnsPage": {"limit": 1, "sortDirection": "desc", "itemsView": "summary"},
        }
        result = self._request("thread/resume", params)
        if result.get("model") != self.state["model"] or result.get("reasoningEffort") != self.state["effort"]:
            raise ProtocolError("thread/resume did not honor the frozen model and effort")
        page = result.get("initialTurnsPage") or {}
        turns = page.get("data") if isinstance(page, dict) else None
        self._resumed_turn = None
        if isinstance(turns, list) and turns and isinstance(turns[0], dict):
            self._resumed_turn = self._record_turn(turns[0])
        self._update_settings()

    def _prompt(self) -> str:
        return artifacts.read(self.cfg, self.state["source"]["artifact"]["id"]).decode("utf-8")

    def _ensure_goal(self) -> None:
        objective = _objective(self.state, self._prompt())
        digest = hashlib.sha256(objective.encode()).hexdigest()
        self.state["objective_sha256"] = digest
        existing = self._request("thread/goal/get", {"threadId": self.state["thread_id"]}).get("goal")
        if existing is not None:
            if not isinstance(existing, dict) or hashlib.sha256(str(existing.get("objective", "")).encode()).hexdigest() != digest:
                raise ProtocolError("durable goal objective differs from the frozen run")
            self.state["goal"] = _goal_summary(existing)
            goal_submission = self.state.setdefault("submissions", {}).get("goal_set")
            if isinstance(goal_submission, dict) and goal_submission.get("state") == "pending":
                self.state["submissions"]["goal_set"] = {
                    "state": "reconciled", "objective_sha256": digest, "at": _utc(time.time()),
                }
            status = existing.get("status")
            before_deadline = time.time() < _parse_utc(self.state["timing"]["deadline_at"])
            turn = self._resumed_turn or {}
            # Only an explicitly resumed, freshly confirmed capacity failure may
            # reactivate a blocked goal. Quota/policy errors and genuine blockers
            # stay blocked; a later goal update also invalidates this evidence.
            capacity_failure = (
                status == "blocked" and turn.get("status") == "failed"
                and turn.get("error_code") == "serverOverloaded"
                and isinstance(turn.get("completed_at"), (int, float))
                and isinstance(existing.get("updatedAt"), (int, float))
                and turn["completed_at"] >= existing["updatedAt"]
            )
            if self.explicit_resume and before_deadline and (status in {"paused", "usageLimited"} or capacity_failure):
                existing = self._request("thread/goal/set", {
                    "threadId": self.state["thread_id"], "status": "active",
                }).get("goal")
                self.state["goal"] = _goal_summary(existing)
                if capacity_failure:
                    self.state.setdefault("provider_recoveries", []).append({
                        "at": _utc(time.time()), "turn_id": turn["id"],
                        "error_code": "serverOverloaded", "explicit_resume": True,
                    })
            self.state.update(status="running", phase="goal_active")
            self.save()
            return
        self.state.setdefault("submissions", {})["goal_set"] = {
            "state": "pending", "objective_sha256": digest, "at": _utc(time.time()),
        }
        self.state.update(status="starting", phase="goal_submission_pending")
        self.save()
        goal = self._request("thread/goal/set", {
            "threadId": self.state["thread_id"], "objective": objective, "status": "active",
        }).get("goal")
        if not isinstance(goal, dict):
            raise ProtocolError("thread/goal/set returned no goal receipt")
        returned_objective = goal.get("objective")
        if not isinstance(returned_objective, str) or hashlib.sha256(returned_objective.encode()).hexdigest() != digest:
            raise ProtocolError("thread/goal/set did not preserve the frozen objective")
        self.state["submissions"]["goal_set"] = {
            "state": "received", "objective_sha256": digest, "at": _utc(time.time()),
        }
        self.state["goal"] = _goal_summary(goal)
        self.state.update(status="running", phase="goal_active")
        self.save()

    def _goal_status(self) -> str | None:
        goal = self.state.get("goal") or {}
        return goal.get("status") if isinstance(goal, dict) else None

    def _wait_research(self) -> str:
        deadline = _parse_utc(self.state["timing"]["deadline_at"])
        while time.time() < deadline:
            status = self._goal_status()
            if status in TERMINAL_GOALS:
                if status == "complete":
                    self.state.update(status="premature_complete", phase="terminal_before_deadline")
                    self.save()
                    return "premature_complete"
                if status == "blocked":
                    self._capture_terminal_turn()
                self.state.update(status="goal_" + status, phase="terminal_goal")
                self.save()
                return status
            timeout = min(55.0, max(0.01, deadline - time.time()))
            try:
                assert self.client is not None
                event = self.client.event(timeout)
            except TimeoutError:
                continue
            self.on_event(event)
        return "deadline"

    def _wait_active_turn(self, until: float) -> None:
        progress = self.state.setdefault("progress", {})
        while progress.get("active_turn_id") and time.time() < until:
            try:
                assert self.client is not None
                event = self.client.event(min(55.0, max(0.01, until - time.time())))
            except TimeoutError:
                continue
            self.on_event(event)
        active = progress.get("active_turn_id")
        if active:
            self._request("turn/interrupt", {"threadId": self.state["thread_id"], "turnId": active})
            progress.pop("active_turn_id", None)
            progress["research_turn_interrupted_at_deadline"] = active
            self.save()

    def _finalize(self) -> str:
        final_deadline = _parse_utc(self.state["timing"]["final_deadline_at"])
        current = self._request("thread/goal/get", {"threadId": self.state["thread_id"]}).get("goal")
        self.state["goal"] = _goal_summary(current)
        if isinstance(current, dict) and current.get("status") == "complete":
            self.state.update(status="complete", phase="complete")
            self.save()
            return "complete"
        if isinstance(current, dict) and current.get("status") == "active":
            paused = self._request("thread/goal/set", {
                "threadId": self.state["thread_id"], "status": "paused",
            }).get("goal")
            self.state["goal"] = _goal_summary(paused)
        self.state.update(status="finalizing", phase="goal_paused_at_deadline")
        self.save()
        self._wait_active_turn(min(final_deadline, time.time() + 55))
        # The research turn can finish its report while we wait for it to stop.
        # Recheck before admitting a redundant paid finalization turn.
        current = self._request("thread/goal/get", {"threadId": self.state["thread_id"]}).get("goal")
        self.state["goal"] = _goal_summary(current)
        if isinstance(current, dict) and current.get("status") == "complete":
            self.state.update(status="complete", phase="complete")
            self.save()
            return "complete"
        if time.time() >= final_deadline:
            self.state.update(status="needs_finalization", phase="final_deadline_elapsed")
            self.save()
            return "needs_finalization"
        final_submission = self.state.setdefault("submissions", {}).get("final_turn") or {}
        if self.state.get("final_turn_id"):
            turn_id = self.state["final_turn_id"]
        elif final_submission.get("state") == "pending":
            self.state.update(status="needs_finalization", phase="final_turn_receipt_unknown")
            self.save()
            return "needs_finalization"
        else:
            self.state["submissions"]["final_turn"] = {
                "state": "pending", "at": _utc(time.time()),
            }
            self.state.update(status="finalizing", phase="final_turn_submission_pending")
            self.save()
            response = self._request("turn/start", {
                "threadId": self.state["thread_id"],
                "model": self.state["model"],
                "effort": self.state["effort"],
                "cwd": self.state["root"],
                "approvalPolicy": "never",
                "approvalsReviewer": "user",
                "sandboxPolicy": _sandbox(Path(self.state["primary_root"])),
                "runtimeWorkspaceRoots": [self.state["primary_root"], "/tmp"],
                "turnTrigger": "goal-finalization",
                "input": [{"type": "text", "text": (
                    "The research deadline has passed and the native goal is paused. Do no new research. "
                    "Use this single finalization turn to inspect the existing workspace and recorded es receipts, "
                    "finish only already-started checks when safe, and give the compact final report required by the "
                    f"goal. The hard stop is {self.state['timing']['final_deadline_at']}. Mark the native goal complete "
                    "only if the report and its claims are supported; otherwise leave it paused or blocked and state why."
                ), "text_elements": []}],
            }, timeout=30)
            turn = response.get("turn") or {}
            turn_id = turn.get("id") if isinstance(turn, dict) else None
            if not isinstance(turn_id, str):
                raise ProtocolError("turn/start returned no final-turn receipt")
            self.state["final_turn_id"] = turn_id
            self.state["submissions"]["final_turn"] = {
                "state": "received", "turn_id": turn_id, "at": _utc(time.time()),
            }
            self.state["phase"] = "final_turn_active"
            self.state.setdefault("progress", {})["active_turn_id"] = turn_id
            self.save()
        while time.time() < final_deadline:
            progress = self.state.setdefault("progress", {})
            if progress.get("last_turn_id") == turn_id:
                goal = self._request("thread/goal/get", {"threadId": self.state["thread_id"]}).get("goal")
                self.state["goal"] = _goal_summary(goal)
                if isinstance(goal, dict) and goal.get("status") == "complete":
                    self.state.update(status="complete", phase="complete")
                    self.save()
                    return "complete"
                self.state.update(status="needs_finalization", phase="final_turn_did_not_complete_goal")
                self.save()
                return "needs_finalization"
            try:
                assert self.client is not None
                event = self.client.event(min(55.0, max(0.01, final_deadline - time.time())))
            except TimeoutError:
                continue
            self.on_event(event)
        active = self.state.setdefault("progress", {}).get("active_turn_id")
        if active == turn_id:
            self._request("turn/interrupt", {"threadId": self.state["thread_id"], "turnId": turn_id})
        self.state.update(status="needs_finalization", phase="final_turn_timed_out")
        self.save()
        return "needs_finalization"

    def _account(self, complete: bool) -> None:
        window_id = self.state.get("window_id")
        source = self.state.get("thread_path")
        if window_id and source:
            try:
                imported = usage.ingest(self.cfg, source, window_id)
                report = usage.report(self.cfg, window_id)
                totals = report.get("usage") or {}
                self.state["usage"] = {
                    key: totals.get(key)
                    for key in ("input_tokens", "cached_input_tokens", "output_tokens", "reasoning_output_tokens", "uncached_input_tokens")
                    if totals.get(key) is not None
                }
                self.state["usage"]["responses"] = report.get("responses")
                self.state["usage"]["coverage"] = imported.get("coverage")
            except (OSError, UsageError) as exc:
                self.state["accounting_error"] = _error_summary(exc)
        if window_id:
            try:
                current = usage.window(self.cfg, window_id)
                target = "complete" if complete else "paused"
                if current["status"] != target:
                    usage.transition(self.cfg, window_id, target)
                handoff = bundles.handoff(self.cfg, window_id)
                self.state["handoff"] = artifacts.put_json(self.cfg, handoff, "agent-run-handoff-v1")
            except (OSError, UsageError) as exc:
                self.state["accounting_error"] = _error_summary(exc)
        self.save()

    def _pause_for_stop(self) -> None:
        try:
            if self.client and self.state.get("thread_id") and self._goal_status() == "active":
                goal = self._request("thread/goal/set", {"threadId": self.state["thread_id"], "status": "paused"}, 10).get("goal")
                self.state["goal"] = _goal_summary(goal)
        except Exception as exc:
            self.state["last_error"] = _error_summary(exc, "pause_failed")
        self.state.update(status="paused_by_user", phase="interrupted")
        self.save()

    def run(self) -> int:
        ambient_job = os.environ.get("ES_JOB_ID")
        if ambient_job:
            ids = self.state.setdefault("host_job_ids", [])
            if ambient_job not in ids:
                ids.append(ambient_job)
            self.state["current_host_job_id"] = ambient_job
        self.state.update(status="starting", phase="app_server_starting")
        self.save()
        try:
            client_options: dict[str, Any] = {"on_event": self.on_event}
            if self.client_class is CodexClient:
                client_options["command"] = [
                    self.state["codex_executable"], "app-server", "--stdio",
                    "-c", "mcp_servers.lean-lsp.enabled=false",
                ]
            with self.client_class(**client_options) as client:
                self.client = client
                try:
                    client.initialize()
                    thread_submission = (self.state.get("submissions") or {}).get("thread_start") or {}
                    if not self.state.get("thread_id"):
                        if thread_submission.get("state") == "pending":
                            raise ProtocolError("thread receipt unknown; refusing duplicate thread/start")
                        self._ensure_window()
                        self._new_thread()
                        # The thread is live in this App Server process, but has no
                        # persisted rollout until its first turn.  Do not resume it.
                        self._update_settings()
                    else:
                        if not self.explicit_resume:
                            raise ProtocolError("an existing thread requires explicit --resume")
                        self._ensure_window()
                        current_window = usage.window(self.cfg, self.state["window_id"])
                        if current_window["status"] == "paused":
                            usage.transition(self.cfg, self.state["window_id"], "active")
                        self._resume_thread()
                    self._ensure_goal()
                    outcome = self._wait_research()
                    if outcome == "deadline":
                        outcome = self._finalize()
                    complete = outcome == "complete"
                    self._account(complete)
                    return 0 if complete else 1
                except StopRequested:
                    # Pause while App Server is still connected, then let the context close it.
                    self._pause_for_stop()
                    self._account(False)
                    return 130
        except (ProtocolError, TimeoutError, OSError) as exc:
            # Reconnection is deliberately an explicit operator action.  A pending request
            # is retained so resume cannot silently duplicate it.
            self.state["last_error"] = _error_summary(exc, "transport_or_protocol")
            pending = self.state.get("submissions") or {}
            if (pending.get("thread_start") or {}).get("state") == "pending" and not self.state.get("thread_id"):
                self.state.update(status="needs_reconciliation", phase="thread_receipt_unknown")
            elif (pending.get("goal_set") or {}).get("state") == "pending":
                self.state.update(status="needs_resume", phase="goal_receipt_unknown")
            elif (pending.get("final_turn") or {}).get("state") == "pending":
                self.state.update(status="needs_finalization", phase="final_turn_receipt_unknown")
            else:
                self.state.update(status="needs_resume", phase="transport_stopped")
            self.save()
            self._account(False)
            return 1
        finally:
            self.client = None


def run_host(root: Path, out: Path, *, resume: bool = False, client_class=CodexClient) -> int:
    cfg = load_config(root)
    out_path, _ = _output(cfg, out)
    lock_path = out_path / LOCK_NAME
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a+") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise CheckFailed(f"an agent host already owns {out_path}")
        host = AgentHost(cfg, out_path, explicit_resume=resume, client_class=client_class)
        previous: dict[int, Any] = {}

        def stop(signum, _frame):
            raise StopRequested(f"signal {signum}")

        for signum in (signal.SIGINT, signal.SIGTERM):
            previous[signum] = signal.signal(signum, stop)
        try:
            return host.run()
        finally:
            for signum, handler in previous.items():
                signal.signal(signum, handler)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="python -m es.agent_run")
    sub = parser.add_subparsers(dest="command", required=True)
    host = sub.add_parser("host")
    host.add_argument("--root", required=True, type=Path)
    host.add_argument("--out", required=True, type=Path)
    host.add_argument("--resume", action="store_true")
    args = parser.parse_args(argv)
    try:
        rc = run_host(args.root.resolve(), args.out, resume=args.resume)
        cfg = load_config(args.root.resolve())
        print(json.dumps(status_agent_run(cfg, args.out), sort_keys=True), flush=True)
        return rc
    except (UsageError, CheckFailed) as exc:
        print(json.dumps({"status": "host_error", "error": str(exc)[:240]}, sort_keys=True), flush=True)
        return exc.exit_code


if __name__ == "__main__":
    raise SystemExit(main())
