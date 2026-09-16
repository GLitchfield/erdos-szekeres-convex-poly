from __future__ import annotations

import json
from pathlib import Path
import time

import pytest

from es import agent_run
from es.codex_client import HOST_MARKERS, clean_environment
from es.errors import CheckFailed, UsageError


def _submit(cfg, project, monkeypatch, *, hours=0.03):
    prompt = project / "prompt.txt"
    prompt.write_text("Prove the selected result without leaking this text to state.")
    captured = {}

    def fake_submit(_cfg, **kwargs):
        captured.update(kwargs)
        return {
            "id": "job-test", "status": "queued", "memory_max": kwargs["memory_max"],
            "log_path": "/tmp/job-test.log",
        }

    monkeypatch.setattr(agent_run, "submit_run", fake_submit)
    monkeypatch.setattr(agent_run.shutil, "which", lambda _name: "/opt/codex/bin/codex")
    result = agent_run.submit_agent_run(
        cfg,
        agent="codex:operator",
        out="runs/native",
        prompt=str(prompt),
        model="gpt-5.6-sol",
        effort="xhigh",
        hours=hours,
    )
    return project / "runs/native", result, captured


def test_clean_environment_removes_enclosing_job_reservation():
    source = {name: "outer" for name in HOST_MARKERS} | {"PATH": "/bin", "KEEP": "yes"}
    cleaned = clean_environment(source)
    assert all(name not in cleaned for name in HOST_MARKERS)
    assert cleaned["PATH"] == "/bin"
    assert cleaned["KEEP"] == "yes"


def test_submit_freezes_source_and_queues_two_gib_host(cfg, project, monkeypatch):
    out, result, captured = _submit(cfg, project, monkeypatch)
    state_text = (out / agent_run.STATE_NAME).read_text()
    state = json.loads(state_text)

    assert captured["queue"] is True
    assert captured["memory_max"] == "2G"
    assert captured["budget_min"] == 33
    assert captured["outputs"] == ["runs/native"]
    assert captured["command"][:2] == ["/usr/bin/env", f"PYTHONPATH={cfg.root / 'tools' / 'es'}"]
    assert captured["command"][-2:] == ["--out", str(out.resolve())]
    assert state["codex_executable"] == "/opt/codex/bin/codex"
    assert state["researcher_agent"].startswith("codex:agent-run-")
    assert state["source"]["artifact"]["id"] == state["source"]["sha256"]
    assert "Prove the selected result" not in state_text
    assert result["run"]["status"] == "queued"


@pytest.mark.parametrize("hours", [0, -1, float("inf"), float("nan")])
def test_hours_must_be_finite_and_positive(cfg, project, monkeypatch, hours):
    prompt = project / "prompt.txt"
    prompt.write_text("task")
    monkeypatch.setattr(agent_run.shutil, "which", lambda _name: "/bin/codex")
    with pytest.raises(UsageError, match="finite and positive"):
        agent_run.submit_agent_run(cfg, agent="tester", out="runs/bad", prompt=str(prompt), hours=hours)


def test_oversized_goal_is_rejected_before_job_submission(cfg, project, monkeypatch):
    prompt = project / "long-prompt.md"
    prompt.write_text("x" * 4001)
    monkeypatch.setattr(agent_run.shutil, "which", lambda _name: "/bin/codex")

    def unexpected(*_args, **_kwargs):
        raise AssertionError("oversized goal must not create a host job")

    monkeypatch.setattr(agent_run, "submit_run", unexpected)
    with pytest.raises(UsageError, match="limit is 4000"):
        agent_run.submit_agent_run(cfg, agent="tester", out="runs/oversized", prompt=str(prompt))
    assert not (project / "runs/oversized" / agent_run.STATE_NAME).exists()


def test_resume_refuses_unknown_thread_start_receipt(cfg, project, monkeypatch):
    out, _result, _captured = _submit(cfg, project, monkeypatch)
    path = out / agent_run.STATE_NAME
    state = json.loads(path.read_text())
    state["status"] = "needs_reconciliation"
    state["phase"] = "thread_receipt_unknown"
    state["submissions"]["thread_start"] = {"state": "pending"}
    agent_run._atomic_json(path, state)

    called = False

    def should_not_submit(*_args, **_kwargs):
        nonlocal called
        called = True

    monkeypatch.setattr(agent_run, "submit_run", should_not_submit)
    with pytest.raises(CheckFailed, match="receipt is unknown"):
        agent_run.submit_agent_run(cfg, agent="tester", out="runs/native", resume=True)
    assert called is False


def test_event_state_is_whitelisted_and_token_writes_are_throttled(cfg, project, monkeypatch):
    out, _result, _captured = _submit(cfg, project, monkeypatch)
    host = agent_run.AgentHost(cfg, out)
    host.state["thread_id"] = "thread-1"
    saves = []
    monkeypatch.setattr(host, "save", lambda: saves.append(json.loads(json.dumps(host.state))))
    host._last_save_monotonic = time.monotonic() - 31

    host.on_event({"method": "item/completed", "params": {
        "threadId": "thread-1", "item": {"type": "agentMessage", "text": "secret conversation"},
    }})
    assert saves == []
    host.on_event({"method": "thread/tokenUsage/updated", "params": {
        "threadId": "thread-1", "turnId": "turn-1",
        "tokenUsage": {"total": {
            "inputTokens": 10, "cachedInputTokens": 4, "outputTokens": 3,
            "reasoningOutputTokens": 2, "totalTokens": 13,
        }, "last": {"inputTokens": 1}},
    }})
    assert host.state["usage"] == {
        "input_tokens": 10, "cached_input_tokens": 4, "output_tokens": 3,
        "reasoning_output_tokens": 2, "total_tokens": 13,
    }
    assert len(saves) == 1
    host._last_save_monotonic = time.monotonic()
    host.on_event({"method": "thread/tokenUsage/updated", "params": {
        "threadId": "thread-1", "turnId": "turn-1",
        "tokenUsage": {"total": {"outputTokens": 4}},
    }})
    assert len(saves) == 1
    assert "secret conversation" not in json.dumps(host.state)


def test_resume_applies_exact_model_environment_and_sandbox(cfg, project, monkeypatch):
    out, _result, _captured = _submit(cfg, project, monkeypatch)
    host = agent_run.AgentHost(cfg, out)
    host.state.update(
        thread_id="thread-1", thread_path="/tmp/thread.jsonl", researcher_agent="codex:thread-1",
        window_id="window-1",
    )
    calls = []

    class Requests:
        def request(self, method, params, timeout=30):
            calls.append((method, params, timeout))
            if method == "thread/resume":
                return {"model": "gpt-5.6-sol", "reasoningEffort": "xhigh", "initialTurnsPage": None}
            return {}

    host.client = Requests()
    monkeypatch.setattr(host, "save", lambda: None)
    host._resume_thread()

    resume = calls[0][1]
    policy = calls[1][1]
    env = resume["config"]["shell_environment_policy"]["set"]
    assert resume["model"] == "gpt-5.6-sol"
    assert resume["approvalPolicy"] == "never"
    assert env["ES_AGENT"] == "codex:thread-1"
    assert env["ES_WINDOW_ID"] == "window-1"
    assert env["PATH"].startswith(str(project / "tools/es/bin") + ":")
    assert resume["config"]["mcp_servers"]["lean-lsp"]["enabled"] is False
    assert policy["sandboxPolicy"]["type"] == "workspaceWrite"
    assert policy["sandboxPolicy"]["writableRoots"] == [str(project), "/tmp"]
    assert policy["approvalsReviewer"] == "user"


def test_fresh_start_sets_identity_without_resuming_unpersisted_thread(cfg, project, monkeypatch):
    out, _result, _captured = _submit(cfg, project, monkeypatch)
    calls = []

    class Client:
        def __init__(self, **_kwargs):
            pass

        def __enter__(self):
            return self

        def __exit__(self, *_args):
            pass

        def initialize(self):
            return {}

        def request(self, method, params, timeout=30):
            calls.append((method, params, timeout))
            if method == "thread/start":
                return {
                    "model": "gpt-5.6-sol", "reasoningEffort": "xhigh",
                    "thread": {"id": "thread-fresh", "path": "/tmp/not-materialized.jsonl"},
                }
            if method == "thread/settings/update":
                return {}
            raise AssertionError(f"unexpected request {method}")

    host = agent_run.AgentHost(cfg, out, client_class=Client)
    researcher = host.state["researcher_agent"]
    monkeypatch.setattr(host, "_ensure_goal", lambda: None)
    monkeypatch.setattr(host, "_wait_research", lambda: "paused")
    monkeypatch.setattr(host, "_account", lambda _complete: None)

    assert host.run() == 1
    assert [method for method, _params, _timeout in calls] == ["thread/start", "thread/settings/update"]
    start = calls[0][1]
    shell = start["config"]["shell_environment_policy"]["set"]
    assert shell["ES_AGENT"] == researcher
    assert shell["ES_WINDOW_ID"] == host.state["window_id"]
    assert host.state["thread_id"] == "thread-fresh"
    assert host.state["researcher_agent"] == researcher


def test_paused_goal_exits_research_wait_immediately(cfg, project, monkeypatch):
    out, _result, _captured = _submit(cfg, project, monkeypatch)
    host = agent_run.AgentHost(cfg, out)
    host.state["timing"] = {"deadline_at": agent_run._utc(time.time() + 600)}
    host.state["goal"] = {"status": "paused"}
    monkeypatch.setattr(host, "save", lambda: None)
    assert host._wait_research() == "paused"
    assert host.state["status"] == "goal_paused"


def test_blocked_notification_captures_later_provider_failure_receipt(cfg, project, monkeypatch):
    out, _result, _captured = _submit(cfg, project, monkeypatch)
    host = agent_run.AgentHost(cfg, out)
    host.state.update(thread_id="thread-1", goal={"status": "blocked"})
    host.state["timing"] = {"deadline_at": agent_run._utc(time.time() + 600)}
    host.state["progress"]["active_turn_id"] = "turn-1"

    class Client:
        def request(self, method, params, timeout=30):
            assert method == "thread/turns/list"
            assert params["itemsView"] == "summary"
            assert timeout == 5
            return {"data": [{"id": "turn-1", "status": "failed", "completedAt": 123,
                              "error": {"codexErrorInfo": "serverOverloaded", "message": "PRIVATE"},
                              "items": [{"text": "PRIVATE"}]}]}

    host.client = Client()
    assert host._wait_research() == "blocked"
    saved = json.loads((out / agent_run.STATE_NAME).read_text())
    assert saved["progress"]["last_turn_error_code"] == "serverOverloaded"
    assert "active_turn_id" not in saved["progress"]
    assert "PRIVATE" not in json.dumps(saved)


@pytest.mark.parametrize("code,expired,later_update,explicit,should_resume", [
    ("serverOverloaded", False, False, True, True),
    ("serverOverloaded", True, False, True, False),
    ("serverOverloaded", False, True, True, False),
    ("serverOverloaded", False, False, False, False),
    ("usageLimitExceeded", False, False, True, False),
    ("rateLimitExceeded", False, False, True, False),
    ("misalignmentPolicyViolation", False, False, True, False),
    (None, False, False, True, False),
])
def test_explicit_capacity_resume_requires_current_failure_and_frozen_deadline(
    cfg, project, monkeypatch, code, expired, later_update, explicit, should_resume,
):
    out, _result, _captured = _submit(cfg, project, monkeypatch)
    host = agent_run.AgentHost(cfg, out, explicit_resume=explicit)
    completed = int(time.time()) - 10
    host.state.update(thread_id="thread-1", window_id="window-1", timing={
        "deadline_at": agent_run._utc(time.time() + (-1 if expired else 600)),
        "finalization_start_at": agent_run._utc(time.time() + 300),
        "final_deadline_at": agent_run._utc(time.time() + 2400),
    })
    timing = dict(host.state["timing"])
    objective = agent_run._objective(host.state, host._prompt())
    calls = []

    class Client:
        def request(self, method, params, timeout=30):
            calls.append((method, params))
            if method == "thread/resume":
                return {"model": "gpt-5.6-sol", "reasoningEffort": "xhigh", "initialTurnsPage": {
                    "data": [{"id": "turn-1", "status": "failed", "completedAt": completed,
                              "error": {"codexErrorInfo": code}}]}}
            if method == "thread/settings/update":
                return {}
            if method == "thread/goal/get":
                return {"goal": {"objective": objective, "status": "blocked",
                                 "updatedAt": completed + int(later_update)}}
            assert method == "thread/goal/set" and should_resume
            assert params == {"threadId": "thread-1", "status": "active"}
            return {"goal": {"objective": objective, "status": "active"}}

    host.client = Client()
    host._resume_thread()
    host._ensure_goal()
    assert any(m == "thread/goal/set" for m, _ in calls) is should_resume
    assert host.state["goal"]["status"] == ("active" if should_resume else "blocked")
    assert host.state["timing"] == timing
    assert bool(host.state.get("provider_recoveries")) is should_resume


def test_goal_objective_is_canonical_across_resume(cfg, project, monkeypatch):
    out, _result, _captured = _submit(cfg, project, monkeypatch)
    host = agent_run.AgentHost(cfg, out)
    host.state.update(
        thread_id="thread-1", window_id="window-1",
        timing={
            "deadline_at": agent_run._utc(time.time() + 600),
            "finalization_start_at": agent_run._utc(time.time() + 300),
            "final_deadline_at": agent_run._utc(time.time() + 2400),
        },
    )
    objective = agent_run._objective(host.state, host._prompt())
    assert not objective.endswith("\n")
    methods = []

    class Requests:
        def request(self, method, params, timeout=30):
            methods.append(method)
            assert method == "thread/goal/get"
            return {"goal": {"objective": objective, "status": "active"}}

    host.client = Requests()
    monkeypatch.setattr(host, "save", lambda: None)
    host._ensure_goal()
    assert methods == ["thread/goal/get"]
    assert host.state["goal"]["objective_sha256"] == host.state["objective_sha256"]


def test_research_completion_while_pausing_does_not_start_final_turn(cfg, project, monkeypatch):
    out, _result, _captured = _submit(cfg, project, monkeypatch)
    host = agent_run.AgentHost(cfg, out)
    host.state.update(thread_id="thread-1", goal={"status": "active"})
    host.state["timing"] = {"final_deadline_at": agent_run._utc(time.time() + 600)}
    finished = False
    methods = []

    class Requests:
        def request(self, method, params, timeout=30):
            methods.append(method)
            if method == "thread/goal/get":
                return {"goal": {"status": "complete" if finished else "active"}}
            if method == "thread/goal/set":
                return {"goal": {"status": "paused"}}
            raise AssertionError(f"unexpected paid request {method}")

    def finish(_until):
        nonlocal finished
        finished = True

    host.client = Requests()
    monkeypatch.setattr(host, "_wait_active_turn", finish)
    monkeypatch.setattr(host, "save", lambda: None)
    assert host._finalize() == "complete"
    assert methods == ["thread/goal/get", "thread/goal/set", "thread/goal/get"]
    assert "final_turn_id" not in host.state


def test_final_turn_pending_receipt_is_never_duplicated(cfg, project, monkeypatch):
    out, _result, _captured = _submit(cfg, project, monkeypatch)
    host = agent_run.AgentHost(cfg, out)
    host.state.update(thread_id="thread-1", goal={"status": "paused"})
    host.state["timing"] = {"final_deadline_at": agent_run._utc(time.time() + 600)}
    host.state["submissions"]["final_turn"] = {"state": "pending"}
    methods = []

    class Requests:
        def request(self, method, params, timeout=30):
            methods.append(method)
            if method == "thread/goal/get":
                return {"goal": {"status": "paused", "objective": "", "tokensUsed": 1}}
            raise AssertionError(f"unexpected request {method}")

    host.client = Requests()
    monkeypatch.setattr(host, "save", lambda: None)
    assert host._finalize() == "needs_finalization"
    assert methods == ["thread/goal/get", "thread/goal/get"]
    assert host.state["phase"] == "final_turn_receipt_unknown"


def test_status_reads_compact_file_without_model_contact(cfg, project, monkeypatch):
    out, _result, _captured = _submit(cfg, project, monkeypatch)
    state = agent_run.status_agent_run(cfg, "runs/native")
    assert state["out"] == str(out.resolve())
    assert state["status"] == "queued"
    assert "source" not in state
    assert "codex_executable" not in state
