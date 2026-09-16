from __future__ import annotations

import json
import re
import subprocess

import pytest

from es import artifacts, run_delivery
from es.errors import UsageError
from es.store import Store


THREAD = "018f0d7e-89ab-7def-8123-456789abcdef"
OTHER_THREAD = "018f0d7e-89ab-7def-8123-456789abcdee"


class FakeTransport:
    def __init__(self, result=None):
        self.result = result or {"status": "accepted", "model_requests": 1, "exit_code": 0}
        self.calls = []

    def queue(self, thread, message):
        self.calls.append((thread, message))
        return dict(self.result)


def _enable(cfg):
    cfg.raw.setdefault("automation", {}).setdefault("delivery", {})["enabled"] = True


def _verify(cfg, monkeypatch, transport=None):
    transport = transport or FakeTransport()
    result = run_delivery.request_verification(cfg, "tester", THREAD, transport)
    assert result["status"] == "challenge_sent"
    challenge = re.search(r"es-delivery-verification:([A-Za-z0-9_-]+)", transport.calls[0][1]).group(1)
    monkeypatch.setenv("CODEX_THREAD_ID", THREAD)
    confirmed = run_delivery.confirm_verification(cfg, "tester", challenge)
    assert confirmed["verified"]
    return transport, challenge


def _payload(**extra):
    return {
        "type": "run_terminal",
        "run": "runs/native",
        "status": "complete",
        "goal_status": "complete",
        "host_status": "succeeded",
        "accepted_results_reported": 1,
        **extra,
    }


def test_emit_is_idempotent_immutable_and_packet_is_bounded(cfg):
    review = artifacts.put_json(cfg, {"review": "full"}, "run-review-v1")
    payload = _payload(summary="private " * 2000, jobs={"succeeded": 49, "failed": 1},
                       review={"artifact": review}, theorem_credit="not_inferred",
                       secret="never inline")
    first = run_delivery.emit(cfg, "tester", "run-finished", payload)
    second = run_delivery.emit(cfg, "tester", "run-finished", dict(payload))

    assert first["created"] is True
    assert second["created"] is False
    assert first["packet"]["id"] == second["packet"]["id"]
    raw = artifacts.read(cfg, first["packet"]["id"])
    packet = json.loads(raw)
    assert len(raw) <= run_delivery.PACKET_LIMIT
    assert packet["type"] == "run_terminal"
    assert packet["accepted_results_reported"] == 1
    assert packet["jobs"] == {"failed": 1, "succeeded": 49}
    assert packet["review"]["id"] == review["id"]
    assert packet["theorem_credit"] == "not_inferred"
    assert "secret" not in packet
    assert artifacts.read(cfg, packet["detail"]["id"]) == artifacts.canonical(payload)

    with pytest.raises(UsageError, match="different immutable payload"):
        run_delivery.emit(cfg, "tester", "run-finished", _payload(status="blocked"))


@pytest.mark.parametrize("bad_type", [None, "job_terminal", "proof_finished"])
def test_emit_accepts_only_top_level_run_event_types(cfg, bad_type):
    with pytest.raises(UsageError, match="payload type"):
        run_delivery.emit(cfg, "tester", "bad", {"type": bad_type})


def test_queue_transport_uses_argv_without_overriding_thread_settings():
    seen = {}

    def runner(argv, **kwargs):
        seen["argv"] = argv
        seen["kwargs"] = kwargs
        return subprocess.CompletedProcess(argv, 0)

    result = run_delivery.QueueTransport(executable="/opt/codex", runner=runner).queue(THREAD, "message")
    assert result == {"status": "accepted", "model_requests": 1, "exit_code": 0}
    assert seen["argv"] == ["/opt/codex", "queue", "--thread", THREAD, "--message", "message"]
    assert not any(flag in seen["argv"] for flag in
                   ("--model", "--sandbox", "--approve-for-me", "--dangerously-bypass-approvals-and-sandbox"))
    assert seen["kwargs"]["timeout"] == run_delivery.QUEUE_TIMEOUT_SECONDS
    assert seen["kwargs"]["stdout"] is subprocess.DEVNULL
    assert seen["kwargs"]["stderr"] is subprocess.DEVNULL


def test_queue_transport_timeout_and_unsupported_are_redacted():
    def timeout(_argv, **_kwargs):
        raise subprocess.TimeoutExpired("secret command", 20, output=b"secret output")

    uncertain = run_delivery.QueueTransport(runner=timeout).queue(THREAD, "private message")
    assert uncertain["status"] == "submission_uncertain"
    assert "secret" not in json.dumps(uncertain)

    def missing(_argv, **_kwargs):
        raise FileNotFoundError("secret path")

    unsupported = run_delivery.QueueTransport(runner=missing).queue(THREAD, "private message")
    assert unsupported["status"] == "transport_unsupported"
    assert unsupported["model_requests"] == 0
    assert "secret" not in json.dumps(unsupported)


def test_verify_requires_exact_uuid_and_confirm_requires_exact_owning_thread(cfg, monkeypatch):
    transport = FakeTransport()
    with pytest.raises(UsageError, match="canonical UUID"):
        run_delivery.request_verification(cfg, "tester", "session-name", transport)
    assert transport.calls == []

    result = run_delivery.request_verification(cfg, "tester", THREAD, transport)
    assert result["status"] == "challenge_sent"
    assert transport.calls[0][0] == THREAD
    challenge = re.search(r"es-delivery-verification:([A-Za-z0-9_-]+)", transport.calls[0][1]).group(1)
    monkeypatch.setenv("CODEX_THREAD_ID", OTHER_THREAD)
    with pytest.raises(UsageError, match="does not match"):
        run_delivery.confirm_verification(cfg, "tester", challenge)
    assert not run_delivery.status(cfg, "tester")["verified"]

    monkeypatch.setenv("CODEX_THREAD_ID", THREAD)
    confirmed = run_delivery.confirm_verification(cfg, "tester", challenge)
    repeated = run_delivery.confirm_verification(cfg, "tester", challenge)
    assert confirmed["verified"] and not confirmed["already_confirmed"]
    assert repeated["verified"] and repeated["already_confirmed"]
    state = run_delivery.status(cfg, "tester")
    assert state["verified"] and not state["callback_ready"]
    assert "challenge" not in state


def test_lost_verification_receipt_can_confirm_but_is_never_resubmitted(cfg, monkeypatch):
    transport = FakeTransport({"status": "submission_uncertain", "model_requests": 1})
    first = run_delivery.request_verification(cfg, "tester", THREAD, transport)
    second = run_delivery.request_verification(cfg, "tester", THREAD, transport)
    assert first["status"] == second["status"] == "submission_uncertain"
    assert len(transport.calls) == 1

    challenge = re.search(r"es-delivery-verification:([A-Za-z0-9_-]+)", transport.calls[0][1]).group(1)
    monkeypatch.setenv("CODEX_THREAD_ID", THREAD)
    assert run_delivery.confirm_verification(cfg, "tester", challenge)["verified"]


def test_abandon_uncertain_verification_preserves_audit_and_allows_explicit_fresh_attempt(cfg, monkeypatch):
    first_transport = FakeTransport({"status": "submission_uncertain", "model_requests": 1})
    run_delivery.request_verification(cfg, "tester", THREAD, first_transport)
    stale = re.search(
        r"es-delivery-verification:([A-Za-z0-9_-]+)", first_transport.calls[0][1]
    ).group(1)

    abandoned = run_delivery.abandon_verification(cfg, "tester", THREAD)
    assert abandoned == {
        "status": "abandoned", "agent": "tester", "thread": THREAD,
        "previous_status": "submission_uncertain", "verified": False,
        "model_requests": 0, "queue_cancelled": False, "queue_retried": False,
    }
    with Store(cfg) as store:
        records = [json.loads(row[0]) for row in store.conn.execute(
            "SELECT value FROM automation_meta WHERE key LIKE ?",
            (run_delivery._CHALLENGE_PREFIX + "%",),
        )]
    assert len(records) == 1
    assert records[0]["status"] == "abandoned"
    assert records[0]["abandoned_from"] == "submission_uncertain"

    second_transport = FakeTransport()
    fresh_result = run_delivery.request_verification(cfg, "tester", THREAD, second_transport)
    fresh = re.search(
        r"es-delivery-verification:([A-Za-z0-9_-]+)", second_transport.calls[0][1]
    ).group(1)
    assert fresh_result["status"] == "challenge_sent"
    assert fresh != stale
    assert len(first_transport.calls) == len(second_transport.calls) == 1

    monkeypatch.setenv("CODEX_THREAD_ID", THREAD)
    with pytest.raises(UsageError, match="stale"):
        run_delivery.confirm_verification(cfg, "tester", stale)
    assert run_delivery.confirm_verification(cfg, "tester", fresh)["verified"]


def test_abandon_verification_requires_current_exact_thread(cfg):
    transport = FakeTransport({"status": "submission_uncertain", "model_requests": 1})
    run_delivery.request_verification(cfg, "tester", THREAD, transport)
    with pytest.raises(UsageError, match="does not match"):
        run_delivery.abandon_verification(cfg, "tester", OTHER_THREAD)
    assert run_delivery.status(cfg, "tester")["challenge"]["status"] == "submission_uncertain"


def test_unsupported_verification_stays_explicitly_unverified(cfg, monkeypatch):
    transport = FakeTransport({"status": "transport_unsupported", "model_requests": 0})
    result = run_delivery.request_verification(cfg, "tester", THREAD, transport)
    assert result["status"] == "transport_unsupported"
    assert not run_delivery.status(cfg, "tester")["verified"]
    challenge = re.search(r"es-delivery-verification:([A-Za-z0-9_-]+)", transport.calls[0][1]).group(1)
    monkeypatch.setenv("CODEX_THREAD_ID", THREAD)
    with pytest.raises(UsageError, match="supported transport"):
        run_delivery.confirm_verification(cfg, "tester", challenge)
    assert run_delivery.request_verification(cfg, "tester", THREAD, transport)["model_requests"] == 0
    assert len(transport.calls) == 1


def test_dispatch_is_disabled_or_unverified_without_transport_calls(cfg):
    transport = FakeTransport()
    run_delivery.emit(cfg, "tester", "terminal", _payload())
    assert run_delivery.dispatch(cfg, "tester", transport)["status"] == "disabled"
    _enable(cfg)
    assert run_delivery.dispatch(cfg, "tester", transport)["status"] == "unverified"
    assert transport.calls == []


def test_dispatch_selects_one_run_event_and_never_legacy_delivery(cfg, monkeypatch):
    _enable(cfg)
    _verify(cfg, monkeypatch)
    with Store(cfg) as store:
        store.conn.execute(
            "INSERT INTO deliveries(id,operation_id,agent,payload_json,status,created_at,attempts) "
            "VALUES (?,?,?,?,?,?,?)",
            ("legacy", "operation", "tester", json.dumps({"status": "failed"}), "pending", 0, 0),
        )
    run_delivery.emit(cfg, "tester", "event-1", _payload(run="runs/one"))
    run_delivery.emit(cfg, "tester", "event-2", _payload(run="runs/two"))
    transport = FakeTransport()

    first = run_delivery.dispatch(cfg, "tester", transport)
    assert first["status"] == "delivered"
    assert first["event_id"] == "event-1"
    assert len(transport.calls) == 1
    assert transport.calls[0][0] == THREAD
    assert transport.calls[0][1].startswith("[es-run-event:event-1]\n")
    first_packet = json.loads(transport.calls[0][1].split("\n", 1)[1])
    assert first_packet["run"] == "runs/one"
    with Store(cfg) as store:
        assert store.conn.execute("SELECT status FROM deliveries WHERE id='legacy'").fetchone()[0] == "pending"

    second = run_delivery.dispatch(cfg, "tester", transport)
    assert second["event_id"] == "event-2"
    assert len(transport.calls) == 2
    assert run_delivery.dispatch(cfg, "tester", transport)["status"] == "no_delivery"
    assert len(transport.calls) == 2


def test_uncertain_dispatch_is_never_retried_automatically(cfg, monkeypatch):
    _enable(cfg)
    _verify(cfg, monkeypatch)
    run_delivery.emit(cfg, "tester", "uncertain-event", _payload())
    transport = FakeTransport({"status": "submission_uncertain", "model_requests": 1})

    first = run_delivery.dispatch(cfg, "tester", transport)
    second = run_delivery.dispatch(cfg, "tester", transport)
    assert first["status"] == "submission_uncertain"
    assert second["status"] == "needs_reconciliation"
    assert second["needs_reconciliation"] == 1
    assert len(transport.calls) == 1
    state = run_delivery.status(cfg, "tester")
    assert state["events"] == {"submission_uncertain": 1}
    assert state["verified"] and not state["callback_ready"]
    assert state["needs_reconciliation"] == 1


def test_unresolved_event_blocks_later_pending_dispatch(cfg, monkeypatch):
    _enable(cfg)
    _verify(cfg, monkeypatch)
    run_delivery.emit(cfg, "tester", "uncertain-event", _payload(run="runs/one"))
    run_delivery.dispatch(
        cfg, "tester", FakeTransport({"status": "transport_unsupported", "model_requests": 0})
    )
    run_delivery.emit(cfg, "tester", "later-event", _payload(run="runs/two"))
    transport = FakeTransport()

    result = run_delivery.dispatch(cfg, "tester", transport)
    assert result["status"] == "needs_reconciliation"
    assert result["needs_reconciliation"] == 1
    assert result["model_requests"] == 0
    assert transport.calls == []
    state = run_delivery.status(cfg, "tester")
    assert state["events"] == {"pending": 1, "transport_unsupported": 1}
    assert state["needs_reconciliation"] == 1
    assert not state["callback_ready"]


def test_active_reverification_suspends_existing_binding(cfg, monkeypatch):
    _enable(cfg)
    _verify(cfg, monkeypatch)
    run_delivery.emit(cfg, "tester", "held", _payload())
    transport = FakeTransport({"status": "submission_uncertain", "model_requests": 1})
    run_delivery.request_verification(cfg, "tester", OTHER_THREAD, transport)

    callback = FakeTransport()
    assert run_delivery.dispatch(cfg, "tester", callback)["status"] == "unverified"
    assert callback.calls == []


def test_status_and_commands_make_no_idle_model_requests(cfg, monkeypatch):
    import es.commands.run_delivery as commands

    state = commands.delivery_status(type("Ctx", (), {"cfg": cfg, "agent": "tester"})()).payload
    assert state["model_requests"] == 0
    assert state["events"] == {}
    assert state["needs_reconciliation"] == 0

    called = {}
    monkeypatch.setattr(run_delivery, "request_verification", lambda _cfg, agent, thread: {
        "status": "challenge_sent", "agent": agent, "thread": thread, "model_requests": 1,
    })
    verified = commands.delivery_verify(type("Ctx", (), {"cfg": cfg, "agent": "tester"})(), THREAD)
    assert verified.payload["thread"] == THREAD
