"""Verified, durable callback delivery for top-level agent-run events.

This outbox is intentionally separate from :mod:`es.delivery`: agent-run
completion is the only event family selected here.  Queue submission has an
unavoidable crash boundary, so an attempted submission without a receipt is
left uncertain and is never retried automatically.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import secrets
import subprocess
import time
import uuid
from typing import Any, Callable

from es import artifacts
from es.errors import UsageError
from es.store import Store


SCHEMA_VERSION = 1
PACKET_LIMIT = 2048
QUEUE_TIMEOUT_SECONDS = 20
ALLOWED_EVENT_TYPES = {"run_terminal", "infrastructure_blocked"}

_PREFIX = "run-delivery-v1:"
_EVENT_PREFIX = _PREFIX + "event:"
_BINDING_PREFIX = _PREFIX + "binding:"
_ACTIVE_PREFIX = _PREFIX + "active-challenge:"
_CHALLENGE_PREFIX = _PREFIX + "challenge:"
_TOKEN = re.compile(r"^[A-Za-z0-9_-]{20,64}$")


def _digest(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def _agent_key(prefix: str, agent: str) -> str:
    return prefix + _digest(agent)


def _event_key(agent: str, event_id: str) -> str:
    return _EVENT_PREFIX + _digest(agent + "\0" + event_id)


def _challenge_key(token: str) -> str:
    return _CHALLENGE_PREFIX + _digest(token)


def _identity(value: str, label: str, limit: int = 256) -> str:
    if not isinstance(value, str) or not value or len(value) > limit:
        raise UsageError(f"{label} must be a nonempty string of at most {limit} characters")
    if any(ord(char) < 32 or ord(char) == 127 for char in value):
        raise UsageError(f"{label} must not contain control characters")
    return value


def _thread_id(value: str | None) -> str:
    if not isinstance(value, str):
        raise UsageError("an exact CODEX thread UUID is required")
    try:
        parsed = uuid.UUID(value)
    except (ValueError, AttributeError) as exc:
        raise UsageError("thread must be an exact canonical UUID, not a session name") from exc
    if str(parsed) != value:
        raise UsageError("thread must be an exact canonical UUID, not a session name")
    return value


def _load(row: Any, label: str) -> dict:
    try:
        value = json.loads(row[0] if not isinstance(row, str) else row)
    except (TypeError, json.JSONDecodeError) as exc:
        raise UsageError(f"corrupt {label} metadata") from exc
    if not isinstance(value, dict) or value.get("schema_version") != SCHEMA_VERSION:
        raise UsageError(f"unsupported {label} metadata")
    return value


def _get(conn, key: str, label: str) -> dict | None:
    row = conn.execute("SELECT value FROM automation_meta WHERE key=?", (key,)).fetchone()
    return _load(row, label) if row else None


def _put(conn, key: str, value: dict) -> None:
    conn.execute(
        "INSERT OR REPLACE INTO automation_meta(key,value) VALUES (?,?)",
        (key, json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)),
    )


def _artifact_ref(value: Any) -> dict | None:
    if not isinstance(value, dict) or not isinstance(value.get("id"), str):
        return None
    if not re.fullmatch(r"[0-9a-f]{64}", value["id"]):
        return None
    return {key: value[key] for key in ("id", "bytes", "kind") if key in value}


def _brief_jobs(value: Any) -> list[Any] | dict[str, int] | None:
    if isinstance(value, dict):
        return {
            str(key)[:80]: count
            for key, count in list(sorted(value.items(), key=lambda item: str(item[0])))[:12]
            if isinstance(count, int) and not isinstance(count, bool)
        }
    if not isinstance(value, list):
        return None
    result: list[Any] = []
    for item in value[:8]:
        if isinstance(item, str):
            result.append(item[:160])
        elif isinstance(item, dict):
            brief = {
                key: item[key]
                for key in ("id", "status", "exit_code", "seconds", "peak_mib")
                if key in item and isinstance(item[key], (str, int, float, bool, type(None)))
            }
            result.append(brief)
    return result


def _packet(event_id: str, payload: dict, detail: dict) -> dict:
    packet: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "event_id": event_id,
        "type": payload["type"],
        "detail": detail,
    }
    for key in (
        "run", "status", "phase", "goal_status", "job_id", "host_status", "reason", "theorem_credit",
    ):
        value = payload.get(key)
        if isinstance(value, str):
            packet[key] = value[:240]
    if isinstance(payload.get("accepted_results_reported"), int):
        packet["accepted_results_reported"] = payload["accepted_results_reported"]
    if isinstance(payload.get("summary"), str):
        packet["summary"] = payload["summary"][:480]
    unresolved = payload.get("unresolved_job_ids")
    if isinstance(unresolved, list):
        packet["unresolved_job_ids"] = [str(value)[:160] for value in unresolved[:8]]
    jobs = _brief_jobs(payload.get("jobs"))
    if jobs is not None:
        packet["jobs"] = jobs
    review_value = payload.get("review")
    review = _artifact_ref(review_value)
    if review is None and isinstance(review_value, dict):
        review = _artifact_ref(review_value.get("artifact"))
    if review:
        packet["review"] = review
    # Drop optional fields from least to most useful until the hard packet
    # bound is met.  The complete input remains in ``detail``.
    for key in ("jobs", "unresolved_job_ids", "summary", "reason", "phase", "host_status"):
        if len(artifacts.canonical(packet)) <= PACKET_LIMIT:
            break
        packet.pop(key, None)
    if len(artifacts.canonical(packet)) > PACKET_LIMIT:
        raise UsageError("event identifiers and artifact references exceed the callback packet limit")
    return packet


class QueueTransport:
    """Installed ``codex queue`` transport with no setting overrides.

    Output is sent to ``DEVNULL``: no provider, filesystem, or authentication
    diagnostic can leak into durable state.  The retained result is therefore
    both bounded and redacted.
    """

    def __init__(
        self,
        executable: str = "codex",
        timeout: int = QUEUE_TIMEOUT_SECONDS,
        runner: Callable[..., Any] = subprocess.run,
    ):
        self.executable = executable
        self.timeout = timeout
        self.runner = runner

    def queue(self, thread: str, message: str) -> dict:
        argv = [self.executable, "queue", "--thread", thread, "--message", message]
        try:
            completed = self.runner(
                argv,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=self.timeout,
                check=False,
            )
        except FileNotFoundError:
            return {"status": "transport_unsupported", "model_requests": 0,
                    "reason": "installed codex client was not found"}
        except OSError:
            return {"status": "transport_unsupported", "model_requests": 0,
                    "reason": "installed codex queue transport could not start"}
        except subprocess.TimeoutExpired:
            return {"status": "submission_uncertain", "model_requests": 1,
                    "reason": "codex queue timed out; output suppressed"}
        if completed.returncode == 0:
            return {"status": "accepted", "model_requests": 1, "exit_code": 0}
        return {"status": "submission_uncertain", "model_requests": 1,
                "exit_code": int(completed.returncode),
                "reason": "codex queue returned no acceptance receipt; output suppressed"}


def emit(cfg, agent: str, event_id: str, payload: dict) -> dict:
    """Idempotently store one top-level run event and its immutable packet."""
    agent = _identity(agent, "agent")
    event_id = _identity(event_id, "event ID")
    if not isinstance(payload, dict) or payload.get("type") not in ALLOWED_EVENT_TYPES:
        allowed = ", ".join(sorted(ALLOWED_EVENT_TYPES))
        raise UsageError(f"run delivery payload type must be one of: {allowed}")
    detail = artifacts.put_json(cfg, payload, "run-delivery-payload-v1")
    packet = _packet(event_id, payload, detail)
    packet_ref = artifacts.put_json(cfg, packet, "run-delivery-packet-v1")
    key = _event_key(agent, event_id)
    with Store(cfg) as store:
        store.conn.execute("BEGIN IMMEDIATE")
        existing = _get(store.conn, key, "run delivery event")
        if existing:
            if existing.get("agent") != agent or existing.get("event_id") != event_id:
                raise UsageError("run delivery event key collision")
            if existing.get("payload_artifact", {}).get("id") != detail["id"]:
                raise UsageError("event ID already names a different immutable payload")
            return {"event_id": event_id, "status": existing["status"],
                    "packet": existing["packet_artifact"], "created": False}
        event = {
            "schema_version": SCHEMA_VERSION,
            "agent": agent,
            "event_id": event_id,
            "event_type": payload["type"],
            "payload_artifact": detail,
            "packet_artifact": packet_ref,
            "status": "pending",
            "created_at": time.time(),
        }
        _put(store.conn, key, event)
    return {"event_id": event_id, "status": "pending", "packet": packet_ref, "created": True}


def _challenge_message(agent: str, token: str) -> str:
    return (
        f"[es-delivery-verification:{token}]\n"
        "A callback binding was requested for this exact Codex thread. "
        f"The coordinator identity is {json.dumps(agent)}. "
        "From this thread, with its existing CODEX_THREAD_ID and ES_AGENT unchanged, run:\n"
        f"tools/es/bin/es delivery confirm --challenge {token}\n"
        "This challenge binds only this thread; do not forward it."
    )


def request_verification(cfg, agent: str, thread: str, transport: Any | None = None) -> dict:
    """Send one challenge to an exact thread; repeated calls never resubmit it."""
    agent = _identity(agent, "agent")
    thread = _thread_id(thread)
    binding_key = _agent_key(_BINDING_PREFIX, agent)
    active_key = _agent_key(_ACTIVE_PREFIX, agent)
    token: str
    with Store(cfg) as store:
        store.conn.execute("BEGIN IMMEDIATE")
        binding = _get(store.conn, binding_key, "run delivery binding")
        active = _get(store.conn, active_key, "active run delivery challenge")
        if binding and binding.get("status") == "verified" and binding.get("thread") == thread and not active:
            return {"status": "already_verified", "agent": agent, "thread": thread,
                    "verified": True, "model_requests": 0}
        if active and active.get("thread") == thread:
            challenge = _get(store.conn, _challenge_key(active["token"]), "run delivery challenge")
            if challenge:
                return {"status": challenge["status"], "agent": agent, "thread": thread,
                        "verified": False, "model_requests": 0, "resubmitted": False}
        token = secrets.token_urlsafe(24)
        challenge = {
            "schema_version": SCHEMA_VERSION,
            "agent": agent,
            "thread": thread,
            "token": token,
            # Persist uncertainty before crossing the process boundary.  A crash
            # at any later point must not cause a blind duplicate queue call.
            "status": "submission_uncertain",
            "requested_at": time.time(),
        }
        _put(store.conn, _challenge_key(token), challenge)
        _put(store.conn, active_key, {
            "schema_version": SCHEMA_VERSION, "agent": agent, "thread": thread, "token": token,
        })
    result = (transport or QueueTransport()).queue(thread, _challenge_message(agent, token))
    state = result.get("status") if isinstance(result, dict) else None
    if state not in {"accepted", "submission_uncertain", "transport_unsupported"}:
        state = "submission_uncertain"
        result = {"status": state, "model_requests": 1,
                  "reason": "queue transport returned an invalid receipt"}
    challenge_status = "challenge_sent" if state == "accepted" else state
    with Store(cfg) as store:
        store.conn.execute("BEGIN IMMEDIATE")
        current = _get(store.conn, _challenge_key(token), "run delivery challenge")
        # Confirmation or explicit abandonment can race the transport return.
        # Neither transition may be overwritten by a late queue receipt.
        if current and current.get("status") == "submission_uncertain":
            current["status"] = challenge_status
            current["receipt_at"] = time.time()
            current["transport"] = {key: result[key] for key in ("status", "model_requests", "exit_code", "reason") if key in result}
            _put(store.conn, _challenge_key(token), current)
    return {"status": challenge_status, "agent": agent, "thread": thread, "verified": False,
            "model_requests": int(result.get("model_requests", 1)), "resubmitted": False}


def confirm_verification(
    cfg,
    agent: str,
    challenge: str,
) -> dict:
    """Confirm a challenge only from the exact thread named in its request."""
    agent = _identity(agent, "agent")
    if not isinstance(challenge, str) or not _TOKEN.fullmatch(challenge):
        raise UsageError("invalid delivery verification challenge")
    thread = _thread_id(os.environ.get("CODEX_THREAD_ID"))
    challenge_key = _challenge_key(challenge)
    binding_key = _agent_key(_BINDING_PREFIX, agent)
    active_key = _agent_key(_ACTIVE_PREFIX, agent)
    with Store(cfg) as store:
        store.conn.execute("BEGIN IMMEDIATE")
        record = _get(store.conn, challenge_key, "run delivery challenge")
        if not record or record.get("token") != challenge:
            raise UsageError("unknown delivery verification challenge")
        if record.get("agent") != agent:
            raise UsageError("challenge belongs to a different coordinator agent")
        if record.get("thread") != thread:
            raise UsageError("CODEX_THREAD_ID does not match the requested callback thread")
        binding = _get(store.conn, binding_key, "run delivery binding")
        if record.get("status") == "confirmed" and binding and binding.get("thread") == thread:
            return {"status": "verified", "agent": agent, "thread": thread,
                    "verified": True, "already_confirmed": True, "model_requests": 0}
        active = _get(store.conn, active_key, "active run delivery challenge")
        if not active or active.get("token") != challenge:
            raise UsageError("delivery verification challenge is stale")
        if record.get("status") not in {"challenge_sent", "submission_uncertain"}:
            raise UsageError("delivery challenge was not accepted by a supported transport")
        now = time.time()
        _put(store.conn, binding_key, {
            "schema_version": SCHEMA_VERSION,
            "agent": agent,
            "thread": thread,
            "status": "verified",
            "verified_at": now,
            "challenge_digest": _digest(challenge),
            "transport": "codex-queue-v1",
        })
        record["status"] = "confirmed"
        record["confirmed_at"] = now
        _put(store.conn, challenge_key, record)
        store.conn.execute("DELETE FROM automation_meta WHERE key=?", (active_key,))
    return {"status": "verified", "agent": agent, "thread": thread,
            "verified": True, "already_confirmed": False, "model_requests": 0}


def abandon_verification(cfg, agent: str, thread: str) -> dict:
    """Retire the active challenge without cancelling or replaying its queue call."""
    agent = _identity(agent, "agent")
    thread = _thread_id(thread)
    active_key = _agent_key(_ACTIVE_PREFIX, agent)
    with Store(cfg) as store:
        store.conn.execute("BEGIN IMMEDIATE")
        active = _get(store.conn, active_key, "active run delivery challenge")
        if not active:
            raise UsageError("no active delivery verification challenge")
        if active.get("agent") != agent or active.get("thread") != thread:
            raise UsageError("active delivery challenge does not match the requested thread")
        challenge_key = _challenge_key(active["token"])
        record = _get(store.conn, challenge_key, "run delivery challenge")
        if not record or record.get("token") != active["token"]:
            raise UsageError("active delivery verification challenge is corrupt")
        if record.get("status") not in {
            "challenge_sent", "submission_uncertain", "transport_unsupported",
        }:
            raise UsageError("active delivery verification challenge is not pending")
        previous = record["status"]
        record.update(status="abandoned", abandoned_at=time.time(), abandoned_from=previous)
        _put(store.conn, challenge_key, record)
        store.conn.execute("DELETE FROM automation_meta WHERE key=?", (active_key,))
    return {
        "status": "abandoned",
        "agent": agent,
        "thread": thread,
        "previous_status": previous,
        "verified": False,
        "model_requests": 0,
        "queue_cancelled": False,
        "queue_retried": False,
    }


def _events(conn, agent: str) -> list[tuple[str, dict]]:
    rows = conn.execute(
        "SELECT key,value FROM automation_meta WHERE key LIKE ?", (_EVENT_PREFIX + "%",)
    ).fetchall()
    result: list[tuple[str, dict]] = []
    for row in rows:
        event = _load(row["value"], "run delivery event")
        if event.get("agent") == agent:
            result.append((row["key"], event))
    result.sort(key=lambda item: (item[1].get("created_at", 0), item[1].get("event_id", "")))
    return result


def dispatch(cfg, agent: str, transport: Any | None = None) -> dict:
    """Attempt at most one pending run event through a verified binding."""
    agent = _identity(agent, "agent")
    if not cfg.get("automation", "delivery", "enabled", default=False):
        return {"status": "disabled", "agent": agent, "model_requests": 0}
    binding_key = _agent_key(_BINDING_PREFIX, agent)
    active_key = _agent_key(_ACTIVE_PREFIX, agent)
    with Store(cfg) as store:
        store.conn.execute("BEGIN IMMEDIATE")
        binding = _get(store.conn, binding_key, "run delivery binding")
        active = _get(store.conn, active_key, "active run delivery challenge")
        if not binding or binding.get("status") != "verified" or active:
            return {"status": "unverified", "agent": agent, "model_requests": 0}
        events = _events(store.conn, agent)
        unresolved = [event for _key, event in events
                      if event.get("status") in {"submission_uncertain", "transport_unsupported"}]
        if unresolved:
            return {"status": "needs_reconciliation", "agent": agent,
                    "needs_reconciliation": len(unresolved), "model_requests": 0}
        pending = next(((key, event) for key, event in events if event.get("status") == "pending"), None)
        if pending is None:
            return {"status": "no_delivery", "agent": agent, "model_requests": 0}
        key, event = pending
        attempt_id = secrets.token_hex(16)
        # The uncertain state is durable before process submission.  Only an
        # explicit operator reconciliation may later change it.
        event.update(status="submission_uncertain", attempted_at=time.time(),
                     attempt_id=attempt_id, thread=binding["thread"])
        _put(store.conn, key, event)
    raw_packet = artifacts.read(cfg, event["packet_artifact"]["id"])
    if len(raw_packet) > PACKET_LIMIT:
        raise UsageError("stored callback packet exceeds its size bound")
    marker = f"[es-run-event:{event['event_id']}]"
    message = marker + "\n" + raw_packet.decode("utf-8")
    result = (transport or QueueTransport()).queue(binding["thread"], message)
    state = result.get("status") if isinstance(result, dict) else None
    if state not in {"accepted", "submission_uncertain", "transport_unsupported"}:
        state = "submission_uncertain"
        result = {"status": state, "model_requests": 1,
                  "reason": "queue transport returned an invalid receipt"}
    final = "delivered" if state == "accepted" else state
    with Store(cfg) as store:
        store.conn.execute("BEGIN IMMEDIATE")
        current = _get(store.conn, key, "run delivery event")
        if current and current.get("attempt_id") == attempt_id:
            current["status"] = final
            current["receipt_at"] = time.time()
            current["transport"] = {field: result[field] for field in
                                    ("status", "model_requests", "exit_code", "reason") if field in result}
            _put(store.conn, key, current)
    return {"status": final, "agent": agent, "thread": binding["thread"],
            "event_id": event["event_id"], "packet": event["packet_artifact"],
            "model_requests": int(result.get("model_requests", 1))}


def status(cfg, agent: str) -> dict:
    """Read callback readiness and run-event counts without contacting Codex."""
    agent = _identity(agent, "agent")
    with Store(cfg) as store:
        binding = _get(store.conn, _agent_key(_BINDING_PREFIX, agent), "run delivery binding")
        active = _get(store.conn, _agent_key(_ACTIVE_PREFIX, agent), "active run delivery challenge")
        challenge = (_get(store.conn, _challenge_key(active["token"]), "run delivery challenge")
                     if active else None)
        counts: dict[str, int] = {}
        for _key, event in _events(store.conn, agent):
            state = str(event.get("status", "unknown"))
            counts[state] = counts.get(state, 0) + 1
    enabled = bool(cfg.get("automation", "delivery", "enabled", default=False))
    verified = bool(binding and binding.get("status") == "verified" and not active)
    needs_reconciliation = sum(
        counts.get(state, 0) for state in ("submission_uncertain", "transport_unsupported")
    )
    result: dict[str, Any] = {
        "agent": agent,
        "enabled": enabled,
        "verified": verified,
        "callback_ready": enabled and verified and needs_reconciliation == 0,
        "needs_reconciliation": needs_reconciliation,
        "model_requests": 0,
        "events": counts,
    }
    if binding:
        result["binding"] = {key: binding[key] for key in
                             ("thread", "status", "verified_at", "transport") if key in binding}
    if challenge:
        result["challenge"] = {"thread": challenge.get("thread"), "status": challenge.get("status")}
    return result
