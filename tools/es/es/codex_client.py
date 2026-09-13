"""Small JSON-RPC client for a job-owned Codex App Server.

The client deliberately keeps protocol transport separate from research policy.  It
does not retain notifications, conversation items, or server stderr.
"""
from __future__ import annotations

import json
import os
import selectors
import subprocess
import time
from collections.abc import Callable


HOST_MARKERS = (
    "ES_AGENT",
    "ES_JOB_ID",
    "ES_STAGE_MEMORY",
    "ES_IN_GUARDED_STAGE",
    "ES_OPERATION_ID",
    "ES_PROJECT_ROOT",
    "ES_WINDOW_ID",
)


class ProtocolError(RuntimeError):
    """App Server returned an error or lost its stdio transport."""


def clean_environment(source: dict[str, str] | None = None) -> dict[str, str]:
    """Remove an enclosing es reservation before Codex starts independent tools."""
    env = dict(os.environ if source is None else source)
    for name in HOST_MARKERS:
        env.pop(name, None)
    return env


class CodexClient:
    """Synchronous request/notification access to one App Server stdio process."""

    def __init__(
        self,
        *,
        on_event: Callable[[dict], None] | None = None,
        popen: Callable[..., subprocess.Popen] = subprocess.Popen,
        command: list[str] | None = None,
    ) -> None:
        argv = command or [
            "codex",
            "app-server",
            "--stdio",
            "-c",
            "mcp_servers.lean-lsp.enabled=false",
        ]
        self.proc = popen(
            argv,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            env=clean_environment(),
            bufsize=0,
        )
        if self.proc.stdin is None or self.proc.stdout is None:
            raise ProtocolError("App Server stdio was not created")
        self.selector = selectors.DefaultSelector()
        self.selector.register(self.proc.stdout, selectors.EVENT_READ)
        self.buffer = b""
        self.ident = 0
        self.on_event = on_event or (lambda _message: None)

    def _send(self, message: dict) -> None:
        try:
            self.proc.stdin.write((json.dumps(message, separators=(",", ":")) + "\n").encode())
            self.proc.stdin.flush()
        except (BrokenPipeError, OSError) as exc:
            raise ProtocolError("App Server disconnected while sending") from exc

    def _receive(self, timeout: float) -> dict:
        """Receive one message, never blocking for more than 55 seconds."""
        timeout = max(0.0, min(55.0, timeout))
        deadline = time.monotonic() + timeout
        while b"\n" not in self.buffer:
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not self.selector.select(remaining):
                raise TimeoutError("App Server event wait expired")
            try:
                part = os.read(self.proc.stdout.fileno(), 65536)
            except OSError as exc:
                raise ProtocolError("App Server stdout failed") from exc
            if not part:
                raise ProtocolError("App Server closed stdout")
            self.buffer += part
        line, self.buffer = self.buffer.split(b"\n", 1)
        try:
            value = json.loads(line)
        except json.JSONDecodeError as exc:
            raise ProtocolError("App Server emitted invalid JSON") from exc
        if not isinstance(value, dict):
            raise ProtocolError("App Server emitted a non-object message")
        return value

    def _deny_server_request(self, message: dict) -> None:
        method = str(message.get("method") or "unknown")[:120]
        self._send({
            "id": message["id"],
            "error": {"code": -32601, "message": "unattended host does not grant approvals or client tools"},
        })
        self.on_event({"method": "client/request-denied", "params": {"method": method}})

    def request(self, method: str, params: dict, timeout: float = 30) -> dict:
        self.ident += 1
        ident = self.ident
        self._send({"id": ident, "method": method, "params": params})
        deadline = time.monotonic() + timeout
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError(method)
            message = self._receive(min(55.0, remaining))
            if "method" in message and "id" in message:
                self._deny_server_request(message)
                continue
            if message.get("id") == ident:
                if "error" in message:
                    error = message.get("error") or {}
                    code = error.get("code") if isinstance(error, dict) else None
                    raise ProtocolError(f"{method} failed" + (f" ({code})" if code is not None else ""))
                result = message.get("result") or {}
                if not isinstance(result, dict):
                    raise ProtocolError(f"{method} returned a non-object result")
                return result
            self.on_event(message)

    def event(self, timeout: float = 55) -> dict:
        """Return the next notification, denying any unexpected server request."""
        deadline = time.monotonic() + min(55.0, timeout)
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("App Server event wait expired")
            message = self._receive(remaining)
            if "method" in message and "id" in message:
                self._deny_server_request(message)
                continue
            if "method" in message:
                return message
            self.on_event(message)

    def initialize(self) -> dict:
        result = self.request(
            "initialize",
            {"clientInfo": {"name": "es-agent-run", "version": "1"},
             "capabilities": {"experimentalApi": True}},
        )
        self._send({"method": "initialized"})
        return result

    def close(self) -> None:
        try:
            self.selector.close()
        finally:
            if self.proc.poll() is None:
                self.proc.terminate()
                try:
                    self.proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    self.proc.kill()
                    self.proc.wait()

    def __enter__(self) -> "CodexClient":
        return self

    def __exit__(self, *_exc) -> None:
        self.close()
