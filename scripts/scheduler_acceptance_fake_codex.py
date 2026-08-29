#!/usr/bin/env python3
"""Deterministic no-network Codex CLI stand-in for scheduler acceptance only."""

from __future__ import annotations

import json
from pathlib import Path
import re
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
TASK_RE = re.compile(r"Task packet: `([^`]+)`")


def fail(message: str) -> int:
    print(message, file=sys.stderr)
    return 2


def main(argv: list[str]) -> int:
    if argv == ["--version"]:
        print("codex-cli scheduler-acceptance-fake-1")
        return 0
    if not argv or argv[0] != "exec":
        return fail("acceptance fake accepts only --version or exec")
    try:
        last_index = argv.index("--output-last-message")
        last_message_path = Path(argv[last_index + 1])
    except (ValueError, IndexError):
        return fail("missing --output-last-message")
    prompt = sys.stdin.read()
    matched = TASK_RE.search(prompt)
    if matched is None:
        return fail("worker prompt lacks task packet")
    task_path = (ROOT / matched.group(1)).resolve()
    task = json.loads(task_path.read_text(encoding="utf-8"))
    controls = []
    for item in task.get("inputs", []):
        path = (ROOT / item["path"]).resolve()
        if path.suffix == ".json":
            try:
                value = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue
            if value.get("protocol") == "scheduler-acceptance-control-v1":
                controls.append(value)
    if len(controls) != 1:
        return fail("task does not bind exactly one acceptance control")
    control = controls[0]
    ready = (ROOT / control["ready_path"]).resolve()
    release = (ROOT / control["release_path"]).resolve()
    ready.parent.mkdir(parents=True, exist_ok=True)
    ready.write_text(task["task_id"] + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "type": "thread.started",
                "thread_id": f"acceptance-{task['task_id']}",
            },
            sort_keys=True,
        ),
        flush=True,
    )
    deadline = time.monotonic() + int(control.get("wait_seconds", 90))
    while not release.is_file():
        if time.monotonic() >= deadline:
            return fail("acceptance release deadline expired")
        time.sleep(0.1)
    result_path = (ROOT / task["deliverables"][-1]).resolve()
    report_path = (ROOT / task["deliverables"][0]).resolve()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(
        f"deterministic supervised acceptance worker {task['task_id']} completed\n",
        encoding="utf-8",
    )
    result = {
        "schema_version": 1,
        "task_id": task["task_id"],
        "status": "completed",
        "claim_level": "proposal",
        "summary": "Deterministic scheduler acceptance worker completed.",
        "supports": ["A real supervised local worker traversed the frozen scheduler path."],
        "does_not_support": ["No provider, network, or mathematical claim was tested."],
        "changes": [task["deliverables"][0], task["deliverables"][-1]],
        "checks": [{"command": "acceptance release barrier", "outcome": "passed"}],
        "evidence": [f"thread_id=acceptance-{task['task_id']}"],
        "limitations": ["Deterministic fake Codex executable; live provider remains untested."],
        "blocked_by": None,
    }
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    result_path.write_text(encoded, encoding="utf-8")
    last_message_path.parent.mkdir(parents=True, exist_ok=True)
    last_message_path.write_text(encoded, encoding="utf-8")
    print(json.dumps({"type": "item.completed", "thread_id": f"acceptance-{task['task_id']}"}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
