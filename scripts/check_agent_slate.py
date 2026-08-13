#!/usr/bin/env python3
"""Verify that every task in an execution slate has one terminal result."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
ORCHESTRATION_CHECKER = ROOT / "scripts/check_agent_orchestration.py"
TERMINAL_STATUSES = {
    "completed", "refuted", "blocked", "inconclusive", "superseded"
}


def load_object(path: Path, label: str) -> dict:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot parse {label} {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise ValueError(f"{label} {path} must be a JSON object")
    return value


def resolve_repo_path(value: object, label: str) -> Path:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{label} must be a nonempty repository-relative path")
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        raise ValueError(f"{label} must stay inside the repository")
    resolved = ROOT / path
    if not resolved.is_file():
        raise ValueError(f"{label} does not exist: {value}")
    return resolved


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--slate", required=True, type=Path)
    args = parser.parse_args()

    slate_path = args.slate if args.slate.is_absolute() else ROOT / args.slate
    try:
        slate = load_object(slate_path, "slate")
        if slate.get("schema_version") != 1:
            raise ValueError("slate schema_version must be 1")
        run_id = slate.get("run_id")
        if not isinstance(run_id, str) or not run_id:
            raise ValueError("slate run_id must be a nonempty string")
        threads = slate.get("threads")
        if not isinstance(threads, list) or not threads:
            raise ValueError("slate threads must be a nonempty array")

        seen_tasks: set[str] = set()
        seen_results: set[Path] = set()
        for index, thread in enumerate(threads):
            if not isinstance(thread, dict) or set(thread) != {"task_packet", "result"}:
                raise ValueError(
                    f"threads[{index}] must contain exactly task_packet and result"
                )
            task_path = resolve_repo_path(
                thread["task_packet"], f"threads[{index}].task_packet"
            )
            result_path = resolve_repo_path(
                thread["result"], f"threads[{index}].result"
            )
            task = load_object(task_path, "task packet")
            result = load_object(result_path, "result")
            task_id = task.get("task_id")
            if not isinstance(task_id, str) or not task_id:
                raise ValueError(f"threads[{index}] task_id is missing")
            if task_id in seen_tasks:
                raise ValueError(f"duplicate task_id in slate: {task_id}")
            if result_path in seen_results:
                raise ValueError(f"duplicate result path in slate: {result_path}")
            seen_tasks.add(task_id)
            seen_results.add(result_path)
            if task.get("run_id") != run_id:
                raise ValueError(f"{task_id} has run_id different from slate")
            if result.get("task_id") != task_id:
                raise ValueError(f"{task_id} result task_id does not match")
            if result.get("status") not in TERMINAL_STATUSES:
                raise ValueError(f"{task_id} has nonterminal result status")

            completed = subprocess.run(
                [
                    sys.executable,
                    str(ORCHESTRATION_CHECKER),
                    "--task-packet", str(task_path),
                    "--result", str(result_path),
                ],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            if completed.returncode != 0:
                detail = completed.stderr.strip() or completed.stdout.strip()
                raise ValueError(f"{task_id} task/result validation failed: {detail}")
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    print(f"agent slate complete: {run_id}, {len(threads)} terminal results")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
