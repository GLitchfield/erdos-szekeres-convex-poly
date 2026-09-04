#!/usr/bin/env python3
"""Run a sequential build plan through scripts/guarded_lake_build.sh.

The plan is a JSON list of stages, executed in order.  Stage kinds:

* ``{"kind": "lake", "name": ..., "targets": [...], "batch": 8, "mem": "14G",
  "cpus": 8, "continue_on_fail": false}`` - builds the targets, ``batch`` per
  lake invocation, each invocation inside its own memory-capped cgroup.  A
  failed batch is retried in halves down to single targets.
* ``{"kind": "shell", "name": ..., "command": "...", "mem": "12G"}`` - runs a
  shell command inside a memory-capped cgroup (no swap).
* ``{"kind": "wait", "name": ..., "marker": "...", "fail_marker": "..."}`` -
  polls the guard log until ``marker`` appears (aborts on ``fail_marker``).

Only one heavy job of this driver runs at a time; a separately started
checkpoint chain may run concurrently, which is why GUARD_ALLOW_CONCURRENT is
set.  Total worst-case memory = this driver's cap + the chain's cap.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
GUARD = REPO / "scripts" / "guarded_lake_build.sh"


def log(handle, message: str) -> None:
    stamp = datetime.datetime.now().strftime("%F %T")
    handle.write(f"{stamp} {message}\n")
    handle.flush()


def run_lake(targets: list[str], mem: str, cpus: int, guard_log: Path, handle,
             threads: int = 2, retry_mems: list[str] | None = None) -> bool:
    env = dict(os.environ, GUARD_ALLOW_CONCURRENT="1")
    command = [str(GUARD), "-m", mem, "-c", str(cpus), "-t", str(threads), "-l", str(guard_log), *targets]
    result = subprocess.run(command, cwd=REPO, env=env, capture_output=True, text=True)
    tail = "\n".join(result.stdout.strip().splitlines()[-3:] + result.stderr.strip().splitlines()[-3:])
    if result.returncode == 0:
        log(handle, f"ok   {len(targets)} target(s): {targets[0]}..{targets[-1]} | {tail.splitlines()[-1] if tail else ''}")
        return True
    log(handle, f"FAIL rc={result.returncode} {len(targets)} target(s): {targets[0]}..{targets[-1]}\n{tail}")
    attempts = 0
    while result.returncode == 125 and attempts < 240:
        # guard refused (memory short or a foreign compiler running): wait for room
        attempts += 1
        time.sleep(60)
        result = subprocess.run(command, cwd=REPO, env=env, capture_output=True, text=True)
        if result.returncode == 0:
            log(handle, f"ok   after {attempts} min wait: {targets[0]}..{targets[-1]}")
            return True
    if len(targets) == 1 and result.returncode in (137, 143):
        escalations = retry_mems if retry_mems is not None else (["20G"] if mem != "20G" else [])
        for bigger in escalations:
            log(handle, f"retrying {targets[0]} alone at {bigger} (threads={threads}) after an OOM kill")
            if run_lake(targets, bigger, cpus, guard_log, handle, threads, []):
                return True
        return False
    if len(targets) > 1:
        middle = len(targets) // 2
        return run_lake(targets[:middle], mem, cpus, guard_log, handle, threads, retry_mems) and \
            run_lake(targets[middle:], mem, cpus, guard_log, handle, threads, retry_mems)
    return False


def run_stage(stage: dict, guard_log: Path, handle) -> bool:
    kind = stage["kind"]
    name = stage["name"]
    start = time.time()
    log(handle, f"== stage {name} ({kind}) start")
    ok = True
    if kind == "lake":
        targets = stage["targets"]
        batch = int(stage.get("batch", 1))
        for index in range(0, len(targets), batch):
            chunk = targets[index:index + batch]
            if not run_lake(chunk, stage.get("mem", "14G"), int(stage.get("cpus", 4)), guard_log, handle,
                            int(stage.get("threads", 2)), stage.get("retry_mems")):
                ok = False
                break
    elif kind == "shell":
        command = ["systemd-run", "--user", "--scope", "-q",
                   "-p", f"MemoryMax={stage.get('mem', '12G')}", "-p", "MemorySwapMax=0",
                   "-p", f"CPUQuota={int(stage.get('cpus', 2)) * 100}%",
                   "--", "bash", "-c", stage["command"]]
        result = subprocess.run(command, cwd=REPO, capture_output=True, text=True)
        tail = "\n".join((result.stdout + result.stderr).strip().splitlines()[-6:])
        log(handle, f"shell rc={result.returncode}\n{tail}")
        ok = result.returncode == 0
    elif kind == "wait":
        marker = stage["marker"]
        fail_marker = stage.get("fail_marker")
        while True:
            text = guard_log.read_text() if guard_log.exists() else ""
            if marker in text:
                break
            if fail_marker and fail_marker in text:
                log(handle, f"wait: saw fail marker {fail_marker!r}")
                ok = False
                break
            time.sleep(30)
    else:
        log(handle, f"unknown stage kind {kind}")
        ok = False
    elapsed = int(time.time() - start)
    log(handle, f"== stage {name} {'done' if ok else 'FAILED'} in {elapsed}s")
    return ok


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("plan", type=Path)
    parser.add_argument("--guard-log", type=Path, required=True)
    parser.add_argument("--log", type=Path, required=True)
    args = parser.parse_args()
    stages = json.loads(args.plan.read_text())
    with args.log.open("a") as handle:
        log(handle, f"plan {args.plan} with {len(stages)} stages")
        for stage in stages:
            if not run_stage(stage, args.guard_log, handle):
                if stage.get("continue_on_fail"):
                    log(handle, f"continuing past failed stage {stage['name']}")
                    continue
                log(handle, "plan ABORTED")
                sys.exit(1)
        log(handle, "plan COMPLETE")


if __name__ == "__main__":
    main()
