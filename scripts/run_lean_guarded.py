#!/usr/bin/env python3
"""Run one Lean/Lake command with liveness and aggregate-resource guards."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


RESOURCE_EXIT = 125
TIMEOUT_EXIT = 124


def process_group_snapshot(pgid: int) -> tuple[int, int, list[str]]:
    """Return (Lean compiler count, aggregate RSS KiB, command summaries)."""
    lean_count = 0
    rss_kib = 0
    commands: list[str] = []
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            stat = (entry / "stat").read_text(encoding="utf-8")
            tail = stat[stat.rfind(")") + 2 :].split()
            if len(tail) < 3 or int(tail[2]) != pgid:
                continue
            status = (entry / "status").read_text(encoding="utf-8")
            for line in status.splitlines():
                if line.startswith("VmRSS:"):
                    rss_kib += int(line.split()[1])
                    break
            raw = (entry / "cmdline").read_bytes().split(b"\0")
            argv = [part.decode("utf-8", errors="replace") for part in raw if part]
            command = " ".join(argv[:4]) if argv else f"[{entry.name}]"
            commands.append(command)
            if argv and Path(argv[0]).name == "lean":
                lean_count += 1
        except (FileNotFoundError, PermissionError, ProcessLookupError, ValueError):
            continue
    return lean_count, rss_kib, commands


def stop_group(process: subprocess.Popen[bytes], grace_seconds: float) -> None:
    if process.poll() is not None:
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        process.wait(timeout=grace_seconds)
        return
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        return
    process.wait()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout-seconds", type=float, required=True)
    parser.add_argument("--max-rss-mib", type=int, required=True)
    parser.add_argument("--max-lean-processes", type=int, default=1)
    parser.add_argument("--heartbeat-seconds", type=float, default=45.0)
    parser.add_argument("--poll-seconds", type=float, default=1.0)
    parser.add_argument("--grace-seconds", type=float, default=5.0)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()

    command = args.command
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        parser.error("a command is required after --")
    if args.timeout_seconds <= 0 or args.max_rss_mib <= 0:
        parser.error("timeout and RSS cap must be positive")
    if args.max_lean_processes < 0:
        parser.error("Lean process cap must be nonnegative")
    if args.heartbeat_seconds <= 0 or args.poll_seconds <= 0:
        parser.error("heartbeat and poll intervals must be positive")

    started = time.monotonic()
    next_heartbeat = started
    process = subprocess.Popen(command, start_new_session=True)
    try:
        while True:
            returncode = process.poll()
            lean_count, rss_kib, commands = process_group_snapshot(process.pid)
            elapsed = time.monotonic() - started
            if returncode is not None:
                print(
                    f"guard: exit={returncode} elapsed={elapsed:.1f}s "
                    f"lean={lean_count} rss={rss_kib / 1024:.1f}MiB",
                    file=sys.stderr,
                    flush=True,
                )
                return returncode
            if lean_count > args.max_lean_processes:
                print(
                    f"guard: Lean process cap exceeded: {lean_count} > "
                    f"{args.max_lean_processes}; commands={commands}",
                    file=sys.stderr,
                    flush=True,
                )
                stop_group(process, args.grace_seconds)
                return RESOURCE_EXIT
            if rss_kib > args.max_rss_mib * 1024:
                print(
                    f"guard: aggregate RSS cap exceeded: {rss_kib / 1024:.1f}MiB "
                    f"> {args.max_rss_mib}MiB",
                    file=sys.stderr,
                    flush=True,
                )
                stop_group(process, args.grace_seconds)
                return RESOURCE_EXIT
            if elapsed >= args.timeout_seconds:
                print(
                    f"guard: timeout after {elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )
                stop_group(process, args.grace_seconds)
                return TIMEOUT_EXIT
            if time.monotonic() >= next_heartbeat:
                print(
                    f"guard: live elapsed={elapsed:.1f}s lean={lean_count} "
                    f"rss={rss_kib / 1024:.1f}MiB",
                    file=sys.stderr,
                    flush=True,
                )
                next_heartbeat = time.monotonic() + args.heartbeat_seconds
            time.sleep(args.poll_seconds)
    except KeyboardInterrupt:
        stop_group(process, args.grace_seconds)
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
