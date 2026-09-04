from __future__ import annotations

import json
import os
import signal
import time
from pathlib import Path

from es import EXIT_CHECK_FAILED, EXIT_OK
from es.context import Ctx
from es.errors import UsageError
from es.jobs import run_job, worker_loop
from es.output import Result, table
from es.spec import Arg, CommandSpec, command
from es.store import Store


def _fmt(ts):
    return time.strftime("%m-%d %H:%M", time.localtime(ts)) if ts else ""


def run_list(ctx: Ctx, status: str | None = None, limit: int = 20) -> Result:
    with Store(ctx.cfg) as st:
        jobs = st.jobs(status=status, limit=limit)
    rows = [[j["id"], j["kind"], j.get("node") or "", j["status"], j.get("exit_code"), _fmt(j["created_at"]), _fmt(j.get("finished_at")), j.get("agent") or ""] for j in jobs]
    res = Result(EXIT_OK, {"jobs": jobs})
    res.human.extend(table(rows, ["id", "kind", "node", "status", "rc", "created", "finished", "agent"]) or ["no jobs"])
    return res


def run_status(ctx: Ctx, id: str) -> Result:
    with Store(ctx.cfg) as st:
        job = st.job(id)
    if job is None:
        raise UsageError(f"unknown job {id}")
    result = None
    if job.get("result_json"):
        try:
            result = json.loads(job["result_json"])
        except json.JSONDecodeError:
            result = None
    res = Result(EXIT_OK, {"job": job, "result": result})
    res.line(f"{job['id']} {job['kind']} {job.get('node') or ''}: {job['status']} rc={job.get('exit_code')} log={job.get('log_path')}")
    return res


def run_log(ctx: Ctx, id: str, lines: int = 60) -> Result:
    with Store(ctx.cfg) as st:
        job = st.job(id)
    if job is None:
        raise UsageError(f"unknown job {id}")
    text = Path(job["log_path"]).read_text(errors="replace") if job.get("log_path") and Path(job["log_path"]).exists() else ""
    tail = text.splitlines()[-lines:]
    return Result(EXIT_OK, {"job": job["id"], "log": tail}, tail or ["(empty log)"])


def run_cancel(ctx: Ctx, id: str) -> Result:
    cfg = ctx.cfg
    with Store(cfg) as st:
        job = st.job(id)
        if job is None:
            raise UsageError(f"unknown job {id}")
        if job["status"] in ("done", "failed", "killed"):
            return Result(EXIT_CHECK_FAILED, {"job": job}, [f"{job['id']} already {job['status']}"])
        if job.get("pid"):
            try:
                os.killpg(os.getpgid(job["pid"]), signal.SIGTERM)
            except (OSError, ProcessLookupError):
                pass
        st.job_update(job["id"], status="killed", finished_at=time.time())
        st.event("job-killed", job.get("node"), ctx.agent, {"id": job["id"]})
    return Result(EXIT_OK, {"job": job["id"]}, [f"killed {job['id']}"])


def run_run(ctx: Ctx, id: str) -> Result:
    job = run_job(ctx.cfg, id)
    return Result(EXIT_OK if job.get("exit_code") == 0 else EXIT_CHECK_FAILED, {"job": job}, [f"{job['id']}: {job['status']} rc={job.get('exit_code')}"])


def run_worker(ctx: Ctx, once: bool = False) -> Result:
    worker_loop(ctx.cfg, once=once)
    return Result(EXIT_OK, {}, ["worker stopped"])


command(CommandSpec(name="job_list", cli=["job", "list"], help="List jobs.", run=run_list,
                    args=[Arg("status", "filter by status", choices=["queued", "running", "done", "failed", "killed"]), Arg("limit", "max rows", "int", default=20)]))
command(CommandSpec(name="job_status", cli=["job", "status"], help="Job status and (when finished) its JSON result.", run=run_status,
                    args=[Arg("id", "job id (prefix ok)", positional=True, required=True)]))
command(CommandSpec(name="job_log", cli=["job", "log"], help="Tail of a job's log.", run=run_log,
                    args=[Arg("id", "job id (prefix ok)", positional=True, required=True), Arg("lines", "lines from the end", "int", default=60)]))
command(CommandSpec(name="job_cancel", cli=["job", "cancel"], help="Kill a queued or running job.", run=run_cancel,
                    args=[Arg("id", "job id (prefix ok)", positional=True, required=True)]))
command(CommandSpec(name="job_run", cli=["job", "run"], help="Execute one queued job in the foreground (used by the detached runner).", run=run_run, mcp=False,
                    args=[Arg("id", "job id", positional=True, required=True)]))
command(CommandSpec(name="worker", cli=["worker"], help="Run queued jobs one at a time (foreground; run under tmux/systemd-user).", run=run_worker, mcp=False,
                    args=[Arg("once", "run at most one job then exit", "bool")]))
