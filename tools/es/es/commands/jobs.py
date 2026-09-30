from __future__ import annotations

import json
import os
import signal
import time
from pathlib import Path

from es import EXIT_CHECK_FAILED, EXIT_OK
from es.context import Ctx
from es.errors import UsageError
from es.jobs import review_due, run_job, submit_run, worker_loop
from es.output import Result, table
from es.spec import Arg, CommandSpec, command
from es.store import Store


def _fmt(ts):
    return time.strftime("%m-%d %H:%M", time.localtime(ts)) if ts else ""


def _short(text: str | None, n: int) -> str:
    text = (text or "").replace("\n", " ")
    return text if len(text) <= n else text[: n - 1] + "…"


def _elapsed(j: dict) -> str:
    start = j.get("started_at")
    if not start:
        return ""
    end = j.get("finished_at") or time.time()
    return f"{(end - start) / 60:.0f}m"


def _status(j: dict) -> str:
    from es.jobs import review_due
    return j["status"] + (" REVIEW DUE" if review_due(j) else "")


def job_rows(jobs: list[dict]) -> list[list]:
    return [[j["id"], j["kind"], _short(j.get("node"), 34), _status(j), j.get("exit_code"), _fmt(j["created_at"]), _elapsed(j),
             j.get("memory_max") or "", j.get("peak_mib") or "", _short(j.get("agent"), 24), _short(j.get("why"), 48)] for j in jobs]


JOB_HEADERS = ["id", "kind", "node", "status", "rc", "created", "elapsed", "cap", "peak MiB", "agent", "why"]


def run_list(ctx: Ctx, status: str | None = None, limit: int = 20) -> Result:
    with Store(ctx.cfg) as st:
        jobs = st.jobs(status=status, limit=limit)
    res = Result(EXIT_OK, {"jobs": jobs})
    res.human.extend(table(job_rows(jobs), JOB_HEADERS) or ["no jobs"])
    return res


def run_run(ctx: Ctx, command: list[str], why: str, out: list[str], node: str | None = None, mem: str | None = None,
            budget: int | None = None, cpu: int | None = None, queue: bool = False, review: int | None = None) -> Result:
    """Submit an arbitrary command as a guarded, recorded job."""
    from es.nodes import find_node
    if node:
        node = find_node(ctx.cfg, node).name
    job = submit_run(ctx.cfg, command=list(command), why=why, outputs=list(out), agent=ctx.agent, node=node, memory_max=mem,
                     budget_min=budget, cpu_cores=cpu, queue=queue, review_min=review)
    if job.get("queued_for_worker"):
        return Result(EXIT_OK, {"job": job}, [f"queued {job['id']} (cap {job['memory_max']}): this process cannot reach the systemd user bus "
                                              f"(sandbox), so an `es worker` running outside it will execute the job; `es job wait {job['id']}` to follow completion"])
    if queue:
        return Result(EXIT_OK, {"job": job}, [f"queued {job['id']} (cap {job['memory_max']}) for `es worker`; `es job wait {job['id']}` to follow completion"])
    return Result(EXIT_OK, {"job": job}, [f"submitted {job['id']} (cap {job['memory_max']}, log {job['log_path']}); `es job wait {job['id']}` to follow completion"])


def run_requeue(ctx: Ctx, id: str) -> Result:
    """Put a failed or killed job back in the queue (same command, cap and outputs) for `es worker`."""
    with Store(ctx.cfg) as st:
        job = st.job(id)
        if job is None:
            raise UsageError(f"unknown job {id}")
        if job["status"] in ("queued", "starting", "running", "unknown_execution"):
            return Result(EXIT_CHECK_FAILED, {"job": job}, [f"{job['id']} is {job['status']}"])
        st.job_update(job["id"], status="queued", exit_code=None, started_at=None, finished_at=None, pid=None, peak_mib=None, seconds=None,
                      cancel_requested=0, process_start=None, heartbeat_at=None)
        st.event("job-requeued", job.get("node"), ctx.agent, {"id": job["id"], "previous": job["status"]})
    return Result(EXIT_OK, {"job": job["id"]}, [f"requeued {job['id']} for `es worker`"])


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
    if job.get("why"):
        res.line(f"why: {job['why']}")
    from es.jobs import review_due, review_due_at
    due = review_due_at(job)
    if due and job["status"] in ("running", "starting"):
        res.line(("REVIEW DUE since " if review_due(job) else "next progress review ") + _fmt(due)
                 + f" (`es job review {job['id']} --note ...`)")
    if job["kind"] == "run":
        res.line(f"command: {' '.join(json.loads(job['argv']))}")
        res.line(f"agent {job.get('agent')}; cap {job.get('memory_max')}; elapsed {_elapsed(job) or '-'}; peak {job.get('peak_mib') or '-'} MiB; outputs {', '.join(json.loads(job.get('outputs') or '[]')) or '-'}")
    return res


def run_log(ctx: Ctx, id: str, lines: int = 60) -> Result:
    with Store(ctx.cfg) as st:
        job = st.job(id)
    if job is None:
        raise UsageError(f"unknown job {id}")
    text = Path(job["log_path"]).read_text(errors="replace") if job.get("log_path") and Path(job["log_path"]).exists() else ""
    tail = text.splitlines()[-lines:]
    return Result(EXIT_OK, {"job": job["id"], "log": tail}, tail or ["(empty log)"])


def run_wait(ctx: Ctx, id: str, timeout: int = 55) -> Result:
    """Wait without model polling, holding no database transaction between observations.

    Like job status, exit zero means the read succeeded, not that the job succeeded.
    A wait-window expiry leaves the job untouched and tells the caller to keep waiting.
    """
    if not 0 <= timeout <= 60:
        raise UsageError("--timeout must be between 0 and 60 seconds")
    deadline = time.monotonic() + timeout
    while True:
        with Store(ctx.cfg) as st:
            job = st.job(id)
        if job is None:
            raise UsageError(f"unknown job {id}")
        id = job["id"]  # resolve the prefix once, even if another job is submitted later
        terminal = job["status"] in ("done", "failed", "killed")
        remaining = deadline - time.monotonic()
        if not terminal and review_due(job):
            payload = {"job_id": id, "status": job["status"], "terminal": False, "timed_out": False,
                       "review_due": True, "log_path": job.get("log_path"),
                       "outputs": json.loads(job.get("outputs") or "[]")}
            return Result(EXIT_OK, payload, [
                f"{id}: {job['status']} for {_elapsed(job)}; REVIEW CHECKPOINT: read its progress (`es job log {id}`, "
                f"its outputs), estimate how much is done, then decide: leave it running, make it cheaper, or get the "
                f"answer another way. Record the estimate and decision with `es job review {id} --note \"...\" "
                f"[--next MIN]` (a checkpoint never stops the job)."])
        if terminal or remaining <= 0:
            payload = {"job_id": id, "status": job["status"], "terminal": terminal,
                       "timed_out": not terminal}
            if terminal:
                payload.update(job_exit_code=job.get("exit_code"), log_path=job.get("log_path"),
                               outputs=json.loads(job.get("outputs") or "[]"))
                line = f"{id}: {job['status']} rc={job.get('exit_code')}; inspect outputs and report the result"
            else:
                line = f"{id}: {job['status']} (wait window expired; keep waiting)"
            return Result(EXIT_OK, payload, [line])
        time.sleep(min(1.0, remaining))


def run_review(ctx: Ctx, id: str, note: str, next: int | None = None) -> Result:
    """Record a progress review of a running job and schedule the next one.

    The note states what the job has done (fraction, rate, estimated time to finish) and the
    decision (leave it, replace it with a cheaper job, or answer the question another way).
    The job keeps running; to stop it, `es job cancel` and log the replacement plan."""
    from es.jobs import review_due_at
    if not note or not note.strip():
        raise UsageError("--note is required: the progress estimate and the decision")
    with Store(ctx.cfg) as st:
        job = st.job(id)
        if job is None:
            raise UsageError(f"unknown job {id}")
        if job["status"] not in ("running", "starting", "queued"):
            raise UsageError(f"{job['id']} is {job['status']}: review the outputs instead")
        interval = next or job.get("review_min") or ctx.cfg.jobs_review_after_min or 20
        due = time.time() + 60 * interval
        st.job_update(job["id"], review_at=due, review_min=interval)
        st.event("job-review", job.get("node"), ctx.agent,
                 {"id": job["id"], "elapsed_min": round((time.time() - (job.get("started_at") or time.time())) / 60, 1),
                  "note": note.strip(), "next_review_min": interval,
                  "previous_due": review_due_at(job)})
    return Result(EXIT_OK, {"job_id": job["id"], "next_review_at": due},
                  [f"{job['id']}: review recorded; next checkpoint {_fmt(due)}"])


def run_cancel(ctx: Ctx, id: str) -> Result:
    from es.jobs import request_cancel
    job = request_cancel(ctx.cfg, id)
    acknowledged = job['status'] in ('done', 'failed', 'killed')
    return Result(EXIT_OK, {'job_id': job['id'], 'status': job['status'], 'cancel_requested': True,
                           'termination_acknowledged': acknowledged},
                  [f"{job['id']}: " + ('terminal' if acknowledged else 'cancellation requested; awaiting worker acknowledgement')])


def run_exec(ctx: Ctx, id: str) -> Result:
    job = run_job(ctx.cfg, id)
    return Result(EXIT_OK if job.get("exit_code") == 0 else EXIT_CHECK_FAILED, {"job": job}, [f"{job['id']}: {job['status']} rc={job.get('exit_code')}"])


def run_worker(ctx: Ctx, once: bool = False) -> Result:
    worker_loop(ctx.cfg, once=once)
    return Result(EXIT_OK, {}, ["worker stopped"])


command(CommandSpec(name="job_list", cli=["job", "list"], help="List jobs.", run=run_list,
                    args=[Arg("status", "filter by status", choices=["queued", "starting", "running", "done", "failed", "killed"]), Arg("limit", "max rows", "int", default=20)]))
command(CommandSpec(name="job_status", cli=["job", "status"], help="Job status and (when finished) its JSON result.", run=run_status,
                    args=[Arg("id", "job id (prefix ok)", positional=True, required=True)]))
command(CommandSpec(name="job_log", cli=["job", "log"], help="Tail of a job's log.", run=run_log,
                    args=[Arg("id", "job id (prefix ok)", positional=True, required=True), Arg("lines", "lines from the end", "int", default=60)]))
command(CommandSpec(name="job_wait", cli=["job", "wait"],
                    help="Wait up to 55 seconds for a terminal job state or a due progress review. Keep the reporting turn open, repeat while terminal=false; on review_due=true read the job's progress and record `es job review`; when terminal, inspect outputs and report success or failure. Does not wake a closed client or cancel the job.",
                    run=run_wait,
                    args=[Arg("id", "job id (prefix ok)", positional=True, required=True),
                          Arg("timeout", "wait window in seconds (0–60); expiration is not job completion", "int", default=55)]))
command(CommandSpec(name="job_review", cli=["job", "review"],
                    help="Record a progress review of a running job (estimate done / rate / time left, and the decision) and schedule the next checkpoint; never stops the job.",
                    run=run_review,
                    args=[Arg("id", "job id (prefix ok)", positional=True, required=True),
                          Arg("note", "progress estimate and decision: leave it, make it cheaper, or answer another way", required=True),
                          Arg("next", "minutes until the next checkpoint (default: the job's interval)", "int")]))
command(CommandSpec(name="job_cancel", cli=["job", "cancel"], help="Request cancellation; the owning worker acknowledges process termination.", run=run_cancel,
                    args=[Arg("id", "job id (prefix ok)", positional=True, required=True)]))
command(CommandSpec(name="job_run", cli=["job", "run"],
                    help="Run a command as a recorded job: memory-guarded scope, purpose, node, cap, outputs, agent and measured peak are kept in the job table. Put the command after `--`.",
                    run=run_run,
                    args=[Arg("command", "the command and its arguments (after `--`)", "list", positional=True, required=True),
                          Arg("why", "what the job is for (one sentence)", required=True),
                          Arg("out", "result path(s) under runs/ or data/ (repeat or comma-separate)", "list", required=True),
                          Arg("node", "node the job serves, if any"), Arg("mem", "cgroup MemoryMax, e.g. 2G (default from config)"),
                          Arg("budget", "wall-clock KILL in minutes: only for a deadline the user set (use --review otherwise)", "int"),
                          Arg("cpu", "CPU quota in cores", "int"),
                          Arg("queue", "queue for `es worker` instead of starting now", "bool"),
                          Arg("review", "minutes of running before the first progress review (default [jobs] review_after_min; 0: none); never stops the job", "int")]))
command(CommandSpec(name="job_requeue", cli=["job", "requeue"], help="Put a failed or killed job back in the queue for `es worker`.", run=run_requeue,
                    args=[Arg("id", "job id (prefix ok)", positional=True, required=True)]))
command(CommandSpec(name="job_exec", cli=["job", "exec"], help="Execute one queued job in the foreground (used by the detached runner).", run=run_exec, mcp=False,
                    args=[Arg("id", "job id", positional=True, required=True)]))
command(CommandSpec(name="worker", cli=["worker"], help="Start queued jobs whenever they fit the memory budget, several at once (foreground; run under systemd-user).", run=run_worker, mcp=False,
                    args=[Arg("once", "one pass over the queue, then exit", "bool")]))
