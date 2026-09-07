"""Background jobs: submitted rows in SQLite, executed by a detached `es job exec` or by `es worker`.

Two kinds of job: harness commands (build, check, falsify: ``argv`` is an `es` argument
list) and ``run`` jobs (`es job run`: ``argv`` is an arbitrary command, executed inside
the memory-guarded scope with its purpose, cap, outputs and measured peak recorded)."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
import uuid
from pathlib import Path

from es.build import _mem_gib, available_gib, bus_available, run_guarded
from es.config import Config
from es.errors import CheckFailed
from es.store import Store


def _es_argv() -> list[str]:
    return [sys.executable, "-m", "es"]


def submit(cfg: Config, *, kind: str, node: str | None, argv: list[str], agent: str, budget_min: int | None = None,
           queue: bool = False) -> dict:
    job_id = time.strftime("%Y%m%d-%H%M%S-") + uuid.uuid4().hex[:6]
    log_dir = cfg.build_log_dir
    log_dir.mkdir(parents=True, exist_ok=True)
    log_path = log_dir / f"job-{job_id}.log"
    job = {
        "id": job_id, "kind": kind, "node": node, "argv": json.dumps(argv), "cwd": str(cfg.root),
        "status": "queued", "exit_code": None, "created_at": time.time(), "started_at": None, "finished_at": None,
        "log_path": str(log_path), "budget_min": budget_min, "agent": agent, "pid": None, "result_json": None,
    }
    with Store(cfg) as st:
        st.job_insert(job)
        st.event("job-submitted", node, agent, {"id": job_id, "kind": kind})
    if not queue:
        spawn_runner(cfg, job_id)
    return job


def job_memory_gib(cfg: Config, job: dict) -> float:
    """The memory cap a job runs under (its own for `run` jobs, the configured one otherwise)."""
    if job.get("memory_max"):
        return _mem_gib(str(job["memory_max"]))
    kind = job.get("kind")
    if kind == "falsify":
        return _mem_gib(cfg.falsify_memory_max or "0")
    if kind in ("build", "check"):
        return _mem_gib(cfg.build_memory_max)
    return 0.0


def live_memory_gib(cfg: Config, jobs: list[dict]) -> float:
    return sum(job_memory_gib(cfg, j) for j in jobs)


def check_outputs(cfg: Config, outputs: list[str]) -> list[str]:
    """Normalize `--out` paths and refuse any outside the configured output roots."""
    roots = cfg.jobs_output_roots
    out = []
    for o in outputs:
        p = (cfg.root / o).resolve()
        try:
            rel = p.relative_to(cfg.root)
        except ValueError:
            raise CheckFailed(f"output {o} is outside the project; results must land under {', '.join(roots)}/")
        if not any(rel == Path(r) or Path(r) in rel.parents for r in roots):
            raise CheckFailed(f"output {o} is not under {', '.join(roots)}/ (results must be findable by other agents, not in a scratch directory)")
        out.append(str(rel))
    return out


def submit_run(cfg: Config, *, command: list[str], why: str, outputs: list[str], agent: str, node: str | None = None,
               memory_max: str | None = None, budget_min: int | None = None, cpu_cores: int | None = None,
               queue: bool = False) -> dict:
    """Submit an arbitrary command as a guarded, recorded job."""
    if not command:
        raise CheckFailed("no command given (put it after `--`)")
    if not why or not why.strip():
        raise CheckFailed("--why is required: say what the job is for")
    memory_max = memory_max or cfg.jobs_default_memory_max
    outs = check_outputs(cfg, outputs)
    if not outs:
        raise CheckFailed("--out is required: where the results will be written (under " + ", ".join(cfg.jobs_output_roots) + "/)")
    cap = _mem_gib(memory_max)
    for o in outs:
        # the job writes here; create the directory so a script that only opens the file works
        (cfg.root / o).parent.mkdir(parents=True, exist_ok=True)
    with Store(cfg) as st:
        live = st.live_jobs()
    used = live_memory_gib(cfg, live)
    budget = _mem_gib(cfg.jobs_memory_budget)
    if used + cap > budget:
        names = ", ".join(f"{j['id']} ({j.get('memory_max') or j['kind']})" for j in live)
        raise CheckFailed(f"memory budget: {used:.0f} GiB of caps already live ({names}) + {cap:.0f} GiB > budget {budget:.0f} GiB; "
                          "wait, cancel a job, or lower --mem")
    avail = available_gib()
    if avail < cap + cfg.jobs_run_margin_gib:
        raise CheckFailed(f"only {avail:.0f} GiB available; a {memory_max} job needs {cap + cfg.jobs_run_margin_gib:.0f} GiB")
    job_id = time.strftime("%Y%m%d-%H%M%S-") + uuid.uuid4().hex[:6]
    log_dir = cfg.build_log_dir
    log_dir.mkdir(parents=True, exist_ok=True)
    job = {
        "id": job_id, "kind": "run", "node": node, "argv": json.dumps(command), "cwd": str(cfg.root),
        "status": "queued", "exit_code": None, "created_at": time.time(), "started_at": None, "finished_at": None,
        "log_path": str(log_dir / f"job-{job_id}.log"), "budget_min": budget_min, "agent": agent, "pid": None, "result_json": None,
        "why": why.strip(), "memory_max": memory_max, "outputs": json.dumps(outs), "peak_mib": None, "seconds": None,
    }
    if cpu_cores:
        job["result_json"] = json.dumps({"cpu_cores": cpu_cores})
    # a process that cannot create a guarded scope (a sandbox without the systemd user bus)
    # leaves the job queued for an `es worker` running outside the sandbox
    job["queued_for_worker"] = False
    if not queue and cfg.build_guard and not bus_available():
        queue = True
        job["queued_for_worker"] = True
    row = {k: v for k, v in job.items() if k != "queued_for_worker"}
    with Store(cfg) as st:
        st.job_insert(row)
        st.event("job-submitted", node, agent, {"id": job_id, "kind": "run", "why": job["why"], "memory_max": memory_max,
                                                "outputs": outs, "command": command, "queued": queue})
    if not queue:
        spawn_runner(cfg, job_id)
    return job


def spawn_runner(cfg: Config, job_id: str) -> None:
    env = dict(os.environ)
    env["ES_PROJECT_ROOT"] = str(cfg.root)
    subprocess.Popen(
        _es_argv() + ["job", "exec", job_id],
        cwd=cfg.root, env=env, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        start_new_session=True,
    )


def run_job(cfg: Config, job_id: str) -> dict:
    with Store(cfg) as st:
        job = st.job(job_id)
        if job is None:
            raise ValueError(f"unknown job {job_id}")
        if job["status"] not in ("queued",):
            return job
        st.job_update(job["id"], status="running", started_at=time.time(), pid=os.getpid())
    argv = json.loads(job["argv"])
    env = dict(os.environ)
    env["ES_PROJECT_ROOT"] = str(cfg.root)
    if job.get("agent"):
        env["ES_AGENT"] = job["agent"]
    if job["kind"] == "run":
        return _run_command_job(cfg, job, argv)
    with open(job["log_path"], "a") as log:
        proc = subprocess.run(_es_argv() + ["--json", *argv], cwd=job["cwd"], env=env, stdout=log, stderr=subprocess.STDOUT)
    rc = proc.returncode
    result_json = None
    try:
        text = Path(job["log_path"]).read_text()
        start = text.rfind("\n{")
        if start >= 0:
            result_json = text[start + 1 :]
            json.loads(result_json)
    except (OSError, json.JSONDecodeError):
        result_json = None
    with Store(cfg) as st:
        st.job_update(job["id"], status="done" if rc == 0 else "failed", exit_code=rc, finished_at=time.time(), result_json=result_json)
        st.event("job-finished", job.get("node"), job.get("agent"), {"id": job["id"], "rc": rc})
        return st.job(job["id"]) or job


def _run_command_job(cfg: Config, job: dict, argv: list[str]) -> dict:
    """Execute a `run` job inside the guarded scope and record what it used."""
    cpu = None
    try:
        cpu = (json.loads(job.get("result_json") or "{}") or {}).get("cpu_cores")
    except json.JSONDecodeError:
        cpu = None
    # the budget and availability were checked at submission; `force` skips the
    # lean-compiler check, which is about lake builds, not about arbitrary commands
    res = run_guarded(cfg, argv, log_path=Path(job["log_path"]), budget_min=job.get("budget_min"),
                      memory_max=job.get("memory_max") or cfg.jobs_default_memory_max, cpu_quota_cores=cpu or 0,
                      env_extra={"ES_AGENT": job.get("agent") or ""}, cwd=Path(job["cwd"]), force=True, count_built=False)
    outputs = json.loads(job.get("outputs") or "[]")
    present = [o for o in outputs if (cfg.root / o).exists()]
    status = "done" if res.rc == 0 and not res.budget_exceeded else ("killed" if res.budget_exceeded else "failed")
    result = {"rc": res.rc, "seconds": round(res.seconds, 1), "peak_mib": res.peak_mib, "oom_kills": res.oom_kills,
              "budget_exceeded": res.budget_exceeded, "outputs_present": present, "outputs_missing": [o for o in outputs if o not in present],
              "refused": res.refused, "tail": res.tail[-5:]}
    with Store(cfg) as st:
        st.job_update(job["id"], status=status, exit_code=res.rc, finished_at=time.time(), peak_mib=res.peak_mib,
                      seconds=round(res.seconds, 1), result_json=json.dumps(result))
        st.event("job-finished", job.get("node"), job.get("agent"), {"id": job["id"], "kind": "run", "rc": res.rc, "status": status,
                                                                    "seconds": round(res.seconds, 1), "peak_mib": res.peak_mib,
                                                                    "memory_max": job.get("memory_max"), "why": job.get("why"),
                                                                    "outputs_present": present})
        return st.job(job["id"]) or job


def worker_loop(cfg: Config, poll_s: float = 5.0, once: bool = False) -> None:
    if cfg.build_guard and not bus_available():
        raise CheckFailed("this process cannot reach the systemd user bus, so it cannot run guarded jobs; start `es worker` from an unsandboxed shell")
    with Store(cfg) as st:
        st.event("worker-started", None, os.environ.get("ES_AGENT"), {"pid": os.getpid()})
    while True:
        with Store(cfg) as st:
            job = st.next_queued_job()
        if job is None:
            if once:
                return
            time.sleep(poll_s)
            continue
        run_job(cfg, job["id"])
        if once:
            return
