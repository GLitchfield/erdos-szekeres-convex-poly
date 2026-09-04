"""Background jobs: submitted rows in SQLite, executed by a detached `es job run` or by `es worker`."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
import uuid
from pathlib import Path

from es.config import Config
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


def spawn_runner(cfg: Config, job_id: str) -> None:
    env = dict(os.environ)
    env["ES_PROJECT_ROOT"] = str(cfg.root)
    subprocess.Popen(
        _es_argv() + ["job", "run", job_id],
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


def worker_loop(cfg: Config, poll_s: float = 5.0, once: bool = False) -> None:
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
