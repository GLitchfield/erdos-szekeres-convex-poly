"""Progress-review checkpoints: long jobs are reviewed, never killed by an arbitrary clock."""
import json
import time

import pytest

from es.commands.jobs import job_rows, run_review, run_status, run_wait
from es.context import Ctx
from es.errors import UsageError
from es.jobs import review_due, review_due_at, submit, submit_run
from es.store import Store


def running(cfg, *, started_ago_min, review=None):
    job = submit_run(cfg, command=["true"], why="review test", outputs=["runs/result"], agent="tester",
                     queue=True, review_min=review)
    with Store(cfg) as st:
        st.job_update(job["id"], status="running", started_at=time.time() - 60 * started_ago_min)
        return st.job(job["id"])


def test_jobs_get_the_configured_first_checkpoint(cfg):
    job = running(cfg, started_ago_min=1)
    assert job["review_min"] == cfg.jobs_review_after_min == 20
    assert review_due_at(job) == pytest.approx(job["started_at"] + 20 * 60)
    assert not review_due(job)
    assert running(cfg, started_ago_min=1, review=5)["review_min"] == 5


def test_wait_returns_at_a_due_review_and_the_job_keeps_running(cfg, monkeypatch):
    job = running(cfg, started_ago_min=25)
    monkeypatch.setattr("es.commands.jobs.time.sleep", lambda _: pytest.fail("a due review must not wait"))
    result = run_wait(Ctx(cfg), job["id"])
    assert result.payload["review_due"] is True and result.payload["terminal"] is False
    assert "REVIEW CHECKPOINT" in result.human[0] and "never stops the job" in result.human[0]
    with Store(cfg) as st:
        assert st.job(job["id"])["status"] == "running"
    assert "REVIEW DUE" in job_rows([job])[0][3]
    assert any("REVIEW DUE" in line for line in run_status(Ctx(cfg), job["id"]).human)


def test_review_records_the_decision_and_schedules_the_next(cfg, monkeypatch):
    job = running(cfg, started_ago_min=25)
    with pytest.raises(UsageError):
        run_review(Ctx(cfg), job["id"], note="  ")
    res = run_review(Ctx(cfg), job["id"], note="3 of 8 cases done at 4 min each; leave it", next=30)
    with Store(cfg) as st:
        after = st.job(job["id"])
        ev = [dict(r) for r in st.conn.execute("SELECT * FROM events WHERE kind='job-review'")]
    assert after["status"] == "running" and not review_due(after)
    assert after["review_at"] == pytest.approx(time.time() + 30 * 60, abs=5)
    detail = json.loads(ev[-1]["detail"])
    assert detail["note"].startswith("3 of 8") and detail["next_review_min"] == 30 and detail["elapsed_min"] >= 24
    # not due any more: an ordinary wait window
    now = [0.0]
    monkeypatch.setattr("es.commands.jobs.time.monotonic", lambda: now[0])
    monkeypatch.setattr("es.commands.jobs.time.sleep", lambda s: now.__setitem__(0, now[0] + s))
    assert run_wait(Ctx(cfg), job["id"], timeout=2).payload["timed_out"] is True
    assert res.payload["job_id"] == job["id"]


def test_review_zero_disables_checkpoints(cfg):
    job = running(cfg, started_ago_min=500, review=0)
    assert review_due_at(job) is None and not review_due(job)


def test_finished_jobs_are_not_reviewed(cfg):
    job = running(cfg, started_ago_min=25)
    with Store(cfg) as st:
        st.job_update(job["id"], status="done", exit_code=0)
        done = st.job(job["id"])
    assert not review_due(done)
    with pytest.raises(UsageError, match="review the outputs"):
        run_review(Ctx(cfg), job["id"], note="late")


def test_background_falsify_has_no_default_time_limit(cfg, monkeypatch):
    from types import SimpleNamespace

    from es.commands import falsify

    node = SimpleNamespace(name="TCore.foo_node", falsifier="f.py", short="foo_node")
    monkeypatch.setattr(falsify, "find_node", lambda *_: node)
    (cfg.falsifiers_dir).mkdir(parents=True, exist_ok=True)
    (cfg.falsifiers_dir / "f.py").write_text("print('ok')\n")
    job = falsify.run(Ctx(cfg), node.name, async_=True).payload["job"]
    assert job["budget_min"] is None and "--timeout=0" in json.loads(job["argv"])
    assert job["review_min"] == cfg.jobs_review_after_min
    explicit = falsify.run(Ctx(cfg), node.name, async_=True, timeout=90).payload["job"]
    assert explicit["budget_min"] == 90 and "--timeout=90" in json.loads(explicit["argv"])


def test_submit_accepts_a_review_interval(cfg):
    job = submit(cfg, kind="check", node=None, argv=["check", "x"], agent="t", queue=True, review_min=7)
    assert job["review_min"] == 7


def test_falsify_memory_cap_can_be_sized(cfg, monkeypatch):
    from types import SimpleNamespace

    from es.commands import falsify

    node = SimpleNamespace(name="TCore.foo_node", falsifier="f.py", short="foo_node")
    monkeypatch.setattr(falsify, "find_node", lambda *_: node)
    (cfg.falsifiers_dir).mkdir(parents=True, exist_ok=True)
    (cfg.falsifiers_dir / "f.py").write_text("print('ok')\n")
    job = falsify.run(Ctx(cfg), node.name, async_=True, mem="2G").payload["job"]
    assert job["memory_max"] == "2G" and "--mem=2G" in json.loads(job["argv"])
    assert falsify.run(Ctx(cfg), node.name, async_=True).payload["job"]["memory_max"] == cfg.falsify_memory_max
