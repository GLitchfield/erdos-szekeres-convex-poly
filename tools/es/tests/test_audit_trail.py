"""The audit trail (design §8.4): recorded jobs with a memory budget, intent on claims, outcomes on
releases, the journal, the staleness warning, the hook, and the CLAUDE.md/AGENTS.md rule sync."""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

import pytest

from es.cli import main
from es.errors import CheckFailed
from es.nodes import Node, compute
from es.store import Store

HERE = Path(__file__).resolve()
REPO = HERE.parents[3]


def write_index(cfg, names=("TCore.a",)):
    nodes = []
    for name in names:
        tags = {"ws": "A", "kind": "formalization", "depends": [], "consumer": "TCore.c"}
        nodes.append(Node(name=name, module=f"TBlueprint.A.{name.split('.')[-1].capitalize()}", type_pp="True", type_hash="h" + name,
                          sorry=True, axioms=["propext"], nonstandard_axioms=[], deps_actual=[], tags=tags))
    lock = {n.name: {"type_hash": n.type_hash} for n in nodes}
    compute(cfg, nodes, [], core_names=set(), claims={}, falsify={}, lock=lock, allow=[])
    cfg.nodes_json.write_text(json.dumps({"generated_at": "now", "git_sha": "abc", "nodes": [n.to_json() for n in nodes],
                                          "destinations": [], "problems": []}))
    cfg.lock_file.write_text(json.dumps(lock))
    return nodes


def run(args, capsys):
    rc = main(args)
    return rc, capsys.readouterr().out


def test_job_run_records_command_purpose_outputs_and_resources(cfg, monkeypatch):
    from es.jobs import run_job, submit_run
    monkeypatch.setattr("es.jobs.available_gib", lambda: 100.0)
    (cfg.root / "runs").mkdir()
    job = submit_run(cfg, command=[sys.executable, "-c", "open('runs/sub/out.txt','w').write('1')"], why="write a marker",
                     outputs=["runs/sub/out.txt"], agent="tester", node=None, memory_max="1G", queue=True)
    assert (cfg.root / "runs" / "sub").is_dir()
    assert job["kind"] == "run" and job["why"] == "write a marker" and json.loads(job["outputs"]) == ["runs/sub/out.txt"]
    done = run_job(cfg, job["id"])
    assert done["status"] == "done" and done["exit_code"] == 0 and done["seconds"] is not None
    result = json.loads(done["result_json"])
    assert result["outputs_present"] == ["runs/sub/out.txt"] and result["outputs_missing"] == []
    with Store(cfg) as st:
        kinds = [(e["kind"], json.loads(e["detail"])) for e in st.events_since(0) if e["kind"].startswith("job-")]
    assert kinds[0][0] == "job-submitted" and kinds[0][1]["why"] == "write a marker"
    assert kinds[-1][0] == "job-finished" and "peak_mib" in kinds[-1][1] and kinds[-1][1]["status"] == "done"


def test_job_run_refuses_scratch_outputs_and_missing_purpose(cfg, monkeypatch):
    from es.jobs import submit_run
    monkeypatch.setattr("es.jobs.available_gib", lambda: 100.0)
    with pytest.raises(CheckFailed, match="outside the project"):
        submit_run(cfg, command=["true"], why="x", outputs=["/tmp/scratch/out.json"], agent="tester", queue=True)
    with pytest.raises(CheckFailed, match="not under runs, data"):
        submit_run(cfg, command=["true"], why="x", outputs=["docs/out.json"], agent="tester", queue=True)
    with pytest.raises(CheckFailed, match="--why"):
        submit_run(cfg, command=["true"], why="  ", outputs=["runs/o"], agent="tester", queue=True)
    with pytest.raises(CheckFailed, match="--out"):
        submit_run(cfg, command=["true"], why="x", outputs=[], agent="tester", queue=True)


def test_job_run_enforces_memory_budget(cfg, monkeypatch):
    from es.config import load_config
    from es.jobs import submit_run
    toml = cfg.root / "harness" / "config.toml"
    toml.write_text(toml.read_text() + '\n[jobs]\nmemory_budget = "3G"\n')
    cfg2 = load_config(cfg.root)
    monkeypatch.setattr("es.jobs.available_gib", lambda: 100.0)
    monkeypatch.setattr("es.jobs.bus_available", lambda: True)
    monkeypatch.setattr("es.jobs.spawn_runner", lambda cfg_, jid: None)
    first = submit_run(cfg2, command=["true"], why="first", outputs=["runs/a"], agent="tester", memory_max="2G")
    with Store(cfg2) as st:
        st.job_update(first["id"], status="running")
    with pytest.raises(CheckFailed, match="memory budget") as exc:
        submit_run(cfg2, command=["true"], why="second", outputs=["runs/b"], agent="tester", memory_max="2G")
    assert first["id"] in str(exc.value)
    small = submit_run(cfg2, command=["true"], why="third", outputs=["runs/c"], agent="tester", memory_max="1G")
    assert small["status"] == "queued"  # inserted queued; the runner flips it to running
    # a queued submission is accepted even when it does not fit now
    waiting = submit_run(cfg2, command=["true"], why="fourth", outputs=["runs/d"], agent="tester", memory_max="2G", queue=True)
    assert waiting["status"] == "queued"
    with pytest.raises(CheckFailed, match="exceeds the memory budget"):
        submit_run(cfg2, command=["true"], why="huge", outputs=["runs/e"], agent="tester", memory_max="9G", queue=True)


def test_claim_needs_why_and_release_needs_outcome_note(cfg, capsys):
    write_index(cfg)
    rc, out = run(["claim", "TCore.a"], capsys)
    assert rc != 0
    rc, out = run(["claim", "TCore.a", "--why", "prove it by induction"], capsys)
    assert rc == 0 and "prove it by induction" in out
    rc, out = run(["status"], capsys)
    assert "tester: prove it by induction" in out
    rc, out = run(["release", "TCore.a", "--outcome", "partial"], capsys)
    assert rc != 0
    rc, out = run(["release", "TCore.a", "--outcome", "partial", "--note", "base case done, step open"], capsys)
    assert rc == 0
    rc, out = run(["status"], capsys)
    assert "(partial" in out and "base case done" in out
    with Store(cfg) as st:
        att = st.attempts("TCore.a")
    assert att[-1]["outcome"] == "partial" and att[-1]["note"] == "base case done, step open"


def test_log_and_journal(cfg, capsys):
    write_index(cfg)
    rc, _ = run(["claim", "TCore.a", "--why", "try the window identity"], capsys)
    rc, out = run(["log", "the naive path lemma is false, switching to windows", "--node", "TCore.a"], capsys)
    assert rc == 0
    rc, out = run(["journal", "--since", "1h"], capsys)
    assert rc == 0 and "switching to windows" in out and "try the window identity" in out
    rc, out = run(["journal", "--since", "1h", "--kind", "log"], capsys)
    assert "switching to windows" in out and "try the window identity" not in out
    rc, out = run(["journal", "--since", "1h", "--agent", "nobody"], capsys)
    assert "nothing recorded" in out


def test_log_repeatable_attachments_are_immutable_artifacts(cfg, capsys, monkeypatch):
    import importlib

    from es.artifacts import read

    log_cmd = importlib.import_module("es.commands.log")
    (cfg.root / "runs").mkdir(exist_ok=True)
    first = cfg.root / "runs" / "first.txt"
    second = cfg.root / "runs" / "second.txt"
    first.write_bytes(b"first evidence")
    second.write_bytes(b"second evidence")
    monkeypatch.chdir(cfg.root)
    rc, out = run(["log", "attached finding", "--attach", "runs/first.txt",
                   "--attach", "runs/second.txt"], capsys)
    assert rc == 0 and "attached artifact(s)" in out
    with Store(cfg) as st:
        event = dict(st.events_since(0, kinds=["log"])[-1])
    detail = json.loads(event["detail"])
    refs = detail["artifacts"]
    assert [read(cfg, ref["id"]) for ref in refs] == [b"first evidence", b"second evidence"]
    assert [ref["source"] for ref in refs] == ["runs/first.txt", "runs/second.txt"]

    monkeypatch.setattr(log_cmd, "LOG_ATTACHMENT_MAX_BYTES", 4)
    too_large = cfg.root / "runs" / "too-large.txt"
    too_large.write_bytes(b"12345")
    rc = main(["log", "oversized", "--attach", "runs/too-large.txt"])
    captured = capsys.readouterr()
    assert rc != 0
    assert "attachment exceeds 4 bytes" in captured.err


def test_release_preserves_cited_worktree_evidence_without_overwrite(cfg, tmp_path, monkeypatch):
    import importlib

    from es.artifacts import read
    from es.commands.claims import run_release
    from es.config import load_config
    from es.context import Ctx

    write_index(cfg)
    wt = tmp_path / "runs" / "worktrees" / "wt"
    shutil.copytree(cfg.root, wt, ignore=shutil.ignore_patterns(".git"))
    (wt / ".git").write_text(f"gitdir: {cfg.root}/.git/worktrees/wt\n")
    evidence = wt / "runs" / "handoff" / "FINDINGS.md"
    evidence.parent.mkdir(parents=True)
    evidence.write_text("durable finding\n")
    evidence.chmod(0o640)
    wt_cfg = load_config(wt)
    with Store(wt_cfg) as st:
        st.claim("TCore.a", "tester", ttl_hours=1, note="test preservation")
    result = run_release(Ctx(cfg=wt_cfg, json_mode=False, agent="tester"), "TCore.a", "partial",
                         note=f"see {evidence}")
    primary_copy = cfg.root / "runs" / "handoff" / "FINDINGS.md"
    assert primary_copy.read_text() == "durable finding\n"
    assert primary_copy.stat().st_mode & 0o777 == 0o640
    assert result.payload["evidence"]["copied"] == ["runs/handoff/FINDINGS.md"]

    with Store(wt_cfg) as st:
        st.claim("TCore.a", "tester", ttl_hours=1, note="test conflict")
    evidence.write_text("different finding\n")
    result = run_release(Ctx(cfg=wt_cfg, json_mode=False, agent="tester"), "TCore.a", "partial",
                         note="see runs/worktrees/wt/runs/handoff/FINDINGS.md")
    with Store(wt_cfg) as st:
        assert "TCore.a" not in st.claims()
    assert primary_copy.read_text() == "durable finding\n"
    assert read(wt_cfg, result.payload["evidence"]["artifacts"][0]["id"]) == b"different finding\n"

    evidence.write_text("durable finding\n")
    primary_copy.unlink()
    primary_copy.symlink_to(evidence)
    with Store(wt_cfg) as st:
        st.claim("TCore.a", "tester", ttl_hours=1, note="test final symlink")
    result = run_release(Ctx(cfg=wt_cfg, json_mode=False, agent="tester"), "TCore.a", "partial",
                         note="see runs/handoff/FINDINGS.md")
    with Store(wt_cfg) as st:
        assert "TCore.a" not in st.claims()
    assert result.payload["evidence"]["artifacts"]

    primary_copy.unlink()
    primary_copy.parent.rmdir()
    outside = tmp_path / "outside"
    outside.mkdir()
    primary_copy.parent.symlink_to(outside, target_is_directory=True)
    with Store(wt_cfg) as st:
        st.claim("TCore.a", "tester", ttl_hours=1, note="test parent symlink")
    result = run_release(Ctx(cfg=wt_cfg, json_mode=False, agent="tester"), "TCore.a", "partial",
                         note="see runs/handoff/FINDINGS.md")
    with Store(wt_cfg) as st:
        assert "TCore.a" not in st.claims()
    assert result.payload["evidence"]["artifacts"]
    assert not (outside / "FINDINGS.md").exists()

    primary_copy.parent.unlink()
    primary_copy.parent.mkdir()
    evidence.write_text("publication failed\n")
    claims_cmd = importlib.import_module("es.commands.claims")

    def unavailable(_source, _destination):
        raise OSError("simulated publication failure")

    monkeypatch.setattr(claims_cmd, "_publish_without_overwrite", unavailable)
    with Store(wt_cfg) as st:
        st.claim("TCore.a", "tester", ttl_hours=1, note="test publication failure")
    result = run_release(Ctx(cfg=wt_cfg, json_mode=False, agent="tester"), "TCore.a", "partial",
                         note="see runs/handoff/FINDINGS.md")
    with Store(wt_cfg) as st:
        assert "TCore.a" not in st.claims()
    artifact = result.payload["evidence"]["artifacts"][0]
    assert "simulated publication failure" in artifact["reason"]
    assert read(wt_cfg, artifact["id"]) == b"publication failed\n"


def test_status_and_ready_warn_when_lock_has_unindexed_nodes(cfg, capsys):
    write_index(cfg)
    lock = json.loads(cfg.lock_file.read_text())
    lock["TCore.added_later"] = {"type_hash": "x"}
    cfg.lock_file.write_text(json.dumps(lock))
    rc, out = run(["status"], capsys)
    assert rc == 0 and "index is stale: 1 node(s)" in out and "added_later" in out
    rc, out = run(["ready"], capsys)
    assert "index is stale" in out


def test_status_lists_live_jobs(cfg, capsys, monkeypatch):
    from es.jobs import submit_run
    write_index(cfg)
    monkeypatch.setattr("es.jobs.available_gib", lambda: 100.0)
    job = submit_run(cfg, command=["sleep", "0"], why="a sweep for the table", outputs=["runs/t"], agent="tester", queue=True)
    rc, out = run(["status"], capsys)
    assert "jobs live: 1" in out and "a sweep for the table" in out and job["id"] in out


def test_burn_down_deduplicates_release_close_and_index_transition(cfg):
    from es.commands.status import burn_down

    with Store(cfg) as st:
        st.claim("TCore.a", "tester", ttl_hours=1)
        st.release("TCore.a", "tester", outcome="closed")
        st.event("closed", "TCore.a", "tester")
        st.event("index-status", "TCore.a", "tester",
                 {"from": "open", "to": "closed", "primary_checkout": True})
        st.event("index-status", "TCore.b", "tester",
                 {"from": "open", "to": "closed", "primary_checkout": True})
        st.event("index-status", "TCore.worktree_only", "tester",
                 {"from": "open", "to": "closed", "primary_checkout": False})
        st.event("index-status", "TCore.legacy_untagged", "tester",
                 {"from": "open", "to": "closed"})
        st.claim("TCore.c", "tester", ttl_hours=1)
        st.release("TCore.c", "tester", outcome="partial")
    rows = burn_down(cfg, weeks=1)
    assert sum(row["closed"] for row in rows) == 2


def test_status_computes_burn_down_once(cfg, capsys, monkeypatch):
    import es.commands.status as status_cmd

    write_index(cfg)
    original = status_cmd.burn_down
    calls = 0

    def counted(*args, **kwargs):
        nonlocal calls
        calls += 1
        return original(*args, **kwargs)

    monkeypatch.setattr(status_cmd, "burn_down", counted)
    rc, _ = run(["status"], capsys)
    assert rc == 0
    assert calls == 1


def test_status_renders_consumer_free_root_cone(cfg, capsys):
    write_index(cfg, names=("TCore.a", "TCore.root"))
    data = json.loads(cfg.nodes_json.read_text())
    for rec in data["nodes"]:
        if rec["name"] == "TCore.a":
            rec["status"] = "closed"
        else:
            rec["status"] = "open"
            rec["tags"].pop("consumer")
            rec["deps_actual"] = ["TCore.a"]
    cfg.nodes_json.write_text(json.dumps(data))
    rc, out = run(["status"], capsys)
    assert rc == 0 and "root cones (indexed Lean dependencies" in out
    assert "TCore.root" in out and "open root" in out


def test_hook_blocks_bare_nohup_and_systemd_run():
    hook = REPO / "tools" / "es" / "hooks" / "pre_bash.sh"

    def rc_for(command: str) -> int:
        return subprocess.run(["bash", str(hook)], input=json.dumps({"tool_input": {"command": command}}), text=True,
                              capture_output=True).returncode

    assert rc_for("nohup python3 scripts/sweep.py > runs/x.log &") == 2
    assert rc_for("systemd-run --user --scope -p MemoryMax=2G -- python3 x.py") == 2
    assert rc_for("tools/es/bin/es job run --why x --out runs/a -- python3 x.py") == 0
    assert rc_for("ls -la; echo nohup_is_not_a_word_boundary_here") == 0


def test_agents_md_rules_match_claude_md():
    claude = [line for line in (REPO / "CLAUDE.md").read_text().splitlines() if line.startswith("- ")]
    agents = [line for line in (REPO / "AGENTS.md").read_text().splitlines() if line.startswith("- ")]
    assert claude, "CLAUDE.md has no rule lines"
    assert claude == agents, "AGENTS.md rule list differs from CLAUDE.md: edit both"
    for cmd in ("es job run", "es claim", "es release", "es log", "es journal"):
        assert any(cmd in line for line in claude), f"rules do not mention {cmd}"


def test_read_only_database_serves_reads_and_refuses_writes(cfg, capsys):
    """A sandboxed agent (Codex workspace-write) can read the shared state; writes fail with the fix spelled out."""
    import os
    from es.errors import EsError
    write_index(cfg)
    with Store(cfg) as st:
        st.claim("TCore.a", "other-agent", ttl_hours=1, note="theirs")
    db = cfg.db_path
    os.chmod(db, 0o444)
    os.chmod(db.parent, 0o555)
    try:
        with Store(cfg) as st:
            assert st.readonly
            assert st.claims()["TCore.a"]["agent"] == "other-agent"
            with pytest.raises(EsError, match="read-only"):
                st.log("x", None, "me")
        rc, out = run(["status"], capsys)
        assert rc == 0 and "other-agent: theirs" in out
        rc, out = run(["journal", "--since", "1h", "--no-commits"], capsys)
        assert rc == 0 and "theirs" in out
        rc, out = run(["log", "trying to write from a sandbox"], capsys)
        assert rc == 2
    finally:
        os.chmod(db.parent, 0o755)
        os.chmod(db, 0o644)
    with Store(cfg) as st:
        assert not st.readonly


def test_es_home_from_config_is_inside_the_checkout(cfg, monkeypatch):
    from es.config import load_config
    monkeypatch.delenv("ES_HOME", raising=False)
    toml = cfg.root / "harness" / "config.toml"
    toml.write_text(toml.read_text().replace('id = "testproj"', 'id = "testproj"\nes_home = ".es"'))
    cfg2 = load_config(cfg.root)
    assert cfg2.es_home == (cfg.root / ".es" / "testproj").resolve()
    assert cfg2.db_path.parent == cfg2.es_home
    monkeypatch.setenv("ES_HOME", str(cfg.root / "elsewhere"))
    assert load_config(cfg.root).es_home == cfg.root / "elsewhere" / "testproj"


def test_job_run_queues_when_the_bus_is_unreachable(cfg, monkeypatch, capsys):
    from es.jobs import submit_run
    monkeypatch.setattr("es.jobs.available_gib", lambda: 100.0)
    monkeypatch.setattr("es.jobs.bus_available", lambda: False)
    toml = cfg.root / "harness" / "config.toml"
    toml.write_text(toml.read_text().replace("guard = false", "guard = true"))
    from es.config import load_config
    cfg2 = load_config(cfg.root)
    job = submit_run(cfg2, command=["true"], why="from a sandbox", outputs=["runs/s"], agent="codex:1")
    assert job["status"] == "queued" and job["queued_for_worker"]
    write_index(cfg2)
    rc, out = run(["job", "requeue", job["id"]], capsys)
    assert rc != 0  # still queued
    with Store(cfg2) as st:
        st.job_update(job["id"], status="failed", exit_code=1)
    rc, out = run(["job", "requeue", job["id"][:15]], capsys)
    assert rc == 0
    with Store(cfg2) as st:
        assert st.job(job["id"])["status"] == "queued"


def test_status_uses_live_claims_and_lists_claims_on_unindexed_nodes(cfg, capsys):
    from es.errors import UsageError
    write_index(cfg)
    with Store(cfg) as st:
        st.claim("TCore.a", "agent-x", ttl_hours=1, note="prove it")
        st.claim("TCore.on_a_branch", "agent-y", ttl_hours=1, note="new node in a worktree")
    # the index was written before the claim; status must still show the claim, and the release after it
    rc, out = run(["status"], capsys)
    assert "agent-x: prove it" in out and "claimed" in out
    assert "not in this index" in out and "on_a_branch" in out and "agent-y" in out
    rc, out = run(["ready"], capsys)
    assert "TCore.a" not in out
    with Store(cfg) as st:
        st.release("TCore.a", "agent-x", outcome="partial", note="half")
    rc, out = run(["status"], capsys)
    assert "(partial" in out and "agent-x: prove it" not in out
    rc, out = run(["ready"], capsys)
    assert "TCore.a" in out
    with Store(cfg) as st:
        with pytest.raises(UsageError, match="unexpanded"):
            st.log("x", None, "codex:${CODEX_THREAD_ID:-x}")


def test_forced_claim_keeps_its_purpose(cfg, capsys):
    write_index(cfg, names=("TCore.a", "TCore.b"))
    import json
    data = json.loads(cfg.nodes_json.read_text())
    for rec in data["nodes"]:
        if rec["name"] == "TCore.b":
            rec["ready"], rec["blocked_by"] = False, ["TCore.a"]
    cfg.nodes_json.write_text(json.dumps(data))
    rc, out = run(["claim", "TCore.b", "--why", "prove it anyway", "--force"], capsys)
    assert rc == 0
    with Store(cfg) as st:
        assert st.claims()["TCore.b"]["note"] == "prove it anyway"


def test_worktree_shares_the_primary_checkout_state(cfg, monkeypatch, tmp_path):
    from es.config import load_config, primary_root
    monkeypatch.delenv("ES_HOME", raising=False)
    toml = cfg.root / "harness" / "config.toml"
    toml.write_text(toml.read_text().replace('id = "testproj"', 'id = "testproj"\nes_home = ".es"'))
    wt = tmp_path / "wt"
    shutil.copytree(cfg.root, wt, ignore=shutil.ignore_patterns(".git"))
    (wt / ".git").write_text(f"gitdir: {cfg.root}/.git/worktrees/wt\n")
    assert primary_root(wt) == cfg.root
    assert load_config(wt).es_home == (cfg.root / ".es" / "testproj").resolve()
    assert load_config(cfg.root).es_home == (cfg.root / ".es" / "testproj").resolve()


def test_configured_git_dir_uses_linked_worktree_metadata(cfg, monkeypatch, tmp_path):
    from es.config import load_config
    from es.gitutil import head_sha
    from es.nodes import opened_dates

    toml = cfg.root / "harness" / "config.toml"
    toml.write_text(toml.read_text() + '\n[git]\ngit_dir = ".git-data"\n')
    subprocess.run(["git", "-c", "user.email=t@t", "-c", "user.name=t", "add", "harness/config.toml"],
                   cwd=cfg.root, check=True)
    subprocess.run(["git", "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-q", "-m", "configure git dir"],
                   cwd=cfg.root, check=True)
    wt = tmp_path / "configured-wt"
    subprocess.run(["git", "worktree", "add", "-q", "-b", "configured-wt", str(wt)], cwd=cfg.root, check=True)

    monkeypatch.setenv("ES_PROJECT_ROOT", str(wt))
    wt_cfg = load_config(wt)
    pointer = Path((wt / ".git").read_text().removeprefix("gitdir:").strip())
    assert wt_cfg.git_dir == pointer
    assert head_sha(wt_cfg) == subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=wt, text=True).strip()
    assert opened_dates(wt_cfg, ["TBlueprint.A.Foo"])["TBlueprint.A.Foo"] != "uncommitted"


def test_worker_starts_queued_jobs_within_the_budget(cfg, monkeypatch):
    from es.config import load_config
    from es.jobs import submit_run, worker_start_fitting
    toml = cfg.root / "harness" / "config.toml"
    toml.write_text(toml.read_text() + '\n[jobs]\nmemory_budget = "5G"\n')
    cfg2 = load_config(cfg.root)
    monkeypatch.setattr("es.jobs.available_gib", lambda: 100.0)
    a = submit_run(cfg2, command=["true"], why="a", outputs=["runs/a"], agent="t", memory_max="3G", queue=True)
    b = submit_run(cfg2, command=["true"], why="b", outputs=["runs/b"], agent="t", memory_max="3G", queue=True)
    c = submit_run(cfg2, command=["true"], why="c", outputs=["runs/c"], agent="t", memory_max="2G", queue=True)
    spawned = []
    started = worker_start_fitting(cfg2, spawn=lambda cfg_, jid: spawned.append(jid))
    # a (3G) fits, b (3G) would exceed 5G, c (2G) fits next to a
    assert started == [a["id"], c["id"]] and spawned == started
    with Store(cfg2) as st:
        assert st.job(b["id"])["status"] == "queued" and st.job(a["id"])["status"] == "starting"
    # queued submission is allowed even when it does not fit now
    big = submit_run(cfg2, command=["true"], why="d", outputs=["runs/d"], agent="t", memory_max="4G", queue=True)
    assert big["status"] == "queued"


def test_worker_refuses_live_project_lock_but_ignores_stale_file(cfg, monkeypatch):
    from es.jobs import worker_lock, worker_loop

    monkeypatch.setattr("es.jobs.bus_available", lambda: True)
    monkeypatch.setattr("es.jobs.worker_start_fitting", lambda cfg_: [])
    monkeypatch.setattr("es.operations.advance", lambda cfg_: None)
    monkeypatch.setattr("es.run_monitor.tick", lambda cfg_: None)

    with worker_lock(cfg):
        with pytest.raises(CheckFailed, match="another es worker is already running"):
            worker_loop(cfg, once=True)

    lock_path = cfg.es_home / "worker.lock"
    lock_path.write_text("999999")
    worker_loop(cfg, once=True)
    assert lock_path.read_text() == str(os.getpid())


def test_worker_lock_blocks_a_second_process_until_release(cfg):
    from es.jobs import worker_lock

    probe = """
import sys
from pathlib import Path
from es.config import load_config
from es.errors import CheckFailed
from es.jobs import worker_lock

try:
    with worker_lock(load_config(Path(sys.argv[1]))):
        pass
except CheckFailed as exc:
    print(exc, file=sys.stderr)
    raise SystemExit(3)
"""
    with worker_lock(cfg):
        blocked = subprocess.run(
            [sys.executable, "-c", probe, str(cfg.root)], capture_output=True, text=True)
    assert blocked.returncode == 3
    assert "another es worker is already running" in blocked.stderr

    released = subprocess.run(
        [sys.executable, "-c", probe, str(cfg.root)], capture_output=True, text=True)
    assert released.returncode == 0, released.stderr
