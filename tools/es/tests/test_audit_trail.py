"""The audit trail (design §8.4): recorded jobs with a memory budget, intent on claims, outcomes on
releases, the journal, the staleness warning, the hook, and the CLAUDE.md/AGENTS.md rule sync."""
from __future__ import annotations

import json
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
    job = submit_run(cfg, command=[sys.executable, "-c", "open('runs/out.txt','w').write('1')"], why="write a marker",
                     outputs=["runs/out.txt"], agent="tester", node=None, memory_max="1G", queue=True)
    assert job["kind"] == "run" and job["why"] == "write a marker" and json.loads(job["outputs"]) == ["runs/out.txt"]
    done = run_job(cfg, job["id"])
    assert done["status"] == "done" and done["exit_code"] == 0 and done["seconds"] is not None
    result = json.loads(done["result_json"])
    assert result["outputs_present"] == ["runs/out.txt"] and result["outputs_missing"] == []
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
    first = submit_run(cfg2, command=["true"], why="first", outputs=["runs/a"], agent="tester", memory_max="2G", queue=True)
    with pytest.raises(CheckFailed, match="memory budget") as exc:
        submit_run(cfg2, command=["true"], why="second", outputs=["runs/b"], agent="tester", memory_max="2G", queue=True)
    assert first["id"] in str(exc.value)
    small = submit_run(cfg2, command=["true"], why="third", outputs=["runs/c"], agent="tester", memory_max="1G", queue=True)
    assert small["status"] == "queued"


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
