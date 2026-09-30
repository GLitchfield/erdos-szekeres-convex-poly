"""`es node commit`: exactly one node's files, on its node/ branch, routed to the worker when the
git metadata is read-only (a Codex sandbox)."""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

from es.context import Ctx
from es.errors import CheckFailed, UsageError

NODE = "TCore.foo_node"


def _git(root: Path, *args: str) -> str:
    return subprocess.run(["git", "-c", "user.email=t@t", "-c", "user.name=t", *args], cwd=root,
                          check=True, capture_output=True, text=True).stdout


@pytest.fixture
def branch(cfg):
    """A node branch with the node in the lock (as a targeted `es node add` leaves it) and edits
    to the node's files plus one unrelated file."""
    root = cfg.root
    # the harness commits with the repository's identity (CI runners have no global one)
    _git(root, "config", "user.email", "t@t")
    _git(root, "config", "user.name", "t")
    cfg.nodes_json.write_text(json.dumps({"nodes": []}) + "\n")
    _git(root, "add", "harness/nodes.json")
    _git(root, "commit", "-q", "-m", "index")
    _git(root, "checkout", "-q", "-b", "node/Foo")
    lock = {NODE: {"type_hash": "h", "type_pp": "True", "approved_by": "t", "approved_at": "2026-09-30",
                   "kind": "formalization", "ws": "A", "module": "TBlueprint.A.Foo"}}
    (root / "harness" / "statements.lock").write_text(json.dumps(lock, indent=1) + "\n")
    (root / "TBlueprint" / "A" / "Foo.lean").write_text("import TCore\ntheorem foo_node : True := trivial\n")
    (root / "TCore" / "Basic.lean").write_text("theorem foo : True := trivial\n-- unrelated edit\n")
    return root


def _committed(root: Path) -> list[str]:
    return sorted(_git(root, "show", "--name-only", "--format=", "HEAD").split())


def test_commits_only_the_node_files(cfg, branch):
    from es.commands.node import run_commit

    res = run_commit(Ctx(cfg), NODE, message="foo_node: close\n\nCo-Authored-By: t <t@t>")
    assert res.exit_code == 0
    assert _committed(branch) == ["TBlueprint/A/Foo.lean", "harness/statements.lock"]
    assert res.payload["left_uncommitted"] == ["TCore/Basic.lean"]
    assert _git(branch, "log", "-1", "--format=%B").startswith("foo_node: close\n\nCo-Authored-By")
    assert _git(branch, "diff", "--cached", "--name-only") == ""


def test_refuses_the_default_branch_and_a_dirty_index(cfg, branch):
    from es.commands.node import run_commit

    (branch / "TCore" / "Basic.lean").write_text("theorem foo : True := trivial\n-- staged\n")
    _git(branch, "add", "TCore/Basic.lean")
    with pytest.raises(UsageError, match="already holds staged changes"):
        run_commit(Ctx(cfg), NODE, message="m")
    _git(branch, "reset", "-q")
    _git(branch, "stash", "-q", "-u")
    _git(branch, "checkout", "-q", "main")
    _git(branch, "stash", "pop", "-q")
    with pytest.raises(UsageError, match="node/<Name>"):
        run_commit(Ctx(cfg), NODE, message="m")


def test_include_only_research_artifacts(cfg, branch):
    from es.commands.node import run_commit

    with pytest.raises(UsageError, match="only research artifacts"):
        run_commit(Ctx(cfg), NODE, message="m", include=["TCore/Basic.lean"])
    (branch / "runs" / "r").mkdir(parents=True)
    (branch / "runs" / "r" / "HANDOFF.md").write_text("handoff\n")
    run_commit(Ctx(cfg), NODE, message="m", include=["runs/r/HANDOFF.md"])
    assert "runs/r/HANDOFF.md" in _committed(branch)


def test_whitespace_problems_leave_nothing_staged(cfg, branch):
    from es.commands.node import run_commit

    (branch / "TBlueprint" / "A" / "Foo.lean").write_text("import TCore\ntheorem foo_node : True := trivial   \n")
    head = _git(branch, "rev-parse", "HEAD")
    with pytest.raises(CheckFailed, match="whitespace"):
        run_commit(Ctx(cfg), NODE, message="m")
    assert _git(branch, "rev-parse", "HEAD") == head
    assert _git(branch, "diff", "--cached", "--name-only") == ""


def test_read_only_git_queues_a_small_commit_job(cfg, branch, monkeypatch):
    from es.commands import node
    from es.store import Store

    monkeypatch.setattr(node, "git_writable", lambda _cfg: False)
    res = node.run_commit(Ctx(cfg), NODE, message="from the sandbox")
    job = res.payload["job"]
    assert res.payload["queued"] and job["status"] == "queued" and job["kind"] == "commit"
    assert job["memory_max"] == "1G" and job["lock_key"] == f"git:{branch.resolve()}"
    argv = json.loads(job["argv"])
    assert argv[:4] == ["node", "commit", NODE, "--direct"]
    assert Path(argv[argv.index("--message-file") + 1]).read_text() == "from the sandbox\n"
    with Store(cfg) as st:
        assert st.job(job["id"])["status"] == "queued"
    assert _git(branch, "log", "-1", "--format=%s") == "index\n"  # nothing committed in the sandbox


def test_the_worker_runs_the_queued_commit(cfg, branch, monkeypatch):
    """End to end: the queued job, run as `es worker` would, commits on the branch."""
    from es import jobs
    from es.commands import node

    monkeypatch.setattr(node, "git_writable", lambda _cfg: False)
    job = node.run_commit(Ctx(cfg), NODE, message="queued commit").payload["job"]
    monkeypatch.setenv("PYTHONPATH", str(Path(jobs.__file__).resolve().parents[1]) + os.pathsep
                       + os.environ.get("PYTHONPATH", ""))
    done = jobs.run_job(cfg, job["id"])
    assert done["status"] == "done", Path(done["log_path"]).read_text()
    assert _git(branch, "log", "-1", "--format=%s") == "queued commit\n"
    assert _committed(branch) == ["TBlueprint/A/Foo.lean", "harness/statements.lock"]


def test_git_writable_detects_a_read_only_git_dir(cfg, monkeypatch):
    from es.commands import node

    assert node.git_writable(cfg)
    gd = cfg.root / ".git"
    os.chmod(gd, 0o555)
    try:
        if os.access(gd, os.W_OK):  # running as root: permissions are not enforced
            pytest.skip("permissions not enforced for this user")
        assert not node.git_writable(cfg)
    finally:
        os.chmod(gd, 0o755)


def test_cli_exposes_node_commit():
    from es.spec import REGISTRY
    import es.commands.node  # noqa: F401

    spec = next(s for s in REGISTRY if s.cli == ["node", "commit"])
    assert {a.name for a in spec.args} >= {"name", "message", "message_file", "include", "direct"}
    assert sys.modules["es.commands.node"].run_commit is spec.run
