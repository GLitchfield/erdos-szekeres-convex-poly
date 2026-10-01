"""Memory caps sized to a module's import closure (`es node add`, `es check`, targeted extract)."""
from __future__ import annotations

import os
from pathlib import Path
from types import SimpleNamespace

from es.build import BuildResult
from es.context import Ctx

import pytest

CLOSURE = ["TCore", "TCore.Basic", "TCore.Consumer", "TCore.Chunk000", "TCore.Encoding"]


@pytest.fixture(autouse=True)
def lake_says_current(monkeypatch):
    from es.commands import node

    state = {"built": True, "calls": []}

    def fake(cfg, modules, mods):
        state["calls"].append(list(modules))
        return state["built"], "" if state["built"] else "a dependency needs a rebuild"

    monkeypatch.setattr(node, "dependencies_built", fake)
    return state


def _olean(cfg, module: str, size: int = 1024, *, age: float = 0.0) -> Path:
    lib = cfg.root / ".lake" / "build" / "lib" / "lean"
    path = lib / Path(*module.split(".")).with_suffix(".olean")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("wb") as fh:
        fh.truncate(size)  # sparse: st_size counts, the disk does not
    src = cfg.root / Path(*module.split(".")).with_suffix(".lean")
    stamp = src.stat().st_mtime + 60 - age
    os.utime(path, (stamp, stamp))
    return path


def test_thin_closure_gets_the_floor(cfg):
    from es.commands.node import closure_stats, elaboration_memory_max, targeted_extract_memory_max

    for m in CLOSURE:
        _olean(cfg, m)
    gib, unbuilt = closure_stats(cfg, ["TBlueprint.A.Foo"])
    assert unbuilt == [] and gib < 0.001
    assert elaboration_memory_max(cfg, ["TBlueprint.A.Foo"]) == "4G"
    assert targeted_extract_memory_max(cfg, gib) == "4G"


def test_cap_grows_with_the_closure_and_stops_at_the_configured_cap(cfg):
    from es.commands.node import closure_stats, elaboration_memory_max, targeted_extract_memory_max

    for m in CLOSURE:
        _olean(cfg, m)
    _olean(cfg, "TCore.Basic", 2 * 2**30)
    gib, _ = closure_stats(cfg, ["TBlueprint.A.Foo"])
    assert 2.0 <= gib < 2.01
    assert elaboration_memory_max(cfg, ["TBlueprint.A.Foo"]) == "12G"  # ceil(3 + 4 * 2.0...)
    assert targeted_extract_memory_max(cfg, gib) == "8G"  # ceil(3 + 2 * 2.0...)
    _olean(cfg, "TCore.Basic", 5 * 2**30)
    assert elaboration_memory_max(cfg, ["TBlueprint.A.Foo"]) == cfg.build_memory_max
    assert targeted_extract_memory_max(cfg, 5.0) == cfg.extract_targeted_memory_max


def test_a_dependency_needing_a_rebuild_gets_the_full_cap(cfg, lake_says_current):
    from es.commands.node import closure_stats, elaboration_memory_max

    for m in CLOSURE:
        if m != "TCore.Encoding":
            _olean(cfg, m)
    assert closure_stats(cfg, ["TBlueprint.A.Foo"])[1] == ["TCore.Encoding"]
    assert elaboration_memory_max(cfg, ["TBlueprint.A.Foo"]) == cfg.build_memory_max
    assert lake_says_current["calls"] == []  # a missing olean needs no second opinion
    _olean(cfg, "TCore.Encoding")
    assert elaboration_memory_max(cfg, ["TBlueprint.A.Foo"]) == "4G"
    # every olean present, but Lake's traces say a dependency changed
    lake_says_current["built"] = False
    assert elaboration_memory_max(cfg, ["TBlueprint.A.Foo"]) == cfg.build_memory_max


def test_dependencies_built_asks_lake_about_the_imports_only(cfg, monkeypatch):
    from es.commands import node
    from es.modules import scan_modules

    monkeypatch.undo()  # the real dependencies_built
    seen = []

    def fake(cfg_, argv, **kw):
        seen.append((argv, kw["memory_max"]))
        return _result(rc=0 if len(seen) == 1 else 3)

    monkeypatch.setattr(node, "run_guarded", fake)
    mods = scan_modules(cfg)
    assert node.dependencies_built(cfg, ["TBlueprint.A.Foo"], mods) == (True, "")
    assert seen[0] == ([cfg.lake, "build", "--no-build", "TCore"], cfg.build_nobuild_memory_max)
    assert node.dependencies_built(cfg, ["TBlueprint.A.Foo"], mods) == (False, "a dependency needs a rebuild")
    monkeypatch.setattr(node, "run_guarded", lambda *_a, **_k: _result(rc=125, refused="busy"))
    assert node.dependencies_built(cfg, ["TBlueprint.A.Foo"], mods) == (False, "busy")
    assert node.dependencies_built(cfg, ["TCore.Basic"], mods) == (True, "")  # no project imports


def test_the_target_itself_may_be_unbuilt(cfg):
    from es.commands.node import closure_stats

    for m in CLOSURE:
        _olean(cfg, m)
    assert closure_stats(cfg, ["TBlueprint.A.Foo"])[1] == []


def test_sizing_is_configurable(cfg):
    from es.commands.node import elaboration_memory_max

    for m in CLOSURE:
        _olean(cfg, m)
    cfg.raw["build"].update(elaborate_memory_base="1G", elaborate_memory_min="2G")
    assert elaboration_memory_max(cfg, ["TBlueprint.A.Foo"]) == "2G"


def _result(*, rc=0, oom=0, refused=None, log="x.log"):
    return BuildResult(rc, 1.0, 0, log, ["lake"], oom_kills=oom, refused=refused, tail=["tail"])


def test_oom_under_the_sized_cap_retries_once_at_the_full_cap(cfg, monkeypatch, tmp_path):
    from es import build

    calls = []

    def fake(cfg_, argv, **kw):
        calls.append((kw["memory_max"], Path(kw["log_path"]).name))
        return _result(rc=-9, oom=1) if len(calls) == 1 else _result()

    monkeypatch.setattr(build, "run_guarded", fake)
    res = build.run_guarded_retry(cfg, ["lake", "build", "M"], log_path=tmp_path / "elab.log", budget_min=1,
                                  memory_max="4G", retry_memory_max="20G")
    assert res.ok
    assert calls == [("4G", "elab.log"), ("20G", "elab-retry.log")]
    assert "retried under 20G" in res.tail[0]


def test_no_retry_without_an_oom_kill_or_headroom(cfg, monkeypatch, tmp_path):
    from es import build

    calls = []
    monkeypatch.setattr(build, "run_guarded", lambda cfg_, argv, **kw: calls.append(kw["memory_max"]) or _result(rc=1))
    res = build.run_guarded_retry(cfg, ["lake"], log_path=tmp_path / "a.log", budget_min=1,
                                  memory_max="4G", retry_memory_max="20G")
    assert not res.ok and calls == ["4G"]  # an ordinary compile error is not retried
    calls.clear()
    monkeypatch.setattr(build, "run_guarded", lambda cfg_, argv, **kw: calls.append(kw["memory_max"]) or _result(rc=-9, oom=1))
    build.run_guarded_retry(cfg, ["lake"], log_path=tmp_path / "a.log", budget_min=1,
                            memory_max="20G", retry_memory_max="20G")
    assert calls == ["20G"]


def test_a_refused_retry_reports_the_original_oom(cfg, monkeypatch, tmp_path):
    from es import build

    results = iter([_result(rc=-9, oom=1), _result(rc=125, refused="20G cannot fit shared budget 30G")])
    monkeypatch.setattr(build, "run_guarded", lambda cfg_, argv, **kw: next(results))
    res = build.run_guarded_retry(cfg, ["lake"], log_path=tmp_path / "a.log", budget_min=1,
                                  memory_max="4G", retry_memory_max="20G")
    assert res.oom_kills == 1 and res.refused is None
    assert "retry under 20G refused (20G cannot fit shared budget 30G)" in res.tail[-1]


def test_elaborate_module_and_check_request_the_sized_cap(cfg, monkeypatch):
    from es.commands import check, node

    for m in CLOSURE:
        _olean(cfg, m)
    seen = []

    def fake(cfg_, argv, **kw):
        seen.append((argv[-1], kw["memory_max"], kw["retry_memory_max"]))
        return _result()

    monkeypatch.setattr(node, "run_guarded_retry", fake)
    node.elaborate_module(Ctx(cfg), "TBlueprint.A.Foo")
    assert seen == [("TBlueprint.A.Foo", "4G", cfg.build_memory_max)]

    declaration = SimpleNamespace(name="TCore.foo_node", module="TBlueprint.A.Foo", short="foo_node")
    monkeypatch.setattr(check, "find_node", lambda *_: declaration)
    monkeypatch.setattr(check, "run_guarded_retry",
                        lambda cfg_, argv, **kw: seen.append((argv[-1], kw["memory_max"], kw["retry_memory_max"]))
                        or SimpleNamespace(ok=False, seconds=0, peak_mib=0, tail=[], summary=lambda: "rc=1"))
    check.run(Ctx(cfg), declaration.name, targeted=True)
    assert seen[-1] == ("TBlueprint.A.Foo", "4G", cfg.build_memory_max)


def test_targeted_extract_sizes_the_build_and_the_extractor(cfg, monkeypatch):
    from es.commands import extract, node

    for m in CLOSURE:
        _olean(cfg, m)
    seen = {}
    monkeypatch.setattr(extract, "run_extract", lambda ctx, **kw: seen.update(kw) or ({}, [], []))
    node.targeted_extract(Ctx(cfg), "TBlueprint.A.Foo")
    assert seen["memory_max"] == "4G" and seen["build_memory_max"] == "4G"
    assert seen["imports"] == ["TBlueprint.A.Foo"]


def test_async_targeted_check_reserves_the_sized_cap(cfg, monkeypatch):
    from es.commands import check

    for m in CLOSURE:
        _olean(cfg, m)
    declaration = SimpleNamespace(name="TCore.foo_node", module="TBlueprint.A.Foo", short="foo_node")
    monkeypatch.setattr(check, "find_node", lambda *_: declaration)
    monkeypatch.setattr("es.jobs.spawn_runner", lambda *_a, **_k: None)
    job = check.run(Ctx(cfg), declaration.name, async_=True, targeted=True).payload["job"]
    assert job["memory_max"] == "4G"
    full = check.run(Ctx(cfg), declaration.name, async_=True).payload["job"]
    assert full["memory_max"] == cfg.build_memory_max  # a full check still extracts everything


def test_dependency_check_runs_directly_without_a_systemd_bus(cfg, monkeypatch):
    """Sandboxed agents cannot open a guarded scope; the trace check must still size the cap."""
    from types import SimpleNamespace

    from es import build
    from es.commands import node
    from es.modules import scan_modules

    monkeypatch.undo()  # the real dependencies_built
    cfg.raw["build"]["guard"] = True
    monkeypatch.setattr(build, "bus_available", lambda *_a, **_k: False)
    monkeypatch.setattr(node, "run_guarded", lambda *_a, **_k: pytest.fail("no guarded scope without a bus"))
    calls = []
    import subprocess
    monkeypatch.setattr(subprocess, "run", lambda argv, **kw: calls.append(argv) or SimpleNamespace(returncode=0))
    assert node.dependencies_built(cfg, ["TBlueprint.A.Foo"], scan_modules(cfg)) == (True, "")
    assert calls and calls[0][1:3] == ["build", "--no-build"]
    monkeypatch.setattr(subprocess, "run", lambda argv, **kw: SimpleNamespace(returncode=3))
    assert node.dependencies_built(cfg, ["TBlueprint.A.Foo"], scan_modules(cfg))[0] is False


def _fake_extractor(calls):
    def fake_retry(cfg_, argv, **kw):
        calls.append(("extract", kw["memory_max"], kw["retry_memory_max"]))
        Path(argv[argv.index("--out") + 1]).write_text("{}")
        Path(argv[argv.index("--index") + 1]).write_text("[]")
        return _result()
    return fake_retry


def test_full_extract_skips_a_current_build_and_sizes_the_extractor(cfg, monkeypatch, tmp_path):
    from es import lean

    calls = []
    monkeypatch.setattr(lean, "_targets_current", lambda cfg_, targets: True)
    monkeypatch.setattr(lean, "run_guarded", lambda *_a, **_k: pytest.fail("no full-cap build when Lake reports current"))
    monkeypatch.setattr(lean, "run_guarded_retry", _fake_extractor(calls))
    monkeypatch.delenv("ES_EXTRACT_MEMORY_MAX", raising=False)
    lean.run_extractor(cfg, out=tmp_path / "n.json", index=tmp_path / "i.json", mods={})
    # measured steady-state peak ~5.3 GiB: first attempt at the sized cap, one OOM retry at the configured cap
    assert calls == [("extract", cfg.extract_full_memory_max, cfg.extract_memory_max)]


def test_full_extract_builds_a_stale_blueprint_first(cfg, monkeypatch, tmp_path):
    from es import lean

    calls = []
    monkeypatch.setattr(lean, "_targets_current", lambda cfg_, targets: False)
    monkeypatch.setattr(lean, "run_guarded", lambda cfg_, argv, **kw: calls.append(("build", argv[1])) or _result())
    monkeypatch.setattr(lean, "run_guarded_retry", _fake_extractor(calls))
    monkeypatch.delenv("ES_EXTRACT_MEMORY_MAX", raising=False)
    lean.run_extractor(cfg, out=tmp_path / "n.json", index=tmp_path / "i.json", mods={})
    assert calls[0] == ("build", "build") and calls[1][0] == "extract"


def test_extract_memory_env_pins_both_full_extract_attempts(cfg, monkeypatch):
    monkeypatch.setenv("ES_EXTRACT_MEMORY_MAX", "18G")
    assert cfg.extract_full_memory_max == "18G" and cfg.extract_memory_max == "18G"
