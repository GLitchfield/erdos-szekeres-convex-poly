"""Incremental index: fingerprints, `es extract --incremental`, the no-Lean `--check`, and the
build-guard fixes that came with it.

The extractor is replaced by a source-driven fake that behaves like the real one on what the
index depends on: it reads each blueprint module in the environment (the whole blueprint, or the
import closure of `--import` modules) and reports one record per documented theorem. The central
property: after any blueprint-only change, the incremental update writes exactly the files a full
extraction writes (up to the volatile lines)."""
from __future__ import annotations

import hashlib
import re
import subprocess

import pytest

DECL = re.compile(r"/--(.*?)-/\s*theorem\s+(\S+)\s*:(.*?):=\s*by\s+(\w+)", re.S)


def _write_blueprint(root, modules: dict[str, str]) -> None:
    for name, text in modules.items():
        path = root / (name.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    (root / "TBlueprint.lean").write_text("".join(f"import {m}\n" for m in sorted(modules)))


def _node(name: str, *, imports=("TCore",), sorry: bool = True, typ: str = "True", consumer: str | None = "TCore.foo") -> str:
    tags = "@node\n@ws A\n@kind formalization\n" + (f"@consumer {consumer}\n" if consumer else "")
    body = "sorry" if sorry else "trivial"
    return "".join(f"import {i}\n" for i in imports) + f"/-- {name}\n{tags}-/\ntheorem {name} : {typ} := by {body}\n"


def _foo(**kw) -> str:
    return _node("foo_node", **kw)


def _bar(**kw) -> str:
    return _node("bar_node", imports=("TCore", "TBlueprint.A.Foo"), typ="1 = 1", **kw)


def _commit(root) -> None:
    subprocess.run(["git", "-c", "user.email=t@t", "-c", "user.name=t", "add", "-A"], cwd=root, check=True)
    subprocess.run(["git", "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-q", "-m", "wip"], cwd=root, check=True)


@pytest.fixture
def fake(project, monkeypatch):
    """Install the fake extractor; return the list of recorded `imports` (None = whole environment)."""
    from es.build import BuildResult
    from es.commands import extract as extract_cmd
    from es.commands import node as node_cmd
    from es.config import load_config
    from es.fingerprint import blueprint_closure, blueprint_modules
    from es.lean import ExtractOutput
    from es.modules import scan_modules

    calls: list = []

    def run_extractor(cfg, *, out, index, mods=None, imports=None, **_kwargs):
        cfg = load_config(project)
        mods = scan_modules(cfg)
        names = blueprint_closure(cfg, mods, list(imports)) if imports else blueprint_modules(cfg, mods)
        calls.append(sorted(imports) if imports else None)
        decls = []
        for m in sorted(names):
            for doc, name, typ, body in DECL.findall((cfg.root / mods[m].path).read_text()):
                sorry = body == "sorry"
                decls.append({"name": "TCore." + name, "module": m, "doc": doc.strip(), "type_pp": typ.strip(),
                              "type_hash": hashlib.sha256(typ.strip().encode()).hexdigest()[:16], "sorry": sorry,
                              "axioms": ["sorryAx"] if sorry else ["propext"],
                              "nonstandard_axioms": ["sorryAx"] if sorry else [], "deps": [],
                              "internal": False, "kind": "theorem"})
        dest = {"name": "TCore.dest", "module": "TCore.Basic", "doc": "d", "type_pp": "True", "type_hash": "d0",
                "sorry": False, "axioms": ["propext"], "nonstandard_axioms": [], "deps": [], "internal": False,
                "kind": "theorem"}
        raw = {"declarations": decls, "destinations": [] if imports else [dest],
               "missing_destinations": ["TCore.dest"] if imports else [], "toolchain": "t",
               "modules": 100 + len(names), "nonstandard_axioms": ["sorryAx"], "taint": {"cached_modules": 1}}
        idx = [{"name": "TCore.foo", "module": "TCore.Basic", "kind": "theorem", "type_hash": "core-foo"}]
        return ExtractOutput(nodes=raw, index=idx, result=BuildResult(0, 0.1, 0, "", []))

    monkeypatch.setattr(extract_cmd, "run_extractor", run_extractor)
    monkeypatch.setattr(node_cmd, "closure_olean_gib", lambda *_a, **_k: 0.0)
    return calls


def _files(cfg) -> tuple[str, str, str]:
    from es.commands.extract import _strip_volatile

    return tuple(_strip_volatile(p.read_text()) for p in (cfg.nodes_json, cfg.status_md, cfg.index_json))


def _full_files(ctx) -> tuple[str, str, str]:
    from es.commands.extract import run_extract

    run_extract(ctx, no_cache=True)
    return _files(ctx.cfg)


@pytest.fixture
def seeded(project, fake):
    """Two committed nodes (Bar imports Foo), a full index and matching lock entries."""
    from es.commands.extract import run_extract
    from es.context import Ctx
    from es.lock import lock_entry, write_lock

    _write_blueprint(project, {"TBlueprint.A.Foo": _foo(), "TBlueprint.A.Bar": _bar(sorry=False)})
    _commit(project)
    ctx = Ctx.load(project)
    payload, _, _ = run_extract(ctx)
    write_lock(ctx.cfg.lock_file, {n["name"]: lock_entry(n["type_hash"], n["type_pp"], "t", "formalization", "A")
                                   for n in payload["nodes"]})
    run_extract(ctx)
    fake.clear()
    return ctx


def test_full_extract_records_fingerprints(seeded):
    import json

    data = json.loads(seeded.cfg.nodes_json.read_text())
    fps = data["fingerprints"]
    assert set(fps["blueprint"]) == {"TBlueprint.A.Foo", "TBlueprint.A.Bar"} and fps["core"]
    assert data["extract_mode"] == "full"


def test_fast_check_needs_no_lean_when_nothing_changed(seeded, fake):
    from es.commands.extract import fast_check

    _, _, problems = fast_check(seeded)
    assert problems == [] and fake == []


def test_fast_check_names_stale_modules_without_building(project, seeded, fake):
    from es.commands.extract import fast_check

    (project / "TBlueprint/A/Bar.lean").write_text(_bar(sorry=True))
    _, _, problems = fast_check(seeded)
    assert fake == []
    assert len(problems) == 1 and "TBlueprint.A.Bar" in problems[0] and "--incremental" in problems[0]


@pytest.mark.parametrize("change", ["edit-proof", "edit-dependency", "add-node", "remove-node", "claim-only"])
def test_incremental_update_equals_full_extract(project, seeded, fake, change):
    from es.commands.extract import fast_check, run_incremental
    from es.store import Store

    expected_imports = {
        "edit-proof": ["TBlueprint.A.Bar"],
        "edit-dependency": ["TBlueprint.A.Bar", "TBlueprint.A.Foo"],  # Bar's closure contains Foo
        "add-node": ["TBlueprint.A.Baz"],
        "remove-node": None,
        "claim-only": None,
    }[change]
    mods = {"TBlueprint.A.Foo": _foo(), "TBlueprint.A.Bar": _bar(sorry=False)}
    if change == "edit-proof":
        mods["TBlueprint.A.Bar"] = _bar(sorry=True)
    elif change == "edit-dependency":
        mods["TBlueprint.A.Foo"] = _foo(sorry=False)
    elif change == "add-node":
        mods["TBlueprint.A.Baz"] = _node("baz_node", typ="3 = 3", consumer=None)  # also exercises a tag problem
    elif change == "remove-node":
        del mods["TBlueprint.A.Bar"]
        (project / "TBlueprint/A/Bar.lean").unlink()
    elif change == "claim-only":
        with Store(seeded.cfg) as st:
            st.claim("TCore.foo_node", "someone", 1, note="testing")
    _write_blueprint(project, mods)

    payload, _, _ = run_incremental(seeded)
    assert fake == ([expected_imports] if expected_imports else [])
    assert payload["_incremental"]["removed"] == (["TBlueprint.A.Bar"] if change == "remove-node" else [])
    incremental = _files(seeded.cfg)
    # the updated index verifies without Lean (real problems, like the added node's tag error, remain)
    assert not [p for p in fast_check(seeded)[2] if "stale" in p]
    assert incremental == _full_files(seeded), "incremental index must equal a full extraction"


def test_incremental_refuses_when_core_changes(project, seeded, fake):
    from es.commands.extract import NeedsFullExtract, fast_check, run_incremental

    (project / "TCore" / "Basic.lean").write_text("theorem foo : True := trivial\ntheorem foo2 : True := trivial\n")
    with pytest.raises(NeedsFullExtract, match="core"):
        run_incremental(seeded)
    with pytest.raises(NeedsFullExtract):
        fast_check(seeded)
    assert fake == []


def test_incremental_refuses_index_without_fingerprints(project, seeded):
    import json

    from es.commands.extract import NeedsFullExtract, run_incremental

    data = json.loads(seeded.cfg.nodes_json.read_text())
    data.pop("fingerprints")
    seeded.cfg.nodes_json.write_text(json.dumps(data))
    with pytest.raises(NeedsFullExtract, match="fingerprints"):
        run_incremental(seeded)


def test_check_command_uses_fingerprints_and_falls_back(project, seeded, fake):
    from es.commands.extract import run

    assert run(seeded, check=True).payload["mode"] == "fingerprint" and fake == []
    (project / "TCore" / "Basic.lean").write_text("theorem foo : True := trivial\ntheorem foo3 : True := trivial\n")
    res = run(seeded, check=True)
    assert res.payload["mode"] == "full" and fake == [None]


def test_check_changed_passes_changes_that_touch_no_index_input(project, seeded, fake):
    from es.commands.extract import run

    _commit(project)
    (project / "NOTES.md").write_text("tooling or docs only\n")
    res = run(seeded, check=True, changed=True)
    assert res.exit_code == 0 and res.payload["mode"] == "unchanged" and fake == []
    (project / "TBlueprint/A/Bar.lean").write_text(_bar(sorry=True))
    res = run(seeded, check=True, changed=True)
    assert res.exit_code != 0 and res.payload["mode"] == "fingerprint" and fake == []
    assert "--incremental" in "\n".join(res.payload["problems"])


def test_check_no_cache_forces_full_extraction(seeded, fake):
    """The nightly backstop (`--check --no-cache`) must re-derive the index, not trust fingerprints."""
    from es.commands.extract import run

    res = run(seeded, check=True, no_cache=True)
    assert res.payload["mode"] == "full" and fake == [None] and res.exit_code == 0


def test_targeted_extract_keeps_full_cache_entries(seeded, fake):
    from es.commands.extract import run_extract
    from es.fingerprint import extract_key
    from es.store import Store

    th = extract_key(seeded.cfg)
    run_extract(seeded)  # full entry for th
    run_extract(seeded, no_cache=True, write=False, imports=["TBlueprint.A.Bar"])
    with Store(seeded.cfg) as st:
        assert st.cache_get(th) is not None, "a targeted run must not evict the full-environment entry"


def _hand_edit_record(cfg) -> None:
    import json

    data = json.loads(cfg.nodes_json.read_text())
    data["nodes"][0]["type_pp"] = "False (edited without the extractor)"
    cfg.nodes_json.write_text(json.dumps(data, indent=1, ensure_ascii=False) + "\n")


def test_check_changed_rejects_hand_edited_record(project, seeded, fake):
    """Matching fingerprints do not vouch for records the extractor never produced."""
    from es.commands.extract import NeedsFullExtract, fast_check, run

    _commit(project)
    _hand_edit_record(seeded.cfg)
    with pytest.raises(NeedsFullExtract, match="attested"):
        fast_check(seeded)
    res = run(seeded, check=True, changed=True)
    assert res.exit_code != 0 and res.payload["mode"] == "full"
    assert "harness/nodes.json is stale; run `es extract`" in res.payload["problems"]


def test_incremental_refuses_hand_edited_base(project, seeded, fake):
    """An incremental update carries unchanged records over, so it must not launder an edited base."""
    from es.commands.extract import NeedsFullExtract, fast_check, run_incremental

    _hand_edit_record(seeded.cfg)
    (project / "TBlueprint/A/Bar.lean").write_text(_bar(sorry=True))
    with pytest.raises(NeedsFullExtract, match="attested"):
        run_incremental(seeded)
    (project / "TBlueprint/A/Bar.lean").write_text(_bar(sorry=False))
    with pytest.raises(NeedsFullExtract, match="attested"):
        fast_check(seeded)  # nothing was attested on the way
    assert fake == []


def test_attested_index_survives_a_commit(project, seeded, fake):
    from es.commands.extract import run

    (project / "TBlueprint/A/Bar.lean").write_text(_bar(sorry=True))
    assert run(seeded, incremental=True).exit_code == 0
    _commit(project)
    fake.clear()
    res = run(seeded, check=True)
    assert res.exit_code == 0 and res.payload["mode"] == "fingerprint" and fake == []


def test_toolchain_change_reextracts_instead_of_reusing_the_cache(project, seeded, fake, monkeypatch):
    from es.commands import extract as extract_cmd
    from es.commands.extract import run

    inner = extract_cmd.run_extractor

    def toolchain_sensitive(cfg, **kwargs):
        out = inner(cfg, **kwargs)
        out.nodes["toolchain"] = (project / "lean-toolchain").read_text().strip()
        return out

    monkeypatch.setattr(extract_cmd, "run_extractor", toolchain_sensitive)
    (project / "lean-toolchain").write_text("changed-toolchain\n")
    res = run(seeded, check=True)
    assert fake == [None], "a new toolchain must miss the raw-output cache"
    assert res.exit_code != 0 and res.payload["mode"] == "full"


def test_extractor_template_change_misses_the_cache(project, seeded, fake):
    from es.fingerprint import extract_key

    template = project / "harness" / "Extract.lean.tmpl"
    template.write_text("-- one extractor\n")
    seeded.cfg.raw.setdefault("extract", {})["template"] = "harness/Extract.lean.tmpl"
    before = extract_key(seeded.cfg)
    template.write_text("-- a different extractor\n")
    assert extract_key(seeded.cfg) != before


def test_check_changed_detects_deleted_index_files(project, seeded, fake):
    from es.commands.extract import run

    _commit(project)
    for path in (seeded.cfg.nodes_json, seeded.cfg.status_md, seeded.cfg.index_json):
        text = path.read_text()
        path.unlink()
        res = run(seeded, check=True, changed=True)
        assert res.exit_code != 0 and res.payload["mode"] != "unchanged", path
        path.write_text(text)
    assert run(seeded, check=True, changed=True).payload["mode"] == "unchanged"


@pytest.fixture
def axiom_marker(project, fake, monkeypatch):
    """Extend the fake extractor: `-- declares_axiom` in Foo declares a blueprint axiom, reported as
    an axiom record of Foo and in the global list (as the real extractor reports a `native_decide`
    auxiliary axiom)."""
    from es.commands import extract as extract_cmd

    inner = extract_cmd.run_extractor

    def with_axiom(cfg, **kwargs):
        out = inner(cfg, **kwargs)
        in_env = any(d["module"] == "TBlueprint.A.Foo" for d in out.nodes["declarations"])
        if in_env and "-- declares_axiom" in (project / "TBlueprint/A/Foo.lean").read_text():
            out.nodes["declarations"].append({
                "name": "TCore.foo_aux_ax", "module": "TBlueprint.A.Foo", "doc": "", "type_pp": "True",
                "type_hash": "ax", "sorry": False, "axioms": ["TCore.foo_aux_ax"],
                "nonstandard_axioms": ["TCore.foo_aux_ax"], "deps": [], "internal": True, "kind": "axiom"})
            out.nodes["nonstandard_axioms"] = ["TCore.foo_aux_ax"] + out.nodes["nonstandard_axioms"]
        return out

    monkeypatch.setattr(extract_cmd, "run_extractor", with_axiom)


@pytest.mark.parametrize("change", ["add", "remove", "remove-module"])
def test_incremental_tracks_blueprint_declared_axioms(project, seeded, fake, axiom_marker, change):
    import json

    from es.commands.extract import fast_check, run_extract, run_incremental

    if change != "add":
        (project / "TBlueprint/A/Foo.lean").write_text(_foo() + "-- declares_axiom\n")
        run_extract(seeded)
    mods = {"TBlueprint.A.Foo": _foo() + ("-- declares_axiom\n" if change == "add" else ""),
            "TBlueprint.A.Bar": _bar(sorry=False)}
    if change == "remove-module":
        del mods["TBlueprint.A.Foo"]
        (project / "TBlueprint/A/Foo.lean").unlink()
        mods["TBlueprint.A.Bar"] = _node("bar_node", typ="1 = 1", sorry=False)
    _write_blueprint(project, mods)
    run_incremental(seeded)
    data = json.loads(seeded.cfg.nodes_json.read_text())
    assert ("TCore.foo_aux_ax" in data["nonstandard_axioms"]) == (change == "add")
    assert data["nonstandard_axioms"] == sorted(data["nonstandard_axioms"])
    incremental = _files(seeded.cfg)
    assert not [p for p in fast_check(seeded)[2] if "stale" in p]
    assert incremental == _full_files(seeded), "incremental index must equal a full extraction"


def test_node_add_targeted_updates_index_with_one_extractor_run(project, seeded, fake, monkeypatch):
    import json

    from es.commands import node as node_cmd

    monkeypatch.setattr(node_cmd, "elaborate_module", lambda *_a, **_k: None)
    res = node_cmd.run_add(seeded, name="qux_node", ws="A", kind="formalization", type=": 2 = 2",
                           description="qux", consumer="TCore.foo", targeted=True, no_search=True)
    assert "updated incrementally" in "\n".join(res.human)
    assert fake == [["TBlueprint.A.QuxNode"]], "the incremental merge must reuse the targeted extraction"
    names = {n["name"] for n in json.loads(seeded.cfg.nodes_json.read_text())["nodes"]}
    assert "TCore.qux_node" in names


def test_node_add_targeted_rejects_duplicate_outside_the_closure(project, seeded, fake, monkeypatch):
    from es.commands import node as node_cmd
    from es.errors import CheckFailed

    monkeypatch.setattr(node_cmd, "elaborate_module", lambda *_a, **_k: None)
    # same statement as bar_node ("True"), but the new module does not import Bar
    with pytest.raises(CheckFailed, match="duplicates"):
        node_cmd.run_add(seeded, name="dup_node", ws="A", kind="formalization", type=": True",
                         description="dup", consumer="TCore.foo", targeted=True, no_search=True)
    assert not (project / "TBlueprint/A/DupNode.lean").exists()


# ---------------------------------------------------------------------------
# build guard


def test_scope_oom_kills_reads_the_journal(monkeypatch):
    from es import build

    class Out:
        def __init__(self, text):
            self.stdout = text

    monkeypatch.setattr(build.subprocess, "run", lambda *a, **k: Out(
        "es-x.scope: A process of this unit has been killed by the OOM killer.\nFailed with result 'oom-kill'.\n"))
    assert build.scope_oom_kills("es-x", since=0) == 1
    monkeypatch.setattr(build.subprocess, "run", lambda *a, **k: Out("Started es-x.scope\n"))
    assert build.scope_oom_kills("es-x", since=0) == 0

    def boom(*_a, **_k):
        raise OSError("no journalctl")

    monkeypatch.setattr(build.subprocess, "run", boom)
    assert build.scope_oom_kills("es-x", since=0) == 0


def test_async_build_reserves_its_final_step(cfg, monkeypatch):
    from es import jobs
    from es.build import build_reservation

    monkeypatch.setattr(jobs, "spawn_runner", lambda *_a, **_k: None)
    job = jobs.submit(cfg, kind="build", node=None, argv=["build", "blueprint"], agent="t")
    assert job["memory_max"] == build_reservation(cfg) == "30G"
    check_job = jobs.submit(cfg, kind="check", node=None, argv=["check", "x"], agent="t")
    assert check_job["memory_max"] == cfg.build_memory_max
