from __future__ import annotations

import json
import os
import subprocess
import shutil
from copy import deepcopy
from pathlib import Path

import pytest

from es.build import BuildResult, run_guarded
from es.config import Config
from es.errors import CheckFailed
from es.setup_metadata import apply_setup_manifest, create_setup_manifest, prune_setup_metadata


def _enable(cfg) -> None:
    cfg.raw.setdefault("build", {})["setup_metadata_cleanup"] = {
        "enabled": True,
        "ir_dir": ".lake/build/ir",
        "toolchain": "leanprover/lean4:v4.29.1",
    }
    (cfg.root / "lean-toolchain").write_text("leanprover/lean4:v4.29.1\n")


def _setup(cfg, relative: str, *, plugins=None, dynlibs=None) -> Path:
    path = cfg.root / ".lake" / "build" / "ir" / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({
        "plugins": [] if plugins is None else plugins,
        "package": "testproj",
        "name": relative.removesuffix(".setup.json").replace("/", "."),
        "isModule": False,
        "importArts": {},
        "dynlibs": [] if dynlibs is None else dynlibs,
    }))
    return path


def test_missing_root_and_dry_run_are_non_destructive(cfg, tmp_path):
    _enable(cfg)
    missing = prune_setup_metadata(cfg, apply=False, output_dir=tmp_path / "missing")
    assert missing["files"] == 0
    path = _setup(cfg, "A.setup.json")
    receipt = prune_setup_metadata(cfg, apply=False, output_dir=tmp_path / "dry")
    assert receipt["status"] == "dry-run"
    assert receipt["files"] == 1
    assert path.exists()


def test_symlink_root_refused_and_symlink_candidate_skipped(cfg, tmp_path):
    _enable(cfg)
    outside = tmp_path / "outside"
    outside.mkdir()
    (cfg.root / ".lake").symlink_to(outside, target_is_directory=True)
    with pytest.raises(CheckFailed, match="crosses a symlink"):
        create_setup_manifest(cfg)


def test_symlink_candidate_skipped_but_plugin_and_dynlib_setup_are_in_scope(cfg, tmp_path):
    _enable(cfg)
    ordinary = _setup(cfg, "Good.setup.json")
    linked = ordinary.parent / "Linked.setup.json"
    linked.symlink_to(ordinary.name)
    plugin = tmp_path / "plugin.so"
    dynlib = tmp_path / "lib.so"
    plugin.write_bytes(b"plugin")
    dynlib.write_bytes(b"dynlib")
    _setup(cfg, "Plugin.setup.json", plugins=[str(plugin)])
    _setup(cfg, "Dynlib.setup.json", dynlibs=[str(dynlib)])
    manifest = create_setup_manifest(cfg)
    assert [row["path"] for row in manifest["candidates"]] == [
        "Dynlib.setup.json", "Good.setup.json", "Plugin.setup.json"
    ]
    assert manifest["skipped_symlinks"] == ["Linked.setup.json"]
    apply_setup_manifest(cfg, manifest)
    assert plugin.read_bytes() == b"plugin"
    assert dynlib.read_bytes() == b"dynlib"


def test_replacement_or_mutation_aborts_before_any_unlink(cfg):
    _enable(cfg)
    first = _setup(cfg, "A.setup.json")
    second = _setup(cfg, "B.setup.json")
    manifest = create_setup_manifest(cfg)
    replacement = first.with_name("replacement")
    replacement.write_text(first.read_text() + " ")
    os.replace(replacement, first)
    with pytest.raises(CheckFailed, match="candidate changed"):
        apply_setup_manifest(cfg, manifest)
    assert first.exists() and second.exists()


@pytest.mark.parametrize("tamper", ["absolute", "alias", "duplicate", "summary", "toolchain"])
def test_apply_rejects_tampered_manifest_before_unlink(cfg, tamper):
    _enable(cfg)
    first = _setup(cfg, "A.setup.json")
    second = _setup(cfg, "B.setup.json")
    manifest = create_setup_manifest(cfg)
    broken = deepcopy(manifest)
    if tamper == "absolute":
        broken["candidates"][0]["path"] = "/tmp/escape.setup.json"
    elif tamper == "alias":
        broken["candidates"][0]["path"] = "./A.setup.json"
    elif tamper == "duplicate":
        broken["candidates"][1]["path"] = broken["candidates"][0]["path"]
    elif tamper == "toolchain":
        cfg.raw["build"]["setup_metadata_cleanup"]["toolchain"] = "leanprover/lean4:v9.99.0"
    else:
        broken["summary"]["logical_bytes"] += 1
    with pytest.raises(CheckFailed):
        apply_setup_manifest(cfg, broken)
    assert first.exists() and second.exists()


def test_partial_unlink_failure_receipt_reports_completed_effects(monkeypatch, cfg, tmp_path):
    _enable(cfg)
    first = _setup(cfg, "A.setup.json")
    second = _setup(cfg, "B.setup.json")
    first_size = first.stat().st_size
    first_allocated = first.stat().st_blocks * 512
    original = os.unlink
    setup_unlinks = 0

    def fail_second(path, *args, dir_fd=None, **kwargs):
        nonlocal setup_unlinks
        if dir_fd is not None and str(path).endswith(".setup.json"):
            setup_unlinks += 1
            if setup_unlinks == 2:
                raise OSError("injected unlink failure")
        return original(path, *args, dir_fd=dir_fd, **kwargs)

    monkeypatch.setattr("es.setup_metadata.os.unlink", fail_second)
    out = tmp_path / "partial"
    with pytest.raises(CheckFailed, match="stopped after 1 unlink"):
        prune_setup_metadata(cfg, apply=True, output_dir=out)
    receipt = json.loads((out / "receipt.json").read_text())
    assert receipt["status"] == "partial"
    assert receipt["files_removed"] == 1
    assert receipt["logical_bytes_removed"] == first_size
    assert receipt["allocated_bytes_reclaimed"] == first_allocated
    assert not first.exists() and second.exists()


def test_hardlink_accounting_separates_logical_and_allocated_bytes(cfg, tmp_path):
    _enable(cfg)
    first = _setup(cfg, "A.setup.json")
    second = first.with_name("B.setup.json")
    os.link(first, second)
    manifest = create_setup_manifest(cfg)
    allocated = first.stat().st_blocks * 512
    assert manifest["summary"]["logical_bytes"] == 2 * first.stat().st_size
    assert manifest["summary"]["allocated_bytes_reclaimable"] == allocated
    receipt = prune_setup_metadata(cfg, apply=True, output_dir=tmp_path / "apply")
    assert receipt["files_removed"] == 2
    assert receipt["allocated_bytes_reclaimed"] == allocated
    assert not first.exists() and not second.exists()


def test_external_hardlink_means_no_claimed_physical_reclamation(cfg, tmp_path):
    _enable(cfg)
    first = _setup(cfg, "A.setup.json")
    external = tmp_path / "external-link"
    os.link(first, external)
    receipt = prune_setup_metadata(cfg, apply=True, output_dir=tmp_path / "apply")
    assert receipt["logical_bytes_removed"] > 0
    assert receipt["allocated_bytes_reclaimed"] == 0
    assert external.exists()


@pytest.mark.parametrize(
    "argv,rc,ack,removed",
    [
        (None, 0, True, True),
        (["python3", "build"], 0, True, False),
        (None, 1, True, False),
        (None, 0, False, False),
    ],
)
def test_posthook_only_successful_acknowledged_lake_build(monkeypatch, cfg, tmp_path, argv, rc, ack, removed):
    _enable(cfg)
    path = _setup(cfg, "TCore/Basic.setup.json")
    log = tmp_path / "build.log"
    command = argv or [cfg.lake, "build", "TCore.Basic"]

    def fake(_cfg, actual, **kwargs):
        Path(kwargs["log_path"]).write_text("✔ [1/1] Built TCore.Basic (1ms)\n")
        return BuildResult(rc, 0.1, 1, str(kwargs["log_path"]), actual, termination_acknowledged=ack)

    monkeypatch.setattr("es.build._run_guarded", fake)
    result = run_guarded(cfg, command, log_path=log, budget_min=1, force=True)
    assert path.exists() is (not removed)
    assert (result.setup_cleanup is not None) is removed


def test_tiny_lake_recreates_pruned_setup_only_after_real_recompile(cfg, tmp_path):
    _enable(cfg)
    (cfg.root / "lakefile.toml").write_text(
        'name = "T"\nversion = "0.1.0"\ndefaultTargets = ["TCore"]\n'
        '[[lean_lib]]\nname = "TCore"\n'
    )
    first = subprocess.run([cfg.lake, "build", "TCore"], cwd=cfg.root, capture_output=True, text=True, timeout=60)
    assert first.returncode == 0, first.stdout + first.stderr
    setup = cfg.root / ".lake/build/ir/TCore/Basic.setup.json"
    assert setup.is_file()
    prune_setup_metadata(cfg, apply=True, output_dir=tmp_path / "apply")
    assert not setup.exists()
    cached = subprocess.run([cfg.lake, "build", "TCore"], cwd=cfg.root, capture_output=True, text=True, timeout=60)
    assert cached.returncode == 0
    assert not setup.exists()
    source = cfg.root / "TCore/Basic.lean"
    source.write_text(source.read_text() + "\ntheorem setup_regenerated : True := by trivial\n")
    rebuilt = subprocess.run([cfg.lake, "build", "TCore"], cwd=cfg.root, capture_output=True, text=True, timeout=60)
    assert rebuilt.returncode == 0, rebuilt.stdout + rebuilt.stderr
    assert setup.is_file()


def test_native_module_plugin_setup_is_pruned_without_touching_shared_libraries(cfg, tmp_path):
    source_fixture = Path(__file__).parent / "fixtures" / "setup_plugin"
    root = tmp_path / "plugin"
    shutil.copytree(source_fixture, root)
    raw = deepcopy(cfg.raw)
    raw.setdefault("build", {})["setup_metadata_cleanup"] = {
        "enabled": True,
        "ir_dir": ".lake/build/ir",
        "toolchain": "leanprover/lean4:v4.29.1",
    }
    plugin_cfg = Config(root, raw)

    initial = subprocess.run([plugin_cfg.lake, "build"], cwd=root, capture_output=True, text=True, timeout=60)
    assert initial.returncode == 0, initial.stdout + initial.stderr
    assert "PLUGIN_SETUP_FIXTURE_INITIALIZED" in initial.stdout + initial.stderr
    setup = root / ".lake/build/ir/PluginSmoke/Consumer.setup.json"
    metadata = json.loads(setup.read_text())
    references = [Path(path) for path in metadata["plugins"] + metadata["dynlibs"]]
    assert metadata["plugins"] and metadata["dynlibs"]
    assert all(path.is_file() for path in references)

    receipt = prune_setup_metadata(
        plugin_cfg, apply=True, output_dir=tmp_path / "plugin-receipt", modules=["PluginSmoke.Consumer"]
    )
    assert receipt["files_removed"] == 1
    assert not setup.exists()
    assert all(path.is_file() for path in references)

    cached = subprocess.run([plugin_cfg.lake, "build"], cwd=root, capture_output=True, text=True, timeout=60)
    assert cached.returncode == 0
    assert " Built " not in cached.stdout + cached.stderr
    assert not setup.exists()

    consumer = root / "PluginSmoke/Consumer.lean"
    consumer.write_text(consumer.read_text().replace(":= 1", ":= 2"))
    rebuilt = subprocess.run([plugin_cfg.lake, "build"], cwd=root, capture_output=True, text=True, timeout=60)
    assert rebuilt.returncode == 0, rebuilt.stdout + rebuilt.stderr
    assert setup.is_file()
    rebuilt_metadata = json.loads(setup.read_text())
    assert rebuilt_metadata["plugins"] and rebuilt_metadata["dynlibs"]
