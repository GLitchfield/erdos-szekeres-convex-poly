"""Audited pruning of Lake 4.29.1's untracked ``*.setup.json`` spill files."""

from __future__ import annotations

import hashlib
import json
import os
import re
import stat
import tempfile
import time
from collections import Counter
from pathlib import Path, PurePosixPath
from typing import Iterable

from es.errors import CheckFailed


CONTRACT = "lake-4.29.1-untracked-setup-v1"
SCHEMA_VERSION = 1
SUPPORTED_TOOLCHAIN = "leanprover/lean4:v4.29.1"
_MODULE = re.compile(r"^[A-Za-z0-9_']+(?:\.[A-Za-z0-9_']+)*$")
_BUILT = re.compile(r"\bBuilt ([A-Za-z0-9_']+(?:\.[A-Za-z0-9_']+)*)\b")
_NOFOLLOW = getattr(os, "O_NOFOLLOW", 0)
_DIRECTORY = getattr(os, "O_DIRECTORY", 0)


class SetupCleanupPartial(CheckFailed):
    def __init__(self, message: str, progress: dict[str, int]):
        super().__init__(message)
        self.progress = progress


def _write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
    fd, tmp = tempfile.mkstemp(prefix=".setup-metadata-", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(encoded)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(tmp, path)
        directory_fd = os.open(path.parent, os.O_RDONLY | _DIRECTORY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        Path(tmp).unlink(missing_ok=True)


def _fingerprint(info: os.stat_result) -> dict[str, int]:
    return {
        "dev": info.st_dev,
        "ino": info.st_ino,
        "mode": info.st_mode,
        "size": info.st_size,
        "mtime_ns": info.st_mtime_ns,
        "ctime_ns": info.st_ctime_ns,
        "nlink": info.st_nlink,
        "blocks": getattr(info, "st_blocks", 0),
        "allocated_bytes": getattr(info, "st_blocks", 0) * 512,
    }


def _matches(record: dict, info: os.stat_result, *, removed_links: int = 0) -> bool:
    current = _fingerprint(info)
    keys = ("dev", "ino", "mode", "size", "mtime_ns", "blocks")
    # Unlinking another manifest path to the same inode changes ctime/nlink.
    # Before our first unlink, ctime remains part of the mutation fingerprint.
    if not removed_links:
        keys += ("ctime_ns",)
    expected = {key: record[key] for key in keys}
    if any(current[key] != value for key, value in expected.items()):
        return False
    return current["nlink"] == record["nlink"] - removed_links


def _validated_ir_path(cfg) -> tuple[Path, bool]:
    root = cfg.root.absolute()
    try:
        root_info = root.lstat()
    except OSError as exc:
        raise CheckFailed(f"cannot inspect project root {root}: {exc}") from exc
    if stat.S_ISLNK(root_info.st_mode) or not stat.S_ISDIR(root_info.st_mode) or root.resolve() != root:
        raise CheckFailed(f"project root must be a real directory, not a symlink: {root}")
    current = root
    for part in cfg.build_setup_cleanup_ir_dir.parts:
        current = current / part
        try:
            info = current.lstat()
        except FileNotFoundError:
            return current.joinpath(*cfg.build_setup_cleanup_ir_dir.parts[len(current.relative_to(root).parts):]), False
        except OSError as exc:
            raise CheckFailed(f"cannot inspect setup metadata path {current}: {exc}") from exc
        if stat.S_ISLNK(info.st_mode):
            raise CheckFailed(f"setup metadata path crosses a symlink: {current}")
        if not stat.S_ISDIR(info.st_mode):
            raise CheckFailed(f"setup metadata path component is not a directory: {current}")
    return current, True


def _check_toolchain(cfg) -> str:
    path = cfg.root / "lean-toolchain"
    try:
        actual = path.read_text().strip()
    except OSError as exc:
        raise CheckFailed(f"cannot read pinned toolchain {path}: {exc}") from exc
    expected = cfg.build_setup_cleanup_toolchain
    if expected != SUPPORTED_TOOLCHAIN:
        raise CheckFailed(
            f"setup metadata cleanup configuration names unsupported toolchain {expected}; "
            f"implementation supports only {SUPPORTED_TOOLCHAIN}"
        )
    if actual != expected:
        raise CheckFailed(f"setup metadata cleanup supports {expected}, found {actual or '(empty)'}")
    return actual


def _open_dir_at(parent_fd: int, parts: Iterable[str]) -> int:
    fd = os.dup(parent_fd)
    try:
        for part in parts:
            child = os.open(part, os.O_RDONLY | _DIRECTORY | _NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = child
        return fd
    except Exception:
        os.close(fd)
        raise


def _stat_at(root_fd: int, relative: str) -> os.stat_result:
    parsed = PurePosixPath(relative)
    parts = parsed.parts
    if parsed.is_absolute() or not parts or any(part in ("", ".", "..", "/") for part in parts):
        raise CheckFailed(f"invalid setup metadata manifest path {relative!r}")
    parent = _open_dir_at(root_fd, parts[:-1])
    try:
        return os.stat(parts[-1], dir_fd=parent, follow_symlinks=False)
    finally:
        os.close(parent)


def _scan_dir(
    fd: int,
    prefix: PurePosixPath,
    candidates: list[dict],
    skipped: list[str],
) -> None:
    with os.scandir(fd) as entries:
        ordered = sorted(entries, key=lambda entry: entry.name)
    for entry in ordered:
        relative = prefix / entry.name
        try:
            info = entry.stat(follow_symlinks=False)
        except OSError as exc:
            raise CheckFailed(f"cannot inspect {relative}: {exc}") from exc
        if stat.S_ISLNK(info.st_mode):
            if entry.name.endswith(".setup.json"):
                skipped.append(relative.as_posix())
            continue
        if stat.S_ISDIR(info.st_mode):
            try:
                child = os.open(entry.name, os.O_RDONLY | _DIRECTORY | _NOFOLLOW, dir_fd=fd)
            except OSError as exc:
                raise CheckFailed(f"cannot safely enter {relative}: {exc}") from exc
            try:
                _scan_dir(child, relative, candidates, skipped)
            finally:
                os.close(child)
        elif stat.S_ISREG(info.st_mode) and entry.name.endswith(".setup.json"):
            candidates.append({"path": relative.as_posix(), **_fingerprint(info)})


def _candidate_paths(modules: Iterable[str]) -> list[str]:
    paths = []
    for module in sorted(set(modules)):
        if not _MODULE.fullmatch(module):
            raise CheckFailed(f"invalid built module name {module!r}")
        paths.append(module.replace(".", "/") + ".setup.json")
    return paths


def _allocated_reclaimable(candidates: list[dict]) -> int:
    inode_counts = Counter((row["dev"], row["ino"]) for row in candidates)
    first_by_inode: dict[tuple[int, int], dict] = {}
    for row in candidates:
        first_by_inode.setdefault((row["dev"], row["ino"]), row)
    return sum(
        row["allocated_bytes"]
        for key, row in first_by_inode.items()
        if inode_counts[key] == row["nlink"]
    )


def _validated_candidates(manifest: dict) -> list[dict]:
    candidates = manifest.get("candidates")
    if not isinstance(candidates, list):
        raise CheckFailed("setup metadata manifest candidates are invalid")
    integer_fields = ("dev", "ino", "mode", "size", "mtime_ns", "ctime_ns", "nlink", "blocks", "allocated_bytes")
    paths: set[str] = set()
    for record in candidates:
        if not isinstance(record, dict) or not isinstance(record.get("path"), str):
            raise CheckFailed("setup metadata manifest candidate is malformed")
        parsed = PurePosixPath(record["path"])
        if (
            parsed.is_absolute()
            or not parsed.parts
            or any(part in ("", ".", "..", "/") for part in parsed.parts)
            or record["path"] != parsed.as_posix()
            or not record["path"].endswith(".setup.json")
        ):
            raise CheckFailed(f"invalid setup metadata manifest path {record['path']!r}")
        if record["path"] in paths:
            raise CheckFailed(f"duplicate setup metadata manifest path {record['path']!r}")
        paths.add(record["path"])
        if any(type(record.get(key)) is not int for key in integer_fields):
            raise CheckFailed(f"malformed setup metadata fingerprint for {record['path']}")
        if record["size"] < 0 or record["nlink"] < 1 or record["blocks"] < 0 or record["allocated_bytes"] != record["blocks"] * 512:
            raise CheckFailed(f"invalid setup metadata fingerprint for {record['path']}")
        if not stat.S_ISREG(record["mode"]):
            raise CheckFailed(f"manifest candidate is not a regular file: {record['path']}")
    summary = manifest.get("summary")
    expected = {
        "files": len(candidates),
        "logical_bytes": sum(record["size"] for record in candidates),
        "allocated_bytes_reclaimable": _allocated_reclaimable(candidates),
    }
    if not isinstance(summary, dict) or any(summary.get(key) != value for key, value in expected.items()):
        raise CheckFailed("setup metadata manifest summary does not match its candidates")
    return candidates


def create_setup_manifest(cfg, *, modules: Iterable[str] | None = None) -> dict:
    """Snapshot exact regular files eligible under the pinned cleanup contract."""
    toolchain = _check_toolchain(cfg)
    ir_path, exists = _validated_ir_path(cfg)
    candidates: list[dict] = []
    skipped: list[str] = []
    root_fingerprint = None
    if exists:
        root_fd = os.open(ir_path, os.O_RDONLY | _DIRECTORY | _NOFOLLOW)
        try:
            root_fingerprint = _fingerprint(os.fstat(root_fd))
            if modules is None:
                _scan_dir(root_fd, PurePosixPath(), candidates, skipped)
            else:
                for relative in _candidate_paths(modules):
                    try:
                        info = _stat_at(root_fd, relative)
                    except FileNotFoundError:
                        continue
                    except OSError as exc:
                        raise CheckFailed(f"cannot safely inspect {relative}: {exc}") from exc
                    if stat.S_ISLNK(info.st_mode):
                        skipped.append(relative)
                    elif stat.S_ISREG(info.st_mode):
                        candidates.append({"path": relative, **_fingerprint(info)})
                    else:
                        raise CheckFailed(f"setup metadata candidate is not a regular file: {relative}")
        finally:
            os.close(root_fd)

    allocated = _allocated_reclaimable(candidates)
    return {
        "schema_version": SCHEMA_VERSION,
        "contract": CONTRACT,
        "created_at": time.time(),
        "project_root": str(cfg.root.resolve()),
        "ir_root": str(ir_path),
        "ir_root_exists": exists,
        "ir_root_fingerprint": root_fingerprint,
        "toolchain": toolchain,
        "selection": "all" if modules is None else "built-modules",
        "candidates": candidates,
        "skipped_symlinks": skipped,
        "summary": {
            "files": len(candidates),
            "logical_bytes": sum(row["size"] for row in candidates),
            "allocated_bytes_reclaimable": allocated,
            "skipped_symlinks": len(skipped),
        },
    }


def apply_setup_manifest(cfg, manifest: dict) -> dict:
    """Revalidate a manifest in full, then unlink only its exact inode snapshots."""
    if manifest.get("schema_version") != SCHEMA_VERSION or manifest.get("contract") != CONTRACT:
        raise CheckFailed("unsupported setup metadata manifest contract")
    if manifest.get("project_root") != str(cfg.root.resolve()):
        raise CheckFailed("setup metadata manifest belongs to another project root")
    if type(manifest.get("ir_root_exists")) is not bool:
        raise CheckFailed("setup metadata manifest root state is invalid")
    root_record = manifest.get("ir_root_fingerprint")
    if manifest["ir_root_exists"]:
        if not isinstance(root_record, dict) or any(type(root_record.get(key)) is not int for key in ("dev", "ino", "mode")):
            raise CheckFailed("setup metadata manifest root fingerprint is malformed")
        if not stat.S_ISDIR(root_record["mode"]):
            raise CheckFailed("setup metadata manifest root is not a directory")
    elif root_record is not None:
        raise CheckFailed("setup metadata manifest has a fingerprint for a missing root")
    _check_toolchain(cfg)
    ir_path, exists = _validated_ir_path(cfg)
    candidates = _validated_candidates(manifest)
    if not exists:
        if candidates:
            raise CheckFailed("setup metadata root disappeared after manifest creation")
        return {"files_removed": 0, "logical_bytes_removed": 0, "allocated_bytes_reclaimed": 0}
    if str(ir_path) != manifest.get("ir_root"):
        raise CheckFailed("setup metadata root changed after manifest creation")

    root_fd = os.open(ir_path, os.O_RDONLY | _DIRECTORY | _NOFOLLOW)
    try:
        expected_root = manifest.get("ir_root_fingerprint") or {}
        current_root = _fingerprint(os.fstat(root_fd))
        if any(current_root.get(key) != expected_root.get(key) for key in ("dev", "ino", "mode")):
            raise CheckFailed("setup metadata root was replaced after manifest creation")

        # Validate everything before deleting anything.  This turns ordinary
        # rebuild/mutation races into a refusal rather than a partial cleanup.
        for record in candidates:
            try:
                info = _stat_at(root_fd, record["path"])
            except (FileNotFoundError, NotADirectoryError, OSError) as exc:
                raise CheckFailed(f"setup metadata candidate changed: {record.get('path')}") from exc
            if not stat.S_ISREG(info.st_mode) or not _matches(record, info):
                raise CheckFailed(f"setup metadata candidate changed: {record['path']}")

        removed_by_inode: Counter[tuple[int, int]] = Counter()
        files_removed = logical_removed = allocated_reclaimed = 0
        try:
            for record in candidates:
                key = (record["dev"], record["ino"])
                parts = PurePosixPath(record["path"]).parts
                parent = _open_dir_at(root_fd, parts[:-1])
                try:
                    info = os.stat(parts[-1], dir_fd=parent, follow_symlinks=False)
                    if not stat.S_ISREG(info.st_mode) or not _matches(record, info, removed_links=removed_by_inode[key]):
                        raise CheckFailed(f"setup metadata candidate changed during cleanup: {record['path']}")
                    os.unlink(parts[-1], dir_fd=parent)
                    removed_by_inode[key] += 1
                    files_removed += 1
                    logical_removed += record["size"]
                    if removed_by_inode[key] == record["nlink"]:
                        allocated_reclaimed += record["allocated_bytes"]
                finally:
                    os.close(parent)
        except (OSError, CheckFailed) as exc:
            raise SetupCleanupPartial(
                f"cleanup stopped after {files_removed} unlink(s): {exc}",
                {
                    "files_removed": files_removed,
                    "logical_bytes_removed": logical_removed,
                    "allocated_bytes_reclaimed": allocated_reclaimed,
                },
            ) from exc
    finally:
        os.close(root_fd)

    return {
        "files_removed": files_removed,
        "logical_bytes_removed": logical_removed,
        "allocated_bytes_reclaimed": allocated_reclaimed,
    }


def prune_setup_metadata(cfg, *, apply: bool, output_dir: Path, modules: Iterable[str] | None = None) -> dict:
    """Write a durable manifest and receipt for a dry run or guarded deletion."""
    output_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = output_dir / "manifest.json"
    receipt_path = output_dir / "receipt.json"
    manifest = create_setup_manifest(cfg, modules=modules)
    _write_json(manifest_path, manifest)
    manifest_sha256 = hashlib.sha256(manifest_path.read_bytes()).hexdigest()
    receipt = {
        "schema_version": SCHEMA_VERSION,
        "contract": CONTRACT,
        "mode": "apply" if apply else "dry-run",
        "status": "dry-run",
        "manifest": str(manifest_path),
        "manifest_sha256": manifest_sha256,
        **manifest["summary"],
        "files_removed": 0,
        "logical_bytes_removed": 0,
        "allocated_bytes_reclaimed": 0,
    }
    try:
        if apply:
            receipt.update(apply_setup_manifest(cfg, manifest), status="removed")
    except Exception as exc:
        progress = getattr(exc, "progress", {})
        receipt.update(
            status="partial" if progress.get("files_removed", 0) else "failed",
            error=f"{type(exc).__name__}: {exc}",
            **progress,
        )
        _write_json(receipt_path, receipt)
        raise CheckFailed(f"setup metadata cleanup failed: {exc}; receipt {receipt_path}") from exc
    _write_json(receipt_path, receipt)
    receipt["receipt"] = str(receipt_path)
    return receipt


def built_modules(log_path: Path) -> list[str]:
    try:
        text = log_path.read_text(errors="replace")
    except OSError:
        return []
    return sorted(set(match.group(1) for match in _BUILT.finditer(text)))


def post_build_cleanup(cfg, log_path: Path) -> dict | None:
    """Prune only setup files named by successful Lake ``Built`` log records."""
    modules = built_modules(log_path)
    if not modules:
        return None
    output_dir = log_path.parent / "setup-metadata" / log_path.stem
    return prune_setup_metadata(cfg, apply=True, output_dir=output_dir, modules=modules)
