#!/usr/bin/env python3
"""Freeze mutable orchestration context for a rolling agent lane.

The capsule embeds the exact UTF-8 bytes needed by a worker.  Canonical files
may then change during serial reconciliation without changing the worker's
input.  Mathematical sources and executable artifacts should remain direct
task inputs; this tool is for root-owned orchestration context.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
SCHEMA_VERSION = 1
TOP_LEVEL_FIELDS = {
    "schema_version",
    "snapshot_id",
    "base_revision",
    "source_entries",
    "aggregate_sha256",
}
ENTRY_FIELDS = {"path", "bytes", "sha256", "content"}


class SnapshotError(ValueError):
    """Raised when a context capsule is malformed or cannot be frozen."""


def compact_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def normalize_source(root: Path, raw_path: str) -> tuple[str, bytes]:
    candidate = Path(raw_path)
    if candidate.is_absolute():
        raise SnapshotError(f"source path must be relative: {raw_path}")
    resolved_root = root.resolve()
    resolved = (resolved_root / candidate).resolve()
    try:
        relative = resolved.relative_to(resolved_root)
    except ValueError as exc:
        raise SnapshotError(f"source escapes repository root: {raw_path}") from exc
    if not resolved.is_file():
        raise SnapshotError(f"source is not a regular file: {raw_path}")
    data = resolved.read_bytes()
    try:
        data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise SnapshotError(f"source is not UTF-8 text: {raw_path}") from exc
    return relative.as_posix(), data


def build_snapshot(
    *, root: Path, snapshot_id: str, base_revision: str, sources: Iterable[str]
) -> dict[str, Any]:
    if not snapshot_id:
        raise SnapshotError("snapshot_id must be nonempty")
    if not base_revision:
        raise SnapshotError("base_revision must be nonempty")

    entries_by_path: dict[str, dict[str, Any]] = {}
    for raw_path in sources:
        relative, data = normalize_source(root, raw_path)
        if relative in entries_by_path:
            raise SnapshotError(f"duplicate source path: {relative}")
        entries_by_path[relative] = {
            "path": relative,
            "bytes": len(data),
            "sha256": sha256_bytes(data),
            "content": data.decode("utf-8"),
        }
    if not entries_by_path:
        raise SnapshotError("at least one source is required")

    entries = [entries_by_path[path] for path in sorted(entries_by_path)]
    return {
        "schema_version": SCHEMA_VERSION,
        "snapshot_id": snapshot_id,
        "base_revision": base_revision,
        "source_entries": entries,
        "aggregate_sha256": sha256_bytes(compact_bytes(entries)),
    }


def validate_snapshot(
    snapshot: Any, *, root: Path | None = None, compare_live: bool = False
) -> list[str]:
    errors: list[str] = []
    if not isinstance(snapshot, dict):
        return ["snapshot must be a JSON object"]
    if set(snapshot) != TOP_LEVEL_FIELDS:
        errors.append("snapshot has unexpected or missing top-level fields")
    if snapshot.get("schema_version") != SCHEMA_VERSION:
        errors.append("schema_version must be 1")
    if not isinstance(snapshot.get("snapshot_id"), str) or not snapshot.get(
        "snapshot_id"
    ):
        errors.append("snapshot_id must be a nonempty string")
    if not isinstance(snapshot.get("base_revision"), str) or not snapshot.get(
        "base_revision"
    ):
        errors.append("base_revision must be a nonempty string")

    entries = snapshot.get("source_entries")
    if not isinstance(entries, list) or not entries:
        errors.append("source_entries must be a nonempty array")
        return errors

    paths: list[str] = []
    for index, entry in enumerate(entries):
        label = f"source_entries[{index}]"
        if not isinstance(entry, dict) or set(entry) != ENTRY_FIELDS:
            errors.append(f"{label} has unexpected or missing fields")
            continue
        path = entry.get("path")
        content = entry.get("content")
        byte_count = entry.get("bytes")
        digest = entry.get("sha256")
        if not isinstance(path, str) or not path or Path(path).is_absolute():
            errors.append(f"{label}.path must be a nonempty relative path")
            continue
        if ".." in Path(path).parts:
            errors.append(f"{label}.path must not escape the repository")
            continue
        paths.append(path)
        if not isinstance(content, str):
            errors.append(f"{label}.content must be UTF-8 text")
            continue
        data = content.encode("utf-8")
        if byte_count != len(data):
            errors.append(f"{label}.bytes mismatch")
        if digest != sha256_bytes(data):
            errors.append(f"{label}.sha256 mismatch")
        if compare_live:
            if root is None:
                errors.append("compare_live requires a repository root")
            else:
                try:
                    _, live_data = normalize_source(root, path)
                except SnapshotError as exc:
                    errors.append(str(exc))
                else:
                    if sha256_bytes(live_data) != digest:
                        errors.append(f"live source drift: {path}")

    if paths != sorted(paths):
        errors.append("source_entries must be sorted by path")
    if len(paths) != len(set(paths)):
        errors.append("source_entries contain duplicate paths")
    if snapshot.get("aggregate_sha256") != sha256_bytes(compact_bytes(entries)):
        errors.append("aggregate_sha256 mismatch")
    return errors


def write_new(path: Path, payload: dict[str, Any]) -> None:
    if path.exists():
        raise SnapshotError(f"refusing to overwrite frozen snapshot: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp")
    if temporary.exists():
        raise SnapshotError(f"temporary output already exists: {temporary}")
    temporary.write_bytes(compact_bytes(payload) + b"\n")
    temporary.replace(path)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    create = subparsers.add_parser("create", help="create one immutable capsule")
    create.add_argument("--snapshot-id", required=True)
    create.add_argument("--base-revision", required=True)
    create.add_argument("--output", type=Path, required=True)
    create.add_argument("--source", action="append", required=True)

    verify = subparsers.add_parser("verify", help="verify one capsule")
    verify.add_argument("--snapshot", type=Path, required=True)
    verify.add_argument("--compare-live", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if args.command == "create":
            payload = build_snapshot(
                root=ROOT,
                snapshot_id=args.snapshot_id,
                base_revision=args.base_revision,
                sources=args.source,
            )
            write_new(args.output, payload)
            print(
                json.dumps(
                    {
                        "snapshot": str(args.output),
                        "sources": len(payload["source_entries"]),
                        "aggregate_sha256": payload["aggregate_sha256"],
                    },
                    sort_keys=True,
                )
            )
            return 0

        snapshot = json.loads(args.snapshot.read_text(encoding="utf-8"))
        errors = validate_snapshot(
            snapshot, root=ROOT, compare_live=args.compare_live
        )
        if errors:
            raise SnapshotError("; ".join(errors))
        print(
            json.dumps(
                {
                    "snapshot": str(args.snapshot),
                    "sources": len(snapshot["source_entries"]),
                    "aggregate_sha256": snapshot["aggregate_sha256"],
                    "live_compared": bool(args.compare_live),
                },
                sort_keys=True,
            )
        )
        return 0
    except (OSError, json.JSONDecodeError, SnapshotError) as exc:
        print(f"context snapshot error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
