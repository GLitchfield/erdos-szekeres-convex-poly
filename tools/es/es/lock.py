"""Statement lock: node name -> approved type hash."""

from __future__ import annotations

import json
import time
from pathlib import Path


def read_lock(path: Path) -> dict[str, dict]:
    if not path.exists():
        return {}
    try:
        data = json.loads(path.read_text() or "{}")
    except json.JSONDecodeError as exc:
        raise ValueError(f"{path} is not valid JSON: {exc}") from exc
    return data if isinstance(data, dict) else {}


def write_lock(path: Path, lock: dict[str, dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(dict(sorted(lock.items())), indent=2, ensure_ascii=False) + "\n")


def lock_entry(type_hash: str, type_pp: str, approved_by: str, kind: str, ws: str) -> dict:
    return {
        "type_hash": type_hash,
        "type_pp": type_pp,
        "approved_by": approved_by,
        "approved_at": time.strftime("%Y-%m-%d"),
        "kind": kind,
        "ws": ws,
    }


def check_lock(lock: dict[str, dict], nodes: list) -> list[str]:
    """Problems: nodes missing from the lock or whose hash changed."""
    problems = []
    for n in nodes:
        entry = lock.get(n.name)
        if entry is None:
            problems.append(f"{n.name}: not in statements.lock (approve with `es node add`/`es node restate`)")
        elif entry.get("type_hash") != n.type_hash:
            problems.append(f"{n.name}: statement changed by hand (lock {entry.get('type_hash')}, now {n.type_hash}); use `es node restate`")
    return problems
