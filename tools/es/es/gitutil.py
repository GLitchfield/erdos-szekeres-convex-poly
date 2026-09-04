"""Git access honouring a configured git-dir (some checkouts keep metadata elsewhere)."""

from __future__ import annotations

import hashlib
import subprocess
from pathlib import Path

from es.config import Config


def git_argv(cfg: Config) -> list[str]:
    if cfg.git_dir is not None:
        return ["git", f"--git-dir={cfg.git_dir}", f"--work-tree={cfg.root}"]
    return ["git", "-C", str(cfg.root)]


def git(cfg: Config, *args: str, check: bool = True) -> str:
    proc = subprocess.run(git_argv(cfg) + list(args), capture_output=True, text=True, cwd=cfg.root)
    if check and proc.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed: {proc.stderr.strip()}")
    return proc.stdout


def git_ok(cfg: Config) -> bool:
    try:
        git(cfg, "rev-parse", "--show-toplevel")
        return True
    except (RuntimeError, OSError):
        return False


def head_sha(cfg: Config) -> str:
    try:
        return git(cfg, "rev-parse", "HEAD").strip()
    except (RuntimeError, OSError):
        return "unknown"


def tree_hash(cfg: Config, dirs: list[str]) -> str:
    """HEAD tree hash mixed with the content of uncommitted changes under ``dirs``."""
    h = hashlib.sha256()
    try:
        h.update(git(cfg, "rev-parse", "HEAD^{tree}").strip().encode())
        status = git(cfg, "status", "--porcelain", "--untracked-files=all", "--", *dirs)
    except (RuntimeError, OSError):
        # no git: hash every file under dirs
        for d in dirs:
            for p in sorted((cfg.root / d).rglob("*") if (cfg.root / d).is_dir() else [cfg.root / d]):
                if p.is_file():
                    h.update(str(p.relative_to(cfg.root)).encode())
                    h.update(p.read_bytes())
        return h.hexdigest()[:16]
    for line in sorted(status.splitlines()):
        h.update(line.encode())
        rel = line[3:].split(" -> ")[-1].strip()
        p = cfg.root / rel
        if p.is_file():
            h.update(p.read_bytes())
    return h.hexdigest()[:16]


def changed_files(cfg: Config, ref: str) -> list[str]:
    out = git(cfg, "diff", "--name-only", ref, "--", check=False)
    files = {line.strip() for line in out.splitlines() if line.strip()}
    status = git(cfg, "status", "--porcelain", "--untracked-files=all", check=False)
    for line in status.splitlines():
        files.add(line[3:].split(" -> ")[-1].strip())
    return sorted(files)


def git_mv(cfg: Config, src: Path, dst: Path) -> None:
    dst.parent.mkdir(parents=True, exist_ok=True)
    try:
        git(cfg, "mv", str(src), str(dst))
    except (RuntimeError, OSError):
        src.rename(dst)
