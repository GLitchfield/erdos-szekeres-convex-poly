from __future__ import annotations

import hashlib
import os
import re
import shutil
import tempfile
import time
from pathlib import Path

from es import EXIT_CHECK_FAILED, EXIT_OK
from es.context import Ctx
from es.config import primary_root
from es.errors import CheckFailed
from es.nodes import find_node, load_nodes_json, nodes_from_json
from es.output import Result
from es.spec import Arg, CommandSpec, command
from es.store import Store


def run_claim(ctx: Ctx, name: str, why: str | None = None, agent: str | None = None, note: str | None = None, force: bool = False) -> Result:
    cfg = ctx.cfg
    agent = agent or ctx.agent
    why = (why or note or "").strip() or None
    if cfg.claims_require_why and not why:
        raise CheckFailed("--why is required: say what you intend to do with the node (shown in `es status`)")
    n = find_node(cfg, name)
    with Store(cfg) as st:
        existing = st.claims().get(n.name)
        if existing and existing["agent"] != agent:
            raise CheckFailed(f"{n.name} is claimed by {existing['agent']} until {time.strftime('%Y-%m-%d %H:%M', time.localtime(existing['expires_at']))}")
        if n.status == "proposed" and n.kind == "conjecture":
            raise CheckFailed(f"{n.name} is a conjecture whose falsifier has not passed; run `es falsify {n.short}` first")
        if not n.ready and not existing:
            reason = "blocked by " + ", ".join(n.blocked_by) if n.blocked_by else f"status {n.status}"
            if not force:
                raise CheckFailed(f"{n.name} is not ready ({reason}); use --force to claim anyway")
            st.event("claim-forced", n.name, agent, {"reason": reason, "why": why})
        claim = st.claim(n.name, agent, cfg.claim_ttl_hours, why)
    return Result(EXIT_OK, {"claim": claim}, [f"claimed {n.name} for {agent} until {time.strftime('%Y-%m-%d %H:%M', time.localtime(claim['expires_at']))}"
                                              + (f": {why}" if why else "")])


OUTCOMES = ["closed", "partial", "blocked", "abandoned", "refuted"]


RUN_PATH = re.compile(r"(?<![A-Za-z0-9_.-])(runs/[A-Za-z0-9_@+./-]+)")


def _digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def _publish_without_overwrite(source: Path, destination: Path) -> str:
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.is_symlink():
        raise CheckFailed(f"release evidence conflict: {destination} is a symlink")
    if destination.exists():
        if destination.is_file() and _digest(source) == _digest(destination):
            return "present"
        raise CheckFailed(f"release evidence conflict: {destination} already exists with different content")
    fd, temporary = tempfile.mkstemp(prefix=".es-release-", dir=destination.parent)
    try:
        os.fchmod(fd, source.stat().st_mode & 0o777)
        with source.open("rb") as src, os.fdopen(fd, "wb") as dst:
            shutil.copyfileobj(src, dst)
            dst.flush()
            os.fsync(dst.fileno())
        try:
            os.link(temporary, destination)
        except FileExistsError:
            if not destination.is_symlink() and destination.is_file() and _digest(source) == _digest(destination):
                return "present"
            raise CheckFailed(f"release evidence conflict: {destination} appeared with different content") from None
    finally:
        Path(temporary).unlink(missing_ok=True)
    directory = os.open(destination.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(directory)
    finally:
        os.close(directory)
    return "copied"


def _normalize_run_citation(rel: str) -> str:
    """Map a primary-relative worktree citation back to its worktree-local runs path."""
    parts = Path(rel).parts
    if len(parts) >= 5 and parts[0:2] == ("runs", "worktrees") and parts[3] == "runs":
        return str(Path("runs", *parts[4:]))
    return rel


def preserve_release_evidence(cfg, note: str | None) -> dict[str, list]:
    """Publish cited worktree ``runs/`` files at the same primary-checkout paths."""
    primary = primary_root(cfg.root).resolve()
    if not note or primary == cfg.root.resolve():
        return {"copied": [], "present": [], "missing": [], "artifacts": []}
    cited = list(dict.fromkeys(
        _normalize_run_citation(match.rstrip(".,;:)]}")) for match in RUN_PATH.findall(note)))
    found: list[tuple[str, Path, Path]] = []
    missing: list[str] = []
    artifacts: list[dict] = []
    source_runs = (cfg.root / "runs").resolve()
    primary_runs = (primary / "runs").resolve()

    def preserve_artifact(rel: str, source: Path, reason: str) -> None:
        from es.artifacts import put

        ref = put(cfg, source.read_bytes(), "release-evidence-conflict-v1")
        artifacts.append(ref | {"source": rel, "reason": reason})

    for rel in cited:
        source = (cfg.root / rel).resolve()
        candidate = primary / rel
        try:
            source.relative_to(source_runs)
        except ValueError:
            missing.append(rel)
            continue
        if not source.is_file():
            missing.append(rel)
            continue
        try:
            parent_rel = candidate.parent.relative_to(primary)
        except ValueError:
            preserve_artifact(rel, source, "destination escapes primary checkout")
            continue
        current = primary
        unsafe_parent = None
        for part in parent_rel.parts:
            current /= part
            if current.is_symlink():
                unsafe_parent = current
                break
        if unsafe_parent is not None:
            preserve_artifact(rel, source, f"destination has symlink parent {unsafe_parent}")
            continue
        # Resolve `..` components only after rejecting existing parent
        # symlinks, and keep the final component intact for its own check.
        destination = candidate.parent.resolve() / candidate.name
        try:
            destination.parent.relative_to(primary_runs)
        except ValueError:
            preserve_artifact(rel, source, "destination escapes primary runs directory")
            continue
        found.append((rel, source, destination))
    result = {"copied": [], "present": [], "missing": missing, "artifacts": artifacts}
    for rel, source, destination in found:
        try:
            result[_publish_without_overwrite(source, destination)].append(rel)
        except (CheckFailed, OSError) as exc:
            preserve_artifact(rel, source, str(exc))
    result["artifacts"] = artifacts
    return result


def run_release(ctx: Ctx, name: str, outcome: str, note: str | None = None, agent: str | None = None) -> Result:
    cfg = ctx.cfg
    n = find_node(cfg, name)
    note = (note or "").strip() or None
    # releasing a node that is already sorry-free is not an abandoned attempt
    if outcome in ("abandoned", "partial") and n.status in ("closed", "merged"):
        outcome = "closed"
    if outcome in ("partial", "blocked", "abandoned") and not note:
        raise CheckFailed(f"--note is required with --outcome {outcome}: say what was done and what stopped you, for the next agent")
    with Store(cfg) as st:
        if n.name not in st.claims():
            return Result(EXIT_CHECK_FAILED, {"released": False}, [f"{n.name} was not claimed"])
    evidence = preserve_release_evidence(cfg, note)
    with Store(cfg) as st:
        ok = st.release(n.name, agent or ctx.agent, outcome=outcome, note=note)
    if not ok:
        return Result(EXIT_CHECK_FAILED, {"released": False}, [f"{n.name} was not claimed"])
    human = [f"released {n.name} ({outcome}" + (f": {note}" if note else "") + ")"]
    if evidence["copied"]:
        human.append("preserved release evidence in primary checkout: " + ", ".join(evidence["copied"]))
    if evidence["missing"]:
        human.append("cited release evidence not found in worktree: " + ", ".join(evidence["missing"]))
    if evidence["artifacts"]:
        human.append("release evidence conflicts preserved as immutable artifact(s): " +
                     ", ".join(a["id"] for a in evidence["artifacts"]))
    return Result(EXIT_OK, {"released": True, "outcome": outcome, "note": note, "evidence": evidence}, human)


command(CommandSpec(name="claim", cli=["claim"], help="Claim a ready node for this agent (12 h by default); --why records the intent shown in `es status`.", run=run_claim,
                    args=[Arg("name", "node name", positional=True, required=True), Arg("why", "what you intend to do (required unless [claims] require_why = false)"),
                          Arg("agent", "agent id (default: ES_AGENT)"), Arg("note", "alias of --why"), Arg("force", "claim a node that is not ready (logged)", "bool")]))
command(CommandSpec(name="release", cli=["release"], help="Release a claim with an outcome; partial/blocked/abandoned need --note (what was done, what stopped you).", run=run_release,
                    args=[Arg("name", "node name", positional=True, required=True),
                          Arg("outcome", "closed | partial | blocked | abandoned | refuted", required=True, choices=OUTCOMES),
                          Arg("note", "what was done and what remains"), Arg("agent", "agent id")]))
