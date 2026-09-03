#!/usr/bin/env python3
"""Run a bounded, self-refilling, chat-independent research-seed service."""

from __future__ import annotations

import argparse
import copy
from contextlib import contextmanager, nullcontext
from datetime import datetime, timedelta, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from typing import Any
import uuid

try:
    from scripts import build_sol_idea_packet
    from scripts import check_research_campaign as campaign
except ModuleNotFoundError:  # Direct `python3 scripts/...` execution.
    import build_sol_idea_packet
    import check_research_campaign as campaign


ROOT = Path(__file__).resolve().parents[1]
RUNS_ROOT = (ROOT / "runs" / "agents").resolve()
DEFAULT_SERVICE_DIR = Path("runs/agents/continuous-idea-generator")
PROTOCOL_VERSION = "continuous-idea-generator-v3"
CLAIM_PROTOCOL = "continuous-idea-generator-v3-claim-v3"
RATE_ACCOUNTING_PROTOCOLS = {
    "continuous-idea-generator-v2",
    "continuous-idea-generator-v2.1",
    PROTOCOL_VERSION,
}
NON_RATE_HISTORICAL_PROTOCOLS = {"continuous-idea-generator-v1"}
WAYFINDER_TICKET = (
    "docs/wayfinder/tickets/0119-adopt-self-refilling-investigation-loop.md"
)
SUPPORTED_MODES = {"context_rich", "failure_dual", "recombination"}
DEFAULT_GENERATION_MODES = ("context_rich", "failure_dual", "recombination")
ACTIVE_AUTHORIZATION_NAME = "active-authorization.json"
AUTHORIZATION_DIRECTORY_NAME = "authorizations"
SYSTEMD_UNIT_NAME = "erdos-szekeres-continuous-idea-generator.service"
SAFE_LEAF_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")
FEEDBACK_SCHEMA = (
    ROOT / "docs/agents/schemas/research-investigation-feedback.schema.json"
)
ROOT_SEMANTIC_SCREEN_SCHEMA = (
    ROOT / "docs/agents/schemas/research-root-semantic-screen.schema.json"
)
SNAPSHOT_BUILD_SCHEMA = (
    ROOT / "docs/agents/schemas/research-snapshot-build-receipt.schema.json"
)
VALIDATED_LEARNING_EXPORT_SCHEMA = (
    ROOT / "docs/agents/schemas/research-validated-learning-export.schema.json"
)
FIRST_TEST_GUARD = (ROOT / "scripts/run_first_test_guarded.py").resolve()
FIRST_TEST_EXECUTION_ENVELOPE_SCHEMA = (
    ROOT
    / "docs/agents/schemas/research-first-test-execution-envelope.schema.json"
).resolve()
SNAPSHOT_ADMISSION_PROTOCOL = (
    "continuous-idea-generator-snapshot-admission-v1"
)
SNAPSHOT_ADMISSION_NAME = "snapshot-admission.json"
MIGRATION_ROOT = (
    ROOT / "docs/agents/continuous-idea-generator-v3-migration-root.json"
)
EXPECTED_MIGRATION_ROOT_SHA256 = (
    "79ab68c3e1313b4d0f5b6d08be9e1dc5c0ce262ac927cdb05e9f05feb7e25dc9"
)
INVOCATION_LEDGER_PROTOCOL = "continuous-idea-generator-invocation-ledger-v1"
ACCOUNTING_BASELINE_DIRECTORY = "accounting-baselines"
ACCOUNTING_EVENT_DIRECTORY = "invocation-ledger/events"
ACCOUNTING_HEAD_NAME = "invocation-ledger/head.json"
AUTHORIZATION_ACTIVATION_PROTOCOL = (
    "continuous-idea-generator-authorization-activation-v1"
)
AUTHORIZATION_ACTIVATION_DIRECTORY = "authorization-activations/events"
AUTHORIZATION_ACTIVATION_HEAD_NAME = "authorization-activations/head.json"
PROVIDER_RESULT_TERMINALS = {
    "SEED-BATCH-COMPLETE",
    "SEED-BATCH-NOVELTY-STOP",
    "SEED-BATCH-PROVIDER-STOP",
    "SEED-BATCH-PACKET-MISMATCH",
}
DEDUP_TRANSFORM_PROTOCOL = "continuous-idea-generator-dedup-v1"
STRIPPED_SCHEMA_KEYS = {
    "$schema",
    "$id",
    "title",
    "description",
    "examples",
    "default",
    "pattern",
    "format",
    "minLength",
    "maxLength",
    "minimum",
    "maximum",
    "exclusiveMinimum",
    "exclusiveMaximum",
    "minItems",
    "maxItems",
    "uniqueItems",
}


class ServiceError(ValueError):
    """The service contract or an immutable receipt failed."""


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def repo_relative(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError as exc:
        raise ServiceError(f"path is outside the repository: {path}") from exc


def service_directory(value: Path) -> Path:
    path = value if value.is_absolute() else ROOT / value
    path = path.resolve()
    try:
        path.relative_to(RUNS_ROOT)
    except ValueError as exc:
        raise ServiceError("service directory must be under runs/agents") from exc
    return path


def canonical_service_state_root(service_dir: Path) -> Path:
    """Resolve the one permitted non-aliased service-state root."""
    lexical = service_dir if service_dir.is_absolute() else ROOT / service_dir
    absolute = Path(os.path.abspath(lexical))
    resolved = absolute.resolve()
    try:
        resolved.relative_to(RUNS_ROOT)
    except ValueError as exc:
        raise ServiceError("service directory must be under runs/agents") from exc
    if absolute != resolved or absolute.is_symlink():
        raise ServiceError("service directory must be a canonical non-symlink path")
    return absolute


def validate_service_state_layout(service_dir: Path) -> Path:
    """Authenticate the service root and reject every descendant symlink.

    Service receipts intentionally name one physical state tree.  A lexical
    child which is later rebound through a directory or leaf symlink is not
    that tree, even when it still resolves somewhere below ``runs/agents``.
    This check is deliberately stronger than receipt containment: no service
    state artifact has symlink semantics.
    """
    absolute = canonical_service_state_root(service_dir)
    if not absolute.exists():
        return absolute
    if not absolute.is_dir():
        raise ServiceError("service state root is not a directory")
    for parent, directory_names, file_names in os.walk(
        absolute, topdown=True, followlinks=False
    ):
        parent_path = Path(parent)
        for name in [*directory_names, *file_names]:
            child = parent_path / name
            if child.is_symlink():
                raise ServiceError(
                    f"service state contains a symlink alias: {child}"
                )
            try:
                child.resolve().relative_to(absolute)
            except ValueError as exc:
                raise ServiceError(
                    f"service state escapes its canonical root: {child}"
                ) from exc
    return absolute


def service_state_path(service_dir: Path, *parts: str) -> Path:
    """Return one lexical service child after exact containment checks."""
    root = canonical_service_state_root(service_dir)
    if not parts or any(
        not isinstance(part, str)
        or not part
        or Path(part).is_absolute()
        or ".." in Path(part).parts
        for part in parts
    ):
        raise ServiceError("service state path components are invalid")
    target = root.joinpath(*parts)
    cursor = root
    for part in target.relative_to(root).parts:
        cursor /= part
        if cursor.is_symlink():
            raise ServiceError(f"service state contains a symlink alias: {cursor}")
    try:
        target.resolve(strict=False).relative_to(root)
    except ValueError as exc:
        raise ServiceError("service state path escapes its canonical root") from exc
    return target


def exact_queue_children(service_dir: Path) -> list[Path]:
    """Return every exact queue object, rejecting hidden/aliased children."""
    queue_dir = service_state_path(service_dir, "queue")
    if not queue_dir.exists():
        return []
    if not queue_dir.is_dir():
        raise ServiceError("queue state is not a directory")
    children = sorted(queue_dir.iterdir(), key=lambda path: path.name)
    if any(
        child.is_symlink()
        or not child.is_file()
        or child.suffix != ".json"
        for child in children
    ):
        raise ServiceError(
            "queue contains a non-JSON, directory, or symlink-alias child"
        )
    return children


def safe_leaf_id(value: Any, label: str) -> str:
    if (
        not isinstance(value, str)
        or value in {".", ".."}
        or SAFE_LEAF_ID.fullmatch(value) is None
    ):
        raise ServiceError(
            f"{label} must be a safe single path-component identity"
        )
    return value


@contextmanager
def locked_service_state(service_dir: Path):
    """Serialize every short transition that changes queue-visible state."""
    service_dir.mkdir(parents=True, exist_ok=True)
    service_dir = validate_service_state_layout(service_dir)
    handle = service_state_path(service_dir, "state-transition.lock").open("a+")
    fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
    try:
        yield
    finally:
        fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
        handle.close()


def fsync_directory(path: Path) -> None:
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    descriptor = os.open(path, flags)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def durable_mkdir(path: Path) -> None:
    missing: list[Path] = []
    cursor = path
    while not cursor.exists():
        missing.append(cursor)
        cursor = cursor.parent
    path.mkdir(parents=True, exist_ok=True)
    for directory in reversed(missing):
        fsync_directory(directory)
        fsync_directory(directory.parent)


def atomic_json(path: Path, value: Any) -> None:
    durable_mkdir(path.parent)
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}-{time.time_ns()}")
    encoded = json.dumps(value, indent=2, sort_keys=True) + "\n"
    try:
        with temporary.open("x", encoding="utf-8") as handle:
            handle.write(encoded)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
        fsync_directory(path.parent)
    finally:
        if temporary.exists():
            temporary.unlink()


def write_once(path: Path, value: Any) -> None:
    encoded = json.dumps(value, indent=2, sort_keys=True) + "\n"
    if path.exists():
        if path.read_text(encoding="utf-8") != encoded:
            raise ServiceError(f"immutable artifact already exists with other bytes: {path}")
        return
    durable_mkdir(path.parent)
    try:
        with path.open("x", encoding="utf-8") as handle:
            handle.write(encoded)
            handle.flush()
            os.fsync(handle.fileno())
    except FileExistsError:
        if path.read_text(encoding="utf-8") != encoded:
            raise ServiceError(
                f"immutable artifact already exists with other bytes: {path}"
            )
        return
    fsync_directory(path.parent)


def read_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ServiceError(f"cannot read {label} {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise ServiceError(f"{label} must be a JSON object: {path}")
    return value


def file_receipt(path: Path) -> dict[str, str]:
    return {"path": repo_relative(path), "sha256": sha256(path)}


def implementation_component_paths() -> list[Path]:
    """Return every executable/schema component covered by standing authority."""
    return [
        Path(__file__).resolve(),
        Path(build_sol_idea_packet.__file__).resolve(),
        Path(campaign.__file__).resolve(),
        FIRST_TEST_GUARD,
        campaign.SEED_SCHEMA.resolve(),
        campaign.BRIEF_SCHEMA.resolve(),
        campaign.RECEIPT_SCHEMA.resolve(),
        campaign.TASK_SCHEMA.resolve(),
        campaign.EVENT_VERIFICATION_SCHEMA.resolve(),
        FEEDBACK_SCHEMA.resolve(),
        ROOT_SEMANTIC_SCREEN_SCHEMA.resolve(),
        SNAPSHOT_BUILD_SCHEMA.resolve(),
        VALIDATED_LEARNING_EXPORT_SCHEMA.resolve(),
        FIRST_TEST_EXECUTION_ENVELOPE_SCHEMA,
        MIGRATION_ROOT.resolve(),
        (ROOT / "AGENTS.md").resolve(),
        (ROOT / "docs/agents/continuous-idea-generator.md").resolve(),
        (ROOT / "docs/agents/research-campaign.md").resolve(),
        (ROOT / WAYFINDER_TICKET).resolve(),
    ]


def normalized_json(value: Any) -> Any:
    """Normalize proposal text for deterministic literal-duplicate memory."""
    if isinstance(value, dict):
        return {key: normalized_json(value[key]) for key in sorted(value)}
    if isinstance(value, list):
        return [normalized_json(item) for item in value]
    if isinstance(value, str):
        return " ".join(value.casefold().split())
    return value


def seed_fingerprint(seed: dict[str, Any]) -> str:
    core = {
        "target_ref": seed.get("target_ref"),
        "model": seed.get("model"),
        "mechanism": seed.get("mechanism"),
        "first_test_question": (seed.get("first_test") or {}).get("question"),
    }
    encoded = json.dumps(
        normalized_json(core), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def generated_seed_memory(
    service_dir: Path, *, exclude_campaign: str | None = None
) -> dict[str, dict[str, str]]:
    memory: dict[str, dict[str, str]] = {}
    batches = service_dir / "batches"
    if not batches.exists():
        return memory
    for seed_path in sorted(batches.glob("*/seed-batch.json")):
        try:
            batch = read_json(seed_path, "seed batch")
        except ServiceError:
            continue
        campaign_id = batch.get("campaign_id")
        if campaign_id == exclude_campaign or batch.get("terminal") not in {
            "SEED-BATCH-COMPLETE",
            "SEED-BATCH-NOVELTY-STOP",
        }:
            continue
        for seed in batch.get("seeds", []):
            if not isinstance(seed, dict):
                continue
            fingerprint = seed_fingerprint(seed)
            memory.setdefault(
                fingerprint,
                {
                    "campaign_id": str(campaign_id),
                    "seed_id": str(seed.get("seed_id")),
                },
            )
    return memory


def deduplicate_provider_batch(
    service_dir: Path,
    payload: dict[str, Any],
    requested_seed_count: int | None = None,
    *,
    known_memory: dict[str, dict[str, str]] | None = None,
    source_receipt: dict[str, str] | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Drop only deterministic literal repeats; semantic review remains root-only."""
    campaign_id = str(payload.get("campaign_id"))
    known = (
        dict(known_memory)
        if known_memory is not None
        else generated_seed_memory(service_dir, exclude_campaign=campaign_id)
    )
    if source_receipt is not None:
        authenticate_receipt(source_receipt, "deduplication source")
    accepted: list[dict[str, Any]] = []
    accepted_receipts: list[dict[str, str]] = []
    dropped: list[dict[str, str]] = []
    seen = set(known)
    for seed in payload.get("seeds", []):
        fingerprint = seed_fingerprint(seed)
        if fingerprint in seen:
            prior = known.get(fingerprint)
            dropped.append(
                {
                    "seed_id": str(seed.get("seed_id")),
                    "fingerprint": fingerprint,
                    "reason": "literal-semantic-core-duplicate",
                    "prior": (
                        f"{prior['campaign_id']}:{prior['seed_id']}"
                        if prior is not None
                        else "same-batch"
                    ),
                }
            )
            continue
        seen.add(fingerprint)
        accepted.append(seed)
        accepted_receipts.append(
            {"seed_id": str(seed.get("seed_id")), "fingerprint": fingerprint}
        )
    requested = int(
        requested_seed_count
        if requested_seed_count is not None
        else payload.get("requested_seed_count", 5)
    )
    if payload.get("requested_seed_count", 5) != requested:
        raise ServiceError("provider response requested_seed_count differs from packet")
    if len(payload.get("seeds", [])) > requested:
        raise ServiceError("provider returned more seeds than the frozen request")
    batch = copy.deepcopy(payload)
    batch["seeds"] = accepted
    batch["terminal"] = (
        "SEED-BATCH-COMPLETE"
        if len(accepted) == requested
        else "SEED-BATCH-NOVELTY-STOP"
    )
    metrics = batch.get("generation_metrics")
    if isinstance(metrics, dict):
        metrics["literal_duplicates_removed"] = int(
            metrics.get("literal_duplicates_removed") or 0
        ) + len(dropped)
    report = {
        "schema_version": 1,
        "protocol": PROTOCOL_VERSION,
        "transform_protocol": DEDUP_TRANSFORM_PROTOCOL,
        "campaign_id": campaign_id,
        "requested_seed_count": requested,
        "source": source_receipt,
        "prior_fingerprint_count": len(known),
        "prior_fingerprint_memory_sha256": canonical_json_sha256(
            [
                {"fingerprint": fingerprint, **known[fingerprint]}
                for fingerprint in sorted(known)
            ]
        ),
        "provider_seed_count": len(payload.get("seeds", [])),
        "accepted_seed_count": len(accepted),
        "accepted": accepted_receipts,
        "dropped": dropped,
        "meaning": (
            "deterministic literal duplicate filter only; target-equivalence "
            "and mathematical novelty remain root-review obligations"
        ),
    }
    return batch, report


def frozen_generated_seed_memory(
    learning_export: dict[str, Any],
) -> dict[str, dict[str, str]]:
    """Reconstruct v1 duplicate memory from one admitted frozen export."""
    entries = learning_export.get("continuous_entries")
    if not isinstance(entries, list):
        raise ServiceError("validated learning export lacks continuous entries")
    ordered = sorted(
        entries,
        key=lambda item: (
            str(item.get("campaign_id")) if isinstance(item, dict) else "",
            int(item.get("ordinal", -1)) if isinstance(item, dict) else -1,
            str(item.get("seed_id")) if isinstance(item, dict) else "",
        ),
    )
    memory: dict[str, dict[str, str]] = {}
    for index, entry in enumerate(ordered):
        if not isinstance(entry, dict):
            raise ServiceError(f"continuous learning entry {index} is malformed")
        campaign_id = safe_leaf_id(
            entry.get("campaign_id"), f"continuous learning campaign {index}"
        )
        seed_id = safe_leaf_id(
            entry.get("seed_id"), f"continuous learning seed {index}"
        )
        registry = entry.get("registry")
        if not isinstance(registry, dict) or registry.get(
            "registry_id"
        ) != f"continuous:{campaign_id}:{seed_id}":
            raise ServiceError("continuous learning registry identity differs")
        idea = registry.get("idea")
        if not isinstance(idea, dict):
            raise ServiceError("continuous learning registry lacks its idea core")
        core = {
            "target_ref": idea.get("target_ref"),
            "model": idea.get("model"),
            "mechanism": idea.get("mechanism"),
            "first_test": registry.get("cheapest_probe"),
        }
        fingerprint = seed_fingerprint(core)
        memory.setdefault(
            fingerprint,
            {"campaign_id": campaign_id, "seed_id": seed_id},
        )
    return memory


def validate_dedup_transform(
    service_dir: Path,
    *,
    source_path: Path,
    admitted_batch: dict[str, Any],
    report_path: Path,
    requested_seed_count: int,
    learning_export: dict[str, Any],
) -> dict[str, Any]:
    """Replay the versioned source-to-batch transform from frozen memory."""
    source = read_json(source_path, "deduplication source batch")
    campaign.validate_seed_batch(source, authenticate=True)
    expected_batch, expected_report = deduplicate_provider_batch(
        service_dir,
        source,
        requested_seed_count,
        known_memory=frozen_generated_seed_memory(learning_export),
        source_receipt=file_receipt(source_path),
    )
    report = read_json(report_path, "deduplication report")
    if report != expected_report or admitted_batch != expected_batch:
        raise ServiceError(
            "admitted seed batch/dedup report is not the frozen v1 transform"
        )
    return report


def authenticate_receipt(value: Any, label: str) -> Path:
    path = validate_receipt_shape(value, label)
    claimed = value["sha256"]
    rel = value["path"]
    if not path.is_file():
        raise ServiceError(f"{label} is missing: {rel}")
    actual = sha256(path)
    if actual != claimed:
        raise ServiceError(f"{label} hash mismatch: {claimed} != {actual}")
    return path


def validate_receipt_shape(value: Any, label: str) -> Path:
    if not isinstance(value, dict) or set(value) != {"path", "sha256"}:
        raise ServiceError(f"{label} is not an exact file receipt")
    rel = value["path"]
    claimed = value["sha256"]
    if not isinstance(rel, str) or not rel or Path(rel).is_absolute() or ".." in Path(rel).parts:
        raise ServiceError(f"{label}.path must be repository-relative")
    if not isinstance(claimed, str) or len(claimed) != 64:
        raise ServiceError(f"{label}.sha256 is malformed")
    path = (ROOT / rel).resolve()
    try:
        path.relative_to(ROOT.resolve())
    except ValueError as exc:
        raise ServiceError(f"{label} resolves outside the repository") from exc
    return path


def canonical_json_sha256(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def validate_snapshot_build_receipt(
    snapshot_path: Path,
    *,
    service_dir: Path,
    campaign_id: str,
    purpose: str,
    mode: str = "current",
) -> tuple[Path, dict[str, Any]]:
    if mode not in {"current", "historical"}:
        raise ServiceError("snapshot validation mode must be current or historical")
    receipt_path = snapshot_path.parent / build_sol_idea_packet.SNAPSHOT_BUILD_RECEIPT_NAME
    receipt = read_json(receipt_path, "snapshot-build receipt")
    expected = {
        "schema_version",
        "protocol",
        "campaign_id",
        "purpose",
        "started_at",
        "finished_at",
        "terminal",
        "builder_component",
        "invocation",
        "input_state",
        "outputs",
        "output_aggregate_sha256",
        "meaning",
    }
    if set(receipt) != expected or receipt.get("schema_version") != 1:
        raise ServiceError("snapshot-build receipt has an unexpected closed contract")
    if (
        receipt.get("protocol") != build_sol_idea_packet.SNAPSHOT_BUILD_PROTOCOL
        or receipt.get("campaign_id") != campaign_id
        or receipt.get("purpose") != purpose
        or receipt.get("terminal") != "SNAPSHOT-BUILD-COMPLETE"
    ):
        raise ServiceError("snapshot-build receipt identity or terminal differs")
    if (
        parse_timestamp(receipt.get("started_at")) is None
        or parse_timestamp(receipt.get("finished_at")) is None
    ):
        raise ServiceError("snapshot-build timestamps are invalid")
    validate_receipt_shape(receipt.get("builder_component"), "snapshot builder component")
    if mode == "current":
        if receipt.get("builder_component") != file_receipt(
            Path(build_sol_idea_packet.__file__).resolve()
        ):
            raise ServiceError("snapshot-build receipt does not bind the current builder")
        authenticate_receipt(receipt["builder_component"], "snapshot builder component")
    invocation = receipt.get("invocation")
    if not isinstance(invocation, dict) or set(invocation) != {
        "service_dir",
        "output_dir",
        "max_inline_bytes",
        "excluded_campaign_id",
    }:
        raise ServiceError("snapshot-build invocation is malformed")
    if invocation.get("service_dir") != repo_relative(service_dir):
        raise ServiceError("snapshot-build receipt names another service")
    if invocation.get("excluded_campaign_id") != campaign_id:
        raise ServiceError("snapshot-build exclusion differs from its campaign")
    if invocation.get("output_dir") != repo_relative(snapshot_path.parent):
        raise ServiceError("snapshot-build receipt names another output directory")
    if (
        not isinstance(invocation.get("max_inline_bytes"), int)
        or isinstance(invocation.get("max_inline_bytes"), bool)
        or int(invocation["max_inline_bytes"]) < 1
    ):
        raise ServiceError("snapshot-build inline-byte ceiling is invalid")
    outputs = receipt.get("outputs")
    output_keys = {
        "manifest_json",
        "context_md",
        "lean_declarations_md",
        "prior_idea_registry_json",
        "prior_idea_registry_md",
        "learning_state_manifest_json",
        "packet_summary_json",
    }
    if not isinstance(outputs, dict) or set(outputs) != output_keys:
        raise ServiceError("snapshot-build outputs have an unexpected contract")
    expected_names = {
        "manifest_json": "manifest.json",
        "context_md": "context.md",
        "lean_declarations_md": "lean-declarations.md",
        "prior_idea_registry_json": "prior-idea-registry.json",
        "prior_idea_registry_md": "prior-idea-registry.md",
        "learning_state_manifest_json": "learning-state-manifest.json",
        "packet_summary_json": "packet-summary.json",
    }
    for key in sorted(output_keys):
        expected_path = snapshot_path.parent / expected_names[key]
        if outputs[key] != file_receipt(expected_path):
            raise ServiceError(f"snapshot output {key} names another artifact")
        authenticate_receipt(outputs[key], f"snapshot output {key}")
    if outputs["packet_summary_json"] != file_receipt(snapshot_path):
        raise ServiceError("snapshot-build receipt does not authenticate its summary")
    expected_aggregate = canonical_json_sha256(outputs)
    if receipt.get("output_aggregate_sha256") != expected_aggregate:
        raise ServiceError("snapshot-build output aggregate differs")
    input_state = receipt.get("input_state")
    if not isinstance(input_state, dict) or set(input_state) != {
        "validated_learning_export",
        "validated_learning_export_core_sha256",
        "current_input_fingerprint_sha256",
        "learning_state_manifest",
        "learning_epoch_sha256",
        "workspace_manifest_aggregate_sha256",
    }:
        raise ServiceError("snapshot-build input state is malformed")
    export_path = authenticate_receipt(
        input_state.get("validated_learning_export"),
        "snapshot validated learning export",
    )
    export = build_sol_idea_packet.load_validated_learning_export(
        export_path, authenticate_inputs=False
    )
    if (
        export.get("service_dir") != repo_relative(service_dir)
        or export.get("excluded_campaign_id") != campaign_id
        or export.get("export_core_sha256")
        != input_state.get("validated_learning_export_core_sha256")
        or export.get("current_input_fingerprint_sha256")
        != input_state.get("current_input_fingerprint_sha256")
        or export.get("learning_epoch_sha256")
        != input_state.get("learning_epoch_sha256")
    ):
        raise ServiceError("snapshot validated learning export differs")
    if input_state.get("learning_state_manifest") != outputs[
        "learning_state_manifest_json"
    ]:
        raise ServiceError("snapshot learning-state manifest receipt differs")
    learning_path = authenticate_receipt(
        input_state["learning_state_manifest"], "snapshot learning-state manifest"
    )
    learning = read_json(learning_path, "snapshot learning-state manifest")
    if set(learning) != {"schema_version", "purpose", "entries"} or learning.get(
        "schema_version"
    ) != 1:
        raise ServiceError("snapshot learning-state manifest is malformed")
    entries = learning.get("entries")
    if not isinstance(entries, list):
        raise ServiceError("snapshot learning-state entries are missing")
    if entries != sorted(
        entries,
        key=lambda item: (
            str(item.get("kind")) if isinstance(item, dict) else "",
            str((item.get("receipt") or {}).get("path"))
            if isinstance(item, dict)
            else "",
        ),
    ):
        raise ServiceError("snapshot learning-state entries are not sorted")
    identities: set[tuple[str, str]] = set()
    for index, item in enumerate(entries):
        if not isinstance(item, dict) or set(item) != {"kind", "receipt"}:
            raise ServiceError(f"snapshot learning-state entry {index} is malformed")
        if item.get("kind") not in {
            "claim",
            "feedback",
            "canonical_failure_memory",
        }:
            raise ServiceError(f"snapshot learning-state entry {index} kind is invalid")
        artifact = (
            authenticate_receipt(
                item.get("receipt"), f"snapshot learning-state entry {index}"
            )
            if mode == "current"
            else validate_receipt_shape(
                item.get("receipt"), f"snapshot learning-state entry {index}"
            )
        )
        identity = (str(item["kind"]), repo_relative(artifact))
        if identity in identities:
            raise ServiceError("snapshot learning-state entries are not unique")
        identities.add(identity)
    learning_epoch = canonical_json_sha256(entries)
    if input_state.get("learning_epoch_sha256") != learning_epoch:
        raise ServiceError("snapshot learning epoch does not match its manifest")
    summary = read_json(snapshot_path, "snapshot summary")
    if (
        summary.get("feedback_epoch_sha256") != learning_epoch
        or summary.get("manifest_aggregate_sha256")
        != input_state.get("workspace_manifest_aggregate_sha256")
    ):
        raise ServiceError("snapshot summary differs from its build receipt")
    if mode == "current":
        # A builder hash copied into a hand-written receipt is not provenance.
        # Rebuild the deterministic outputs in an ignored quarantine and compare
        # every byte before accepting the snapshot.  Historical validation uses
        # the immutable admission receipt written after this replay instead of
        # consulting later mutable learning state.
        replay_names = tuple(expected_names.values())
        with tempfile.TemporaryDirectory(
            prefix=".snapshot-provenance-replay-", dir=RUNS_ROOT
        ) as replay_text:
            replay_dir = Path(replay_text).resolve()
            replay_export_path = replay_dir / "validated-learning-export.json"
            try:
                authorization_path, authorization, accounting = (
                    current_authorized_accounting(service_dir)
                )
                materialize_validated_learning_export(
                    service_dir,
                    replay_export_path,
                    authorization_path=authorization_path,
                    authorization=authorization,
                    accounting=accounting,
                    excluded_campaign_id=campaign_id,
                )
                if replay_export_path.read_bytes() != export_path.read_bytes():
                    raise ServiceError(
                        "validated learning export was not reproduced from current state"
                    )
                build_sol_idea_packet.build_packet(
                    replay_dir,
                    int(invocation["max_inline_bytes"]),
                    service_dir,
                    campaign_id=campaign_id,
                    purpose=purpose,
                    validated_learning_export=export_path,
                )
            except (OSError, ValueError, json.JSONDecodeError) as exc:
                raise ServiceError(
                    f"independent snapshot provenance replay failed: {exc}"
                ) from exc
            for name in replay_names:
                if (replay_dir / name).read_bytes() != (
                    snapshot_path.parent / name
                ).read_bytes():
                    raise ServiceError(
                        f"snapshot output was not reproduced by the current builder: {name}"
                    )
    return receipt_path, receipt


def snapshot_admission_path(snapshot_path: Path) -> Path:
    resolved_snapshot = snapshot_path.resolve()
    try:
        resolved_snapshot.relative_to(RUNS_ROOT)
    except ValueError as exc:
        raise ServiceError("snapshot admission source must be under runs/agents") from exc
    admission_path = (snapshot_path.parent.parent / SNAPSHOT_ADMISSION_NAME).resolve()
    try:
        admission_path.relative_to(RUNS_ROOT)
    except ValueError as exc:
        raise ServiceError("derived snapshot admission escapes runs/agents") from exc
    return admission_path


def validate_snapshot_admission(
    admission_path: Path,
    *,
    snapshot_path: Path,
    service_dir: Path,
    campaign_id: str,
    purpose: str,
) -> dict[str, Any]:
    value = read_json(admission_path, "snapshot admission")
    expected = {
        "schema_version",
        "protocol",
        "campaign_id",
        "purpose",
        "admitted_at",
        "service_dir",
        "snapshot",
        "snapshot_build",
        "validator_component",
        "builder_component",
        "validated_learning_export",
        "validated_learning_export_core_sha256",
        "current_input_fingerprint_sha256",
        "learning_state_manifest",
        "learning_epoch_sha256",
        "workspace_manifest_aggregate_sha256",
        "snapshot_output_aggregate_sha256",
        "checks",
        "meaning",
    }
    if set(value) != expected or value.get("schema_version") != 1:
        raise ServiceError("snapshot admission has an unexpected closed contract")
    receipt_path, receipt = validate_snapshot_build_receipt(
        snapshot_path,
        service_dir=service_dir,
        campaign_id=campaign_id,
        purpose=purpose,
        mode="historical",
    )
    input_state = receipt["input_state"]
    if (
        value.get("protocol") != SNAPSHOT_ADMISSION_PROTOCOL
        or value.get("campaign_id") != campaign_id
        or value.get("purpose") != purpose
        or parse_timestamp(value.get("admitted_at")) is None
        or value.get("service_dir") != repo_relative(service_dir)
        or value.get("snapshot") != file_receipt(snapshot_path)
        or value.get("snapshot_build") != file_receipt(receipt_path)
        or value.get("builder_component") != receipt.get("builder_component")
        or value.get("validated_learning_export")
        != input_state.get("validated_learning_export")
        or value.get("validated_learning_export_core_sha256")
        != input_state.get("validated_learning_export_core_sha256")
        or value.get("current_input_fingerprint_sha256")
        != input_state.get("current_input_fingerprint_sha256")
        or value.get("learning_state_manifest")
        != input_state.get("learning_state_manifest")
        or value.get("learning_epoch_sha256")
        != input_state.get("learning_epoch_sha256")
        or value.get("workspace_manifest_aggregate_sha256")
        != input_state.get("workspace_manifest_aggregate_sha256")
        or value.get("snapshot_output_aggregate_sha256")
        != receipt.get("output_aggregate_sha256")
        or value.get("checks")
        != {
            "frozen_contract": "pass",
            "live_input_authentication": "pass",
            "cold_reproduction": "pass",
            "post_replay_state": "pass",
        }
        or value.get("meaning")
        != (
            "cold-reproduced against authenticated live inputs exactly once at "
            "admission; later use requires the declared temporal validation mode"
        )
    ):
        raise ServiceError("snapshot admission identity or evidence differs")
    validator_path = validate_receipt_shape(
        value.get("validator_component"), "snapshot admission validator"
    )
    if repo_relative(validator_path) != repo_relative(Path(__file__).resolve()):
        raise ServiceError("snapshot admission names another validator component")
    validate_receipt_shape(
        value.get("builder_component"), "snapshot admission builder"
    )
    return value


def admit_snapshot_build(
    snapshot_path: Path,
    *,
    service_dir: Path,
    campaign_id: str,
    purpose: str,
) -> Path:
    admission_path = snapshot_admission_path(snapshot_path)
    if admission_path.is_file():
        existing = validate_snapshot_admission(
            admission_path,
            snapshot_path=snapshot_path,
            service_dir=service_dir,
            campaign_id=campaign_id,
            purpose=purpose,
        )
        if (
            existing.get("validator_component")
            != file_receipt(Path(__file__).resolve())
            or existing.get("builder_component")
            != file_receipt(Path(build_sol_idea_packet.__file__).resolve())
        ):
            raise ServiceError("existing snapshot admission is not current")
        current, reasons = snapshot_currency(
            existing,
            service_dir=service_dir,
            campaign_id=campaign_id,
        )
        if not current:
            raise ServiceError(
                "existing snapshot admission is stale: " + ",".join(reasons)
            )
        return admission_path
    receipt_path, receipt = validate_snapshot_build_receipt(
        snapshot_path,
        service_dir=service_dir,
        campaign_id=campaign_id,
        purpose=purpose,
        mode="current",
    )
    input_state = receipt["input_state"]
    value = {
        "schema_version": 1,
        "protocol": SNAPSHOT_ADMISSION_PROTOCOL,
        "campaign_id": campaign_id,
        "purpose": purpose,
        "admitted_at": now(),
        "service_dir": repo_relative(service_dir),
        "snapshot": file_receipt(snapshot_path),
        "snapshot_build": file_receipt(receipt_path),
        "validator_component": file_receipt(Path(__file__).resolve()),
        "builder_component": receipt["builder_component"],
        "validated_learning_export": input_state["validated_learning_export"],
        "validated_learning_export_core_sha256": input_state[
            "validated_learning_export_core_sha256"
        ],
        "current_input_fingerprint_sha256": input_state[
            "current_input_fingerprint_sha256"
        ],
        "learning_state_manifest": input_state["learning_state_manifest"],
        "learning_epoch_sha256": input_state["learning_epoch_sha256"],
        "workspace_manifest_aggregate_sha256": input_state[
            "workspace_manifest_aggregate_sha256"
        ],
        "snapshot_output_aggregate_sha256": receipt["output_aggregate_sha256"],
        "checks": {
            "frozen_contract": "pass",
            "live_input_authentication": "pass",
            "cold_reproduction": "pass",
            "post_replay_state": "pass",
        },
        "meaning": (
            "cold-reproduced against authenticated live inputs exactly once at "
            "admission; later use requires the declared temporal validation mode"
        ),
    }
    current, reasons = snapshot_currency(
        value,
        service_dir=service_dir,
        campaign_id=campaign_id,
    )
    if not current:
        raise ServiceError(
            "snapshot state changed after cold replay: " + ",".join(reasons)
        )
    write_once(admission_path, value)
    admission = validate_snapshot_admission(
        admission_path,
        snapshot_path=snapshot_path,
        service_dir=service_dir,
        campaign_id=campaign_id,
        purpose=purpose,
    )
    return admission_path


def snapshot_currency(
    admission: dict[str, Any], *, service_dir: Path, campaign_id: str
) -> tuple[bool, list[str]]:
    reasons: list[str] = []
    export_path = authenticate_receipt(
        admission.get("validated_learning_export"),
        "currency validated learning export",
    )
    frozen_export = build_sol_idea_packet.load_validated_learning_export(
        export_path, authenticate_inputs=False
    )
    with tempfile.TemporaryDirectory(
        prefix=".learning-currency-", dir=RUNS_ROOT
    ) as current_text:
        current_export_path = Path(current_text) / "validated-learning-export.json"
        authorization_path, authorization, accounting = current_authorized_accounting(
            service_dir
        )
        current_export = materialize_validated_learning_export(
            service_dir,
            current_export_path,
            authorization_path=authorization_path,
            authorization=authorization,
            accounting=accounting,
            excluded_campaign_id=campaign_id,
        )
    if current_export.get("learning_epoch_sha256") != admission.get(
        "learning_epoch_sha256"
    ):
        reasons.append("learning_epoch_changed")
    if current_export.get("current_input_fingerprint_sha256") != admission.get(
        "current_input_fingerprint_sha256"
    ):
        reasons.append("learning_input_changed")
    if current_export.get("export_core_sha256") != frozen_export.get(
        "export_core_sha256"
    ):
        reasons.append("validated_learning_export_changed")
    snapshot_path = authenticate_receipt(admission.get("snapshot"), "currency snapshot")
    if not reasons:
        current_manifest = build_sol_idea_packet.current_manifest_aggregate_sha256(
            snapshot_path.parent,
            service_dir,
            excluded_campaign_id=campaign_id,
            validated_learning_export=export_path,
        )
        if current_manifest != admission.get("workspace_manifest_aggregate_sha256"):
            reasons.append("workspace_manifest_changed")
    if admission.get("validator_component") != file_receipt(
        Path(__file__).resolve()
    ):
        reasons.append("validator_component_changed")
    if admission.get("builder_component") != file_receipt(
        Path(build_sol_idea_packet.__file__).resolve()
    ):
        reasons.append("builder_component_changed")
    return not reasons, reasons


def ready_exposure_currency(
    admission: dict[str, Any], *, service_dir: Path, campaign_id: str
) -> tuple[bool, list[str]]:
    """Check ready exposure without treating later ready proposals as learning."""
    _strict_current, strict_reasons = snapshot_currency(
        admission, service_dir=service_dir, campaign_id=campaign_id
    )
    blocking = {
        reason
        for reason in strict_reasons
        if reason
        in {
            "learning_epoch_changed",
            "workspace_manifest_changed",
            "validator_component_changed",
            "builder_component_changed",
        }
    }
    export_path = authenticate_receipt(
        admission.get("validated_learning_export"),
        "ready-exposure validated learning export",
    )
    frozen_export = build_sol_idea_packet.load_validated_learning_export(
        export_path, authenticate_inputs=False
    )
    authorization_path, _authorization = active_standing_authorization(service_dir)
    if frozen_export.get("standing_authorization") != file_receipt(
        authorization_path
    ):
        blocking.add("standing_authorization_changed")
    snapshot_path = authenticate_receipt(
        admission.get("snapshot"), "ready-exposure snapshot"
    )
    current_manifest = build_sol_idea_packet.current_manifest_aggregate_sha256(
        snapshot_path.parent,
        service_dir,
        excluded_campaign_id=campaign_id,
        validated_learning_export=export_path,
    )
    if current_manifest != admission.get("workspace_manifest_aggregate_sha256"):
        blocking.add("workspace_manifest_changed")
    reasons = sorted(blocking)
    return not reasons, reasons


def validate_root_semantic_screen(
    screen_path: Path,
    *,
    source_seed_path: Path,
    batch: dict[str, Any],
    service_dir: Path,
    authorization_path: Path,
    snapshot_path: Path,
    snapshot_build_path: Path,
    prior_registry_path: Path,
    feedback_epoch_sha256: str,
    approval_ref: str,
) -> dict[str, Any]:
    screen = read_json(screen_path, "root semantic screen")
    expected = {
        "schema_version",
        "protocol",
        "screen_id",
        "screened_at",
        "reviewer",
        "authority",
        "campaign_id",
        "approval_ref",
        "standing_authorization",
        "seed_batch",
        "snapshot",
        "snapshot_build",
        "prior_idea_registry",
        "feedback_epoch_sha256",
        "seed_reviews",
        "overall_decision",
        "claim_level",
    }
    if set(screen) != expected or screen.get("schema_version") != 1:
        raise ServiceError("root semantic screen has an unexpected closed contract")
    if (
        screen.get("protocol") != "research-root-semantic-screen-v1"
        or screen.get("reviewer") != "root"
        or screen.get("authority") != "proposal_queue_screen_only"
        or screen.get("campaign_id") != batch.get("campaign_id")
        or screen.get("approval_ref") != approval_ref
        or screen.get("standing_authorization") != file_receipt(authorization_path)
        or screen.get("seed_batch") != file_receipt(source_seed_path)
        or screen.get("snapshot") != file_receipt(snapshot_path)
        or screen.get("snapshot_build") != file_receipt(snapshot_build_path)
        or screen.get("prior_idea_registry") != file_receipt(prior_registry_path)
        or screen.get("feedback_epoch_sha256") != feedback_epoch_sha256
        or screen.get("overall_decision") != "pass"
        or screen.get("claim_level") != "proposal"
    ):
        raise ServiceError("root semantic screen is not bound to this proposal batch")
    for key in ("screen_id", "screened_at"):
        if not isinstance(screen.get(key), str) or not screen[key].strip():
            raise ServiceError(f"root semantic screen {key} is missing")
    reviews = screen.get("seed_reviews")
    seeds = batch.get("seeds") or []
    if not isinstance(reviews, list) or len(reviews) != len(seeds):
        raise ServiceError("root semantic screen does not review every seed exactly once")
    by_id: dict[str, dict[str, Any]] = {}
    for seed in seeds:
        if isinstance(seed, dict) and isinstance(seed.get("seed_id"), str):
            by_id[seed["seed_id"]] = seed
    if len(by_id) != len(seeds):
        raise ServiceError("root semantic screen seed identities are not unique")
    seen: set[str] = set()
    judgment_keys = {
        "semantic_duplicate_absent",
        "target_equivalence_screened",
        "model_tier_and_return_status_explicit",
        "failure_memory_respected",
        "novelty_or_source_status_reviewed",
        "family_correlation_reviewed",
        "no_padding",
    }
    for index, review in enumerate(reviews):
        review_keys = {
            "seed_id",
            "seed_sha256",
            "working_model_tier",
            "machine_checks",
            "root_judgment_checks",
            "decision",
            "rationale",
        }
        if not isinstance(review, dict) or set(review) != review_keys:
            raise ServiceError(f"root semantic seed review {index} is malformed")
        seed_id = review.get("seed_id")
        if seed_id not in by_id or seed_id in seen:
            raise ServiceError("root semantic seed reviews omit, duplicate, or add a seed")
        seen.add(str(seed_id))
        seed = by_id[str(seed_id)]
        if review.get("seed_sha256") != canonical_json_sha256(seed):
            raise ServiceError("root semantic seed hash differs from the source batch")
        if review.get("working_model_tier") != (seed.get("model") or {}).get(
            "working_tier"
        ):
            raise ServiceError("root semantic screen changes a seed model tier")
        machine = review.get("machine_checks")
        machine_keys = {
            "schema_valid",
            "identity_bound",
            "snapshot_bound",
            "proposal_only",
            "literal_duplicate_absent",
            "first_test_within_30_minutes",
        }
        if not isinstance(machine, dict) or set(machine) != machine_keys or any(
            machine.get(key) != "pass" for key in machine_keys
        ):
            raise ServiceError("root semantic machine checks are incomplete")
        if int((seed.get("first_test") or {}).get("ceiling_minutes") or 0) not in range(
            1, 31
        ):
            raise ServiceError("root semantic screen admits an unbounded first test")
        judgments = review.get("root_judgment_checks")
        if not isinstance(judgments, dict) or set(judgments) != judgment_keys:
            raise ServiceError("root semantic judgment checks are incomplete")
        for name, judgment in judgments.items():
            if not isinstance(judgment, dict) or set(judgment) != {
                "status",
                "rationale",
                "record_refs",
            }:
                raise ServiceError(f"root semantic judgment {name} is malformed")
            if judgment.get("status") != "pass" or not isinstance(
                judgment.get("rationale"), str
            ) or not judgment["rationale"].strip():
                raise ServiceError(f"root semantic judgment {name} did not pass")
            refs = judgment.get("record_refs")
            if not isinstance(refs, list):
                raise ServiceError(f"root semantic judgment {name} refs are malformed")
            for ref_index, ref in enumerate(refs):
                authenticate_receipt(
                    ref, f"root semantic judgment {name} ref {ref_index}"
                )
        if review.get("decision") != "pass" or not isinstance(
            review.get("rationale"), str
        ) or not review["rationale"].strip():
            raise ServiceError("root semantic seed review did not pass")
    return screen


def current_revision() -> str:
    command = ["git"]
    if (ROOT / ".git-data").exists():
        command.append("--git-dir=.git-data")
    command.extend(["rev-parse", "HEAD"])
    result = subprocess.run(
        command, cwd=ROOT, check=True, text=True, capture_output=True
    )
    return result.stdout.strip()


def codex_version(executable: str = "codex") -> str:
    result = subprocess.run(
        [executable, "--version"], cwd=ROOT, check=True, text=True, capture_output=True
    )
    return result.stdout.strip()


def strip_provider_schema(value: Any, *, preserve_names: bool = False) -> Any:
    if isinstance(value, dict):
        stripped: dict[str, Any] = {}
        for key, item in value.items():
            if not preserve_names and key in STRIPPED_SCHEMA_KEYS:
                continue
            stripped[key] = strip_provider_schema(
                item, preserve_names=key in {"properties", "$defs"}
            )
        return stripped
    if isinstance(value, list):
        return [strip_provider_schema(item) for item in value]
    return value


def complete_provider_schema_types(value: Any) -> Any:
    if isinstance(value, dict):
        completed = {
            key: complete_provider_schema_types(item) for key, item in value.items()
        }
        if "type" not in completed:
            candidates: list[Any] | None = None
            if "const" in completed:
                candidates = [completed["const"]]
            elif isinstance(completed.get("enum"), list) and completed["enum"]:
                candidates = completed["enum"]
            if candidates is not None:
                inferred = {json_type(item) for item in candidates}
                if len(inferred) == 1:
                    completed["type"] = inferred.pop()
        return completed
    if isinstance(value, list):
        return [complete_provider_schema_types(item) for item in value]
    return value


def json_type(value: Any) -> str:
    if value is None:
        return "null"
    if isinstance(value, bool):
        return "boolean"
    if isinstance(value, int):
        return "integer"
    if isinstance(value, float):
        return "number"
    if isinstance(value, str):
        return "string"
    if isinstance(value, list):
        return "array"
    if isinstance(value, dict):
        return "object"
    raise ServiceError(f"cannot infer JSON Schema type for {value!r}")


def provider_schema(
    campaign_id: str,
    generation_mode: str,
    snapshot_receipt: dict[str, str],
    requested_seed_count: int = 5,
) -> dict[str, Any]:
    schema = strip_provider_schema(
        copy.deepcopy(
            json.loads(campaign.SEED_SCHEMA.read_text(encoding="utf-8"))
        )
    )
    properties = schema["properties"]
    properties["campaign_id"] = {"type": "string", "const": campaign_id}
    properties["generation_mode"] = {
        "type": "string",
        "const": generation_mode,
    }
    required = schema.get("required")
    if not isinstance(required, list):
        raise ServiceError("provider seed schema has no required-field list")
    if "requested_seed_count" not in required:
        required.append("requested_seed_count")
    properties["requested_seed_count"] = {
        "type": "integer",
        "const": requested_seed_count,
    }
    properties["snapshot"] = {
        "type": "object",
        "additionalProperties": False,
        "required": ["path", "sha256"],
        "properties": {
            "path": {"type": "string", "const": snapshot_receipt["path"]},
            "sha256": {"type": "string", "const": snapshot_receipt["sha256"]},
        },
    }
    properties["terminal"] = {
        "type": "string",
        "enum": ["SEED-BATCH-COMPLETE", "SEED-BATCH-NOVELTY-STOP"],
    }
    return complete_provider_schema_types(schema)


def make_prompt(
    campaign_id: str,
    generation_mode: str,
    snapshot_receipt: dict[str, str],
    batch_dir: Path,
    requested_seed_count: int = 5,
) -> str:
    snapshot_dir = batch_dir / "snapshot"
    return f"""# Immutable continuous seed-generation packet

Campaign: `{campaign_id}`
Generation mode: `{generation_mode}`
Snapshot receipt: `{snapshot_receipt['path']}` / `{snapshot_receipt['sha256']}`
Frozen seed request: `{requested_seed_count}`

You are the read-only Research Question Generator for the exact Erdős--Szekeres
happy-ending project. Authenticate every named receipt before interpreting it.
Read `AGENTS.md`, `docs/agents/research-campaign.md`, and
`docs/agents/profiles/research-question-generator.md`. The complete reconciled
coordinator snapshot is under `{repo_relative(snapshot_dir)}`. In particular,
inspect `packet-summary.json`, `context.md`, `lean-declarations.md`, and the full
`prior-idea-registry.json`; use the repository paths committed by `manifest.json`
when the inline context is insufficient.

The prior registry includes every earlier validated continuous-generator seed,
including ready and in-flight items, plus every hash-bound root-admitted
per-seed feedback receipt available when this snapshot was frozen. Never
regenerate ready or in-flight identities. Use fields tagged `verified` as
duplicate/mutation constraints at exactly their admitted scope. Treat fields
tagged `inferred` only as question-generating residue, never as positive
evidence. A mutation must cite its parent and change the mathematical operation
or retained information; renaming, larger instances, more seeds, or more solver
time is not a mutation. Registry presence alone is never endorsement, route
admission, proof movement, or permission to widen a negative result.

Generate up to {requested_seed_count} compact, materially different mathematical questions or
experiments. Be creative: test novel encodings, algebraic/topological/dual or
higher-dimensional viewpoints, counterexample structure, source-backed
machinery transfers, failure-duals, and recombinations where they genuinely
change the mathematical information. You may use live web research as needed,
but prefer primary papers, official repositories, arXiv records, DOI pages, and
publisher pages. A source analogy is not a transfer theorem.

Apply only the seed safety screen. Deduplicate against the entire frozen prior
registry and admitted failure memory, including target-equivalent restatements.
Every seed must name the working and target model tiers, the information at
risk, its concrete objects and new operation, the nearest negative controls,
and one discriminating test executable within thirty minutes. Live, kill, and
no-signal branches must say different things. Mutations cite exactly one
parent; recombinations cite exactly two; de novo seeds cite none. Keep every
canonical seed below 4096 bytes.

The deterministic campaign validator enforces cross-field rules that the
provider JSON schema cannot express. Before returning, audit every seed as
follows: if `transfer_status` is `same_tier`, copy the exact same tier string
into both `working_tier` and `target_tier` and set `bridge_ref` to null. If the
tier strings differ, use `conjectural` unless an exact authenticated bridge is
already named; `verified_bridge` always requires a non-null `bridge_ref`.
Never use logically similar but textually different tier descriptions with
`same_tier`.

Return exactly one JSON object conforming to the supplied output schema. Use
`SEED-BATCH-COMPLETE` only with exactly the frozen requested count of
{requested_seed_count} honest seeds. If fewer survive, return
`SEED-BATCH-NOVELTY-STOP`; never pad. Copy `requested_seed_count` exactly as
{requested_seed_count}. Set unknown tool, token,
source-request, and provider-cost metrics to null. All claims remain
`proposal`. Do not edit files, run solvers, attempt the first tests, promote a
route, schedule work, spawn subagents, or claim proof movement.
"""


def provider_argv(packet: dict[str, Any], batch_dir: Path) -> list[str]:
    provider = packet["provider"]
    return [
        provider.get("executable", "codex"),
        "exec",
        "--model",
        provider["model"],
        "--config",
        f'model_reasoning_effort="{provider["reasoning_effort"]}"',
        "--config",
        'web_search="live"',
        "--config",
        'approval_policy="never"',
        "--config",
        "agents.enabled=false",
        "--sandbox",
        "read-only",
        "--ephemeral",
        "--skip-git-repo-check",
        "--output-schema",
        str((batch_dir / "output-schema.json").resolve()),
        "--output-last-message",
        str((batch_dir / "raw-response.json").resolve()),
        "--json",
        "-",
    ]


def make_task(
    service_dir: Path,
    batch_dir: Path,
    campaign_id: str,
    snapshot_summary: dict[str, Any],
    inputs: list[Path],
    wall_minutes: int,
    requested_seed_count: int = 5,
) -> dict[str, Any]:
    output_names = [
        "events.jsonl",
        "provider.log",
        "raw-response.json",
        "dedup-report.json",
        "seed-batch.json",
        "result-receipt.json",
        "status.json",
    ]
    return {
        "schema_version": 1,
        "run_id": service_dir.name,
        "task_id": campaign_id,
        "wayfinder_ticket": WAYFINDER_TICKET,
        "profile": "research_question_generator",
        "base_revision": current_revision(),
        "workspace_fingerprint": snapshot_summary["manifest_aggregate_sha256"],
        "objective": (
            f"Generate one evidence-first inbox batch of up to {requested_seed_count} compact, "
            "materially distinct proposal-level mathematical seeds from this "
            "cycle's frozen project snapshot under the standing bounded "
            "continuous-generation authorization."
        ),
        "theorem_contract": None,
        "inputs": [file_receipt(path) for path in inputs],
        "ownership": {
            "read_paths": [repo_relative(path) for path in inputs],
            "write_paths": [
                repo_relative(batch_dir / output_name) for output_name in output_names
            ],
        },
        "budget": {
            "wall_minutes": wall_minutes,
            "cpu_cores": 2,
            "memory_gib": 4,
            "output_gib": 0.05,
        },
        "required_checks": [
            "Authenticate the task, prompt, schema, and coordinator snapshot receipts before analysis.",
            "Use only read-only repository inspection and live primary-source web research.",
            "Deduplicate against the full prior registry and admitted failure memory without padding.",
            "Accept deterministic post-provider removal only for literal semantic-core repeats; target equivalence remains root-only review.",
            "Return one object accepted by scripts/check_research_campaign.py --seed-batch.",
            f"Bind requested_seed_count to exactly {requested_seed_count} and never exceed it.",
        ],
        "success": [
            f"SEED-BATCH-COMPLETE: exactly {requested_seed_count} honest seeds validate.",
            f"SEED-BATCH-NOVELTY-STOP: fewer than {requested_seed_count} honest seeds validate without padding.",
            "SEED-BATCH-PROVIDER-STOP: the bounded provider call fails or times out.",
            "SEED-BATCH-PACKET-MISMATCH: an immutable input fails authentication.",
        ],
        "stop": [
            "Stop after one provider invocation, ninety minutes, 4 GiB local process-tree RSS, or 0.05 GiB output, whichever comes first.",
            "Do not edit project or Wayfinder files, run mathematical probes, spawn subagents, mutate git, admit routes, or schedule work.",
            "Do not retry this attempted packet. A later automatically frozen packet is separately identified and remains bounded by the standing authorization.",
        ],
        "deliverables": [
            repo_relative(batch_dir / "seed-batch.json"),
            repo_relative(batch_dir / "result-receipt.json"),
        ],
        "claims_allowed": ["proposal"],
    }


def accounting_baseline_directory(service_dir: Path) -> Path:
    return service_state_path(service_dir, ACCOUNTING_BASELINE_DIRECTORY)


def accounting_head_path(service_dir: Path) -> Path:
    return service_state_path(service_dir, ACCOUNTING_HEAD_NAME)


def accounting_event_directory(service_dir: Path) -> Path:
    return service_state_path(service_dir, ACCOUNTING_EVENT_DIRECTORY)


def validate_accounting_migration_root(
    service_dir: Path,
) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, Any]]]:
    if service_dir.resolve() != (ROOT / DEFAULT_SERVICE_DIR).resolve():
        raise ServiceError(
            "v3 standing authority is bound to the canonical continuous-generator service"
        )
    if not MIGRATION_ROOT.is_file() or sha256(MIGRATION_ROOT) != EXPECTED_MIGRATION_ROOT_SHA256:
        raise ServiceError("the implementation-bound accounting migration root drifted")
    root = read_json(MIGRATION_ROOT, "accounting migration root")
    expected_keys = {
        "schema_version",
        "protocol",
        "service_dir",
        "migration_ref",
        "lifetime_ceiling",
        "charged_protocols",
        "excluded_protocols",
        "entry_fields",
        "path_templates",
        "totals",
        "entries",
        "meaning",
    }
    entry_fields = [
        "campaign_id",
        "protocol",
        "disposition",
        "provider_invocation_ordinal",
        "terminal",
        "seed_count",
        "queue_sha256",
        "packet_sha256",
        "attempt_sha256",
        "provider_start_sha256",
        "result_sha256",
        "seed_batch_sha256",
    ]
    templates = {
        "queue": "runs/agents/continuous-idea-generator/queue/{campaign_id}.json",
        "packet": "runs/agents/continuous-idea-generator/batches/{campaign_id}/packet.json",
        "attempt": "runs/agents/continuous-idea-generator/batches/{campaign_id}/attempt.json",
        "provider_start": "runs/agents/continuous-idea-generator/batches/{campaign_id}/provider-start.json",
        "result": "runs/agents/continuous-idea-generator/batches/{campaign_id}/result-receipt.json",
        "seed_batch": "runs/agents/continuous-idea-generator/batches/{campaign_id}/seed-batch.json",
    }
    if set(root) != expected_keys or root.get("schema_version") != 1:
        raise ServiceError("accounting migration root has an unexpected contract")
    if (
        root.get("protocol") != "continuous-idea-generator-accounting-migration-v1"
        or root.get("service_dir") != repo_relative(service_dir)
        or root.get("migration_ref") != WAYFINDER_TICKET
        or root.get("lifetime_ceiling") != 100
        or root.get("charged_protocols")
        != ["continuous-idea-generator-v2", "continuous-idea-generator-v2.1"]
        or root.get("excluded_protocols") != ["continuous-idea-generator-v1"]
        or root.get("entry_fields") != entry_fields
        or root.get("path_templates") != templates
        or root.get("totals") != {"charged": 30, "excluded": 6, "all": 36}
        or root.get("meaning")
        != "fixed cross-version lifetime root; exactly 30 charged calls and six explicitly excluded v1 calls"
    ):
        raise ServiceError("accounting migration root identity or fixed totals differ")
    entries = root.get("entries")
    if not isinstance(entries, list) or len(entries) != 36:
        raise ServiceError("accounting migration root does not contain 36 entries")
    charged_records: list[dict[str, Any]] = []
    excluded_records: list[dict[str, Any]] = []
    identities: list[str] = []
    artifact_names = (
        "queue",
        "packet",
        "attempt",
        "provider_start",
        "result",
        "seed_batch",
    )
    for index, raw in enumerate(entries):
        if not isinstance(raw, list) or len(raw) != len(entry_fields):
            raise ServiceError(f"accounting migration entry {index} is malformed")
        entry = dict(zip(entry_fields, raw, strict=True))
        campaign_id = safe_leaf_id(
            entry.get("campaign_id"), "migration campaign_id"
        )
        identities.append(campaign_id)
        protocol = entry.get("protocol")
        disposition = entry.get("disposition")
        if (
            protocol == "continuous-idea-generator-v1"
            and disposition == "excluded_v1"
        ):
            target = excluded_records
        elif (
            protocol
            in {"continuous-idea-generator-v2", "continuous-idea-generator-v2.1"}
            and disposition == "charged"
        ):
            target = charged_records
        else:
            raise ServiceError("accounting migration protocol/disposition differs")
        if (
            entry.get("provider_invocation_ordinal") != 1
            or entry.get("terminal") not in PROVIDER_RESULT_TERMINALS
            or not isinstance(entry.get("seed_count"), int)
            or isinstance(entry.get("seed_count"), bool)
            or int(entry["seed_count"]) < 0
        ):
            raise ServiceError("accounting migration terminal metadata differs")
        paths: dict[str, Path] = {}
        receipts: dict[str, dict[str, str]] = {}
        for artifact_name in artifact_names:
            claimed = entry.get(f"{artifact_name}_sha256")
            if not isinstance(claimed, str) or len(claimed) != 64:
                raise ServiceError("accounting migration artifact hash is malformed")
            path = (ROOT / templates[artifact_name].format(
                campaign_id=campaign_id
            )).resolve()
            if not path.is_file() or sha256(path) != claimed:
                raise ServiceError(
                    f"accounting migration artifact differs: {campaign_id}/{artifact_name}"
                )
            paths[artifact_name] = path
            receipts[artifact_name] = file_receipt(path)
        queue = read_json(paths["queue"], "migration queue")
        packet = read_json(paths["packet"], "migration packet")
        attempt = read_json(paths["attempt"], "migration attempt")
        provider_start = read_json(
            paths["provider_start"], "migration provider start"
        )
        result = read_json(paths["result"], "migration result")
        seed_batch = read_json(paths["seed_batch"], "migration seed batch")
        result_receipts = result.get("receipts") or {}
        if (
            queue.get("campaign_id") != campaign_id
            or queue.get("packet") != receipts["packet"]
            or packet.get("campaign_id") != campaign_id
            or packet.get("protocol") != protocol
            or attempt.get("campaign_id") != campaign_id
            or attempt.get("provider_invocation_ordinal") != 1
            or parse_timestamp(attempt.get("started_at")) is None
            or provider_start.get("campaign_id") != campaign_id
            or result.get("campaign_id") != campaign_id
            or result.get("protocol") != protocol
            or result.get("terminal") != entry["terminal"]
            or result.get("seed_count") != entry["seed_count"]
            or result_receipts.get("packet") != receipts["packet"]
            or result_receipts.get("attempt") != receipts["attempt"]
            or result_receipts.get("provider_start") != receipts["provider_start"]
            or result_receipts.get("seed_batch") != receipts["seed_batch"]
            or seed_batch.get("campaign_id") != campaign_id
            or seed_batch.get("terminal") != entry["terminal"]
            or len(seed_batch.get("seeds") or []) != entry["seed_count"]
        ):
            raise ServiceError(
                f"accounting migration artifact chain differs: {campaign_id}"
            )
        record = {
            "campaign_id": campaign_id,
            "protocol": protocol,
            "packet": receipts["packet"],
            "attempt": receipts["attempt"],
            "result": receipts["result"],
            "started_at": attempt["started_at"],
            "terminal": entry["terminal"],
            "seed_count": entry["seed_count"],
        }
        if target is excluded_records:
            record = {
                "campaign_id": campaign_id,
                "protocol": protocol,
                "packet": receipts["packet"],
                "attempt": receipts["attempt"],
                "result": receipts["result"],
                "exclusion_reason": (
                    "pre-standing-v1-not-charged-by-tickets-0083-or-0119"
                ),
            }
        target.append(record)
    if identities != sorted(identities) or len(set(identities)) != 36:
        raise ServiceError("accounting migration identities are not sorted and unique")
    if len(charged_records) != 30 or len(excluded_records) != 6:
        raise ServiceError("accounting migration partition differs from 30+6")
    if historical_batch_invocations(service_dir) != charged_records:
        raise ServiceError("visible charged legacy history differs from the fixed root")
    if historical_nonrate_invocations(service_dir) != excluded_records:
        raise ServiceError("visible excluded v1 history differs from the fixed root")
    return root, charged_records, excluded_records


def historical_batch_invocations(service_dir: Path) -> list[dict[str, Any]]:
    """Strictly enumerate pre-ledger v2/v2.1 calls for one migration baseline."""
    records: list[dict[str, Any]] = []
    batches = service_dir / "batches"
    if not batches.exists():
        return records
    for batch_dir in sorted(path for path in batches.iterdir() if path.is_dir()):
        packet_path = batch_dir / "packet.json"
        attempt_path = batch_dir / "attempt.json"
        result_path = batch_dir / "result-receipt.json"
        if not packet_path.is_file():
            if attempt_path.exists() or result_path.exists():
                raise ServiceError(
                    f"legacy invocation artifact has no packet: {batch_dir.name}"
                )
            continue
        packet = read_json(packet_path, "legacy accounting packet")
        protocol = packet.get("protocol")
        if protocol in NON_RATE_HISTORICAL_PROTOCOLS:
            continue
        if protocol == PROTOCOL_VERSION:
            # V3 attempts belong exclusively to the hash-linked invocation
            # ledger validated after the fixed pre-v3 migration baseline.
            # Rechecking them here makes every first v3 attempt look like
            # unledgered legacy history while its head is being committed.
            continue
        if protocol not in {
            "continuous-idea-generator-v2",
            "continuous-idea-generator-v2.1",
        }:
            if attempt_path.is_file():
                raise ServiceError(
                    "attempted packet uses an unsupported accounting protocol: "
                    f"{batch_dir.name}"
                )
            continue
        if not attempt_path.is_file():
            if result_path.is_file():
                raise ServiceError(
                    f"legacy result has no charged attempt: {batch_dir.name}"
                )
            continue
        if not result_path.is_file():
            raise ServiceError(
                f"legacy accounting has an unresolved attempt: {batch_dir.name}"
            )
        attempt = read_json(attempt_path, "legacy accounting attempt")
        result = read_json(result_path, "legacy accounting result")
        campaign_id = safe_leaf_id(packet.get("campaign_id"), "legacy campaign_id")
        started_at = attempt.get("started_at")
        if attempt.get("campaign_id") != campaign_id or parse_timestamp(started_at) is None:
            raise ServiceError(f"legacy attempt identity is invalid: {batch_dir.name}")
        terminal = result.get("terminal")
        if result.get("campaign_id") != campaign_id or terminal not in PROVIDER_RESULT_TERMINALS:
            raise ServiceError(f"legacy result identity is invalid: {batch_dir.name}")
        seed_count = result.get("seed_count")
        if not isinstance(seed_count, int) or isinstance(seed_count, bool) or seed_count < 0:
            raise ServiceError(f"legacy result seed_count is invalid: {batch_dir.name}")
        records.append(
            {
                "campaign_id": campaign_id,
                "protocol": protocol,
                "packet": file_receipt(packet_path),
                "attempt": file_receipt(attempt_path),
                "result": file_receipt(result_path),
                "started_at": started_at,
                "terminal": terminal,
                "seed_count": seed_count,
            }
        )
    records.sort(key=lambda item: (str(item["started_at"]), str(item["campaign_id"])))
    return records


def historical_nonrate_invocations(service_dir: Path) -> list[dict[str, Any]]:
    """Authenticate explicitly excluded pre-standing v1 calls at migration."""
    records: list[dict[str, Any]] = []
    batches = service_dir / "batches"
    if not batches.exists():
        return records
    for packet_path in sorted(batches.glob("*/packet.json")):
        packet = read_json(packet_path, "historical non-rate packet")
        if packet.get("protocol") not in NON_RATE_HISTORICAL_PROTOCOLS:
            continue
        attempt_path = packet_path.parent / "attempt.json"
        result_path = packet_path.parent / "result-receipt.json"
        if not attempt_path.is_file() or not result_path.is_file():
            raise ServiceError("historical v1 packet is not a resolved invocation")
        attempt = read_json(attempt_path, "historical v1 attempt")
        result = read_json(result_path, "historical v1 result")
        campaign_id = safe_leaf_id(packet.get("campaign_id"), "v1 campaign_id")
        if (
            attempt.get("campaign_id") != campaign_id
            or result.get("campaign_id") != campaign_id
            or parse_timestamp(attempt.get("started_at")) is None
            or result.get("terminal") not in PROVIDER_RESULT_TERMINALS
        ):
            raise ServiceError("historical v1 invocation identity is invalid")
        records.append(
            {
                "campaign_id": campaign_id,
                "protocol": "continuous-idea-generator-v1",
                "packet": file_receipt(packet_path),
                "attempt": file_receipt(attempt_path),
                "result": file_receipt(result_path),
                "exclusion_reason": "pre-standing-v1-not-charged-by-tickets-0083-or-0119",
            }
        )
    return records


def validate_accounting_baseline(
    value: Any,
    *,
    service_dir: Path,
    expected_receipt: dict[str, str] | None = None,
) -> tuple[Path | None, dict[str, Any]]:
    path: Path | None = None
    if isinstance(value, dict) and set(value) == {"path", "sha256"}:
        path = authenticate_receipt(value, "invocation accounting baseline")
        baseline = read_json(path, "invocation accounting baseline")
        if expected_receipt is not None and value != expected_receipt:
            raise ServiceError("accounting baseline receipt differs")
    elif isinstance(value, dict):
        baseline = value
    else:
        raise ServiceError("invocation accounting baseline is missing")
    _migration, fixed_charged, fixed_excluded = validate_accounting_migration_root(
        service_dir
    )
    expected = {
        "schema_version",
        "protocol",
        "created_at",
        "service_dir",
        "migration_ref",
        "migration_root",
        "legacy_charged_count",
        "lifetime_ceiling",
        "legacy_records",
        "legacy_records_sha256",
        "excluded_historical_records",
        "excluded_historical_records_sha256",
        "meaning",
    }
    if set(baseline) != expected or baseline.get("schema_version") != 1:
        raise ServiceError("invocation accounting baseline has an unexpected contract")
    if (
        baseline.get("protocol") != INVOCATION_LEDGER_PROTOCOL
        or baseline.get("service_dir") != repo_relative(service_dir)
        or baseline.get("migration_ref") != WAYFINDER_TICKET
        or baseline.get("migration_root") != file_receipt(MIGRATION_ROOT)
        or baseline.get("lifetime_ceiling") != 100
    ):
        raise ServiceError("invocation accounting baseline identity differs")
    records = baseline.get("legacy_records")
    excluded = baseline.get("excluded_historical_records")
    count = baseline.get("legacy_charged_count")
    if (
        not isinstance(records, list)
        or not isinstance(count, int)
        or isinstance(count, bool)
        or count != len(records)
        or count != len(fixed_charged)
        or records
        != [
            {"charged_ordinal": index, **record}
            for index, record in enumerate(fixed_charged, start=1)
        ]
        or baseline.get("legacy_records_sha256") != canonical_json_sha256(records)
        or not isinstance(excluded, list)
        or baseline.get("excluded_historical_records_sha256")
        != canonical_json_sha256(excluded)
        or excluded != fixed_excluded
    ):
        raise ServiceError("invocation accounting baseline count or digest differs")
    seen: set[str] = set()
    for index, record in enumerate(records, start=1):
        expected_record_keys = {
            "charged_ordinal",
            "campaign_id",
            "protocol",
            "packet",
            "attempt",
            "result",
            "started_at",
            "terminal",
            "seed_count",
        }
        if not isinstance(record, dict) or set(record) != expected_record_keys:
            raise ServiceError(f"accounting baseline record {index} is malformed")
        if record.get("charged_ordinal") != index:
            raise ServiceError("accounting baseline ordinals are not consecutive")
        campaign_id = safe_leaf_id(
            record.get("campaign_id"), "baseline campaign_id"
        )
        if campaign_id in seen:
            raise ServiceError("accounting baseline campaign identities repeat")
        seen.add(campaign_id)
        if record.get("protocol") not in {
            "continuous-idea-generator-v2",
            "continuous-idea-generator-v2.1",
        }:
            raise ServiceError("accounting baseline contains a non-legacy protocol")
        packet_path = authenticate_receipt(record.get("packet"), "baseline packet")
        attempt_path = authenticate_receipt(record.get("attempt"), "baseline attempt")
        result_path = authenticate_receipt(record.get("result"), "baseline result")
        packet = read_json(packet_path, "baseline packet")
        attempt = read_json(attempt_path, "baseline attempt")
        result = read_json(result_path, "baseline result")
        if (
            packet.get("campaign_id") != campaign_id
            or packet.get("protocol") != record.get("protocol")
            or attempt.get("campaign_id") != campaign_id
            or result.get("campaign_id") != campaign_id
            or attempt.get("started_at") != record.get("started_at")
            or parse_timestamp(record.get("started_at")) is None
            or result.get("terminal") != record.get("terminal")
            or result.get("seed_count") != record.get("seed_count")
            or record.get("terminal") not in PROVIDER_RESULT_TERMINALS
        ):
            raise ServiceError("accounting baseline record differs from its artifacts")
    excluded_seen: set[str] = set()
    for index, record in enumerate(excluded):
        if not isinstance(record, dict) or set(record) != {
            "campaign_id",
            "protocol",
            "packet",
            "attempt",
            "result",
            "exclusion_reason",
        }:
            raise ServiceError(f"excluded historical record {index} is malformed")
        campaign_id = safe_leaf_id(record.get("campaign_id"), "excluded campaign_id")
        if campaign_id in seen or campaign_id in excluded_seen:
            raise ServiceError("excluded historical campaign identity repeats")
        excluded_seen.add(campaign_id)
        if (
            record.get("protocol") not in NON_RATE_HISTORICAL_PROTOCOLS
            or record.get("exclusion_reason")
            != "pre-standing-v1-not-charged-by-tickets-0083-or-0119"
        ):
            raise ServiceError("excluded historical record has an invalid basis")
        packet_path = authenticate_receipt(record.get("packet"), "excluded packet")
        attempt_path = authenticate_receipt(record.get("attempt"), "excluded attempt")
        result_path = authenticate_receipt(record.get("result"), "excluded result")
        if (
            read_json(packet_path, "excluded packet").get("campaign_id") != campaign_id
            or read_json(attempt_path, "excluded attempt").get("campaign_id")
            != campaign_id
            or read_json(result_path, "excluded result").get("campaign_id")
            != campaign_id
        ):
            raise ServiceError("excluded historical record differs from its artifacts")
    return path, baseline


def ensure_accounting_baseline(service_dir: Path) -> tuple[Path, dict[str, Any]]:
    _migration, fixed_charged, fixed_excluded = validate_accounting_migration_root(
        service_dir
    )
    directory = accounting_baseline_directory(service_dir)
    existing = sorted(directory.glob("*.json")) if directory.exists() else []
    if len(existing) > 1:
        raise ServiceError("multiple invocation-accounting baselines exist")
    if existing:
        path = existing[0]
        _path, baseline = validate_accounting_baseline(
            file_receipt(path), service_dir=service_dir
        )
    else:
        if accounting_head_path(service_dir).exists() or any(
            accounting_event_directory(service_dir).glob("*.json")
        ):
            raise ServiceError(
                "accounting baseline is missing while v3 ledger state exists"
            )
        authorizations = service_dir / AUTHORIZATION_DIRECTORY_NAME
        if authorizations.exists():
            for prior_path in authorizations.glob("*.json"):
                try:
                    prior = read_json(prior_path, "prior standing authorization")
                except ServiceError:
                    continue
                if prior.get("protocol") == PROTOCOL_VERSION and prior.get(
                    "accounting_baseline"
                ) is not None:
                    raise ServiceError(
                        "accounting baseline is missing but a prior v3 authorization "
                        "proves migration already occurred"
                    )
        records = [
            {"charged_ordinal": index, **record}
            for index, record in enumerate(fixed_charged, start=1)
        ]
        excluded_records = fixed_excluded
        baseline = {
            "schema_version": 1,
            "protocol": INVOCATION_LEDGER_PROTOCOL,
            "created_at": now(),
            "service_dir": repo_relative(service_dir),
            "migration_ref": WAYFINDER_TICKET,
            "migration_root": file_receipt(MIGRATION_ROOT),
            "legacy_charged_count": len(records),
            "lifetime_ceiling": 100,
            "legacy_records": records,
            "legacy_records_sha256": canonical_json_sha256(records),
            "excluded_historical_records": excluded_records,
            "excluded_historical_records_sha256": canonical_json_sha256(
                excluded_records
            ),
            "meaning": (
                "immutable lifetime-accounting migration baseline; all listed "
                "legacy calls remain charged"
            ),
        }
        encoded = json.dumps(baseline, indent=2, sort_keys=True) + "\n"
        digest = hashlib.sha256(encoded.encode("utf-8")).hexdigest()
        path = directory / f"{digest}.json"
        write_once(path, baseline)
        validate_accounting_baseline(file_receipt(path), service_dir=service_dir)
    head_path = accounting_head_path(service_dir)
    if not head_path.exists():
        atomic_json(
            head_path,
            {
                "schema_version": 1,
                "protocol": INVOCATION_LEDGER_PROTOCOL,
                "baseline": file_receipt(path),
                "event_count": 0,
                "charged_count": baseline["legacy_charged_count"],
                "last_event": file_receipt(path),
                "unresolved_attempt_ordinal": None,
                "updated_at": now(),
            },
        )
    return path, baseline


def accounting_event_path(
    service_dir: Path,
    event_index: int,
    event_type: str,
    charged_ordinal: int,
) -> Path:
    if event_type not in {"attempt", "outcome"}:
        raise ServiceError("accounting event type is invalid")
    return accounting_event_directory(service_dir) / (
        f"{event_index:06d}-{event_type}-{charged_ordinal:06d}.json"
    )


def validate_accounting_chain(
    service_dir: Path,
    authorization: dict[str, Any],
    *,
    _validate_committed_prefix_with_one_tail: bool = False,
) -> dict[str, Any]:
    validate_service_state_layout(service_dir)
    baseline_receipt = authorization.get("accounting_baseline")
    baseline_path, baseline = validate_accounting_baseline(
        baseline_receipt, service_dir=service_dir
    )
    assert baseline_path is not None
    head_path = accounting_head_path(service_dir)
    head = read_json(head_path, "invocation accounting head")
    head_keys = {
        "schema_version",
        "protocol",
        "baseline",
        "event_count",
        "charged_count",
        "last_event",
        "unresolved_attempt_ordinal",
        "updated_at",
    }
    if set(head) != head_keys or head.get("schema_version") != 1:
        raise ServiceError("invocation accounting head is malformed")
    if (
        head.get("protocol") != INVOCATION_LEDGER_PROTOCOL
        or head.get("baseline") != baseline_receipt
    ):
        raise ServiceError("invocation accounting head names another baseline")
    events_dir = accounting_event_directory(service_dir)
    all_events = sorted(events_dir.glob("*.json")) if events_dir.exists() else []
    committed_event_count = head.get("event_count")
    if (
        not isinstance(committed_event_count, int)
        or isinstance(committed_event_count, bool)
        or committed_event_count < 0
    ):
        raise ServiceError("invocation accounting head event count is malformed")
    if _validate_committed_prefix_with_one_tail:
        if len(all_events) != committed_event_count + 1:
            raise ServiceError("invocation accounting head/event count differs")
        events = all_events[:committed_event_count]
    else:
        events = all_events
    if committed_event_count != len(events):
        raise ServiceError("invocation accounting head/event count differs")
    previous = file_receipt(baseline_path)
    charged = int(baseline["legacy_charged_count"])
    unresolved: int | None = None
    records: list[dict[str, Any]] = [
        {
            "campaign_id": record["campaign_id"],
            "generation_mode": None,
            "started_at": record["started_at"],
            "result": {
                "terminal": record["terminal"],
                "seed_count": record["seed_count"],
            },
            "provider_invoked": True,
            "charged_ordinal": record["charged_ordinal"],
            "protocol": record["protocol"],
            "attempt_event": None,
            "outcome_event": None,
            "result_receipt": record["result"],
            "seed_batch_receipt": None,
        }
        for record in baseline["legacy_records"]
    ]
    attempt_by_ordinal: dict[int, tuple[dict[str, Any], Path]] = {}
    campaign_attempts: dict[str, dict[str, str]] = {}
    for index, path in enumerate(events, start=1):
        event = read_json(path, "invocation accounting event")
        if event.get("event_index") != index or event.get("previous") != previous:
            raise ServiceError("invocation accounting event chain is discontinuous")
        event_type = event.get("event_type")
        if event_type == "attempt":
            keys = {
                "schema_version",
                "protocol",
                "event_index",
                "event_type",
                "charged_ordinal",
                "previous",
                "campaign_id",
                "created_at",
                "packet",
                "queue",
                "standing_authorization",
                "generation_mode",
                "requested_seed_count",
                "feedback_epoch_sha256",
                "retry_authority",
            }
            if set(event) != keys or index % 2 != 1:
                raise ServiceError("invocation attempt event is malformed or out of order")
            if unresolved is not None:
                raise ServiceError("invocation attempt appears before the prior outcome")
            charged += 1
            ordinal = event.get("charged_ordinal")
            if ordinal != charged:
                raise ServiceError("invocation attempt charged ordinal is discontinuous")
            campaign_id = safe_leaf_id(event.get("campaign_id"), "event campaign_id")
            if campaign_id in campaign_attempts:
                raise ServiceError("invocation accounting campaign is charged twice")
            if (
                event.get("protocol") != INVOCATION_LEDGER_PROTOCOL
                or parse_timestamp(event.get("created_at")) is None
                or event.get("retry_authority") != "none"
                or event.get("generation_mode") not in SUPPORTED_MODES
                or not isinstance(event.get("requested_seed_count"), int)
                or not 1 <= int(event["requested_seed_count"]) <= 5
                or not isinstance(event.get("feedback_epoch_sha256"), str)
                or len(event["feedback_epoch_sha256"]) != 64
            ):
                raise ServiceError("invocation attempt event contract differs")
            packet_path = authenticate_receipt(event.get("packet"), "event packet")
            authenticate_receipt(event.get("queue"), "event queue")
            authenticate_receipt(
                event.get("standing_authorization"), "event standing authorization"
            )
            packet = verify_packet(packet_path, mode="historical")
            if (
                packet.get("campaign_id") != campaign_id
                or packet.get("requested_seed_count") != event["requested_seed_count"]
                or packet.get("feedback_epoch_sha256") != event["feedback_epoch_sha256"]
                or packet.get("generation_mode") != event["generation_mode"]
                or packet.get("standing_authorization")
                != event["standing_authorization"]
            ):
                raise ServiceError("invocation attempt event differs from its packet")
            batch_attempt_path = (
                service_dir / "batches" / campaign_id / "attempt.json"
            )
            if not batch_attempt_path.is_file():
                raise ServiceError("ledgered invocation has no batch attempt receipt")
            batch_attempt = read_json(batch_attempt_path, "batch attempt")
            if (
                batch_attempt.get("campaign_id") != campaign_id
                or batch_attempt.get("provider_invocation_ordinal") != ordinal
                or batch_attempt.get("ledger_event") != file_receipt(path)
                or batch_attempt.get("started_at") != event.get("created_at")
            ):
                raise ServiceError("batch attempt differs from its ledger event")
            unresolved = int(ordinal)
            attempt_by_ordinal[int(ordinal)] = (event, path)
            campaign_attempts[campaign_id] = file_receipt(path)
            records.append(
                {
                    "campaign_id": campaign_id,
                    "generation_mode": event["generation_mode"],
                    "started_at": event["created_at"],
                    "result": None,
                    "provider_invoked": None,
                    "charged_ordinal": ordinal,
                    "protocol": PROTOCOL_VERSION,
                    "attempt_event": file_receipt(path),
                    "outcome_event": None,
                    "result_receipt": None,
                    "seed_batch_receipt": None,
                }
            )
        elif event_type == "outcome":
            keys = {
                "schema_version",
                "protocol",
                "event_index",
                "event_type",
                "charged_ordinal",
                "previous",
                "attempt_event",
                "campaign_id",
                "finished_at",
                "provider_invoked",
                "outcome_class",
                "terminal",
                "seed_count",
                "result",
                "seed_batch",
            }
            if set(event) != keys or index % 2 != 0:
                raise ServiceError("invocation outcome event is malformed or out of order")
            ordinal = event.get("charged_ordinal")
            attempt_pair = attempt_by_ordinal.get(int(ordinal) if isinstance(ordinal, int) else -1)
            if attempt_pair is None:
                raise ServiceError("invocation outcome has no preceding attempt")
            attempt, attempt_path = attempt_pair
            if (
                event.get("protocol") != INVOCATION_LEDGER_PROTOCOL
                or unresolved != ordinal
                or event.get("attempt_event") != previous
                or event.get("attempt_event") != file_receipt(attempt_path)
                or event.get("campaign_id") != attempt.get("campaign_id")
                or parse_timestamp(event.get("finished_at")) is None
                or not isinstance(event.get("provider_invoked"), bool)
                or event.get("outcome_class") not in {
                    "complete",
                    "novelty_stop",
                    "provider_stop",
                    "packet_mismatch_after_invocation",
                    "charged_prelaunch_stop",
                }
                or event.get("terminal") not in PROVIDER_RESULT_TERMINALS
                or not isinstance(event.get("seed_count"), int)
                or isinstance(event.get("seed_count"), bool)
                or int(event["seed_count"]) < 0
            ):
                raise ServiceError("invocation outcome event contract differs")
            result_path = authenticate_receipt(event.get("result"), "event result")
            seed_path = authenticate_receipt(event.get("seed_batch"), "event seed batch")
            result = read_json(result_path, "event result")
            batch = read_json(seed_path, "event seed batch")
            validate_v3_result_receipt(
                service_dir,
                result_path,
                seed_path,
                batch,
            )
            expected_outcome_class = _accounting_outcome_class(
                str(event.get("terminal")),
                provider_invoked=bool(event.get("provider_invoked")),
            )
            if (
                result.get("campaign_id") != event.get("campaign_id")
                or result.get("terminal") != event.get("terminal")
                or result.get("seed_count") != event.get("seed_count")
                or batch.get("terminal") != event.get("terminal")
                or len(batch.get("seeds") or []) != event.get("seed_count")
                or event.get("outcome_class") != expected_outcome_class
                or records[-1].get("charged_ordinal") != ordinal
                or records[-1].get("campaign_id") != event.get("campaign_id")
            ):
                raise ServiceError("invocation outcome differs from its artifacts")
            if event.get("provider_invoked") is True:
                validate_provider_start(
                    service_dir,
                    str(event.get("campaign_id")),
                    expected_attempt_event=file_receipt(attempt_path),
                )
            else:
                validate_charged_prelaunch_stop_result(
                    service_dir,
                    str(event.get("campaign_id")),
                    result,
                )
            records[-1]["result"] = result
            records[-1]["provider_invoked"] = event["provider_invoked"]
            records[-1]["outcome_event"] = file_receipt(path)
            records[-1]["result_receipt"] = file_receipt(result_path)
            records[-1]["seed_batch_receipt"] = file_receipt(seed_path)
            unresolved = None
        else:
            raise ServiceError("invocation accounting event type is invalid")
        if event.get("schema_version") != 1:
            raise ServiceError("invocation accounting event schema is invalid")
        previous = file_receipt(path)
    if (
        head.get("charged_count") != charged
        or head.get("last_event") != previous
        or head.get("unresolved_attempt_ordinal") != unresolved
    ):
        raise ServiceError("invocation accounting head does not match its event chain")
    # Any v3 attempt outside the chain is an accounting-evasion/corruption stop.
    batches = service_dir / "batches"
    if batches.exists():
        for attempt_path in sorted(batches.glob("*/attempt.json")):
            packet_path = attempt_path.parent / "packet.json"
            if not packet_path.is_file():
                raise ServiceError("batch attempt has no packet")
            packet = read_json(packet_path, "attempt packet")
            if packet.get("protocol") != PROTOCOL_VERSION:
                continue
            attempt = read_json(attempt_path, "v3 batch attempt")
            campaign_id = attempt.get("campaign_id")
            if campaign_attempts.get(str(campaign_id)) != attempt.get("ledger_event"):
                raise ServiceError("v3 batch attempt is absent from the invocation ledger")
    closed_v3_by_campaign = {
        str(record["campaign_id"]): record
        for record in records
        if record.get("protocol") == PROTOCOL_VERSION
        and record.get("outcome_event") is not None
    }
    if len(closed_v3_by_campaign) != sum(
        1
        for record in records
        if record.get("protocol") == PROTOCOL_VERSION
        and record.get("outcome_event") is not None
    ):
        raise ServiceError("closed v3 accounting campaign identities repeat")
    unresolved_record = next(
        (
            record
            for record in records
            if record.get("protocol") == PROTOCOL_VERSION
            and record.get("charged_ordinal") == unresolved
        ),
        None,
    )
    return {
        "baseline": file_receipt(baseline_path),
        "head": file_receipt(head_path),
        "event_count": len(events),
        "charged_count": charged,
        "unresolved_attempt_ordinal": unresolved,
        "unresolved_record": unresolved_record,
        "closed_v3_by_campaign": closed_v3_by_campaign,
        "records": records,
    }


def active_authorization_pointer_path(service_dir: Path) -> Path:
    return service_state_path(service_dir, ACTIVE_AUTHORIZATION_NAME)


def authorization_activation_event_directory(service_dir: Path) -> Path:
    return service_state_path(service_dir, AUTHORIZATION_ACTIVATION_DIRECTORY)


def authorization_activation_head_path(service_dir: Path) -> Path:
    return service_state_path(service_dir, AUTHORIZATION_ACTIVATION_HEAD_NAME)


def authorization_activation_event_path(service_dir: Path, index: int) -> Path:
    return authorization_activation_event_directory(service_dir) / (
        f"{index:06d}-activation.json"
    )


def authorization_file_path(
    service_dir: Path, authorization: dict[str, Any]
) -> Path:
    encoded = (json.dumps(authorization, indent=2, sort_keys=True) + "\n").encode(
        "utf-8"
    )
    digest = hashlib.sha256(encoded).hexdigest()
    return service_state_path(
        service_dir, AUTHORIZATION_DIRECTORY_NAME, f"{digest}.json"
    )


def validate_authorization_activation_chain(
    service_dir: Path,
    *,
    allow_absent: bool = False,
    verify_latest_current: bool = True,
) -> dict[str, Any] | None:
    head_path = authorization_activation_head_path(service_dir)
    events_dir = authorization_activation_event_directory(service_dir)
    events = sorted(events_dir.glob("*.json")) if events_dir.exists() else []
    pointer_path = active_authorization_pointer_path(service_dir)
    if not head_path.is_file():
        if events:
            raise ServiceError(
                "authorization activation events exist without an authenticated head"
            )
        if allow_absent:
            if pointer_path.is_file():
                prior_pointer = read_json(
                    pointer_path, "pre-v3 active standing-authorization pointer"
                )
                if prior_pointer.get("protocol") == PROTOCOL_VERSION:
                    raise ServiceError(
                        "v3 active authorization exists without its activation ledger"
                    )
            return None
        raise ServiceError("authorization activation head is missing")
    head = read_json(head_path, "authorization activation head")
    if set(head) != {
        "schema_version",
        "protocol",
        "event_count",
        "last_event",
        "active_authorization",
        "updated_at",
    } or head.get("schema_version") != 1:
        raise ServiceError("authorization activation head is malformed")
    if (
        head.get("protocol") != AUTHORIZATION_ACTIVATION_PROTOCOL
        or parse_timestamp(head.get("updated_at")) is None
        or head.get("event_count") != len(events)
        or not events
    ):
        raise ServiceError("authorization activation head/event state differs")
    previous: dict[str, str] | None = None
    latest_authorization: dict[str, str] | None = None
    latest_event: dict[str, str] | None = None
    latest_activated_at: str | None = None
    for index, event_path in enumerate(events, start=1):
        if event_path != authorization_activation_event_path(service_dir, index):
            raise ServiceError("authorization activation event filename is discontinuous")
        event = read_json(event_path, "authorization activation event")
        if set(event) != {
            "schema_version",
            "protocol",
            "event_index",
            "previous",
            "activated_at",
            "authorization",
            "approval_ref",
            "meaning",
        } or event.get("schema_version") != 1:
            raise ServiceError("authorization activation event is malformed")
        if (
            event.get("protocol") != AUTHORIZATION_ACTIVATION_PROTOCOL
            or event.get("event_index") != index
            or event.get("previous") != previous
            or parse_timestamp(event.get("activated_at")) is None
            or not isinstance(event.get("approval_ref"), str)
            or not event["approval_ref"].strip()
            or event.get("meaning")
            != "only the latest authenticated activation grants service authority"
        ):
            raise ServiceError("authorization activation event chain differs")
        authorization_path = authenticate_receipt(
            event.get("authorization"), "activated standing authorization"
        )
        authorization_root = (service_dir / AUTHORIZATION_DIRECTORY_NAME).resolve()
        try:
            authorization_path.relative_to(authorization_root)
        except ValueError as exc:
            raise ServiceError(
                "activated standing authorization is outside its immutable directory"
            ) from exc
        authorization = verify_standing_authorization(
            authorization_path,
            service_dir=service_dir,
            mode="historical",
        )
        if authorization.get("approval_ref") != event.get("approval_ref"):
            raise ServiceError("activation approval differs from its authorization")
        previous = file_receipt(event_path)
        latest_event = previous
        latest_authorization = file_receipt(authorization_path)
        latest_activated_at = str(event["activated_at"])
    if (
        head.get("last_event") != latest_event
        or head.get("active_authorization") != latest_authorization
    ):
        raise ServiceError("authorization activation head does not name its latest event")
    pointer = read_json(pointer_path, "active standing-authorization pointer")
    if set(pointer) != {
        "schema_version",
        "protocol",
        "activated_at",
        "authorization",
        "activation_event",
    } or pointer.get("schema_version") != 1:
        raise ServiceError("active standing-authorization pointer is malformed")
    if (
        pointer.get("protocol") != PROTOCOL_VERSION
        or pointer.get("activated_at") != latest_activated_at
        or pointer.get("authorization") != latest_authorization
        or pointer.get("activation_event") != latest_event
    ):
        raise ServiceError(
            "active standing-authorization pointer is not the authenticated latest activation"
        )
    assert latest_authorization is not None
    if verify_latest_current:
        latest_path = authenticate_receipt(
            latest_authorization, "latest standing authorization"
        )
        verify_standing_authorization(
            latest_path,
            service_dir=service_dir,
            mode="current",
        )
    return {
        "head": file_receipt(head_path),
        "event_count": len(events),
        "last_event": latest_event,
        "active_authorization": latest_authorization,
        "activated_at": latest_activated_at,
    }


def append_authorization_activation(
    service_dir: Path,
    authorization_path: Path,
    authorization: dict[str, Any],
) -> dict[str, Any]:
    prior = validate_authorization_activation_chain(
        service_dir,
        allow_absent=True,
        verify_latest_current=False,
    )
    verify_standing_authorization(
        authorization_path,
        service_dir=service_dir,
        mode="current",
    )
    index = 1 if prior is None else int(prior["event_count"]) + 1
    previous = None if prior is None else prior["last_event"]
    activated_at = now()
    event = {
        "schema_version": 1,
        "protocol": AUTHORIZATION_ACTIVATION_PROTOCOL,
        "event_index": index,
        "previous": previous,
        "activated_at": activated_at,
        "authorization": file_receipt(authorization_path),
        "approval_ref": authorization["approval_ref"],
        "meaning": "only the latest authenticated activation grants service authority",
    }
    event_path = authorization_activation_event_path(service_dir, index)
    write_once(event_path, event)
    atomic_json(
        authorization_activation_head_path(service_dir),
        {
            "schema_version": 1,
            "protocol": AUTHORIZATION_ACTIVATION_PROTOCOL,
            "event_count": index,
            "last_event": file_receipt(event_path),
            "active_authorization": file_receipt(authorization_path),
            "updated_at": activated_at,
        },
    )
    atomic_json(
        active_authorization_pointer_path(service_dir),
        {
            "schema_version": 1,
            "protocol": PROTOCOL_VERSION,
            "activated_at": activated_at,
            "authorization": file_receipt(authorization_path),
            "activation_event": file_receipt(event_path),
        },
    )
    validated = validate_authorization_activation_chain(service_dir)
    assert validated is not None
    return validated


def active_standing_authorization(
    service_dir: Path,
) -> tuple[Path, dict[str, Any]]:
    validate_service_state_layout(service_dir)
    activation = validate_authorization_activation_chain(service_dir)
    assert activation is not None
    pointer_path = active_authorization_pointer_path(service_dir)
    pointer = read_json(pointer_path, "active standing-authorization pointer")
    if set(pointer) != {
        "schema_version",
        "protocol",
        "activated_at",
        "authorization",
        "activation_event",
    } or pointer.get("schema_version") != 1:
        raise ServiceError("active standing-authorization pointer is malformed")
    if pointer.get("protocol") != PROTOCOL_VERSION:
        raise ServiceError("active standing-authorization pointer protocol drifted")
    authorization_path = authenticate_receipt(
        pointer.get("authorization"), "active standing authorization"
    )
    if pointer.get("authorization") != activation.get("active_authorization"):
        raise ServiceError("active pointer differs from the activation ledger")
    authorization_root = (service_dir / AUTHORIZATION_DIRECTORY_NAME).resolve()
    try:
        authorization_path.relative_to(authorization_root)
    except ValueError as exc:
        raise ServiceError(
            "active standing authorization is outside its immutable directory"
        ) from exc
    authorization = verify_standing_authorization(
        authorization_path, service_dir=service_dir
    )
    return authorization_path, authorization


def current_authorized_accounting(
    service_dir: Path,
) -> tuple[Path, dict[str, Any], dict[str, Any]]:
    """Resolve one current authority/accounting view for a locked transition."""
    authorization_path, authorization = active_standing_authorization(service_dir)
    accounting = validate_accounting_chain(service_dir, authorization)
    return authorization_path, authorization, accounting


def verify_standing_authorization(
    path: Path,
    *,
    service_dir: Path | None = None,
    mode: str = "current",
) -> dict[str, Any]:
    if mode not in {"current", "historical"}:
        raise ServiceError("standing authorization mode must be current or historical")
    value = read_json(path, "standing authorization")
    required = {
        "schema_version",
        "protocol",
        "created_at",
        "approval_ref",
        "service_dir",
        "implementation",
        "supporting_implementation",
        "accounting_baseline",
        "provider",
        "generation_modes",
        "limits",
        "authority",
    }
    if set(value) != required or value.get("schema_version") != 1:
        raise ServiceError("standing authorization has an unexpected contract")
    if value.get("protocol") != PROTOCOL_VERSION:
        raise ServiceError("standing authorization protocol is unsupported")
    implementation = validate_receipt_shape(
        value.get("implementation"), "standing authorization implementation"
    )
    if repo_relative(implementation) != repo_relative(Path(__file__).resolve()):
        raise ServiceError("standing authorization binds another implementation")
    if mode == "current":
        if value.get("implementation") != file_receipt(Path(__file__).resolve()):
            raise ServiceError("standing authorization implementation drifted")
        authenticate_receipt(
            value.get("implementation"), "standing authorization implementation"
        )
    supporting = value.get("supporting_implementation")
    if not isinstance(supporting, list) or not supporting:
        raise ServiceError("standing authorization supporting implementation differs")
    supporting_paths: list[str] = []
    primary_path = repo_relative(Path(__file__).resolve())
    for index, receipt in enumerate(supporting):
        component = validate_receipt_shape(
            receipt, f"standing supporting implementation {index}"
        )
        component_path = repo_relative(component)
        if component_path == primary_path or component_path in supporting_paths:
            raise ServiceError(
                "standing authorization supporting implementation repeats a path"
            )
        supporting_paths.append(component_path)
        if mode == "current":
            authenticate_receipt(
                receipt, f"standing supporting implementation {index}"
            )
    if mode == "current":
        expected_paths = [
            repo_relative(component)
            for component in implementation_component_paths()[1:]
        ]
        if supporting_paths != expected_paths:
            raise ServiceError(
                "standing authorization helper or schema path identity drifted"
            )
    resolved_service = service_directory(Path(str(value.get("service_dir"))))
    if service_dir is not None and resolved_service != service_dir.resolve():
        raise ServiceError("standing authorization binds another service directory")
    validate_accounting_baseline(
        value.get("accounting_baseline"), service_dir=resolved_service
    )
    provider = value.get("provider")
    if not isinstance(provider, dict):
        raise ServiceError("standing provider contract is missing")
    exact_provider = {
        "model": "gpt-5.6-sol",
        "reasoning_effort": "max",
        "web_search": "live",
        "sandbox": "read-only",
        "approval_policy": "never",
        "subagents": "disabled",
        "ephemeral": True,
        "max_concurrent_invocations": 1,
    }
    if set(provider) != set(exact_provider) | {
        "executable",
        "executable_sha256",
        "cli_version",
    }:
        raise ServiceError("standing provider contract has unexpected fields")
    for key, expected in exact_provider.items():
        if provider.get(key) != expected:
            raise ServiceError(f"unsafe or unsupported standing provider field: {key}")
    executable = provider.get("executable")
    if not isinstance(executable, str) or not executable:
        raise ServiceError("standing provider executable is missing")
    executable_path = Path(executable)
    if not executable_path.is_absolute():
        raise ServiceError("standing provider executable is not an absolute path")
    executable_sha = provider.get("executable_sha256")
    cli_version = provider.get("cli_version")
    if (
        not isinstance(executable_sha, str)
        or re.fullmatch(r"[0-9a-f]{64}", executable_sha) is None
        or not isinstance(cli_version, str)
        or not cli_version.strip()
    ):
        raise ServiceError("standing provider identity is malformed")
    if mode == "current":
        if not executable_path.is_file():
            raise ServiceError("standing provider executable is not a file")
        if executable_sha != sha256(executable_path):
            raise ServiceError("standing provider executable bytes drifted")
        if cli_version != codex_version(executable):
            raise ServiceError("Codex CLI version drifted after standing authorization")
    modes = value.get("generation_modes")
    if (
        not isinstance(modes, list)
        or not modes
        or len(set(modes)) != len(modes)
        or any(mode not in SUPPORTED_MODES for mode in modes)
    ):
        raise ServiceError("standing generation modes are invalid")
    limits = value.get("limits")
    if not isinstance(limits, dict):
        raise ServiceError("standing limits are missing")
    expected_limit_fields = {
        "wall_minutes_per_call",
        "cpu_cores_per_call",
        "memory_gib_per_call",
        "output_gib_per_call",
        "ready_seed_target",
        "max_total_invocations",
        "max_consecutive_provider_stops",
        "max_consecutive_zero_seed_batches",
        "max_inline_bytes",
    }
    if set(limits) != expected_limit_fields:
        raise ServiceError("standing limits differ from the v3 closed contract")
    positive_integer_fields = expected_limit_fields - {"output_gib_per_call"}
    for key in positive_integer_fields:
        if not isinstance(limits.get(key), int) or int(limits[key]) < 1:
            raise ServiceError(f"standing limit must be a positive integer: {key}")
    output_gib = limits.get("output_gib_per_call")
    if not isinstance(output_gib, (int, float)) or not 0 < output_gib <= 0.05:
        raise ServiceError("standing output ceiling must be in (0, 0.05] GiB")
    if limits["cpu_cores_per_call"] > 2 or limits["memory_gib_per_call"] > 4:
        raise ServiceError("standing local resource ceiling exceeds v3 envelope")
    maximums = {
        "wall_minutes_per_call": 90,
        "ready_seed_target": 10,
        "max_total_invocations": 100,
        "max_consecutive_provider_stops": 2,
        "max_consecutive_zero_seed_batches": 2,
        "max_inline_bytes": 6 * 1024 * 1024,
    }
    for key, maximum in maximums.items():
        if limits[key] > maximum:
            raise ServiceError(f"standing limit exceeds the v3 ceiling: {key}")
    if limits["ready_seed_target"] != 10:
        raise ServiceError("v3 standing authority requires a ready-seed target of ten")
    authority = value.get("authority")
    required_authority = {
        "may_self_prepare_packets": True,
        "may_invoke_provider_within_limits": True,
        "may_generate_proposals": True,
        "may_research_primary_sources": True,
        "may_retry_attempted_packet": False,
        "may_run_first_tests": False,
        "may_edit_repository": False,
        "may_admit_or_schedule_routes": False,
        "may_consume_or_reconcile_batches": False,
    }
    if authority != required_authority:
        raise ServiceError("standing authority exceeds or differs from v2 envelope")
    return value


def make_standing_authorization(
    service_dir: Path, args: argparse.Namespace
) -> dict[str, Any]:
    if not isinstance(args.approval_ref, str) or not args.approval_ref.strip():
        raise ServiceError("standing approval reference is required")
    requested_maximums = {
        "wall_minutes": 90,
        "ready_seed_target": 10,
        "max_total_invocations": 100,
        "max_consecutive_provider_stops": 2,
        "max_consecutive_zero_seed_batches": 2,
        "max_inline_bytes": 6 * 1024 * 1024,
    }
    for field, maximum in requested_maximums.items():
        value = getattr(args, field)
        if not isinstance(value, int) or not 1 <= value <= maximum:
            raise ServiceError(
                f"requested standing limit must be in [1, {maximum}]: {field}"
            )
    if args.ready_seed_target != 10:
        raise ServiceError("v3 ready-seed target must be exactly ten")
    codex_executable = shutil.which("codex")
    if codex_executable is None:
        raise ServiceError("codex executable is not available")
    baseline_path, _baseline = ensure_accounting_baseline(service_dir)
    return {
        "schema_version": 1,
        "protocol": PROTOCOL_VERSION,
        "created_at": now(),
        "approval_ref": args.approval_ref,
        "service_dir": repo_relative(service_dir),
        "implementation": file_receipt(Path(__file__).resolve()),
        "supporting_implementation": [
            file_receipt(path) for path in implementation_component_paths()[1:]
        ],
        "accounting_baseline": file_receipt(baseline_path),
        "provider": {
            "executable": codex_executable,
            "executable_sha256": sha256(Path(codex_executable)),
            "cli_version": codex_version(codex_executable),
            "model": "gpt-5.6-sol",
            "reasoning_effort": "max",
            "web_search": "live",
            "sandbox": "read-only",
            "approval_policy": "never",
            "subagents": "disabled",
            "ephemeral": True,
            "max_concurrent_invocations": 1,
        },
        "generation_modes": list(args.generation_modes),
        "limits": {
            "wall_minutes_per_call": args.wall_minutes,
            "cpu_cores_per_call": 2,
            "memory_gib_per_call": 4,
            "output_gib_per_call": 0.05,
            "ready_seed_target": args.ready_seed_target,
            "max_total_invocations": args.max_total_invocations,
            "max_consecutive_provider_stops": args.max_consecutive_provider_stops,
            "max_consecutive_zero_seed_batches": args.max_consecutive_zero_seed_batches,
            "max_inline_bytes": args.max_inline_bytes,
        },
        "authority": {
            "may_self_prepare_packets": True,
            "may_invoke_provider_within_limits": True,
            "may_generate_proposals": True,
            "may_research_primary_sources": True,
            "may_retry_attempted_packet": False,
            "may_run_first_tests": False,
            "may_edit_repository": False,
            "may_admit_or_schedule_routes": False,
            "may_consume_or_reconcile_batches": False,
        },
    }


def command_configure(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    with locked_service_state(service_dir):
        return _command_configure_locked(args, service_dir)


def _command_configure_locked(args: argparse.Namespace, service_dir: Path) -> int:
    if daemon_receipt(service_dir) is not None:
        raise ServiceError("stop the live daemon before rotating standing authority")
    unit_state = subprocess.run(
        ["systemctl", "--user", "is-active", SYSTEMD_UNIT_NAME],
        cwd=ROOT,
        text=True,
        capture_output=True,
    ).stdout.strip()
    if unit_state in {"active", "activating", "reloading"}:
        raise ServiceError(
            "the supervised generator unit is live without an authenticated daemon "
            "receipt; stop and diagnose it before rotating authority"
        )
    prior_activation = validate_authorization_activation_chain(
        service_dir,
        allow_absent=True,
        verify_latest_current=False,
    )
    if prior_activation is None:
        migration, _charged, _excluded = validate_accounting_migration_root(
            service_dir
        )
        expected_queue_names = {
            Path(
                str(migration["path_templates"]["queue"]).format(
                    campaign_id=str(entry[0])
                )
            ).name
            for entry in migration["entries"]
        }
        queue_dir = service_state_path(service_dir, "queue")
        try:
            observed_queue_children = exact_queue_children(service_dir)
        except ServiceError as exc:
            raise ServiceError(
                "queue artifacts outside the authenticated migration root block "
                "first v3 configuration"
            ) from exc
        if (
            {path.name for path in observed_queue_children} != expected_queue_names
            or len(observed_queue_children) != len(expected_queue_names)
        ):
            raise ServiceError(
                "queue artifacts outside the authenticated migration root block "
                "first v3 configuration"
            )
    else:
        prior_path = authenticate_receipt(
            prior_activation["active_authorization"],
            "historical active standing authorization",
        )
        prior_authorization = verify_standing_authorization(
            prior_path,
            service_dir=service_dir,
            mode="historical",
        )
        prior_accounting = validate_accounting_chain(
            service_dir, prior_authorization
        )
        if pending_queue(
            service_dir,
            authorization=prior_authorization,
            accounting=prior_accounting,
        ):
            raise ServiceError(
                "resolve or quarantine pending packets before rotating standing authority"
            )
    authorization = make_standing_authorization(service_dir, args)
    accounting = validate_accounting_chain(service_dir, authorization)
    path = authorization_file_path(service_dir, authorization)
    write_once(path, authorization)
    verify_standing_authorization(path, service_dir=service_dir)
    activation = append_authorization_activation(
        service_dir, path, authorization
    )
    pointer_path = active_authorization_pointer_path(service_dir)
    active_path, _ = active_standing_authorization(service_dir)
    if active_path != path:
        raise ServiceError("active authorization pointer did not bind the new receipt")
    print(
        json.dumps(
            {
                "standing_authorization": file_receipt(path),
                "active_authorization_pointer": file_receipt(pointer_path),
                "authorization_activation": activation,
                "limits": authorization["limits"],
                "invocation_accounting": {
                    "baseline": authorization["accounting_baseline"],
                    "charged_count": accounting["charged_count"],
                    "remaining_under_lifetime_ceiling": max(
                        0,
                        int(authorization["limits"]["max_total_invocations"])
                        - int(accounting["charged_count"]),
                    ),
                },
                "generation_modes": authorization["generation_modes"],
                "next": "start the supervised daemon; it will self-prepare immutable cycles",
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


def freeze_campaign_packet(
    service_dir: Path,
    campaign_id: str,
    generation_mode: str,
    authorization_path: Path,
    authorization: dict[str, Any],
    requested_seed_count: int = 5,
) -> dict[str, Any]:
    campaign_id = safe_leaf_id(campaign_id, "campaign_id")
    if generation_mode not in authorization["generation_modes"]:
        raise ServiceError("generation mode is outside the standing authorization")
    if not 1 <= requested_seed_count <= 5:
        raise ServiceError("requested_seed_count must be from one to five")
    limits = authorization["limits"]
    batch_dir = service_dir / "batches" / campaign_id
    packet_path = batch_dir / "packet.json"
    if packet_path.exists():
        raise ServiceError(f"campaign is already frozen: {packet_path}")
    batch_dir.mkdir(parents=True, exist_ok=True)
    snapshot_dir = batch_dir / "snapshot"
    accounting = validate_accounting_chain(service_dir, authorization)
    learning_export_path = snapshot_dir / "validated-learning-export.json"
    materialize_validated_learning_export(
        service_dir,
        learning_export_path,
        authorization_path=authorization_path,
        authorization=authorization,
        accounting=accounting,
        excluded_campaign_id=campaign_id,
    )
    summary = build_sol_idea_packet.build_packet(
        snapshot_dir,
        int(limits["max_inline_bytes"]),
        service_dir,
        campaign_id=campaign_id,
        purpose="provider_generation",
        validated_learning_export=learning_export_path,
    )
    snapshot_path = snapshot_dir / "packet-summary.json"
    snapshot = file_receipt(snapshot_path)
    snapshot_admission_path_value = admit_snapshot_build(
        snapshot_path,
        service_dir=service_dir,
        campaign_id=campaign_id,
        purpose="provider_generation",
    )
    snapshot_build_path = (
        snapshot_path.parent / build_sol_idea_packet.SNAPSHOT_BUILD_RECEIPT_NAME
    )
    snapshot_build = file_receipt(snapshot_build_path)
    snapshot_admission = file_receipt(snapshot_admission_path_value)

    schema_path = batch_dir / "output-schema.json"
    atomic_json(
        schema_path,
        provider_schema(
            campaign_id, generation_mode, snapshot, requested_seed_count
        ),
    )
    prompt_path = batch_dir / "prompt.md"
    prompt_path.write_text(
        make_prompt(
            campaign_id,
            generation_mode,
            snapshot,
            batch_dir,
            requested_seed_count,
        ),
        encoding="utf-8",
    )
    input_paths = [
        Path(__file__).resolve(),
        Path(build_sol_idea_packet.__file__).resolve(),
        Path(campaign.__file__).resolve(),
        authorization_path,
        ROOT / "AGENTS.md",
        ROOT / "docs/agents/research-campaign.md",
        ROOT / "docs/agents/profiles/research-question-generator.md",
        campaign.SEED_SCHEMA,
        snapshot_dir / "manifest.json",
        snapshot_dir / "context.md",
        snapshot_dir / "lean-declarations.md",
        snapshot_dir / "prior-idea-registry.json",
        snapshot_dir / "learning-state-manifest.json",
        learning_export_path,
        snapshot_path,
        snapshot_build_path,
        snapshot_admission_path_value,
        schema_path,
        prompt_path,
    ]
    task_path = batch_dir / "task.json"
    atomic_json(
        task_path,
        make_task(
            service_dir,
            batch_dir,
            campaign_id,
            summary,
            input_paths,
            int(limits["wall_minutes_per_call"]),
            requested_seed_count,
        ),
    )
    provider = authorization["provider"]
    packet = {
        "schema_version": 1,
        "protocol": PROTOCOL_VERSION,
        "campaign_id": campaign_id,
        "generation_mode": generation_mode,
        "requested_seed_count": requested_seed_count,
        "feedback_epoch_sha256": summary["feedback_epoch_sha256"],
        "created_at": now(),
        "service_dir": repo_relative(service_dir),
        "batch_dir": repo_relative(batch_dir),
        "disposition": "standing-authorization-bound",
        "implementation": file_receipt(Path(__file__).resolve()),
        "standing_authorization": file_receipt(authorization_path),
        "snapshot": snapshot,
        "snapshot_build": snapshot_build,
        "snapshot_admission": snapshot_admission,
        "prompt": file_receipt(prompt_path),
        "task": file_receipt(task_path),
        "output_schema": file_receipt(schema_path),
        "provider": {
            "executable": provider["executable"],
            "executable_sha256": provider["executable_sha256"],
            "cli_version": provider["cli_version"],
            "model": provider["model"],
            "reasoning_effort": provider["reasoning_effort"],
            "web_search": "live",
            "sandbox": "read-only",
            "approval_policy": "never",
            "subagents": "disabled",
            "ephemeral": True,
            "max_invocations": 1,
        },
        "limits": {
            "wall_minutes": limits["wall_minutes_per_call"],
            "cpu_cores": limits["cpu_cores_per_call"],
            "memory_gib": limits["memory_gib_per_call"],
            "output_gib": limits["output_gib_per_call"],
        },
        "authority": {
            "standing_authorization_sha256": sha256(authorization_path),
            "may_generate_proposals": True,
            "may_research_primary_sources": True,
            "may_retry_attempted_packet": False,
            "may_run_first_tests": False,
            "may_edit_repository": False,
            "may_admit_or_schedule_routes": False,
            "may_consume_or_reconcile_batches": False,
        },
    }
    atomic_json(packet_path, packet)
    verify_packet(packet_path, mode="current")
    return {
        "campaign_id": campaign_id,
        "requested_seed_count": requested_seed_count,
        "packet": file_receipt(packet_path),
        "prompt": packet["prompt"],
        "task": packet["task"],
        "snapshot": packet["snapshot"],
        "snapshot_build": packet["snapshot_build"],
        "snapshot_admission": packet["snapshot_admission"],
        "standing_authorization": packet["standing_authorization"],
        "next": "queue under the standing authorization",
    }


def command_prepare(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    with locked_service_state(service_dir):
        authorization_path, authorization, _accounting = (
            current_authorized_accounting(service_dir)
        )
        result = freeze_campaign_packet(
            service_dir,
            args.campaign_id,
            args.generation_mode,
            authorization_path,
            authorization,
            args.requested_seed_count,
        )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


def command_prepare_root_snapshot(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    campaign_id = safe_leaf_id(args.campaign_id, "root campaign_id")
    if "-root-seeds-" not in campaign_id:
        raise ServiceError("root-origin campaign identity must contain -root-seeds-")
    output_dir = (
        args.output_dir.resolve()
        if args.output_dir.is_absolute()
        else (ROOT / args.output_dir).resolve()
    )
    try:
        output_dir.relative_to(RUNS_ROOT)
    except ValueError as exc:
        raise ServiceError("root snapshot output must be under runs/agents") from exc
    if output_dir.name != "snapshot":
        raise ServiceError("root snapshot output directory must be named snapshot")
    if output_dir == service_dir or service_dir in output_dir.parents:
        raise ServiceError("root snapshot run must be outside service state")
    with locked_service_state(service_dir):
        authorization_path, authorization, accounting = (
            current_authorized_accounting(service_dir)
        )
        export_path = output_dir / "validated-learning-export.json"
        materialize_validated_learning_export(
            service_dir,
            export_path,
            authorization_path=authorization_path,
            authorization=authorization,
            accounting=accounting,
            excluded_campaign_id=campaign_id,
        )
        summary = build_sol_idea_packet.build_packet(
            output_dir,
            int(authorization["limits"]["max_inline_bytes"]),
            service_dir,
            campaign_id=campaign_id,
            purpose="root_fallback",
            validated_learning_export=export_path,
        )
        snapshot_path = output_dir / "packet-summary.json"
        admission_path = admit_snapshot_build(
            snapshot_path,
            service_dir=service_dir,
            campaign_id=campaign_id,
            purpose="root_fallback",
        )
    print(
        json.dumps(
            {
                "campaign_id": campaign_id,
                "summary": summary,
                "validated_learning_export": file_receipt(export_path),
                "snapshot": file_receipt(snapshot_path),
                "snapshot_build": file_receipt(
                    output_dir / build_sol_idea_packet.SNAPSHOT_BUILD_RECEIPT_NAME
                ),
                "snapshot_admission": file_receipt(admission_path),
                "authority": "root proposal snapshot only",
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


def verify_task_inputs(task: dict[str, Any], *, mode: str) -> None:
    if mode not in {"current", "historical"}:
        raise ServiceError("task-input validation mode must be current or historical")
    inputs = task.get("inputs")
    if not isinstance(inputs, list) or not inputs:
        raise ServiceError("task inputs are missing")
    for index, item in enumerate(inputs):
        if mode == "current":
            authenticate_receipt(item, f"task input {index}")
        else:
            validate_receipt_shape(item, f"task input {index}")


def verify_packet(packet_path: Path, *, mode: str = "current") -> dict[str, Any]:
    if mode not in {"current", "historical"}:
        raise ServiceError("packet validation mode must be current or historical")
    packet = read_json(packet_path, "packet")
    required = {
        "schema_version",
        "protocol",
        "campaign_id",
        "generation_mode",
        "requested_seed_count",
        "feedback_epoch_sha256",
        "created_at",
        "service_dir",
        "batch_dir",
        "disposition",
        "implementation",
        "standing_authorization",
        "snapshot",
        "snapshot_build",
        "snapshot_admission",
        "prompt",
        "task",
        "output_schema",
        "provider",
        "limits",
        "authority",
    }
    if set(packet) != required or packet["schema_version"] != 1:
        raise ServiceError("packet has an unexpected closed-object contract")
    if packet["protocol"] != PROTOCOL_VERSION:
        raise ServiceError("packet protocol is unsupported")
    requested_seed_count = packet.get("requested_seed_count")
    if (
        not isinstance(requested_seed_count, int)
        or isinstance(requested_seed_count, bool)
        or not 1 <= requested_seed_count <= 5
    ):
        raise ServiceError("packet requested_seed_count must be from one to five")
    campaign_id = safe_leaf_id(packet.get("campaign_id"), "packet campaign_id")
    resolved_service = service_directory(Path(str(packet["service_dir"])))
    expected_batch_dir = (resolved_service / "batches" / campaign_id).resolve()
    if (
        packet_path.resolve() != (expected_batch_dir / "packet.json").resolve()
        or packet.get("service_dir") != repo_relative(resolved_service)
        or packet.get("batch_dir") != repo_relative(expected_batch_dir)
    ):
        raise ServiceError("packet is not in its canonical service batch layout")
    expected_local_paths = {
        "snapshot": expected_batch_dir / "snapshot" / "packet-summary.json",
        "snapshot_build": expected_batch_dir
        / "snapshot"
        / build_sol_idea_packet.SNAPSHOT_BUILD_RECEIPT_NAME,
        "snapshot_admission": expected_batch_dir / SNAPSHOT_ADMISSION_NAME,
        "prompt": expected_batch_dir / "prompt.md",
        "task": expected_batch_dir / "task.json",
        "output_schema": expected_batch_dir / "output-schema.json",
    }
    for key, expected_path in expected_local_paths.items():
        actual_path = authenticate_receipt(packet[key], f"packet {key}")
        if (
            actual_path != expected_path.resolve()
            or packet[key].get("path") != repo_relative(expected_path)
        ):
            raise ServiceError(f"packet {key} is outside its canonical batch layout")
    if packet.get("feedback_epoch_sha256") != read_json(
        authenticate_receipt(packet["snapshot"], "packet snapshot"),
        "packet snapshot",
    ).get("feedback_epoch_sha256"):
        raise ServiceError("packet feedback epoch differs from its snapshot")
    for key in (
        "standing_authorization",
        "snapshot",
        "snapshot_build",
        "snapshot_admission",
        "prompt",
        "task",
        "output_schema",
    ):
        authenticate_receipt(packet[key], f"packet {key}")
    if mode == "current":
        authenticate_receipt(packet["implementation"], "packet implementation")
    else:
        validate_receipt_shape(packet["implementation"], "packet implementation")
    authorization_path = authenticate_receipt(
        packet["standing_authorization"], "packet standing authorization"
    )
    authorization = verify_standing_authorization(
        authorization_path,
        service_dir=resolved_service,
        mode=mode,
    )
    snapshot_path = authenticate_receipt(packet["snapshot"], "packet snapshot")
    snapshot_build_path, _snapshot_build = validate_snapshot_build_receipt(
        snapshot_path,
        service_dir=resolved_service,
        campaign_id=str(packet["campaign_id"]),
        purpose="provider_generation",
        mode="historical",
    )
    if packet.get("snapshot_build") != file_receipt(snapshot_build_path):
        raise ServiceError("packet snapshot-build receipt differs")
    admission_path = authenticate_receipt(
        packet["snapshot_admission"], "packet snapshot admission"
    )
    if admission_path != snapshot_admission_path(snapshot_path):
        raise ServiceError("packet snapshot admission names another campaign")
    admission = validate_snapshot_admission(
        admission_path,
        snapshot_path=snapshot_path,
        service_dir=resolved_service,
        campaign_id=str(packet["campaign_id"]),
        purpose="provider_generation",
    )
    if (
        admission.get("validator_component") != packet.get("implementation")
        or admission.get("builder_component")
        != _snapshot_build.get("builder_component")
    ):
        raise ServiceError("packet components differ from snapshot admission")
    task_path = authenticate_receipt(packet["task"], "packet task")
    task = read_json(task_path, "task")
    verify_task_inputs(task, mode=mode)
    if task.get("task_id") != packet["campaign_id"]:
        raise ServiceError("task and packet campaign identities differ")
    if packet.get("disposition") != "standing-authorization-bound":
        raise ServiceError("packet is not bound to the standing authorization")
    if packet.get("generation_mode") not in authorization["generation_modes"]:
        raise ServiceError("packet generation mode is unauthorized")
    expected_provider = {
        **{
            key: authorization["provider"][key]
            for key in (
                "executable",
                "executable_sha256",
                "cli_version",
                "model",
                "reasoning_effort",
                "web_search",
                "sandbox",
                "approval_policy",
                "subagents",
                "ephemeral",
            )
        },
        "max_invocations": 1,
    }
    if packet.get("provider") != expected_provider:
        raise ServiceError("packet provider contract differs from standing authority")
    if packet["provider"].get("max_invocations") != 1:
        raise ServiceError("packet must authorize exactly one provider invocation")
    limits = authorization["limits"]
    expected_limits = {
        "wall_minutes": limits["wall_minutes_per_call"],
        "cpu_cores": limits["cpu_cores_per_call"],
        "memory_gib": limits["memory_gib_per_call"],
        "output_gib": limits["output_gib_per_call"],
    }
    if packet.get("limits") != expected_limits:
        raise ServiceError("packet call limits differ from standing authority")
    expected_authority = {
        "standing_authorization_sha256": sha256(authorization_path),
        "may_generate_proposals": True,
        "may_research_primary_sources": True,
        "may_retry_attempted_packet": False,
        "may_run_first_tests": False,
        "may_edit_repository": False,
        "may_admit_or_schedule_routes": False,
        "may_consume_or_reconcile_batches": False,
    }
    if packet.get("authority") != expected_authority:
        raise ServiceError("packet authority differs from standing authority")
    if mode == "current":
        executable = packet["provider"].get("executable", "codex")
        if packet["provider"].get("cli_version") != codex_version(executable):
            raise ServiceError("Codex CLI version drifted after packet freeze")
    return packet


def process_alive(pid: int) -> bool:
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
    except (ProcessLookupError, PermissionError):
        return False
    return True


def process_identity(pid: int) -> dict[str, Any] | None:
    """Identify a process across PID reuse and Linux/WSL boot boundaries."""
    if not process_alive(pid):
        return None
    try:
        stat = (Path("/proc") / str(pid) / "stat").read_text(encoding="utf-8")
        tail = stat[stat.rfind(")") + 2 :].split()
        start_ticks = int(tail[19])
        boot_id = Path("/proc/sys/kernel/random/boot_id").read_text(
            encoding="utf-8"
        ).strip()
        process_group_id = os.getpgid(pid)
    except (OSError, ValueError, IndexError):
        return None
    return {
        "pid": pid,
        "boot_id": boot_id,
        "start_ticks": start_ticks,
        "process_group_id": process_group_id,
    }


def process_identity_matches(expected: Any) -> bool:
    if not isinstance(expected, dict) or set(expected) != {
        "pid",
        "boot_id",
        "start_ticks",
        "process_group_id",
    }:
        return False
    pid = expected.get("pid")
    return isinstance(pid, int) and process_identity(pid) == expected


def daemon_process_identity(pid: int) -> dict[str, Any] | None:
    base = process_identity(pid)
    if base is None:
        return None
    try:
        executable = (Path("/proc") / str(pid) / "exe").resolve().as_posix()
        command = (Path("/proc") / str(pid) / "cmdline").read_bytes()
    except OSError:
        return None
    return {
        **base,
        "executable": executable,
        "command_sha256": hashlib.sha256(command).hexdigest(),
        "names_generator_script": str(Path(__file__).resolve()).encode() in command,
        "names_serve_command": b"serve" in command.split(b"\0"),
    }


def daemon_process_identity_matches(expected: Any) -> bool:
    if not isinstance(expected, dict):
        return False
    pid = expected.get("pid")
    return isinstance(pid, int) and daemon_process_identity(pid) == expected


def systemd_main_pid() -> int | None:
    result = subprocess.run(
        [
            "systemctl",
            "--user",
            "show",
            SYSTEMD_UNIT_NAME,
            "--property=MainPID",
            "--value",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    try:
        pid = int(result.stdout.strip())
    except (TypeError, ValueError):
        return None
    return pid if result.returncode == 0 and pid > 0 else None


def daemon_receipt(service_dir: Path) -> dict[str, Any] | None:
    path = service_dir / "service.pid"
    if not path.is_file():
        return None
    try:
        value = read_json(path, "service PID")
    except ServiceError:
        return None
    pid = value.get("pid")
    if not isinstance(pid, int):
        return None
    if not daemon_process_identity_matches(value.get("process_identity")):
        return None
    if systemd_main_pid() != pid:
        return None
    value = dict(value)
    value["liveness"] = "authenticated-process-and-systemd-main-pid"
    return value


def queue_packet(
    service_dir: Path,
    packet_path: Path,
    packet_sha: str,
    prompt_sha: str,
    task_sha: str,
    approval_ref: str,
    *,
    state_lock_held: bool = False,
) -> dict[str, Any]:
    if sha256(packet_path) != packet_sha:
        raise ServiceError("approved packet hash does not match")
    packet = verify_packet(packet_path, mode="current")
    admission_path = authenticate_receipt(
        packet["snapshot_admission"], "queued snapshot admission"
    )
    admission = validate_snapshot_admission(
        admission_path,
        snapshot_path=authenticate_receipt(packet["snapshot"], "queued snapshot"),
        service_dir=service_dir,
        campaign_id=str(packet["campaign_id"]),
        purpose="provider_generation",
    )
    current, reasons = snapshot_currency(
        admission,
        service_dir=service_dir,
        campaign_id=str(packet["campaign_id"]),
    )
    if not current:
        raise ServiceError(
            "approved packet is stale before queue admission: " + ",".join(reasons)
        )
    if packet["prompt"]["sha256"] != prompt_sha:
        raise ServiceError("approved prompt hash does not match")
    if packet["task"]["sha256"] != task_sha:
        raise ServiceError("approved task hash does not match")
    entry = {
        "schema_version": 1,
        "protocol": PROTOCOL_VERSION,
        "campaign_id": packet["campaign_id"],
        "queued_at": now(),
        "packet": file_receipt(packet_path),
        "standing_authorization": packet["standing_authorization"],
        "approved_prompt_sha256": prompt_sha,
        "approved_task_sha256": task_sha,
        "approval_ref": approval_ref,
        "provider_invocations_authorized": 1,
        "route_or_experiment_authority": "none",
    }
    queue_path = service_state_path(
        service_dir, "queue", f"{packet['campaign_id']}.json"
    )
    lock_context = (
        nullcontext() if state_lock_held else locked_service_state(service_dir)
    )
    with lock_context:
        authorization_path, authorization, accounting = current_authorized_accounting(
            service_dir
        )
        packet = verify_packet(packet_path, mode="current")
        if packet["standing_authorization"] != file_receipt(authorization_path):
            raise ServiceError(
                "packet is not bound to the active standing authorization"
            )
        admission_path = authenticate_receipt(
            packet["snapshot_admission"], "queued snapshot admission"
        )
        admission = validate_snapshot_admission(
            admission_path,
            snapshot_path=authenticate_receipt(
                packet["snapshot"], "queued snapshot"
            ),
            service_dir=service_dir,
            campaign_id=str(packet["campaign_id"]),
            purpose="provider_generation",
        )
        current, reasons = snapshot_currency(
            admission,
            service_dir=service_dir,
            campaign_id=str(packet["campaign_id"]),
        )
        if not current:
            raise ServiceError(
                "approved packet is stale at queue commit: " + ",".join(reasons)
            )
        if queue_path.exists():
            existing, _existing_packet_path, _existing_packet = authenticate_queue(
                queue_path, mode="current"
            )
            stable_keys = {
                "campaign_id",
                "packet",
                "standing_authorization",
                "approved_prompt_sha256",
                "approved_task_sha256",
                "approval_ref",
                "provider_invocations_authorized",
                "route_or_experiment_authority",
            }
            if any(existing.get(key) != entry.get(key) for key in stable_keys):
                raise ServiceError("existing queue approval differs from this request")
            return existing
        ready_count = sum(
            int(item.get("seed_count") or 0)
            for item in active_reserve(
                service_dir,
                authorization=authorization,
                accounting=accounting,
            )
        )
        capacity = (
            ready_count
            + pending_reserved_capacity(
                service_dir,
                authorization=authorization,
                accounting=accounting,
            )
            + int(packet["requested_seed_count"])
        )
        if capacity > int(authorization["limits"]["ready_seed_target"]):
            raise ServiceError(
                "queued packet would reserve capacity above ten ready seeds"
            )
        write_once(queue_path, entry)
    return entry


def archive_stop_request(service_dir: Path) -> None:
    stop_path = service_dir / "stop.request.json"
    if not stop_path.exists():
        return
    history = service_dir / "history"
    history.mkdir(parents=True, exist_ok=True)
    destination = history / f"stop-{time.time_ns()}.json"
    os.replace(stop_path, destination)


def launch_daemon(
    service_dir: Path,
    *,
    expected_authorization: dict[str, str] | None = None,
) -> dict[str, Any]:
    existing = daemon_receipt(service_dir)
    if existing is not None:
        if existing.get("implementation_sha256") != sha256(Path(__file__).resolve()):
            raise ServiceError(
                "live daemon implementation differs from the current script; "
                "stop it explicitly before starting an approved packet"
            )
        if existing.get("supervisor_ref") != f"systemd-user:{SYSTEMD_UNIT_NAME}":
            raise ServiceError(
                "live daemon is not owned by the persistent v2 user-systemd supervisor"
            )
        if (
            expected_authorization is not None
            and existing.get("standing_authorization") != expected_authorization
        ):
            raise ServiceError(
                "live daemon is bound to another standing authorization"
            )
        return existing
    archive_stop_request(service_dir)
    service_id = str(uuid.uuid4())
    service_dir.mkdir(parents=True, exist_ok=True)
    manager = subprocess.run(
        ["systemctl", "--user", "is-system-running"],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if manager.stdout.strip() not in {"running", "degraded"}:
        raise ServiceError(
            "the user service manager is unavailable; refusing a chat-bound fallback"
        )
    unit_dir = service_dir / "systemd"
    unit_dir.mkdir(parents=True, exist_ok=True)
    unit_path = unit_dir / SYSTEMD_UNIT_NAME
    unit_text = "\n".join(
        [
            "[Unit]",
            "Description=Bounded continuous Erdos-Szekeres idea generator",
            "After=network-online.target",
            "Wants=network-online.target",
            "StartLimitIntervalSec=300",
            "StartLimitBurst=3",
            "",
            "[Service]",
            "Type=simple",
            f"WorkingDirectory={ROOT}",
            "KillMode=control-group",
            "MemoryMax=5G",
            "CPUQuota=200%",
            "TasksMax=128",
            "Restart=on-failure",
            "RestartSec=15",
            "Environment=PYTHONUNBUFFERED=1",
            (
                f"ExecStart={sys.executable} {Path(__file__).resolve()} serve "
                f"--service-dir {service_dir} --service-id {service_id} "
                f"--supervisor-ref systemd-user:{SYSTEMD_UNIT_NAME}"
            ),
            f"StandardOutput=append:{service_dir / 'service.log'}",
            f"StandardError=append:{service_dir / 'service.log'}",
            "",
            "[Install]",
            "WantedBy=default.target",
            "",
        ]
    )
    temporary = unit_path.with_name(f".{unit_path.name}.tmp-{os.getpid()}")
    temporary.write_text(unit_text, encoding="utf-8")
    os.replace(temporary, unit_path)
    linked = subprocess.run(
        ["systemctl", "--user", "link", str(unit_path)],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if linked.returncode != 0 and "already exists" not in linked.stderr:
        raise ServiceError(f"systemd unit link failed: {linked.stderr.strip()}")
    subprocess.run(
        ["systemctl", "--user", "daemon-reload"],
        cwd=ROOT,
        check=True,
        text=True,
        capture_output=True,
    )
    subprocess.run(
        ["systemctl", "--user", "reset-failed", SYSTEMD_UNIT_NAME],
        cwd=ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    launched = subprocess.run(
        ["systemctl", "--user", "enable", "--now", SYSTEMD_UNIT_NAME],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if launched.returncode != 0:
        raise ServiceError(f"systemd supervisor launch failed: {launched.stderr.strip()}")
    deadline = time.monotonic() + 8
    while time.monotonic() < deadline:
        receipt = daemon_receipt(service_dir)
        if receipt is not None and receipt.get("service_id") == service_id:
            if (
                expected_authorization is not None
                and receipt.get("standing_authorization")
                != expected_authorization
            ):
                raise ServiceError(
                    "started daemon published another standing authorization"
                )
            return receipt
        time.sleep(0.1)
    raise ServiceError("daemon did not publish a live PID receipt")


def packet_path_argument(service_dir: Path, value: Path) -> Path:
    path = value if value.is_absolute() else ROOT / value
    path = path.resolve()
    try:
        path.relative_to(service_dir.resolve())
    except ValueError as exc:
        raise ServiceError("packet must be inside the selected service directory") from exc
    return path


def run_artifact_path(value: Path) -> Path:
    path = value if value.is_absolute() else ROOT / value
    path = path.resolve()
    try:
        path.relative_to(RUNS_ROOT)
    except ValueError as exc:
        raise ServiceError("investigation artifact must be under runs/agents") from exc
    return path


def command_enqueue(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    packet_path = packet_path_argument(service_dir, args.packet)
    entry = queue_packet(
        service_dir,
        packet_path,
        args.packet_sha256,
        args.prompt_sha256,
        args.task_sha256,
        args.approval_ref,
    )
    print(json.dumps(entry, indent=2, sort_keys=True))
    return 0


def command_start(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    authorization_path = packet_path_argument(service_dir, args.authorization)
    with locked_service_state(service_dir):
        active_path, authorization = active_standing_authorization(service_dir)
        if authorization_path != active_path:
            raise ServiceError("start must use the service's active standing authorization")
        if sha256(authorization_path) != args.authorization_sha256:
            raise ServiceError("standing authorization hash does not match")
        active_receipt = file_receipt(active_path)
        accounting_transition_preflight(service_dir, authorization)
        for entry_path in pending_queue(service_dir):
            _entry, _packet_path, packet = authenticate_queue(
                entry_path, mode="current"
            )
            if packet.get("standing_authorization") != active_receipt:
                raise ServiceError(
                    "pending queue contains an inactive authorization; resolve it before start"
                )
        validate_accounting_chain(service_dir, authorization)
        daemon = launch_daemon(
            service_dir, expected_authorization=active_receipt
        )
        if daemon.get("standing_authorization") != active_receipt:
            raise ServiceError("daemon start did not bind the requested authorization")
    print(
        json.dumps(
            {
                "daemon": daemon,
                "standing_authorization": file_receipt(authorization_path),
                "generation_modes": authorization["generation_modes"],
                "limits": authorization["limits"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


def stop_batch(packet: dict[str, Any], terminal: str) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "campaign_id": packet["campaign_id"],
        "generation_mode": packet["generation_mode"],
        "requested_seed_count": packet.get("requested_seed_count", 5),
        "snapshot": packet["snapshot"],
        "terminal": terminal,
        "claim_level": "proposal",
        "seeds": [],
        "generation_metrics": {
            "private_seed_count": 0,
            "literal_duplicates_removed": 0,
            "target_equivalent_removed": 0,
            "malformed_removed": 0,
            "tool_calls": None,
            "source_requests": None,
            "input_tokens": None,
            "output_tokens": None,
            "provider_cost_usd": None,
        },
    }


def seed_claim_path(service_dir: Path, campaign_id: str, seed_id: str) -> Path:
    return service_state_path(
        service_dir,
        "claims",
        safe_leaf_id(campaign_id, "campaign_id"),
        f"{safe_leaf_id(seed_id, 'seed_id')}.json",
    )


def seed_feedback_path(service_dir: Path, campaign_id: str, seed_id: str) -> Path:
    return service_state_path(
        service_dir,
        "feedback",
        safe_leaf_id(campaign_id, "campaign_id"),
        f"{safe_leaf_id(seed_id, 'seed_id')}.json",
    )


def validate_legacy_consumption(
    path: Path, campaign_id: str, seed_path: Path
) -> dict[str, Any]:
    value = read_json(path, "legacy batch-consumption receipt")
    expected = {
        "schema_version",
        "protocol",
        "campaign_id",
        "consumed_at",
        "seed_batch",
        "reconciliation_ref",
        "meaning",
    }
    if set(value) != expected or value.get("schema_version") != 1:
        raise ServiceError("legacy batch-consumption receipt is malformed")
    if value.get("protocol") not in {
        "continuous-idea-generator-v1",
        "continuous-idea-generator-v2",
        "continuous-idea-generator-v2.1",
    }:
        raise ServiceError("legacy consumption uses an unsupported protocol")
    if value.get("campaign_id") != campaign_id:
        raise ServiceError("legacy consumption campaign identity differs")
    if value.get("seed_batch") != file_receipt(seed_path):
        raise ServiceError("legacy consumption does not authenticate its seed batch")
    if not isinstance(value.get("reconciliation_ref"), str) or not value[
        "reconciliation_ref"
    ].strip():
        raise ServiceError("legacy consumption reconciliation reference is missing")
    return value


def validate_seed_claim(
    path: Path,
    *,
    campaign_id: str,
    seed_id: str,
    seed_path: Path,
) -> dict[str, Any]:
    value = read_json(path, "seed claim")
    expected = {
        "schema_version",
        "protocol",
        "claim_id",
        "claimed_at",
        "seed",
        "development_brief",
        "task_packet",
        "first_test_validation",
        "meaning",
    }
    if set(value) != expected or value.get("schema_version") != 3:
        raise ServiceError("seed claim has an unexpected closed contract")
    if value.get("protocol") != CLAIM_PROTOCOL:
        raise ServiceError("seed claim protocol differs")
    identity = value.get("seed")
    expected_identity = {
        "campaign_id": campaign_id,
        "seed_id": seed_id,
        "seed_batch": file_receipt(seed_path),
    }
    if identity != expected_identity:
        raise ServiceError("seed claim identity or seed-batch hash differs")
    if value.get("claim_id") != f"{campaign_id}:{seed_id}":
        raise ServiceError("seed claim_id differs from its composite identity")
    brief_path = authenticate_receipt(
        value.get("development_brief"), "claimed development brief"
    )
    brief = read_json(brief_path, "claimed development brief")
    task_path = authenticate_receipt(
        value.get("task_packet"), "claimed first-test task packet"
    )
    task = read_json(task_path, "claimed first-test task packet")
    campaign.validate_brief(
        brief,
        brief_path=brief_path,
        task_packet=task,
        authenticate=True,
    )
    validation = value.get("first_test_validation")
    execution = task.get("first_test_execution") or {}
    expected_validation = {
        "protocol": "ticket-0119-first-test-validation-v1",
        "approval_ref": campaign.FIRST_TEST_APPROVAL_REF,
        "task_packet": file_receipt(task_path),
        "execution_contract_id": execution.get("contract_id"),
        "guard_component": execution.get("guard_component"),
        "budget": task.get("budget"),
        "write_paths": (task.get("ownership") or {}).get("write_paths"),
        "claims_allowed": task.get("claims_allowed"),
        "decision": "pass",
    }
    if validation != expected_validation:
        raise ServiceError("seed claim first-test validation differs from its task")
    brief_seed = brief.get("seed") or {}
    if (
        brief_seed.get("batch_path") != repo_relative(seed_path)
        or brief_seed.get("batch_sha256") != sha256(seed_path)
        or brief_seed.get("seed_id") != seed_id
    ):
        raise ServiceError("claimed development brief names another seed")
    return value


def validate_tagged_learning(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != {
        "status",
        "text",
        "subject_contract_id",
        "evidence_event_ids",
        "learning_claim_id",
    }:
        raise ServiceError(
            f"{label} has an unexpected closed tagged-learning contract"
        )
    status = value.get("status")
    text_value = value.get("text")
    event_ids = value.get("evidence_event_ids")
    learning_claim_id = value.get("learning_claim_id")
    if status not in {"verified", "inferred", "not-established"}:
        raise ServiceError(f"{label} has an invalid epistemic status")
    if (
        not isinstance(event_ids, list)
        or len(event_ids) != len(set(event_ids))
        or any(
            not isinstance(event_id, str)
            or re.fullmatch(r"[0-9a-f]{64}", event_id) is None
            for event_id in event_ids
        )
    ):
        raise ServiceError(f"{label} evidence-event identities are malformed")
    if status == "not-established":
        if (
            text_value is not None
            or value.get("subject_contract_id") is not None
            or event_ids
            or learning_claim_id is not None
        ):
            raise ServiceError(
                f"{label} not-established fields must be null/empty"
            )
    elif not isinstance(text_value, str) or not text_value.strip():
        raise ServiceError(f"{label} established text must be nonempty")
    subject = value.get("subject_contract_id")
    if status == "verified" and (
        not isinstance(subject, str) or re.fullmatch(r"[0-9a-f]{64}", subject) is None
    ):
        raise ServiceError(f"{label} verified learning lacks a contract identity")
    if status == "inferred" and subject is not None and (
        not isinstance(subject, str) or re.fullmatch(r"[0-9a-f]{64}", subject) is None
    ):
        raise ServiceError(f"{label} inferred subject contract is malformed")
    if status == "verified" and (
        len(event_ids) != 1
        or not isinstance(learning_claim_id, str)
        or re.fullmatch(r"[0-9a-f]{64}", learning_claim_id) is None
    ):
        raise ServiceError(
            f"{label} verified learning lacks one event and learning-claim ID"
        )
    if status == "inferred" and (event_ids or learning_claim_id is not None):
        raise ServiceError(
            f"{label} inferred learning cannot claim verifier evidence"
        )
    return value


def validate_failure_memory_ref(
    value: Any,
    *,
    selected_events: list[dict[str, Any]],
    evidence_level: str,
    damage_scope: str,
    primary_contract_id: str,
    model_contract_id: str,
    scope_contract_id: str,
    failing_feature: dict[str, Any],
    strongest_supported_statement: dict[str, Any],
    representation_blindness: dict[str, Any],
    anti_duplication_warning: dict[str, Any],
    expected_stable_family: str,
    expected_model_tier: str,
    expected_home_record_ids: set[str],
) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != {
        "record_path",
        "record_anchor",
        "genome_id",
        "genome_core_sha256",
        "terminal_artifact",
    }:
        raise ServiceError("failure-memory reference must be a closed anchored receipt")
    record_path = value.get("record_path")
    if not isinstance(record_path, str):
        raise ServiceError("failure-memory record path is missing")
    path = (ROOT / record_path).resolve()
    allowed = (
        path == (ROOT / "docs/wayfinder/frontier-portfolio.md").resolve()
        or path == (ROOT / "runs/idea-factory/idea-ledger.md").resolve()
        or (
            path.parent == (ROOT / "docs/wayfinder/tickets").resolve()
            and path.suffix == ".md"
        )
    )
    if not allowed or not path.is_file():
        raise ServiceError(
            "failure-memory reference must name an existing route record"
        )
    anchor = value.get("record_anchor")
    if not isinstance(anchor, str) or not anchor.strip():
        raise ServiceError("failure-memory anchor is missing")
    text_value = path.read_text(encoding="utf-8")
    lines = text_value.splitlines(keepends=True)
    anchor_indices = [
        index for index, line in enumerate(lines) if line.rstrip("\r\n") == anchor
    ]
    heading = re.fullmatch(r"(#{1,6})\s+.+", anchor)
    if len(anchor_indices) != 1 or heading is None:
        raise ServiceError("failure-memory record anchor must be one exact heading")
    start_line = anchor_indices[0]
    level = len(heading.group(1))
    end_line = len(lines)
    for index in range(start_line + 1, len(lines)):
        match = re.match(r"^(#{1,6})\s+", lines[index])
        if match is not None and len(match.group(1)) <= level:
            end_line = index
            break
    record_span = "".join(lines[start_line:end_line])
    genome_id = safe_leaf_id(value.get("genome_id"), "failure genome_id")
    begin = f"<!-- WAYFINDER-FAILURE-GENOME-V2-BEGIN {genome_id} -->"
    end = f"<!-- WAYFINDER-FAILURE-GENOME-V2-END {genome_id} -->"
    eligible_paths = [ROOT / "docs/wayfinder/frontier-portfolio.md"]
    idea_ledger = ROOT / "runs/idea-factory/idea-ledger.md"
    if idea_ledger.is_file():
        eligible_paths.append(idea_ledger)
    eligible_paths.extend(
        sorted(
            candidate
            for candidate in (ROOT / "docs/wayfinder/tickets").glob("*.md")
            if candidate.is_file()
        )
    )
    begin_homes = []
    end_homes = []
    for candidate in eligible_paths:
        contents = candidate.read_text(encoding="utf-8")
        begin_homes.extend([candidate] * contents.count(begin))
        end_homes.extend([candidate] * contents.count(end))
    if begin_homes != [path] or end_homes != [path]:
        raise ServiceError(
            "failure genome must have exactly one bounded canonical home"
        )
    pattern = re.compile(
        re.escape(begin)
        + r"\s*```json\s*(\{.*?\})\s*```\s*"
        + re.escape(end),
        re.DOTALL,
    )
    matches = pattern.findall(record_span)
    if len(matches) != 1:
        raise ServiceError("failure genome block is absent from its record span")
    try:
        core = json.loads(matches[0])
    except json.JSONDecodeError as exc:
        raise ServiceError(f"failure genome core is invalid JSON: {exc}") from exc
    if not isinstance(core, dict) or set(core) != {
        "schema_version",
        "genome_id",
        "home",
        "stable_card_family",
        "model_tier",
        "model_contract_id",
        "scope",
        "terminal",
        "evidence_level",
        "damage_scope",
        "verified_failing_feature",
        "strongest_supported_statement",
        "tagged_learning",
    }:
        raise ServiceError("failure genome core has an unexpected contract")
    if (
        core.get("schema_version") != 2
        or core.get("genome_id") != genome_id
        or value.get("genome_core_sha256") != canonical_json_sha256(core)
    ):
        raise ServiceError("failure genome identity or immutable core digest differs")
    home = core.get("home")
    if not isinstance(home, dict) or set(home) != {
        "kind",
        "record_path",
        "record_anchor",
        "record_id",
    }:
        raise ServiceError("failure genome home is malformed")
    expected_kind = (
        "frontier-portfolio"
        if path == (ROOT / "docs/wayfinder/frontier-portfolio.md").resolve()
        else "idea-ledger"
        if path == idea_ledger.resolve()
        else "decision-ticket"
    )
    if (
        home.get("kind") != expected_kind
        or home.get("record_path") != record_path
        or home.get("record_anchor") != anchor
        or not isinstance(home.get("record_id"), str)
        or not home["record_id"].strip()
        or (
            bool(expected_home_record_ids)
            and home.get("record_id") not in expected_home_record_ids
        )
        or core.get("stable_card_family") != expected_stable_family
        or core.get("model_tier") != expected_model_tier
        or core.get("model_contract_id") != model_contract_id
    ):
        raise ServiceError("failure genome home, family, or model differs")
    scope = core.get("scope")
    if not isinstance(scope, dict) or set(scope) != {
        "scope_contract_id",
        "scope_ceiling",
        "mathematical_scope",
    }:
        raise ServiceError("failure genome scope is malformed")
    if (
        scope.get("scope_contract_id") != scope_contract_id
        or scope.get("scope_ceiling") != damage_scope
        or not isinstance(scope.get("mathematical_scope"), str)
        or not scope["mathematical_scope"].strip()
    ):
        raise ServiceError("failure genome scope differs from admitted evidence")
    terminal_path = authenticate_receipt(
        value.get("terminal_artifact"), "failure-memory terminal artifact"
    )
    artifact_receipt = file_receipt(terminal_path)
    selected_artifacts = {
        canonical_json_sha256(event.get("artifact")): event.get("artifact")
        for event in selected_events
        if isinstance(event, dict) and isinstance(event.get("artifact"), dict)
    }
    if canonical_json_sha256(artifact_receipt) not in selected_artifacts:
        raise ServiceError(
            "failure-memory terminal artifact is not selected falsifier evidence"
        )
    if not any(
        event.get("artifact") == artifact_receipt
        and event.get("kind") in {"exact_falsifier", "claim_refuted"}
        for event in selected_events
        if isinstance(event, dict)
    ):
        raise ServiceError(
            "failure-memory terminal artifact is not exact falsifier/refutation evidence"
        )
    terminal = core.get("terminal")
    selected_event_ids = {
        event.get("event_id")
        for event in selected_events
        if isinstance(event, dict)
    }
    if not isinstance(terminal, dict) or set(terminal) != {
        "kind",
        "event_id",
        "artifact",
    } or (
        terminal.get("kind") != "GATE_FALSIFIER"
        or terminal.get("event_id") not in selected_event_ids
        or terminal.get("artifact") != artifact_receipt
        or core.get("evidence_level") != evidence_level
        or core.get("damage_scope") != damage_scope
    ):
        raise ServiceError("failure genome terminal or evidence fields differ")
    for key, learned in (
        ("verified_failing_feature", failing_feature),
        ("strongest_supported_statement", strongest_supported_statement),
    ):
        genome_learning = core.get(key)
        if not isinstance(genome_learning, dict) or set(genome_learning) != {
            "subject_contract_id",
            "text",
        } or (
            genome_learning.get("subject_contract_id")
            != learned.get("subject_contract_id")
            or genome_learning.get("text") != learned.get("text")
            or genome_learning.get("subject_contract_id")
            not in {primary_contract_id, *{
                str(event.get("binding", {}).get("subject_contract_id"))
                for event in selected_events
                if isinstance(event, dict)
            }}
        ):
            raise ServiceError(f"failure genome {key} differs from feedback")
    tagged = core.get("tagged_learning")
    expected_tagged = {
        "representation_blindness",
        "candidate_discriminator",
        "mutation_directions",
        "anti_duplication_warning",
        "cheapest_falsifier",
    }
    if not isinstance(tagged, dict) or set(tagged) != expected_tagged:
        raise ServiceError("failure genome tagged learning is malformed")
    for key in expected_tagged:
        validate_tagged_learning(tagged[key], f"failure genome {key}")
    if tagged.get("representation_blindness") != representation_blindness:
        raise ServiceError(
            "failure genome representation blindness differs from feedback"
        )
    if tagged.get("anti_duplication_warning") != anti_duplication_warning:
        raise ServiceError(
            "failure genome anti-duplication warning differs from feedback"
        )
    for key in ("candidate_discriminator", "mutation_directions", "cheapest_falsifier"):
        if tagged[key].get("status") == "verified":
            raise ServiceError(
                f"failure genome {key} cannot become verified without a separate learning contract"
            )
    return value


def validate_root_reconciliation(
    path: Path,
    *,
    feedback_id: str,
    reconciled_at: str,
    claim_path: Path,
    development_receipt_path: Path,
    admitted_feedback_core_sha256: str,
    brief: dict[str, Any],
) -> dict[str, Any]:
    value = read_json(path, "root reconciliation")
    if not isinstance(value, dict) or set(value) != {
        "schema_version",
        "protocol",
        "feedback_id",
        "reconciled_at",
        "seed_claim",
        "development_receipt",
        "admitted_feedback_core_sha256",
        "standing_first_test",
        "decision",
    }:
        raise ServiceError("root reconciliation has an unexpected closed contract")
    if (
        value.get("schema_version") != 2
        or value.get("protocol") != "research-root-reconciliation-v2"
        or value.get("feedback_id") != feedback_id
        or value.get("reconciled_at") != reconciled_at
        or parse_timestamp(value.get("reconciled_at")) is None
        or value.get("seed_claim") != file_receipt(claim_path)
        or value.get("development_receipt")
        != file_receipt(development_receipt_path)
        or value.get("admitted_feedback_core_sha256")
        != admitted_feedback_core_sha256
        or value.get("standing_first_test") != brief.get("authority")
        or value.get("decision") != "admit-immutable-feedback"
    ):
        raise ServiceError("root reconciliation does not bind the admitted feedback core")
    return value


def validate_investigation_feedback(
    path: Path,
    *,
    claim: dict[str, Any],
    campaign_id: str,
    seed_id: str,
    seed_path: Path,
) -> dict[str, Any]:
    value = read_json(path, "investigation feedback")
    expected = {
        "schema_version",
        "feedback_id",
        "seed",
        "investigation",
        "root_admission",
        "evidence",
        "proof_distance",
        "learned",
        "next_discriminating_test",
        "canonical_failure_memory_ref",
        "claim_candidate",
        "queue_disposition",
    }
    if set(value) != expected or value.get("schema_version") != 3:
        raise ServiceError("investigation feedback has an unexpected closed contract")
    feedback_id = f"{campaign_id}:{seed_id}"
    if value.get("feedback_id") != feedback_id:
        raise ServiceError("feedback_id differs from its composite seed identity")
    expected_seed = {
        "registry_id": f"continuous:{campaign_id}:{seed_id}",
        "campaign_id": campaign_id,
        "seed_id": seed_id,
        "seed_batch": file_receipt(seed_path),
    }
    if value.get("seed") != expected_seed:
        raise ServiceError("feedback seed identity or seed-batch hash differs")

    investigation = value.get("investigation")
    if not isinstance(investigation, dict) or set(investigation) != {
        "brief_id",
        "brief_sha256",
        "development_receipt",
        "terminal",
    }:
        raise ServiceError("feedback investigation contract is malformed")
    brief_path = authenticate_receipt(
        claim.get("development_brief"), "feedback development brief"
    )
    if investigation.get("brief_sha256") != sha256(brief_path):
        raise ServiceError("feedback brief hash differs from the claim")
    brief = read_json(brief_path, "feedback development brief")
    if investigation.get("brief_id") != brief.get("brief_id"):
        raise ServiceError("feedback brief identity differs from the claim")
    receipt_path = authenticate_receipt(
        investigation.get("development_receipt"), "development receipt"
    )
    receipt = read_json(receipt_path, "development receipt")
    task_path = authenticate_receipt(
        claim.get("task_packet"), "feedback first-test task packet"
    )
    task = read_json(task_path, "feedback first-test task packet")
    campaign.validate_development_receipt(
        receipt,
        brief_path=brief_path,
        task_packet=task,
        authenticate=True,
    )
    terminal = investigation.get("terminal")
    if terminal != receipt.get("terminal"):
        raise ServiceError("feedback terminal differs from development receipt")

    root_admission = value.get("root_admission")
    if not isinstance(root_admission, dict) or set(root_admission) != {
        "reconciled_at",
        "admitted_feedback_core_sha256",
        "reconciliation",
    }:
        raise ServiceError("feedback root-admission contract is malformed")
    if not isinstance(root_admission.get("reconciled_at"), str):
        raise ServiceError("feedback reconciliation timestamp is missing")
    reconciliation_path = authenticate_receipt(
        root_admission.get("reconciliation"), "root reconciliation"
    )

    evidence = value.get("evidence")
    if not isinstance(evidence, dict) or set(evidence) != {
        "level",
        "event_ids",
        "contract_id",
        "model_contract_id",
        "scope_contract_id",
        "damage_scope",
    }:
        raise ServiceError("feedback evidence contract is malformed")
    evidence_level = evidence.get("level")
    if evidence_level not in {
        "proposal",
        "checked_computation",
        "operational_stop",
    }:
        raise ServiceError("feedback evidence level is invalid")
    event_ids = evidence.get("event_ids")
    events = receipt.get("evidence_events") or []
    events_by_id = {
        event.get("event_id"): event
        for event in events
        if isinstance(event, dict) and isinstance(event.get("event_id"), str)
    }
    if (
        not isinstance(event_ids, list)
        or any(event_id not in events_by_id for event_id in event_ids)
        or len(event_ids) != len(set(event_ids))
    ):
        raise ServiceError("feedback evidence event IDs are invalid")
    selected_events = [events_by_id[event_id] for event_id in event_ids]
    primary_events: list[dict[str, Any]] = []
    if terminal == "GATE_POSITIVE_SIGNAL":
        primary_events = [
            event
            for event in events
            if event.get("gate_branch") == "live"
            and event.get("binding", {}).get("polarity") == "supports"
            and event.get("binding", {}).get("subject") == "primary_claim"
        ]
    elif terminal == "GATE_FALSIFIER":
        primary_events = [
            event
            for event in events
            if event.get("gate_branch") == "kill"
            and event.get("binding", {}).get("polarity") == "refutes"
            and event.get("kind") in {"exact_falsifier", "claim_refuted"}
            and event.get("claim_level") != "proposal"
        ]
    elif terminal == "NO_DISCRIMINATING_SIGNAL":
        primary_events = [
            event
            for event in events
            if event.get("gate_branch") == "no_signal"
            and event.get("binding", {}).get("polarity") == "observes"
        ]
    if terminal != "OPERATIONAL_STOP":
        if len(primary_events) != 1:
            raise ServiceError(
                "feedback development terminal lacks one exact primary event"
            )
        if primary_events[0].get("event_id") not in event_ids:
            raise ServiceError("feedback omits its terminal-defining primary event")
    if evidence_level != "operational_stop" and not selected_events:
        raise ServiceError("mathematical feedback must select authenticated evidence")
    if evidence_level == "checked_computation" and not any(
        event.get("claim_level") == "computational_evidence"
        and event.get("kind") != "proposal_only"
        for event in selected_events
        if isinstance(event, dict)
    ):
        raise ServiceError(
            "checked-computation feedback must select non-proposal checked evidence"
        )
    if evidence_level == "operational_stop" and event_ids:
        raise ServiceError("operational feedback cannot select mathematical evidence")
    contract = brief.get("evidence_contract") or {}
    scope_contract = contract.get("scope") or {}
    if (
        evidence.get("contract_id") != contract.get("contract_id")
        or evidence.get("model_contract_id") != contract.get("model_contract_id")
        or evidence.get("scope_contract_id")
        != scope_contract.get("scope_contract_id")
        or any(
            event.get("binding", {}).get("primary_contract_id")
            != contract.get("contract_id")
            or event.get("binding", {}).get("model_contract_id")
            != contract.get("model_contract_id")
            or event.get("binding", {}).get("scope_contract_id")
            != scope_contract.get("scope_contract_id")
            for event in selected_events
        )
    ):
        raise ServiceError("feedback evidence is rebound from its frozen contract")
    damage_scope = evidence.get("damage_scope")
    if damage_scope not in {
        "candidate-local",
        "subfamily",
        "operational-only",
    }:
        raise ServiceError("feedback damage scope is invalid")
    if evidence_level == "operational_stop":
        if terminal != "OPERATIONAL_STOP" or damage_scope != "operational-only":
            raise ServiceError(
                "operational evidence requires an operational terminal and scope"
            )
    elif damage_scope == "operational-only":
        raise ServiceError("mathematical feedback cannot use operational-only scope")
    elif evidence_level == "proposal" and damage_scope != "candidate-local":
        raise ServiceError("proposal feedback is bounded to candidate-local scope")
    elif terminal == "GATE_FALSIFIER":
        if damage_scope not in {"candidate-local", "subfamily"}:
            raise ServiceError(
                "one seed falsifier cannot establish architecture- or mechanism-wide damage"
            )
    elif damage_scope != "candidate-local":
        raise ServiceError(
            "non-falsifier seed feedback is bounded to candidate-local scope"
        )
    brief_damage_ceiling = scope_contract.get("ceiling")
    if brief_damage_ceiling not in {"candidate-local", "subfamily"}:
        raise ServiceError("claimed brief lacks a valid damage-scope ceiling")
    if damage_scope == "subfamily" and brief_damage_ceiling != "subfamily":
        raise ServiceError("feedback exceeds the frozen brief damage-scope ceiling")
    if damage_scope == "subfamily" and not any(
        event.get("gate_branch") == "kill"
        and event.get("kind") in {"exact_falsifier", "claim_refuted"}
        and event.get("binding", {}).get("subject") == "shared_premise"
        and event.get("binding", {}).get("subject_contract_id")
        == (scope_contract.get("subfamily") or {}).get(
            "shared_premise_contract_id"
        )
        and event.get("binding", {}).get("damage_scope_reached") == "subfamily"
        for event in selected_events
    ):
        raise ServiceError(
            "subfamily feedback lacks exact shared-premise coverage evidence"
        )

    proof = value.get("proof_distance")
    if not isinstance(proof, dict) or set(proof) != {
        "net_proof_movement",
        "forward_reduction_receipt",
        "difficulty_displaced",
        "demonstrably_smaller",
        "counterfactual_test",
        "planning_consequence",
    }:
        raise ServiceError("feedback proof-distance contract is malformed")
    movement = proof.get("net_proof_movement")
    if movement not in {"neutral", "backward"}:
        raise ServiceError("feedback net proof movement is invalid")
    if not isinstance(proof.get("demonstrably_smaller"), bool):
        raise ServiceError("feedback demonstrably_smaller must be boolean")
    for key in ("difficulty_displaced", "counterfactual_test"):
        if not isinstance(proof.get(key), str) or not proof[key].strip():
            raise ServiceError(f"feedback proof-distance {key} is missing")
    if proof.get("planning_consequence") not in {
        "promote",
        "retain",
        "demote",
        "suspend",
        "expire",
    }:
        raise ServiceError("feedback planning consequence is invalid")
    if proof.get("forward_reduction_receipt") is not None:
        raise ServiceError(
            "Ticket-0119 standing first tests cannot claim forward proof movement"
        )

    learned = value.get("learned")
    learned_keys = {
        "failing_feature",
        "strongest_supported_statement",
        "surviving_structure",
        "representation_blindness",
        "anti_duplication_warning",
    }
    if not isinstance(learned, dict) or set(learned) != learned_keys:
        raise ServiceError("feedback learned contract is malformed")
    tagged = {
        key: validate_tagged_learning(learned[key], f"learned.{key}")
        for key in learned_keys
    }
    allowed_subject_ids = {str(contract.get("contract_id"))}
    subfamily = scope_contract.get("subfamily")
    if isinstance(subfamily, dict):
        allowed_subject_ids.add(str(subfamily.get("shared_premise_contract_id")))
    if any(
        item["status"] != "not-established"
        and item.get("subject_contract_id") is not None
        and item.get("subject_contract_id") not in allowed_subject_ids
        for item in tagged.values()
    ):
        raise ServiceError("feedback learning is rebound from its contract")
    for role in (
        "surviving_structure",
        "representation_blindness",
        "anti_duplication_warning",
    ):
        if tagged[role]["status"] == "verified":
            raise ServiceError(f"learned.{role} cannot be verifier-established")
    for role in ("failing_feature", "strongest_supported_statement"):
        learned_item = tagged[role]
        if learned_item["status"] != "verified":
            continue
        event_id = learned_item["evidence_event_ids"][0]
        if event_id not in event_ids:
            raise ServiceError(
                f"verified learned.{role} cites an unselected evidence event"
            )
        event = events_by_id[event_id]
        verification_path = authenticate_receipt(
            event.get("verification_receipt"),
            f"verified learned.{role} event verification",
        )
        verification = read_json(
            verification_path, f"verified learned.{role} event verification"
        )
        normalized = verification.get("normalized_result")
        verified_learning = (
            normalized.get("verified_learning")
            if isinstance(normalized, dict)
            else None
        )
        verifier_claim = (
            verified_learning.get(role)
            if isinstance(verified_learning, dict)
            else None
        )
        expected_claim = {
            "learning_claim_id": learned_item["learning_claim_id"],
            "text": learned_item["text"],
            "subject_contract_id": learned_item["subject_contract_id"],
        }
        if verifier_claim != expected_claim:
            raise ServiceError(
                f"verified learned.{role} differs from guarded normalized evidence"
            )
    if evidence_level in {"proposal", "operational_stop"} and any(
        item["status"] == "verified" for item in tagged.values()
    ):
        raise ServiceError(
            "proposal or operational evidence cannot verify mathematical learning"
        )
    if terminal != "GATE_FALSIFIER" and any(
        tagged[key]["status"] == "verified"
        for key in ("failing_feature", "representation_blindness")
    ):
        raise ServiceError(
            "verified failure learning requires an admitted falsifier terminal"
        )

    next_test = value.get("next_discriminating_test")
    if not isinstance(next_test, dict) or set(next_test) != {
        "status",
        "question",
        "changed_mathematical_information",
        "ceiling_minutes",
        "stop_signal",
    }:
        raise ServiceError("feedback next-test contract is malformed")
    if next_test.get("status") == "not-established":
        if any(next_test.get(key) is not None for key in (
            "question",
            "changed_mathematical_information",
            "ceiling_minutes",
            "stop_signal",
        )):
            raise ServiceError("not-established next test must have null details")
    elif next_test.get("status") == "inferred":
        if not isinstance(next_test.get("ceiling_minutes"), int) or not 1 <= int(
            next_test["ceiling_minutes"]
        ) <= 30:
            raise ServiceError("inferred next test must be bounded to 30 minutes")
        for key in ("question", "changed_mathematical_information", "stop_signal"):
            if not isinstance(next_test.get(key), str) or not next_test[key].strip():
                raise ServiceError(f"inferred next test {key} is missing")
    else:
        raise ServiceError("feedback next-test status is invalid")

    service_dir = seed_path.parents[2]
    claim_path = seed_claim_path(service_dir, campaign_id, seed_id)
    failure_ref = value.get("canonical_failure_memory_ref")
    if failure_ref is not None:
        seed_batch = read_json(seed_path, "feedback seed batch")
        seed_matches = [
            seed
            for seed in seed_batch.get("seeds", [])
            if isinstance(seed, dict) and seed.get("seed_id") == seed_id
        ]
        if len(seed_matches) != 1:
            raise ServiceError("feedback seed provenance is ambiguous")
        selected_seed = seed_matches[0]
        lineage = selected_seed.get("lineage") or {}
        controls = selected_seed.get("nearest_controls") or []
        expected_home_ids = {
            str(item)
            for item in lineage.get("parent_refs", [])
            if isinstance(item, str) and item.strip()
        }
        expected_home_ids.update(
            str(item.get("ref"))
            for item in controls
            if isinstance(item, dict)
            and isinstance(item.get("ref"), str)
            and item["ref"].strip()
        )
        validate_failure_memory_ref(
            failure_ref,
            selected_events=selected_events,
            evidence_level=str(evidence_level),
            damage_scope=str(damage_scope),
            primary_contract_id=str(contract.get("contract_id")),
            model_contract_id=str(contract.get("model_contract_id")),
            scope_contract_id=str(scope_contract.get("scope_contract_id")),
            failing_feature=tagged["failing_feature"],
            strongest_supported_statement=tagged[
                "strongest_supported_statement"
            ],
            representation_blindness=tagged["representation_blindness"],
            anti_duplication_warning=tagged["anti_duplication_warning"],
            expected_stable_family=str(
                (selected_seed.get("mechanism") or {}).get("family_hint")
            ),
            expected_model_tier=str(
                (brief.get("evidence_contract") or {})
                .get("model", {})
                .get("working_tier")
            ),
            expected_home_record_ids=expected_home_ids,
        )
    if terminal == "GATE_FALSIFIER":
        if (
            evidence_level in {"proposal", "operational_stop"}
            or damage_scope == "operational-only"
            or tagged["failing_feature"]["status"] != "verified"
            or tagged["strongest_supported_statement"]["status"] != "verified"
            or failure_ref is None
        ):
            raise ServiceError(
                "falsifier feedback lacks checked evidence plus verifier-bound negative memory"
            )
    if terminal == "NO_DISCRIMINATING_SIGNAL" and tagged["failing_feature"][
        "status"
    ] == "verified":
        raise ServiceError("no-signal feedback cannot verify a failing feature")
    if terminal != "GATE_FALSIFIER" and failure_ref is not None:
        raise ServiceError(
            "only an admitted falsifier may point to canonical failure memory"
        )
    if terminal == "OPERATIONAL_STOP":
        if (
            evidence_level != "operational_stop"
            or damage_scope != "operational-only"
            or failure_ref is not None
            or any(item["status"] != "not-established" for item in tagged.values())
        ):
            raise ServiceError("operational feedback contains mathematical learning")
    claim_candidate = value.get("claim_candidate")
    if claim_candidate is not None:
        if not isinstance(claim_candidate, dict) or set(claim_candidate) != {
            "contract_id",
            "model_contract_id",
            "scope_contract_id",
            "downstream",
        }:
            raise ServiceError("feedback claim candidate is malformed")
        if claim_candidate.get("downstream") != "verification_funnel_required":
            raise ServiceError("feedback claim candidate bypasses verification")
        receipt_claim = receipt.get("claim_candidate")
        if not isinstance(receipt_claim, dict):
            raise ServiceError(
                "feedback claim candidate is absent from the development receipt"
            )
        expected_claim = {
            "contract_id": receipt_claim.get("contract_id"),
            "model_contract_id": receipt_claim.get("model_contract_id"),
            "scope_contract_id": receipt_claim.get("scope_contract_id"),
            "downstream": receipt_claim.get("downstream"),
        }
        if claim_candidate != expected_claim:
            raise ServiceError(
                "feedback claim candidate differs from the development receipt"
            )
        receipt_event_ids = receipt_claim.get("evidence_event_ids") or []
        if not set(receipt_event_ids).issubset(set(event_ids)):
            raise ServiceError(
                "feedback omits evidence events supporting its claim candidate"
            )
    elif receipt.get("claim_candidate") is not None:
        raise ServiceError(
            "root feedback cannot silently discard a development claim candidate"
        )
    if terminal == "OPERATIONAL_STOP" and claim_candidate is not None:
        raise ServiceError("operational feedback cannot carry a claim candidate")
    if value.get("queue_disposition") != "investigated-do-not-reselect":
        raise ServiceError("feedback queue disposition is invalid")
    feedback_core = {
        key: value[key]
        for key in value
        if key != "root_admission"
    }
    feedback_core_sha256 = canonical_json_sha256(feedback_core)
    if (
        root_admission.get("admitted_feedback_core_sha256")
        != feedback_core_sha256
    ):
        raise ServiceError("feedback root admission does not bind its complete core")
    validate_root_reconciliation(
        reconciliation_path,
        feedback_id=feedback_id,
        reconciled_at=str(root_admission.get("reconciled_at")),
        claim_path=claim_path,
        development_receipt_path=receipt_path,
        admitted_feedback_core_sha256=feedback_core_sha256,
        brief=brief,
    )
    return value


def validate_v3_result_receipt(
    service_dir: Path,
    result_path: Path,
    seed_path: Path,
    batch: dict[str, Any],
) -> dict[str, Any]:
    validate_service_state_layout(service_dir)
    campaign.validate_seed_batch(batch, authenticate=True)
    result = read_json(result_path, "v3 result receipt")
    common = {
        "schema_version",
        "protocol",
        "campaign_id",
        "requested_seed_count",
        "feedback_epoch_sha256",
        "started_at",
        "finished_at",
        "provider_exit_code",
        "terminal",
        "seed_count",
        "claim_level",
        "validation",
        "terminal_reason",
        "receipts",
        "route_action",
        "proof_movement",
        "origin",
    }
    origin = result.get("origin")
    expected_keys = common | (
        {"approval_ref", "root_commit"}
        if origin == "root-empty-queue-fallback"
        else set()
    )
    if set(result) != expected_keys:
        raise ServiceError("v3 result receipt has an unexpected closed contract")
    if result.get("schema_version") != 1 or result.get("protocol") != PROTOCOL_VERSION:
        raise ServiceError("v3 result receipt protocol is invalid")
    campaign_id = safe_leaf_id(batch.get("campaign_id"), "batch campaign_id")
    expected_batch_dir = (service_dir / "batches" / campaign_id).resolve()
    if (
        seed_path.resolve() != (expected_batch_dir / "seed-batch.json").resolve()
        or result_path.resolve()
        != (expected_batch_dir / "result-receipt.json").resolve()
    ):
        raise ServiceError("v3 result is outside its canonical service batch layout")
    if (
        result.get("campaign_id") != campaign_id
        or result.get("requested_seed_count") != batch.get("requested_seed_count")
        or result.get("terminal") != batch.get("terminal")
        or result.get("seed_count") != len(batch.get("seeds", []))
        or result.get("claim_level") != "proposal"
        or result.get("route_action") != "none"
        or result.get("proof_movement") != "neutral"
    ):
        raise ServiceError("v3 result receipt differs from its admitted seed batch")
    terminal = result.get("terminal")
    if terminal not in PROVIDER_RESULT_TERMINALS:
        raise ServiceError("v3 result terminal is invalid")
    if parse_timestamp(result.get("finished_at")) is None:
        raise ServiceError("v3 result finished_at is invalid")
    exit_code = result.get("provider_exit_code")
    if exit_code is not None and (
        not isinstance(exit_code, int) or isinstance(exit_code, bool)
    ):
        raise ServiceError("v3 result provider_exit_code is invalid")
    if result.get("validation") != "scripts/check_research_campaign.py --seed-batch":
        raise ServiceError("v3 result validation gate differs")
    if not isinstance(result.get("terminal_reason"), str) or not result[
        "terminal_reason"
    ].strip():
        raise ServiceError("v3 result terminal reason is missing")
    epoch = result.get("feedback_epoch_sha256")
    if not isinstance(epoch, str) or len(epoch) != 64:
        raise ServiceError("v3 result learning epoch is malformed")
    receipts = result.get("receipts")
    if not isinstance(receipts, dict):
        raise ServiceError("v3 result receipts are malformed")
    if receipts.get("seed_batch") != file_receipt(seed_path):
        raise ServiceError("result receipt does not authenticate seed batch")
    for key, value in receipts.items():
        if value is not None:
            authenticate_receipt(value, f"v3 result {key}")

    if origin == "standing-authorized-provider":
        expected_receipts = {
            "packet",
            "standing_authorization",
            "snapshot_admission",
            "prompt",
            "task",
            "seed_batch",
            "raw_response",
            "dedup_report",
            "events",
            "provider_log",
            "attempt",
            "provider_start",
            "invocation_event",
        }
        if set(receipts) != expected_receipts:
            raise ServiceError("provider result receipts have an unexpected contract")
        packet_path = authenticate_receipt(receipts["packet"], "result packet")
        packet = verify_packet(packet_path, mode="historical")
        if (
            packet.get("campaign_id") != campaign_id
            or packet.get("requested_seed_count") != result["requested_seed_count"]
            or packet.get("feedback_epoch_sha256") != epoch
            or packet.get("snapshot") != batch.get("snapshot")
            or packet.get("generation_mode") != batch.get("generation_mode")
            or packet.get("standing_authorization")
            != receipts.get("standing_authorization")
            or packet.get("snapshot_admission")
            != receipts.get("snapshot_admission")
            or packet.get("prompt") != receipts.get("prompt")
            or packet.get("task") != receipts.get("task")
        ):
            raise ServiceError("provider result is not bound to its frozen packet")
        if parse_timestamp(result.get("started_at")) is None:
            raise ServiceError("provider result started_at is invalid")
        attempt_receipt = receipts.get("attempt")
        invocation_receipt = receipts.get("invocation_event")
        if terminal in {"SEED-BATCH-COMPLETE", "SEED-BATCH-NOVELTY-STOP"}:
            for required in (
                "raw_response",
                "dedup_report",
                "attempt",
                "provider_start",
                "invocation_event",
            ):
                if receipts.get(required) is None:
                    raise ServiceError(
                        f"successful provider result lacks required {required} receipt"
                    )
            provider_admission_path = authenticate_receipt(
                packet["snapshot_admission"],
                "provider result snapshot admission",
            )
            provider_admission = validate_snapshot_admission(
                provider_admission_path,
                snapshot_path=authenticate_receipt(
                    packet["snapshot"], "provider result snapshot"
                ),
                service_dir=service_dir,
                campaign_id=campaign_id,
                purpose="provider_generation",
            )
            provider_export_path = authenticate_receipt(
                provider_admission["validated_learning_export"],
                "provider result validated learning export",
            )
            provider_export = (
                build_sol_idea_packet.load_validated_learning_export(
                    provider_export_path, authenticate_inputs=False
                )
            )
            validate_dedup_transform(
                service_dir,
                source_path=authenticate_receipt(
                    receipts["raw_response"], "provider raw response"
                ),
                admitted_batch=batch,
                report_path=authenticate_receipt(
                    receipts["dedup_report"], "provider deduplication report"
                ),
                requested_seed_count=int(result["requested_seed_count"]),
                learning_export=provider_export,
            )
        elif terminal == "SEED-BATCH-PROVIDER-STOP":
            if attempt_receipt is None or invocation_receipt is None:
                raise ServiceError(
                    "provider-stop result lacks its charged attempt/ledger receipts"
                )
        elif terminal == "SEED-BATCH-PACKET-MISMATCH":
            if (attempt_receipt is None) != (invocation_receipt is None):
                raise ServiceError(
                    "packet-mismatch attempt and ledger receipts disagree"
                )
            if attempt_receipt is None and any(
                receipts.get(key) is not None
                for key in (
                    "raw_response",
                    "dedup_report",
                    "events",
                    "provider_log",
                    "provider_start",
                )
            ):
                raise ServiceError(
                    "unattempted packet mismatch contains execution artifacts"
                )
        if receipts.get("provider_start") is not None and attempt_receipt is None:
            raise ServiceError("provider-start receipt exists without a charged attempt")
        if attempt_receipt is not None:
            attempt_path = authenticate_receipt(
                attempt_receipt, "provider result attempt"
            )
            attempt = read_json(attempt_path, "provider result attempt")
            attempt_keys = {
                "schema_version",
                "protocol",
                "campaign_id",
                "started_at",
                "queue",
                "packet",
                "command",
                "provider_invocation_ordinal",
                "ledger_event",
                "retry_authority",
            }
            if (
                set(attempt) != attempt_keys
                or attempt.get("schema_version") != 1
                or attempt.get("protocol") != PROTOCOL_VERSION
                or attempt.get("campaign_id") != campaign_id
                or attempt.get("packet") != receipts.get("packet")
                or attempt.get("started_at") != result.get("started_at")
                or attempt.get("ledger_event") != invocation_receipt
                or attempt.get("retry_authority") != "none"
                or not isinstance(attempt.get("provider_invocation_ordinal"), int)
            ):
                raise ServiceError("provider result attempt receipt is malformed")
            event_path = authenticate_receipt(
                invocation_receipt, "provider result invocation event"
            )
            event = read_json(event_path, "provider result invocation event")
            if (
                event.get("event_type") != "attempt"
                or event.get("campaign_id") != campaign_id
                or event.get("charged_ordinal")
                != attempt.get("provider_invocation_ordinal")
                or event.get("packet") != receipts.get("packet")
            ):
                raise ServiceError("provider result invocation event differs")
    elif origin == "root-empty-queue-fallback":
        if "-root-seeds-" not in campaign_id:
            raise ServiceError("root result campaign lacks its root-origin marker")
        expected_receipts = {
            "root_import_packet",
            "standing_authorization",
            "snapshot",
            "snapshot_build",
            "snapshot_admission",
            "semantic_screen",
            "dedup_report",
            "seed_batch",
            "source_seed_batch",
        }
        if set(receipts) != expected_receipts:
            raise ServiceError("root result receipts have an unexpected contract")
        destination_paths = {
            "root_import_packet": expected_batch_dir / "root-import-packet.json",
            "dedup_report": expected_batch_dir / "dedup-report.json",
            "seed_batch": expected_batch_dir / "seed-batch.json",
        }
        for key, expected_path in destination_paths.items():
            actual_path = authenticate_receipt(
                receipts[key], f"root result {key}"
            )
            if (
                actual_path != expected_path.resolve()
                or receipts[key].get("path") != repo_relative(expected_path)
            ):
                raise ServiceError(
                    f"root result {key} is outside its canonical destination layout"
                )
        source_seed_path = authenticate_receipt(
            receipts["source_seed_batch"], "root source seed batch"
        )
        source_run = source_seed_path.parent.resolve()
        service_root = service_dir.resolve()
        try:
            source_run.relative_to(RUNS_ROOT)
        except ValueError as exc:
            raise ServiceError("root result source run escapes runs/agents") from exc
        if (
            source_run == RUNS_ROOT
            or source_run == service_root
            or service_root in source_run.parents
            or source_run in service_root.parents
            or receipts["source_seed_batch"].get("path")
            != repo_relative(source_seed_path)
        ):
            raise ServiceError("root result source run is not isolated from service state")
        expected_snapshot = source_run / "snapshot" / "packet-summary.json"
        expected_snapshot_build = (
            source_run
            / "snapshot"
            / build_sol_idea_packet.SNAPSHOT_BUILD_RECEIPT_NAME
        )
        expected_snapshot_admission = source_run / SNAPSHOT_ADMISSION_NAME
        for key, expected_path in {
            "snapshot": expected_snapshot,
            "snapshot_build": expected_snapshot_build,
            "snapshot_admission": expected_snapshot_admission,
        }.items():
            actual_path = authenticate_receipt(
                receipts[key], f"root result {key}"
            )
            if (
                actual_path != expected_path.resolve()
                or receipts[key].get("path") != repo_relative(expected_path)
            ):
                raise ServiceError(
                    f"root result {key} is outside its frozen source-run layout"
                )
        semantic_screen_path = authenticate_receipt(
            receipts["semantic_screen"], "root semantic screen"
        )
        try:
            semantic_screen_path.relative_to(source_run)
        except ValueError as exc:
            raise ServiceError(
                "root result semantic screen is outside its source run"
            ) from exc
        if (
            service_root == semantic_screen_path
            or service_root in semantic_screen_path.parents
            or receipts["semantic_screen"].get("path")
            != repo_relative(semantic_screen_path)
        ):
            raise ServiceError(
                "root result semantic screen is rebound into service state"
            )
        root_commit = result.get("root_commit")
        if not isinstance(root_commit, dict) or set(root_commit) != {
            "schema_version",
            "protocol",
            "standing_authorization",
            "snapshot_admission",
            "learning_epoch_sha256",
            "workspace_manifest_aggregate_sha256",
            "accounting_checkpoint",
            "checks",
        }:
            raise ServiceError("root result commit evidence is malformed")
        checkpoint = root_commit.get("accounting_checkpoint")
        if not isinstance(checkpoint, dict) or set(checkpoint) != {
            "baseline",
            "event_count",
            "charged_count",
            "unresolved_attempt_ordinal",
            "last_event",
        }:
            raise ServiceError("root result accounting checkpoint is malformed")
        authenticate_receipt(checkpoint.get("baseline"), "root commit baseline")
        authenticate_receipt(checkpoint.get("last_event"), "root commit last event")
        if (
            root_commit.get("schema_version") != 1
            or root_commit.get("protocol")
            != "continuous-idea-generator-root-commit-v1"
            or root_commit.get("standing_authorization")
            != receipts.get("standing_authorization")
            or root_commit.get("snapshot_admission")
            != receipts.get("snapshot_admission")
            or root_commit.get("learning_epoch_sha256") != epoch
            or root_commit.get("checks")
            != {
                "prewrite_current_authority_accounting": "pass",
                "prewrite_snapshot_currency": "pass",
                "postwrite_current_authority_accounting": "pass",
                "postwrite_snapshot_currency": "pass",
            }
            or not isinstance(checkpoint.get("event_count"), int)
            or not isinstance(checkpoint.get("charged_count"), int)
            or (
                checkpoint.get("unresolved_attempt_ordinal") is not None
                and not isinstance(
                    checkpoint.get("unresolved_attempt_ordinal"), int
                )
            )
        ):
            raise ServiceError("root result commit evidence differs")
        packet_path = authenticate_receipt(
            receipts["root_import_packet"], "root import packet"
        )
        packet = read_json(packet_path, "root import packet")
        expected_packet_keys = {
            "schema_version",
            "protocol",
            "origin",
            "campaign_id",
            "created_at",
            "service_dir",
            "requested_seed_count",
            "feedback_epoch_sha256",
            "standing_authorization",
            "snapshot",
            "snapshot_build",
            "snapshot_admission",
            "source_seed_batch",
            "semantic_screen",
            "approval_ref",
            "authority",
        }
        if (
            set(packet) != expected_packet_keys
            or packet.get("schema_version") != 1
            or packet.get("protocol") != PROTOCOL_VERSION
            or packet.get("origin") != origin
            or packet.get("campaign_id") != campaign_id
            or packet.get("requested_seed_count") != result["requested_seed_count"]
            or packet.get("feedback_epoch_sha256") != epoch
            or packet.get("standing_authorization")
            != receipts.get("standing_authorization")
            or packet.get("snapshot") != receipts.get("snapshot")
            or packet.get("snapshot") != batch.get("snapshot")
            or packet.get("snapshot_build") != receipts.get("snapshot_build")
            or packet.get("snapshot_admission")
            != receipts.get("snapshot_admission")
            or packet.get("source_seed_batch")
            != receipts.get("source_seed_batch")
            or packet.get("semantic_screen") != receipts.get("semantic_screen")
            or packet.get("service_dir") != repo_relative(service_dir)
            or packet.get("authority")
            != "proposal import only; no route or proof admission"
            or not isinstance(packet.get("approval_ref"), str)
            or not packet["approval_ref"].strip()
            or result.get("approval_ref") != packet.get("approval_ref")
        ):
            raise ServiceError("root result is not bound to its import packet")
        if (
            result.get("started_at") is not None
            or result.get("provider_exit_code") is not None
            or terminal not in {"SEED-BATCH-COMPLETE", "SEED-BATCH-NOVELTY-STOP"}
            or int(result.get("seed_count") or 0) < 1
        ):
            raise ServiceError("root result has an invalid non-provider terminal")
        snapshot_path = authenticate_receipt(receipts["snapshot"], "root snapshot")
        snapshot_build_path, snapshot_build = validate_snapshot_build_receipt(
            snapshot_path,
            service_dir=service_dir,
            campaign_id=campaign_id,
            purpose="root_fallback",
            mode="historical",
        )
        if receipts.get("snapshot_build") != file_receipt(snapshot_build_path):
            raise ServiceError("root result snapshot-build receipt differs")
        export_path = authenticate_receipt(
            snapshot_build["input_state"]["validated_learning_export"],
            "root result validated learning export",
        )
        frozen_export = build_sol_idea_packet.load_validated_learning_export(
            export_path, authenticate_inputs=False
        )
        if (
            checkpoint != frozen_export.get("accounting_checkpoint")
            or receipts.get("standing_authorization")
            != frozen_export.get("standing_authorization")
        ):
            raise ServiceError(
                "root result accounting/authority checkpoint differs from its "
                "admitted learning export"
            )
        validate_dedup_transform(
            service_dir,
            source_path=authenticate_receipt(
                receipts["source_seed_batch"], "root source seed batch"
            ),
            admitted_batch=batch,
            report_path=authenticate_receipt(
                receipts["dedup_report"], "root deduplication report"
            ),
            requested_seed_count=int(result["requested_seed_count"]),
            learning_export=frozen_export,
        )
        admission_path = authenticate_receipt(
            receipts["snapshot_admission"], "root snapshot admission"
        )
        if admission_path != snapshot_admission_path(snapshot_path):
            raise ServiceError("root result snapshot admission names another batch")
        validate_snapshot_admission(
            admission_path,
            snapshot_path=snapshot_path,
            service_dir=service_dir,
            campaign_id=campaign_id,
            purpose="root_fallback",
        )
        admission = read_json(admission_path, "root snapshot admission")
        if root_commit.get("workspace_manifest_aggregate_sha256") != admission.get(
            "workspace_manifest_aggregate_sha256"
        ):
            raise ServiceError("root result commit workspace digest differs")
        prior_path = authenticate_receipt(
            snapshot_build["outputs"]["prior_idea_registry_json"],
            "root prior-idea registry",
        )
        screen_path = authenticate_receipt(
            receipts["semantic_screen"], "root semantic screen"
        )
        authorization_path = authenticate_receipt(
            receipts["standing_authorization"], "root standing authorization"
        )
        validate_root_semantic_screen(
            screen_path,
            source_seed_path=authenticate_receipt(
                receipts["source_seed_batch"], "root source seed batch"
            ),
            batch=read_json(
                authenticate_receipt(
                    receipts["source_seed_batch"], "root source seed batch"
                ),
                "root source seed batch",
            ),
            service_dir=service_dir,
            authorization_path=authorization_path,
            snapshot_path=snapshot_path,
            snapshot_build_path=snapshot_build_path,
            prior_registry_path=prior_path,
            feedback_epoch_sha256=epoch,
            approval_ref=str(result["approval_ref"]),
        )
    else:
        raise ServiceError("v3 result origin is invalid")
    return result


def seed_inventory(
    service_dir: Path,
    *,
    authorization: dict[str, Any] | None = None,
    accounting: dict[str, Any] | None = None,
    excluded_campaign_id: str | None = None,
    _enforce_current_currency: bool = True,
) -> list[dict[str, Any]]:
    validate_service_state_layout(service_dir)
    inventory: list[dict[str, Any]] = []
    ready_admissions: dict[str, dict[str, Any]] = {}
    pointer_path = active_authorization_pointer_path(service_dir)
    activation_path = authorization_activation_head_path(service_dir)
    v3_state_present = (
        authorization is not None
        or accounting is not None
        or pointer_path.is_file()
        or activation_path.is_file()
    )
    if v3_state_present:
        if authorization is None:
            _authorization_path, authorization = active_standing_authorization(
                service_dir
            )
        if accounting is None:
            accounting = validate_accounting_chain(service_dir, authorization)
    batches = service_dir / "batches"
    if not batches.exists():
        return inventory
    migration, _charged, _excluded = validate_accounting_migration_root(
        service_dir
    )
    legacy_campaign_ids = {
        safe_leaf_id(entry[0], "migration seed campaign_id")
        for entry in migration["entries"]
    }
    seed_paths = [
        path
        for path in sorted(batches.glob("*/seed-batch.json"))
        if path.parent.name != excluded_campaign_id
    ]
    needs_v3_accounting = any(
        path.parent.name not in legacy_campaign_ids
        for path in seed_paths
    )
    if needs_v3_accounting:
        if authorization is None:
            _authorization_path, authorization = active_standing_authorization(
                service_dir
            )
        if accounting is None:
            accounting = validate_accounting_chain(service_dir, authorization)
    elif accounting is None:
        accounting = {
            "unresolved_record": None,
            "closed_v3_by_campaign": {},
        }
    unresolved_record = accounting.get("unresolved_record")
    unresolved_campaign = (
        str(unresolved_record.get("campaign_id"))
        if isinstance(unresolved_record, dict)
        else None
    )
    closed_v3 = accounting.get("closed_v3_by_campaign")
    for seed_path in seed_paths:
        batch = read_json(seed_path, "seed batch")
        campaign.validate_seed_batch(batch, authenticate=True)
        campaign_identity = safe_leaf_id(
            batch.get("campaign_id"), "seed-batch campaign_id"
        )
        if campaign_identity != seed_path.parent.name:
            raise ServiceError("seed batch campaign differs from its directory")
        legacy_batch = campaign_identity in legacy_campaign_ids
        has_v3_count = "requested_seed_count" in batch
        if legacy_batch == has_v3_count:
            raise ServiceError(
                "seed batch legacy/v3 identity differs from the immutable "
                "migration partition"
            )
        if campaign_identity == unresolved_campaign:
            # The result may be durable while its outcome event/head update is
            # still incomplete.  Never expose those seeds before accounting closes.
            continue
        result_path = seed_path.parent / "result-receipt.json"
        validated_result: dict[str, Any] | None = None
        if not legacy_batch:
            if result_path.is_file():
                validated_result = validate_v3_result_receipt(
                    service_dir, result_path, seed_path, batch
                )
                if validated_result.get("origin") == "standing-authorized-provider":
                    closed = closed_v3.get(str(campaign_identity))
                    if (seed_path.parent / "attempt.json").is_file():
                        if not isinstance(closed, dict):
                            raise ServiceError(
                                "provider result is not closed by authenticated accounting"
                            )
                        if (
                            closed.get("result_receipt") != file_receipt(result_path)
                            or closed.get("seed_batch_receipt") != file_receipt(seed_path)
                        ):
                            raise ServiceError(
                                "provider result receipts differ from authenticated accounting"
                            )
                    elif not (
                        validated_result.get("terminal")
                        == "SEED-BATCH-PACKET-MISMATCH"
                        and int(validated_result.get("seed_count") or 0) == 0
                    ):
                        raise ServiceError(
                            "provider result without an attempt is not an unattempted mismatch"
                        )
            elif (seed_path.parent / "attempt.json").is_file():
                # A partially finalized charged attempt never exposes ready seeds;
                # pending_queue keeps this exact identity available for recovery.
                continue
            else:
                raise ServiceError("v3 seed batch has no result receipt")
        if batch.get("terminal") not in {
            "SEED-BATCH-COMPLETE",
            "SEED-BATCH-NOVELTY-STOP",
        }:
            continue
        campaign_id = batch.get("campaign_id")
        if not isinstance(campaign_id, str):
            raise ServiceError("seed batch campaign identity is missing")
        if result_path.is_file():
            result = read_json(result_path, "seed result receipt")
            if batch.get("requested_seed_count") is None:
                receipts = result.get("receipts") or {}
                if receipts.get("seed_batch") != file_receipt(seed_path):
                    raise ServiceError("result receipt does not authenticate seed batch")
            if not legacy_batch:
                assert validated_result is not None
                admission_path = authenticate_receipt(
                    (validated_result.get("receipts") or {}).get(
                        "snapshot_admission"
                    ),
                    "ready-exposure snapshot admission",
                )
                ready_admissions[campaign_id] = read_json(
                    admission_path, "ready-exposure snapshot admission"
                )
        legacy_path = service_dir / "consumed" / f"{campaign_id}.json"
        legacy_consumed = False
        if legacy_path.is_file():
            validate_legacy_consumption(legacy_path, campaign_id, seed_path)
            legacy_consumed = True
        for ordinal, seed in enumerate(batch.get("seeds", [])):
            seed_id = seed.get("seed_id")
            if not isinstance(seed_id, str):
                raise ServiceError("seed identity is missing")
            state = "legacy_reconciled_investigation_unknown" if legacy_consumed else "ready"
            claim_path = seed_claim_path(service_dir, campaign_id, seed_id)
            feedback_path = seed_feedback_path(service_dir, campaign_id, seed_id)
            claim_receipt = None
            feedback_receipt = None
            if claim_path.is_file():
                claim = validate_seed_claim(
                    claim_path,
                    campaign_id=campaign_id,
                    seed_id=seed_id,
                    seed_path=seed_path,
                )
                claim_receipt = file_receipt(claim_path)
                state = "investigating"
                if feedback_path.is_file():
                    validate_investigation_feedback(
                        feedback_path,
                        claim=claim,
                        campaign_id=campaign_id,
                        seed_id=seed_id,
                        seed_path=seed_path,
                    )
                    feedback_receipt = file_receipt(feedback_path)
                    state = "investigated"
            elif feedback_path.is_file():
                raise ServiceError("feedback exists without an authenticated seed claim")
            if legacy_consumed and claim_path.is_file():
                raise ServiceError("legacy-consumed seed cannot acquire a v3 claim")
            inventory.append(
                {
                    "campaign_id": campaign_id,
                    "seed_id": seed_id,
                    "ordinal": ordinal,
                    "state": state,
                    "seed_batch": file_receipt(seed_path),
                    "claim": claim_receipt,
                    "feedback": feedback_receipt,
                }
            )
    if _enforce_current_currency:
        stale_campaigns: set[str] = set()
        for campaign_id, admission in sorted(ready_admissions.items()):
            if not any(
                item["campaign_id"] == campaign_id and item["state"] == "ready"
                for item in inventory
            ):
                continue
            current, _reasons = ready_exposure_currency(
                admission,
                service_dir=service_dir,
                campaign_id=campaign_id,
            )
            if not current:
                stale_campaigns.add(campaign_id)
        if stale_campaigns:
            # Suppression is operational only.  The authenticated historical
            # items remain available to the generator's learning/dedup view via
            # the internal non-exposure inventory used below.
            inventory = [
                item
                for item in inventory
                if not (
                    item["campaign_id"] in stale_campaigns
                    and item["state"] == "ready"
                )
            ]
    return inventory


def active_reserve(
    service_dir: Path,
    *,
    authorization: dict[str, Any] | None = None,
    accounting: dict[str, Any] | None = None,
    excluded_campaign_id: str | None = None,
) -> list[dict[str, Any]]:
    grouped: dict[str, dict[str, Any]] = {}
    for item in seed_inventory(
        service_dir,
        authorization=authorization,
        accounting=accounting,
        excluded_campaign_id=excluded_campaign_id,
    ):
        if item["state"] != "ready":
            continue
        campaign_id = str(item["campaign_id"])
        entry = grouped.setdefault(
            campaign_id,
            {
                "campaign_id": campaign_id,
                "seed_count": 0,
                "seed_ids": [],
                "seed_batch": item["seed_batch"],
            },
        )
        entry["seed_count"] += 1
        entry["seed_ids"].append(item["seed_id"])
    return [grouped[key] for key in sorted(grouped)]


def materialize_validated_learning_export(
    service_dir: Path,
    output_path: Path,
    *,
    authorization_path: Path,
    authorization: dict[str, Any],
    accounting: dict[str, Any],
    excluded_campaign_id: str,
) -> dict[str, Any]:
    """Write the one generator-validated continuous-learning projection."""
    active_path, active = active_standing_authorization(service_dir)
    if file_receipt(active_path) != file_receipt(authorization_path) or active != authorization:
        raise ServiceError("validated learning export authority is not current")
    checked_accounting = validate_accounting_chain(service_dir, authorization)
    if checked_accounting["head"] != accounting.get("head"):
        raise ServiceError("validated learning export accounting view changed")
    inventory = seed_inventory(
        service_dir,
        authorization=authorization,
        accounting=checked_accounting,
        excluded_campaign_id=excluded_campaign_id,
        _enforce_current_currency=False,
    )
    continuous_entries: list[dict[str, Any]] = []
    learning_receipts: list[dict[str, Any]] = []
    accounting_events: list[dict[str, str]] = []
    filtered_charged_count = 0
    for record in checked_accounting["records"]:
        if record.get("protocol") != PROTOCOL_VERSION:
            continue
        if record.get("campaign_id") == excluded_campaign_id:
            continue
        attempt_event = record.get("attempt_event")
        outcome_event = record.get("outcome_event")
        if isinstance(attempt_event, dict):
            accounting_events.append(attempt_event)
            filtered_charged_count += 1
        if isinstance(outcome_event, dict):
            accounting_events.append(outcome_event)
    baseline_path = authenticate_receipt(
        checked_accounting["baseline"], "learning accounting baseline"
    )
    baseline = read_json(baseline_path, "learning accounting baseline")
    filtered_charged_count += int(baseline["legacy_charged_count"])
    unresolved_record = checked_accounting.get("unresolved_record")
    filtered_unresolved = (
        unresolved_record.get("charged_ordinal")
        if isinstance(unresolved_record, dict)
        and unresolved_record.get("campaign_id") != excluded_campaign_id
        else None
    )
    filtered_last_event = (
        accounting_events[-1]
        if accounting_events
        else checked_accounting["baseline"]
    )
    input_receipts: list[dict[str, str]] = [
        file_receipt(authorization_path),
        checked_accounting["baseline"],
        *accounting_events,
    ]
    for item in inventory:
        campaign_id = str(item["campaign_id"])
        seed_id = str(item["seed_id"])
        seed_path = authenticate_receipt(item["seed_batch"], "learning seed batch")
        batch = read_json(seed_path, "learning seed batch")
        seed = next(
            (
                candidate
                for candidate in batch.get("seeds", [])
                if isinstance(candidate, dict) and candidate.get("seed_id") == seed_id
            ),
            None,
        )
        if seed is None:
            raise ServiceError("validated learning inventory seed is absent from batch")
        result_path = seed_path.parent / "result-receipt.json"
        result_receipt = file_receipt(result_path) if result_path.is_file() else None
        claim_receipt = item.get("claim")
        feedback_receipt = item.get("feedback")
        admitted_feedback = None
        feedback_core_sha256 = None
        investigation_status = {
            "ready": "queued_uninvestigated",
            "investigating": "in_flight",
            "legacy_reconciled_investigation_unknown": (
                "legacy_reconciled_investigation_unknown"
            ),
        }.get(str(item["state"]))
        if feedback_receipt is not None:
            feedback_path = authenticate_receipt(
                feedback_receipt, "validated learning feedback"
            )
            feedback = read_json(feedback_path, "validated learning feedback")
            root_admission = feedback.get("root_admission") or {}
            feedback_core_sha256 = root_admission.get(
                "admitted_feedback_core_sha256"
            )
            if not isinstance(feedback_core_sha256, str):
                raise ServiceError("validated learning feedback lacks its full-core digest")
            investigation = feedback.get("investigation") or {}
            admitted_feedback = {
                "receipt": file_receipt(feedback_path),
                "admitted_feedback_core_sha256": feedback_core_sha256,
                "terminal": investigation.get("terminal"),
                "evidence": feedback.get("evidence"),
                "proof_distance": feedback.get("proof_distance"),
                "learned": feedback.get("learned"),
                "next_discriminating_test": feedback.get(
                    "next_discriminating_test"
                ),
                "canonical_failure_memory_ref": feedback.get(
                    "canonical_failure_memory_ref"
                ),
                "claim_candidate": feedback.get("claim_candidate"),
            }
            terminal = str(investigation.get("terminal") or "").casefold()
            investigation_status = f"investigated_{terminal}"
            learning_receipts.append(
                {"kind": "feedback", "receipt": file_receipt(feedback_path)}
            )
            input_receipts.append(file_receipt(feedback_path))
        if claim_receipt is not None:
            claim_path = authenticate_receipt(
                claim_receipt, "validated learning claim"
            )
            learning_receipts.append(
                {"kind": "claim", "receipt": file_receipt(claim_path)}
            )
            input_receipts.append(file_receipt(claim_path))
        if investigation_status is None:
            raise ServiceError("validated learning inventory state is unsupported")
        model = seed.get("model") or {}
        mechanism = seed.get("mechanism") or {}
        first_test = seed.get("first_test") or {}
        registry = {
            "registry_id": f"continuous:{campaign_id}:{seed_id}",
            "origin": "continuous_idea_generator",
            "source_path": repo_relative(seed_path),
            "original_id": seed_id,
            "mechanism_family": mechanism.get("family_hint"),
            "model_tier": model.get("working_tier"),
            "question": first_test.get("question") or seed.get("title"),
            "idea": {
                "target_ref": seed.get("target_ref"),
                "title": seed.get("title"),
                "model": model,
                "mechanism": mechanism,
                "lineage": seed.get("lineage"),
            },
            "cheapest_probe": first_test,
            "investigation_status": investigation_status,
            "claim_receipt": claim_receipt,
            "admitted_feedback": admitted_feedback,
        }
        continuous_entries.append(
            {
                "campaign_id": campaign_id,
                "seed_id": seed_id,
                "ordinal": item["ordinal"],
                "state": item["state"],
                "seed_batch": item["seed_batch"],
                "result": result_receipt,
                "claim": claim_receipt,
                "feedback": feedback_receipt,
                "feedback_core_sha256": feedback_core_sha256,
                "registry": registry,
            }
        )
        input_receipts.append(item["seed_batch"])
        if result_receipt is not None:
            input_receipts.append(result_receipt)

    canonical_paths = [ROOT / "docs/wayfinder/frontier-portfolio.md"]
    idea_ledger = ROOT / "runs/idea-factory/idea-ledger.md"
    if idea_ledger.is_file():
        canonical_paths.append(idea_ledger)
    ticket_dir = ROOT / "docs/wayfinder/tickets"
    canonical_paths.extend(
        sorted(path for path in ticket_dir.glob("*.md") if path.is_file())
    )
    for path in canonical_paths:
        receipt = file_receipt(path)
        learning_receipts.append(
            {"kind": "canonical_failure_memory", "receipt": receipt}
        )
        input_receipts.append(receipt)

    continuous_entries.sort(key=lambda entry: entry["registry"]["registry_id"])
    learning_receipts.sort(
        key=lambda entry: (entry["kind"], entry["receipt"]["path"])
    )
    by_path: dict[str, dict[str, str]] = {}
    for receipt in input_receipts:
        existing = by_path.get(receipt["path"])
        if existing is not None and existing != receipt:
            raise ServiceError("validated learning input path has conflicting receipts")
        by_path[receipt["path"]] = receipt
    input_receipts = [by_path[path] for path in sorted(by_path)]
    value: dict[str, Any] = {
        "schema_version": 1,
        "protocol": build_sol_idea_packet.VALIDATED_LEARNING_EXPORT_PROTOCOL,
        "service_dir": repo_relative(service_dir),
        "excluded_campaign_id": excluded_campaign_id,
        "standing_authorization": file_receipt(authorization_path),
        "accounting_checkpoint": {
            "baseline": checked_accounting["baseline"],
            "event_count": len(accounting_events),
            "charged_count": filtered_charged_count,
            "unresolved_attempt_ordinal": filtered_unresolved,
            "last_event": filtered_last_event,
        },
        "validator_components": {
            "generator": file_receipt(Path(__file__).resolve()),
            "campaign": file_receipt(Path(campaign.__file__).resolve()),
            "first_test_guard": file_receipt(FIRST_TEST_GUARD),
            "seed_schema": file_receipt(campaign.SEED_SCHEMA),
            "brief_schema": file_receipt(campaign.BRIEF_SCHEMA),
            "task_schema": file_receipt(campaign.TASK_SCHEMA),
            "development_receipt_schema": file_receipt(campaign.RECEIPT_SCHEMA),
            "event_verification_schema": file_receipt(
                campaign.EVENT_VERIFICATION_SCHEMA
            ),
            "first_test_execution_envelope_schema": file_receipt(
                FIRST_TEST_EXECUTION_ENVELOPE_SCHEMA
            ),
            "feedback_schema": file_receipt(FEEDBACK_SCHEMA),
        },
        "continuous_entries": continuous_entries,
        "learning_receipts": learning_receipts,
        "input_receipts": input_receipts,
        "learning_epoch_sha256": canonical_json_sha256(learning_receipts),
        "current_input_fingerprint_sha256": canonical_json_sha256(input_receipts),
    }
    value["export_core_sha256"] = canonical_json_sha256(value)
    atomic_json(output_path, value)
    loaded = build_sol_idea_packet.load_validated_learning_export(output_path)
    if loaded != value:
        raise ServiceError("validated learning export did not round-trip")
    return value


def unresolved_accounting_campaign(service_dir: Path) -> str | None:
    head_path = accounting_head_path(service_dir)
    if not head_path.is_file():
        return None
    head = read_json(head_path, "invocation accounting head")
    if head.get("unresolved_attempt_ordinal") is None:
        return None
    last_path = authenticate_receipt(
        head.get("last_event"), "unresolved invocation event"
    )
    last_event = read_json(last_path, "unresolved invocation event")
    if last_event.get("event_type") != "attempt":
        raise ServiceError("accounting head marks an unresolved non-attempt event")
    return safe_leaf_id(last_event.get("campaign_id"), "unresolved campaign_id")


def pending_queue(
    service_dir: Path,
    *,
    authorization: dict[str, Any] | None = None,
    accounting: dict[str, Any] | None = None,
) -> list[Path]:
    validate_service_state_layout(service_dir)
    if authorization is None:
        _authorization_path, authorization = active_standing_authorization(service_dir)
    if accounting is None:
        accounting = validate_accounting_chain(service_dir, authorization)
    migration, _charged, _excluded = validate_accounting_migration_root(
        service_dir
    )
    legacy_campaign_ids = {
        safe_leaf_id(entry[0], "migration queue campaign_id")
        for entry in migration["entries"]
    }
    unresolved_record = accounting.get("unresolved_record")
    unresolved_campaign = (
        str(unresolved_record.get("campaign_id"))
        if isinstance(unresolved_record, dict)
        else None
    )
    pending: list[Path] = []
    closed_v3 = accounting.get("closed_v3_by_campaign")
    for entry_path in exact_queue_children(service_dir):
        entry = read_json(entry_path, "queue entry")
        campaign_id = entry.get("campaign_id")
        if not isinstance(campaign_id, str):
            raise ServiceError("queue entry has no valid campaign identity")
        safe_leaf_id(campaign_id, "queued campaign_id")
        expected_path = service_state_path(
            service_dir, "queue", f"{campaign_id}.json"
        )
        if entry_path != expected_path:
            raise ServiceError("queue entry is outside its canonical campaign path")
        if campaign_id in legacy_campaign_ids:
            # The immutable migration root authenticates the exact legacy queue,
            # result, and batch receipts.  Those identities are historical, not
            # pending v3 reservations.
            continue
        _entry, _packet_path, _packet = authenticate_queue(entry_path)
        batch_dir = service_state_path(service_dir, "batches", campaign_id)
        result_path = batch_dir / "result-receipt.json"
        seed_path = batch_dir / "seed-batch.json"
        if unresolved_campaign == campaign_id:
            pending.append(entry_path)
            continue
        result_exists = result_path.exists()
        seed_exists = seed_path.exists()
        if not result_exists and not seed_exists:
            pending.append(entry_path)
            continue
        if result_exists != seed_exists:
            raise ServiceError(
                "queued campaign has a partial result marker and remains unresolved"
            )
        batch = read_json(seed_path, "queued result seed batch")
        validated_result = validate_v3_result_receipt(
            service_dir, result_path, seed_path, batch
        )
        if validated_result.get("origin") != "standing-authorized-provider":
            raise ServiceError("provider queue is closed by a non-provider result")
        attempt_path = batch_dir / "attempt.json"
        if attempt_path.is_file():
            if not isinstance(closed_v3, dict):
                raise ServiceError(
                    "authenticated accounting lacks its closed-campaign index"
                )
            closed = closed_v3.get(campaign_id)
            if not isinstance(closed, dict):
                raise ServiceError(
                    "queued provider result is not closed by authenticated accounting"
                )
            if (
                closed.get("result_receipt") != file_receipt(result_path)
                or closed.get("seed_batch_receipt") != file_receipt(seed_path)
            ):
                raise ServiceError(
                    "queued provider result differs from authenticated accounting"
                )
        elif not (
            validated_result.get("terminal") == "SEED-BATCH-PACKET-MISMATCH"
            and int(validated_result.get("seed_count") or 0) == 0
        ):
            raise ServiceError(
                "queued provider result without an attempt is not an exact mismatch"
            )
    return pending


def pending_reserved_capacity(
    service_dir: Path,
    *,
    authorization: dict[str, Any] | None = None,
    accounting: dict[str, Any] | None = None,
) -> int:
    reserved = 0
    for entry_path in pending_queue(
        service_dir,
        authorization=authorization,
        accounting=accounting,
    ):
        _entry, _packet_path, packet = authenticate_queue(entry_path)
        requested = packet.get("requested_seed_count")
        if not isinstance(requested, int) or not 1 <= requested <= 5:
            raise ServiceError("pending packet has an invalid seed reservation")
        reserved += requested
    return reserved


def process_tree_rss_bytes(root_pid: int) -> int:
    parents: dict[int, int] = {}
    rss: dict[int, int] = {}
    for proc in Path("/proc").iterdir():
        if not proc.name.isdigit():
            continue
        pid = int(proc.name)
        try:
            stat = (proc / "stat").read_text(encoding="utf-8")
            tail = stat[stat.rfind(")") + 2 :].split()
            parents[pid] = int(tail[1])
            for line in (proc / "status").read_text(encoding="utf-8").splitlines():
                if line.startswith("VmRSS:"):
                    rss[pid] = int(line.split()[1]) * 1024
                    break
        except (OSError, ValueError, IndexError):
            continue
    descendants = {root_pid}
    changed = True
    while changed:
        changed = False
        for pid, parent in parents.items():
            if parent in descendants and pid not in descendants:
                descendants.add(pid)
                changed = True
    return sum(rss.get(pid, 0) for pid in descendants)


def output_bytes(batch_dir: Path) -> int:
    total = 0
    for name in ("events.jsonl", "provider.log", "raw-response.json"):
        path = batch_dir / name
        if path.is_file():
            total += path.stat().st_size
    return total


def terminate_provider(pid: int, expected_identity: dict[str, Any] | None = None) -> None:
    if expected_identity is not None and not process_identity_matches(expected_identity):
        return
    try:
        os.killpg(pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    deadline = time.monotonic() + 8
    while time.monotonic() < deadline and process_alive(pid):
        time.sleep(0.2)
    if process_alive(pid):
        try:
            os.killpg(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def synthesize_terminal(
    batch_dir: Path,
    packet: dict[str, Any],
    terminal: str,
    reason: str,
) -> tuple[dict[str, Any], str]:
    batch = stop_batch(packet, terminal)
    try:
        campaign.validate_seed_batch(batch, authenticate=True)
    except (campaign.CampaignError, OSError) as exc:
        raise ServiceError(f"cannot authenticate synthesized terminal: {exc}") from exc
    write_once(batch_dir / "seed-batch.json", batch)
    return batch, reason


def finalize_provider(
    batch_dir: Path,
    packet_path: Path,
    packet: dict[str, Any],
    exit_code: int | None,
    stop_reason: str | None,
    started_at: str,
    stop_terminal: str = "SEED-BATCH-PROVIDER-STOP",
) -> dict[str, Any]:
    service_dir = batch_dir.parents[1]
    with locked_service_state(service_dir):
        return _finalize_provider_locked(
            batch_dir,
            packet_path,
            packet,
            exit_code,
            stop_reason,
            started_at,
            stop_terminal,
        )


def _finalize_provider_locked(
    batch_dir: Path,
    packet_path: Path,
    packet: dict[str, Any],
    exit_code: int | None,
    stop_reason: str | None,
    started_at: str,
    stop_terminal: str,
) -> dict[str, Any]:
    service_dir = batch_dir.parents[1]
    frozen_packet = verify_packet(packet_path, mode="historical")
    if frozen_packet != packet:
        raise ServiceError("finalizer packet differs from the immutable packet")
    result_path = batch_dir / "result-receipt.json"
    seed_path = batch_dir / "seed-batch.json"
    if result_path.is_file():
        if not seed_path.is_file():
            raise ServiceError("durable provider result has no seed-batch artifact")
        existing_batch = read_json(seed_path, "existing finalized seed batch")
        existing = validate_v3_result_receipt(
            service_dir, result_path, seed_path, existing_batch
        )
        if existing.get("campaign_id") != packet.get("campaign_id"):
            raise ServiceError("existing provider result belongs to another packet")
        if (batch_dir / "attempt.json").is_file():
            _authorization_path, authorization = active_standing_authorization(
                service_dir
            )
            complete_invocation_event(
                service_dir,
                authorization,
                campaign_id=str(packet["campaign_id"]),
                result_path=result_path,
                seed_path=seed_path,
            )
        return existing
    raw_path = batch_dir / "raw-response.json"
    batch: dict[str, Any]
    admission_path = authenticate_receipt(
        packet["snapshot_admission"], "finalization snapshot admission"
    )
    admission = validate_snapshot_admission(
        admission_path,
        snapshot_path=authenticate_receipt(packet["snapshot"], "finalization snapshot"),
        service_dir=service_dir,
        campaign_id=str(packet["campaign_id"]),
        purpose="provider_generation",
    )
    current_snapshot, currency_reasons = snapshot_currency(
        admission,
        service_dir=service_dir,
        campaign_id=str(packet["campaign_id"]),
    )
    frozen_export_path = authenticate_receipt(
        admission["validated_learning_export"],
        "finalization validated learning export",
    )
    frozen_export = build_sol_idea_packet.load_validated_learning_export(
        frozen_export_path, authenticate_inputs=False
    )
    if not current_snapshot:
        stop_reason = (
            "snapshot inputs changed after packet freeze ("
            + ",".join(currency_reasons)
            + "); this identity cannot be retried and its proposals are not admitted"
        )
        stop_terminal = "SEED-BATCH-PACKET-MISMATCH"
    terminal_reason = stop_reason
    if stop_reason is None and exit_code in (0, None) and raw_path.is_file():
        try:
            payload = read_json(raw_path, "provider response")
            campaign.validate_seed_batch(payload, authenticate=True)
            expected_response = {
                "campaign_id": packet["campaign_id"],
                "generation_mode": packet["generation_mode"],
                "requested_seed_count": packet["requested_seed_count"],
                "snapshot": packet["snapshot"],
                "claim_level": "proposal",
            }
            if any(payload.get(key) != expected for key, expected in expected_response.items()):
                raise ServiceError(
                    "provider response identity differs from the frozen packet"
                )
            batch, dedup_report = deduplicate_provider_batch(
                batch_dir.parents[1],
                payload,
                int(packet["requested_seed_count"]),
                known_memory=frozen_generated_seed_memory(frozen_export),
                source_receipt=file_receipt(raw_path),
            )
            campaign.validate_seed_batch(batch, authenticate=True)
            write_once(batch_dir / "dedup-report.json", dedup_report)
            write_once(batch_dir / "seed-batch.json", batch)
        except (ServiceError, campaign.CampaignError, OSError) as exc:
            batch, terminal_reason = synthesize_terminal(
                batch_dir,
                packet,
                "SEED-BATCH-PROVIDER-STOP",
                f"provider output failed deterministic admission: {exc}",
            )
    else:
        reason = stop_reason or f"provider exited with status {exit_code}"
        batch, terminal_reason = synthesize_terminal(
            batch_dir, packet, stop_terminal, reason
        )
    if terminal_reason is None:
        terminal_reason = "provider batch passed deterministic admission"
    receipts: dict[str, Any] = {
        "packet": file_receipt(packet_path),
        "standing_authorization": packet["standing_authorization"],
        "snapshot_admission": packet["snapshot_admission"],
        "prompt": packet["prompt"],
        "task": packet["task"],
        "seed_batch": file_receipt(batch_dir / "seed-batch.json"),
    }
    for key, name in (
        ("raw_response", "raw-response.json"),
        ("dedup_report", "dedup-report.json"),
        ("events", "events.jsonl"),
        ("provider_log", "provider.log"),
        ("attempt", "attempt.json"),
        ("provider_start", "provider-start.json"),
    ):
        path = batch_dir / name
        receipts[key] = file_receipt(path) if path.is_file() else None
    attempt_payload = (
        read_json(batch_dir / "attempt.json", "finalized attempt")
        if (batch_dir / "attempt.json").is_file()
        else None
    )
    receipts["invocation_event"] = (
        attempt_payload.get("ledger_event")
        if isinstance(attempt_payload, dict)
        else None
    )
    result = {
        "schema_version": 1,
        "protocol": PROTOCOL_VERSION,
        "campaign_id": packet["campaign_id"],
        "requested_seed_count": packet["requested_seed_count"],
        "feedback_epoch_sha256": packet["feedback_epoch_sha256"],
        "started_at": started_at,
        "finished_at": now(),
        "provider_exit_code": exit_code,
        "terminal": batch["terminal"],
        "seed_count": len(batch["seeds"]),
        "claim_level": "proposal",
        "validation": "scripts/check_research_campaign.py --seed-batch",
        "terminal_reason": terminal_reason,
        "receipts": receipts,
        "route_action": "none",
        "proof_movement": "neutral",
        "origin": "standing-authorized-provider",
    }
    write_once(result_path, result)
    batch_payload = read_json(seed_path, "finalized seed batch")
    validate_v3_result_receipt(
        service_dir, result_path, seed_path, batch_payload
    )
    if (batch_dir / "attempt.json").is_file():
        _authorization_path, authorization = active_standing_authorization(service_dir)
        complete_invocation_event(
            service_dir,
            authorization,
            campaign_id=str(packet["campaign_id"]),
            result_path=result_path,
            seed_path=seed_path,
        )
    return result


def authenticate_queue(
    entry_path: Path, *, mode: str = "historical"
) -> tuple[dict[str, Any], Path, dict[str, Any]]:
    entry = read_json(entry_path, "queue entry")
    expected_keys = {
        "schema_version",
        "protocol",
        "campaign_id",
        "queued_at",
        "packet",
        "standing_authorization",
        "approved_prompt_sha256",
        "approved_task_sha256",
        "approval_ref",
        "provider_invocations_authorized",
        "route_or_experiment_authority",
    }
    if set(entry) != expected_keys or entry.get("schema_version") != 1:
        raise ServiceError("queue entry has an unexpected closed-object contract")
    if (
        entry.get("protocol") != PROTOCOL_VERSION
        or parse_timestamp(entry.get("queued_at")) is None
        or entry.get("route_or_experiment_authority") != "none"
        or not isinstance(entry.get("approval_ref"), str)
        or not entry["approval_ref"].strip()
        or entry.get("provider_invocations_authorized") != 1
        or isinstance(entry.get("provider_invocations_authorized"), bool)
    ):
        raise ServiceError("queue entry authority or timestamp is invalid")
    packet_path = authenticate_receipt(entry.get("packet"), "queue packet")
    packet = verify_packet(packet_path, mode=mode)
    campaign_id = safe_leaf_id(packet.get("campaign_id"), "queue campaign_id")
    packet_service = service_directory(Path(str(packet.get("service_dir"))))
    validate_service_state_layout(packet_service)
    expected_entry_path = service_state_path(
        packet_service, "queue", f"{campaign_id}.json"
    )
    if Path(os.path.abspath(entry_path)) != expected_entry_path:
        raise ServiceError("queue entry is outside its canonical campaign path")
    if entry.get("campaign_id") != packet["campaign_id"]:
        raise ServiceError("queue and packet campaign identities differ")
    if entry.get("standing_authorization") != packet["standing_authorization"]:
        raise ServiceError("queue and packet standing authorizations differ")
    if entry.get("approved_prompt_sha256") != packet["prompt"]["sha256"]:
        raise ServiceError("queued prompt is not the approved prompt")
    if entry.get("approved_task_sha256") != packet["task"]["sha256"]:
        raise ServiceError("queued task is not the approved task")
    authorization_path = authenticate_receipt(
        packet["standing_authorization"], "queue standing authorization"
    )
    authorization = verify_standing_authorization(
        authorization_path, service_dir=packet_service, mode=mode
    )
    if entry.get("approval_ref") != authorization.get("approval_ref"):
        raise ServiceError("queue approval reference differs from standing authority")
    return entry, packet_path, packet


def validate_provider_start(
    service_dir: Path,
    campaign_id: str,
    *,
    expected_attempt_event: dict[str, str],
) -> dict[str, Any]:
    path = service_dir / "batches" / campaign_id / "provider-start.json"
    if not path.is_file():
        raise ServiceError(
            "charged attempt has no durable provider-start acknowledgement; "
            "operator diagnosis is required"
        )
    value = read_json(path, "provider start")
    expected = {
        "schema_version",
        "protocol",
        "campaign_id",
        "pid",
        "process_identity",
        "started_at",
        "attempt_event",
        "prompt",
        "meaning",
    }
    if set(value) != expected or value.get("schema_version") != 1:
        raise ServiceError("provider-start acknowledgement is malformed")
    if (
        value.get("protocol") != PROTOCOL_VERSION
        or value.get("campaign_id") != campaign_id
        or value.get("attempt_event") != expected_attempt_event
        or parse_timestamp(value.get("started_at")) is None
        or not isinstance(value.get("pid"), int)
        or isinstance(value.get("pid"), bool)
        or int(value["pid"]) < 1
        or not isinstance(value.get("process_identity"), dict)
        or value.get("meaning")
        != "durable process acknowledgement committed before prompt delivery"
    ):
        raise ServiceError("provider-start acknowledgement identity differs")
    identity = value["process_identity"]
    if (
        set(identity) != {"pid", "boot_id", "start_ticks", "process_group_id"}
        or identity.get("pid") != value.get("pid")
        or not isinstance(identity.get("boot_id"), str)
        or not identity["boot_id"].strip()
        or any(
            not isinstance(identity.get(key), int)
            or isinstance(identity.get(key), bool)
            or int(identity[key]) < 1
            for key in ("start_ticks", "process_group_id")
        )
    ):
        raise ServiceError("provider-start process identity is malformed")
    prompt_path = authenticate_receipt(value.get("prompt"), "provider-start prompt")
    packet_path = service_dir / "batches" / campaign_id / "packet.json"
    packet = verify_packet(packet_path, mode="historical")
    if packet.get("campaign_id") != campaign_id or packet.get("prompt") != file_receipt(
        prompt_path
    ):
        raise ServiceError("provider-start acknowledgement names another prompt")
    return value


def set_affinity(pid: int, cores: int) -> None:
    if not hasattr(os, "sched_getaffinity"):
        return
    try:
        allowed = sorted(os.sched_getaffinity(0))[:cores]
        if allowed:
            os.sched_setaffinity(pid, allowed)
    except (OSError, ValueError):
        pass


def begin_invocation_event(
    service_dir: Path,
    *,
    authorization_path: Path,
    authorization: dict[str, Any],
    entry_path: Path,
    packet_path: Path,
    packet: dict[str, Any],
    started_at: str,
    command: list[str],
) -> dict[str, Any]:
    accounting = validate_accounting_chain(service_dir, authorization)
    if accounting["unresolved_attempt_ordinal"] is not None:
        raise ServiceError("an unresolved invocation already holds the provider circuit")
    if accounting["charged_count"] >= int(
        authorization["limits"]["max_total_invocations"]
    ):
        raise ServiceError("provider lifetime ceiling is already reached")
    event_index = int(accounting["event_count"]) + 1
    charged_ordinal = int(accounting["charged_count"]) + 1
    event = {
        "schema_version": 1,
        "protocol": INVOCATION_LEDGER_PROTOCOL,
        "event_index": event_index,
        "event_type": "attempt",
        "charged_ordinal": charged_ordinal,
        "previous": accounting["head"],
        "campaign_id": packet["campaign_id"],
        "created_at": started_at,
        "packet": file_receipt(packet_path),
        "queue": file_receipt(entry_path),
        "standing_authorization": file_receipt(authorization_path),
        "generation_mode": packet["generation_mode"],
        "requested_seed_count": packet["requested_seed_count"],
        "feedback_epoch_sha256": packet["feedback_epoch_sha256"],
        "retry_authority": "none",
    }
    # The event points to the previously committed event, not the mutable head
    # cache.  Replace the helper's head receipt with the head's last_event value.
    head = read_json(accounting_head_path(service_dir), "invocation accounting head")
    event["previous"] = head["last_event"]
    event_path = accounting_event_path(
        service_dir, event_index, "attempt", charged_ordinal
    )
    write_once(event_path, event)
    attempt = {
        "schema_version": 1,
        "protocol": PROTOCOL_VERSION,
        "campaign_id": packet["campaign_id"],
        "started_at": started_at,
        "queue": file_receipt(entry_path),
        "packet": file_receipt(packet_path),
        "command": command,
        "provider_invocation_ordinal": charged_ordinal,
        "ledger_event": file_receipt(event_path),
        "retry_authority": "none",
    }
    attempt_path = service_dir / "batches" / packet["campaign_id"] / "attempt.json"
    write_once(attempt_path, attempt)
    atomic_json(
        accounting_head_path(service_dir),
        {
            "schema_version": 1,
            "protocol": INVOCATION_LEDGER_PROTOCOL,
            "baseline": authorization["accounting_baseline"],
            "event_count": event_index,
            "charged_count": charged_ordinal,
            "last_event": file_receipt(event_path),
            "unresolved_attempt_ordinal": charged_ordinal,
            "updated_at": now(),
        },
    )
    validate_accounting_chain(service_dir, authorization)
    return attempt


def _accounting_outcome_class(
    terminal: str, *, provider_invoked: bool
) -> str:
    if not provider_invoked:
        return "charged_prelaunch_stop"
    outcome = {
        "SEED-BATCH-COMPLETE": "complete",
        "SEED-BATCH-NOVELTY-STOP": "novelty_stop",
        "SEED-BATCH-PROVIDER-STOP": "provider_stop",
        "SEED-BATCH-PACKET-MISMATCH": "packet_mismatch_after_invocation",
    }.get(terminal)
    if outcome is None:
        raise ServiceError("cannot classify an unknown invocation terminal")
    return outcome


def validate_charged_prelaunch_stop_result(
    service_dir: Path,
    campaign_id: str,
    result: dict[str, Any],
) -> None:
    """Accept only the exact operator closure for a spent, unlaunched attempt."""
    receipts = result.get("receipts") or {}
    batch_dir = service_state_path(
        service_dir,
        "batches",
        safe_leaf_id(campaign_id, "prelaunch-stop campaign_id"),
    )
    execution_artifacts = {
        "provider_start": batch_dir / "provider-start.json",
        "raw_response": batch_dir / "raw-response.json",
        "dedup_report": batch_dir / "dedup-report.json",
        "events": batch_dir / "events.jsonl",
        "provider_log": batch_dir / "provider.log",
    }
    if (
        result.get("terminal") != "SEED-BATCH-PROVIDER-STOP"
        or result.get("seed_count") != 0
        or result.get("provider_exit_code") is not None
        or not str(result.get("terminal_reason") or "").startswith(
            "operator-diagnosed charged prelaunch stop;"
        )
        or any(receipts.get(key) is not None for key in execution_artifacts)
        or any(path.exists() for path in execution_artifacts.values())
    ):
        raise ServiceError(
            "an unacknowledged attempt requires one exact operator-diagnosed "
            "prelaunch-stop result with no provider execution artifacts"
        )


def make_invocation_outcome(
    service_dir: Path,
    *,
    head: dict[str, Any],
    campaign_id: str,
    result_path: Path,
    seed_path: Path,
) -> dict[str, Any]:
    result = read_json(result_path, "invocation result")
    terminal = result.get("terminal")
    if terminal not in PROVIDER_RESULT_TERMINALS:
        raise ServiceError("cannot ledger an unknown result terminal")
    batch = read_json(seed_path, "invocation seed batch")
    if (
        result.get("campaign_id") != campaign_id
        or batch.get("campaign_id") != campaign_id
        or batch.get("terminal") != terminal
        or result.get("seed_count") != len(batch.get("seeds") or [])
        or parse_timestamp(result.get("finished_at")) is None
    ):
        raise ServiceError("result artifacts differ from the invocation being closed")
    attempt_path = authenticate_receipt(
        head.get("last_event"), "unresolved attempt event"
    )
    attempt = read_json(attempt_path, "unresolved attempt event")
    if attempt.get("event_type") != "attempt" or attempt.get(
        "campaign_id"
    ) != campaign_id:
        raise ServiceError("result campaign differs from the unresolved attempt")
    ordinal = head.get("unresolved_attempt_ordinal")
    if not isinstance(ordinal, int) or ordinal != attempt.get("charged_ordinal"):
        raise ServiceError("unresolved accounting ordinal differs from its attempt")
    provider_start_path = service_dir / "batches" / campaign_id / "provider-start.json"
    provider_invoked = provider_start_path.is_file()
    if provider_invoked:
        validate_provider_start(
            service_dir,
            campaign_id,
            expected_attempt_event=file_receipt(attempt_path),
        )
    else:
        validate_charged_prelaunch_stop_result(
            service_dir,
            campaign_id,
            result,
        )
    return {
        "schema_version": 1,
        "protocol": INVOCATION_LEDGER_PROTOCOL,
        "event_index": int(head["event_count"]) + 1,
        "event_type": "outcome",
        "charged_ordinal": ordinal,
        "previous": file_receipt(attempt_path),
        "attempt_event": file_receipt(attempt_path),
        "campaign_id": campaign_id,
        "finished_at": result["finished_at"],
        "provider_invoked": provider_invoked,
        "outcome_class": _accounting_outcome_class(
            str(terminal), provider_invoked=provider_invoked
        ),
        "terminal": terminal,
        "seed_count": result["seed_count"],
        "result": file_receipt(result_path),
        "seed_batch": file_receipt(seed_path),
    }


def accounting_transition_preflight(
    service_dir: Path, authorization: dict[str, Any]
) -> dict[str, Any]:
    """Validate strict accounting or commit one exact durable outcome tail."""
    try:
        accounting = validate_accounting_chain(service_dir, authorization)
    except ServiceError as exc:
        if str(exc) != "invocation accounting head/event count differs":
            raise
    else:
        return {
            "recovered": False,
            "campaign_id": None,
            "accounting_head": accounting.get("head"),
            "outcome_event": None,
        }

    head_path = accounting_head_path(service_dir)
    head = read_json(head_path, "invocation accounting head")
    events = sorted(accounting_event_directory(service_dir).glob("*.json"))
    committed_event_count = head.get("event_count")
    if (
        not isinstance(committed_event_count, int)
        or isinstance(committed_event_count, bool)
        or committed_event_count < 0
    ):
        raise ServiceError("invocation accounting head event count is malformed")
    if len(events) != committed_event_count + 1:
        raise ServiceError("invocation accounting head/event count differs")

    committed = validate_accounting_chain(
        service_dir,
        authorization,
        _validate_committed_prefix_with_one_tail=True,
    )
    unresolved = committed.get("unresolved_record")
    if not isinstance(unresolved, dict):
        raise ServiceError(
            "an uncommitted accounting tail has no exact unresolved predecessor"
        )
    campaign_id = safe_leaf_id(
        unresolved.get("campaign_id"), "recoverable outcome campaign_id"
    )
    batch_dir = service_dir / "batches" / campaign_id
    result_path = batch_dir / "result-receipt.json"
    seed_path = batch_dir / "seed-batch.json"
    if not result_path.is_file() or not seed_path.is_file():
        raise ServiceError(
            "recoverable outcome tail lacks its canonical result or seed batch"
        )
    batch = read_json(seed_path, "recoverable outcome seed batch")
    validate_v3_result_receipt(
        service_dir,
        result_path,
        seed_path,
        batch,
    )
    tail_path = events[-1]
    tail = read_json(tail_path, "uncommitted invocation outcome")
    expected_tail = make_invocation_outcome(
        service_dir,
        head=head,
        campaign_id=campaign_id,
        result_path=result_path,
        seed_path=seed_path,
    )
    expected_path = accounting_event_path(
        service_dir,
        int(expected_tail["event_index"]),
        "outcome",
        int(expected_tail["charged_ordinal"]),
    )
    if tail != expected_tail or tail_path != expected_path:
        raise ServiceError(
            "accounting tail exists beyond the head and is not the exact recoverable outcome"
        )
    atomic_json(
        head_path,
        {
            "schema_version": 1,
            "protocol": INVOCATION_LEDGER_PROTOCOL,
            "baseline": authorization["accounting_baseline"],
            "event_count": tail["event_index"],
            "charged_count": tail["charged_ordinal"],
            "last_event": file_receipt(tail_path),
            "unresolved_attempt_ordinal": None,
            "updated_at": now(),
        },
    )
    accounting = validate_accounting_chain(service_dir, authorization)
    return {
        "recovered": True,
        "campaign_id": campaign_id,
        "accounting_head": accounting["head"],
        "outcome_event": file_receipt(tail_path),
    }


def complete_invocation_event(
    service_dir: Path,
    authorization: dict[str, Any],
    *,
    campaign_id: str,
    result_path: Path,
    seed_path: Path,
) -> dict[str, Any]:
    accounting_transition_preflight(service_dir, authorization)
    head_path = accounting_head_path(service_dir)
    accounting = validate_accounting_chain(service_dir, authorization)
    result = read_json(result_path, "invocation result")
    if accounting["unresolved_attempt_ordinal"] is None:
        matches = [
            record
            for record in accounting["records"]
            if record.get("campaign_id") == campaign_id
        ]
        if len(matches) == 1 and isinstance(matches[0].get("result"), dict):
            return matches[0]["result"]
        raise ServiceError("invocation outcome is already closed under another identity")
    head = read_json(head_path, "invocation accounting head")
    outcome = make_invocation_outcome(
        service_dir,
        head=head,
        campaign_id=campaign_id,
        result_path=result_path,
        seed_path=seed_path,
    )
    event_index = int(outcome["event_index"])
    ordinal = int(outcome["charged_ordinal"])
    outcome_path = accounting_event_path(
        service_dir, event_index, "outcome", ordinal
    )
    write_once(outcome_path, outcome)
    atomic_json(
        head_path,
        {
            "schema_version": 1,
            "protocol": INVOCATION_LEDGER_PROTOCOL,
            "baseline": authorization["accounting_baseline"],
            "event_count": event_index,
            "charged_count": ordinal,
            "last_event": file_receipt(outcome_path),
            "unresolved_attempt_ordinal": None,
            "updated_at": now(),
        },
    )
    validate_accounting_chain(service_dir, authorization)
    return result


def resolve_charged_prelaunch_stop(
    service_dir: Path,
    *,
    campaign_id: str,
    approval_ref: str,
    reason: str,
) -> dict[str, Any]:
    """Close one charged attempt proven not to have crossed the provider boundary."""
    campaign_id = safe_leaf_id(campaign_id, "prelaunch-stop campaign_id")
    if not isinstance(approval_ref, str) or not approval_ref.strip():
        raise ServiceError("prelaunch-stop operator approval reference is required")
    if not isinstance(reason, str) or not reason.strip():
        raise ServiceError("prelaunch-stop operator diagnosis is required")
    if daemon_receipt(service_dir) is not None or systemd_main_pid() is not None:
        raise ServiceError("stop the authenticated generator daemon before recovery")

    activation = validate_authorization_activation_chain(
        service_dir,
        verify_latest_current=False,
    )
    assert activation is not None
    authorization_path = authenticate_receipt(
        activation["active_authorization"],
        "historical active standing authorization",
    )
    authorization = verify_standing_authorization(
        authorization_path,
        service_dir=service_dir,
        mode="historical",
    )
    if approval_ref != authorization.get("approval_ref"):
        raise ServiceError(
            "prelaunch-stop approval differs from the attempt's standing authority"
        )
    accounting = validate_accounting_chain(service_dir, authorization)
    unresolved = accounting.get("unresolved_record")
    if not isinstance(unresolved, dict):
        raise ServiceError("there is no unresolved charged attempt to diagnose")
    if unresolved.get("campaign_id") != campaign_id:
        raise ServiceError(
            "prelaunch-stop campaign differs from the unresolved charged attempt"
        )

    batch_dir = service_state_path(service_dir, "batches", campaign_id)
    packet_path = batch_dir / "packet.json"
    attempt_path = batch_dir / "attempt.json"
    packet = verify_packet(packet_path, mode="historical")
    attempt = read_json(attempt_path, "charged prelaunch attempt")
    if (
        packet.get("campaign_id") != campaign_id
        or packet.get("standing_authorization") != file_receipt(authorization_path)
        or attempt.get("campaign_id") != campaign_id
        or attempt.get("packet") != file_receipt(packet_path)
        or attempt.get("ledger_event") != unresolved.get("attempt_event")
    ):
        raise ServiceError("prelaunch-stop packet or attempt identity differs")
    execution_artifacts = [
        batch_dir / "provider-start.json",
        batch_dir / "events.jsonl",
        batch_dir / "provider.log",
        batch_dir / "raw-response.json",
        batch_dir / "dedup-report.json",
    ]
    if any(path.exists() for path in execution_artifacts):
        raise ServiceError(
            "prelaunch-stop recovery found provider execution artifacts"
        )

    seed_path = batch_dir / "seed-batch.json"
    result_path = batch_dir / "result-receipt.json"
    expected_batch = stop_batch(packet, "SEED-BATCH-PROVIDER-STOP")
    campaign.validate_seed_batch(expected_batch, authenticate=True)
    if seed_path.is_file():
        if read_json(seed_path, "prelaunch-stop seed batch") != expected_batch:
            raise ServiceError("existing prelaunch-stop seed batch differs")
    else:
        write_once(seed_path, expected_batch)

    terminal_reason = (
        "operator-diagnosed charged prelaunch stop; "
        f"approval_ref={approval_ref}; reason={reason.strip()}"
    )
    receipts = {
        "packet": file_receipt(packet_path),
        "standing_authorization": packet["standing_authorization"],
        "snapshot_admission": packet["snapshot_admission"],
        "prompt": packet["prompt"],
        "task": packet["task"],
        "seed_batch": file_receipt(seed_path),
        "raw_response": None,
        "dedup_report": None,
        "events": None,
        "provider_log": None,
        "attempt": file_receipt(attempt_path),
        "provider_start": None,
        "invocation_event": attempt["ledger_event"],
    }
    result = {
        "schema_version": 1,
        "protocol": PROTOCOL_VERSION,
        "campaign_id": campaign_id,
        "requested_seed_count": packet["requested_seed_count"],
        "feedback_epoch_sha256": packet["feedback_epoch_sha256"],
        "started_at": attempt["started_at"],
        "finished_at": now(),
        "provider_exit_code": None,
        "terminal": expected_batch["terminal"],
        "seed_count": 0,
        "claim_level": "proposal",
        "validation": "scripts/check_research_campaign.py --seed-batch",
        "terminal_reason": terminal_reason,
        "receipts": receipts,
        "route_action": "none",
        "proof_movement": "neutral",
        "origin": "standing-authorized-provider",
    }
    if result_path.is_file():
        existing = read_json(result_path, "prelaunch-stop result")
        if (
            existing.get("terminal_reason") != terminal_reason
            or {key: value for key, value in existing.items() if key != "finished_at"}
            != {key: value for key, value in result.items() if key != "finished_at"}
        ):
            raise ServiceError("existing prelaunch-stop result differs")
        result = existing
    else:
        write_once(result_path, result)
    validate_v3_result_receipt(service_dir, result_path, seed_path, expected_batch)
    complete_invocation_event(
        service_dir,
        authorization,
        campaign_id=campaign_id,
        result_path=result_path,
        seed_path=seed_path,
    )
    closed = validate_accounting_chain(service_dir, authorization)
    return {
        "campaign_id": campaign_id,
        "terminal": result["terminal"],
        "provider_invoked": False,
        "charged_ordinal": unresolved["charged_ordinal"],
        "accounting_head": closed["head"],
        "result": file_receipt(result_path),
        "seed_batch": file_receipt(seed_path),
    }


def run_provider(
    service_dir: Path,
    entry_path: Path,
    state: dict[str, Any],
    stop_flag: dict[str, bool],
) -> dict[str, Any]:
    entry, packet_path, packet = authenticate_queue(entry_path)
    batch_dir = service_dir / "batches" / packet["campaign_id"]
    attempt_path = batch_dir / "attempt.json"
    provider_start_path = batch_dir / "provider-start.json"
    started_at = now()
    timeout_seconds = int(packet["limits"]["wall_minutes"]) * 60
    max_rss = int(packet["limits"]["memory_gib"] * 1024**3)
    max_output = int(packet["limits"]["output_gib"] * 1024**3)
    fresh_attempt = False
    launch_rejection: str | None = None
    with locked_service_state(service_dir):
        entry, packet_path, packet = authenticate_queue(entry_path)
        authorization_path, authorization = active_standing_authorization(service_dir)
        active_receipt = file_receipt(authorization_path)
        if packet["standing_authorization"] != active_receipt:
            if attempt_path.exists():
                raise ServiceError(
                    "an attempted packet names an inactive standing authorization; "
                    "operator diagnosis is required"
                )
            launch_rejection = "packet standing authorization is no longer active"
        elif not attempt_path.exists():
            packet = verify_packet(packet_path, mode="current")
            safety = provider_safety_status(service_dir, authorization)
            if not safety["allowed"]:
                launch_rejection = (
                    "provider launch rejected by current safety gate: "
                    f"{safety['reason']}"
                )
            ready_count = sum(
                int(item.get("seed_count") or 0)
                for item in active_reserve(service_dir)
            )
            other_reserved = 0
            for other in pending_queue(service_dir):
                if other == entry_path:
                    continue
                _other_entry, _other_packet_path, other_packet = authenticate_queue(
                    other
                )
                if other_packet["standing_authorization"] != active_receipt:
                    raise ServiceError(
                        "pending queue contains a packet under an inactive authorization"
                    )
                other_reserved += int(other_packet["requested_seed_count"])
            if (
                ready_count
                + other_reserved
                + int(packet["requested_seed_count"])
                > int(authorization["limits"]["ready_seed_target"])
            ):
                launch_rejection = (
                    "pending packet exceeds the exact ready-seed reservation target"
                )
            if launch_rejection is None:
                admission_path = authenticate_receipt(
                    packet["snapshot_admission"], "launch snapshot admission"
                )
                admission = validate_snapshot_admission(
                    admission_path,
                    snapshot_path=authenticate_receipt(
                        packet["snapshot"], "launch snapshot"
                    ),
                    service_dir=service_dir,
                    campaign_id=str(packet["campaign_id"]),
                    purpose="provider_generation",
                )
                current, reasons = snapshot_currency(
                    admission,
                    service_dir=service_dir,
                    campaign_id=str(packet["campaign_id"]),
                )
                if not current:
                    launch_rejection = (
                        "packet snapshot is stale before provider launch: "
                        + ",".join(reasons)
                    )
            if launch_rejection is None:
                argv = provider_argv(packet, batch_dir)
                begin_invocation_event(
                    service_dir,
                    authorization_path=authorization_path,
                    authorization=authorization,
                    entry_path=entry_path,
                    packet_path=packet_path,
                    packet=packet,
                    started_at=started_at,
                    command=argv,
                )
                fresh_attempt = True

    if launch_rejection is not None:
        return finalize_provider(
            batch_dir,
            packet_path,
            packet,
            None,
            launch_rejection,
            started_at,
            "SEED-BATCH-PACKET-MISMATCH",
        )

    if attempt_path.exists() and not fresh_attempt:
        attempt = read_json(attempt_path, "attempt")
        started_at = str(attempt.get("started_at", started_at))
        if parse_timestamp(started_at) is None:
            raise ServiceError("recorded provider attempt timestamp is invalid")
        if not provider_start_path.exists():
            raise ServiceError(
                "prior charged attempt has no durable provider-start acknowledgement; "
                "retry and automatic terminalization are forbidden pending operator "
                "diagnosis"
            )
        attempt_event = attempt.get("ledger_event")
        if not isinstance(attempt_event, dict):
            raise ServiceError("recorded attempt lacks its ledger-event receipt")
        provider_start = validate_provider_start(
            service_dir,
            str(packet["campaign_id"]),
            expected_attempt_event=attempt_event,
        )
        pid = int(provider_start["pid"])
        expected_identity = provider_start.get("process_identity")
        if process_alive(pid) and not process_identity_matches(expected_identity):
            raise ServiceError(
                "prior provider PID is alive but cannot be authenticated; "
                "the service is circuit-open pending operator diagnosis"
            )
        started = parse_timestamp(started_at)
        recovered_deadline = (
            started + timedelta(seconds=timeout_seconds)
            if started is not None
            else datetime.now(timezone.utc)
        )
        reason: str | None = None
        while process_identity_matches(expected_identity) and not stop_flag["stop"]:
            rss_bytes = process_tree_rss_bytes(pid)
            captured_bytes = output_bytes(batch_dir)
            state.update(
                {
                    "service_status": "running",
                    "job_status": "recovering-existing-provider",
                    "campaign_id": packet["campaign_id"],
                    "provider_pid": pid,
                    "local_process_tree_rss_bytes": rss_bytes,
                    "output_bytes": captured_bytes,
                    "heartbeat_at": now(),
                }
            )
            atomic_json(service_dir / "state.json", state)
            if datetime.now(timezone.utc) >= recovered_deadline:
                reason = "recovered provider wall-time ceiling reached"
            elif rss_bytes > max_rss:
                reason = "recovered provider local process-tree RSS ceiling reached"
            elif captured_bytes > max_output:
                reason = "recovered provider output ceiling reached"
            if reason is not None:
                terminate_provider(pid, expected_identity)
                break
            time.sleep(5)
        if stop_flag["stop"] and process_identity_matches(expected_identity):
            terminate_provider(pid, expected_identity)
            reason = "service stop requested during recovered provider attempt"
        return finalize_provider(
            batch_dir, packet_path, packet, None, reason, started_at
        )

    argv = provider_argv(packet, batch_dir)
    events_path = batch_dir / "events.jsonl"
    log_path = batch_dir / "provider.log"
    prompt_path = authenticate_receipt(packet["prompt"], "provider prompt")
    process: subprocess.Popen[bytes] | None = None
    identity: dict[str, Any] | None = None
    try:
        with events_path.open("wb") as events, log_path.open("wb") as provider_log:
            process = subprocess.Popen(
                argv,
                cwd=ROOT,
                stdin=subprocess.PIPE,
                stdout=events,
                stderr=provider_log,
                start_new_session=True,
            )
            set_affinity(process.pid, int(packet["limits"]["cpu_cores"]))
            identity = process_identity(process.pid)
            if identity is None:
                raise ServiceError(
                    "provider process identity could not be authenticated before prompt delivery"
                )
            write_once(
                provider_start_path,
                {
                    "schema_version": 1,
                    "protocol": PROTOCOL_VERSION,
                    "campaign_id": packet["campaign_id"],
                    "pid": process.pid,
                    "process_identity": identity,
                    "started_at": now(),
                    "attempt_event": read_json(
                        attempt_path, "provider attempt"
                    )["ledger_event"],
                    "prompt": file_receipt(prompt_path),
                    "meaning": (
                        "durable process acknowledgement committed before prompt delivery"
                    ),
                },
            )
            validate_provider_start(
                service_dir,
                str(packet["campaign_id"]),
                expected_attempt_event=read_json(
                    attempt_path, "provider attempt"
                )["ledger_event"],
            )
            assert process.stdin is not None
            process.stdin.write(prompt_path.read_bytes())
            process.stdin.close()
            deadline = time.monotonic() + timeout_seconds
            stop_reason: str | None = None
            while process.poll() is None:
                state.update(
                    {
                        "service_status": "running",
                        "job_status": "provider-running",
                        "campaign_id": packet["campaign_id"],
                        "provider_pid": process.pid,
                        "heartbeat_at": now(),
                        "local_process_tree_rss_bytes": process_tree_rss_bytes(
                            process.pid
                        ),
                        "output_bytes": output_bytes(batch_dir),
                    }
                )
                atomic_json(service_dir / "state.json", state)
                if stop_flag["stop"]:
                    stop_reason = "service stop requested"
                elif time.monotonic() >= deadline:
                    stop_reason = "provider wall-time ceiling reached"
                elif state["local_process_tree_rss_bytes"] > max_rss:
                    stop_reason = "provider local process-tree RSS ceiling reached"
                elif state["output_bytes"] > max_output:
                    stop_reason = "provider output ceiling reached"
                if stop_reason is not None:
                    terminate_provider(process.pid, identity)
                    break
                time.sleep(5)
            exit_code = process.poll()
    except BaseException:
        if process is not None and process_alive(process.pid):
            terminate_provider(process.pid, identity)
        raise
    return finalize_provider(
        batch_dir, packet_path, packet, exit_code, stop_reason, started_at
    )


def stop_requested(service_dir: Path, service_id: str) -> bool:
    path = service_dir / "stop.request.json"
    if not path.is_file():
        return False
    try:
        request = read_json(path, "stop request")
    except ServiceError:
        return True
    return request.get("service_id") in {None, service_id}


def parse_timestamp(value: Any) -> datetime | None:
    if not isinstance(value, str):
        return None
    try:
        parsed = datetime.fromisoformat(value)
    except ValueError:
        return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed.astimezone(timezone.utc)


def authorized_cycle_records(
    service_dir: Path, authorization: dict[str, Any]
) -> list[dict[str, Any]]:
    if authorization.get("accounting_baseline") is not None:
        accounting = validate_accounting_chain(service_dir, authorization)
        _baseline_path, baseline = validate_accounting_baseline(
            authorization["accounting_baseline"], service_dir=service_dir
        )
        excluded_packets = {
            canonical_json_sha256(record["packet"])
            for record in baseline["excluded_historical_records"]
        }
        records = list(accounting["records"])
        batches = service_dir / "batches"
        if batches.exists():
            for packet_path in sorted(batches.glob("*/packet.json")):
                packet = read_json(packet_path, "accounted packet")
                attempt_path = packet_path.parent / "attempt.json"
                result_path = packet_path.parent / "result-receipt.json"
                seed_path = packet_path.parent / "seed-batch.json"
                protocol = packet.get("protocol")
                if attempt_path.is_file() and protocol not in RATE_ACCOUNTING_PROTOCOLS:
                    if (
                        protocol in NON_RATE_HISTORICAL_PROTOCOLS
                        and canonical_json_sha256(file_receipt(packet_path))
                        in excluded_packets
                    ):
                        continue
                    raise ServiceError(
                        "attempted packet uses an unsupported accounting protocol: "
                        f"{packet_path.parent.name}"
                    )
                if protocol != PROTOCOL_VERSION:
                    continue
                if attempt_path.is_file():
                    if result_path.is_file():
                        if not seed_path.is_file():
                            raise ServiceError("v3 result has no seed-batch artifact")
                        batch = read_json(seed_path, "accounted v3 seed batch")
                        validate_v3_result_receipt(
                            service_dir, result_path, seed_path, batch
                        )
                    continue
                if result_path.is_file():
                    if not seed_path.is_file():
                        raise ServiceError("v3 non-invocation result has no seed batch")
                    batch = read_json(seed_path, "v3 non-invocation seed batch")
                    result = validate_v3_result_receipt(
                        service_dir, result_path, seed_path, batch
                    )
                    traces = [
                        packet_path.parent / "provider-start.json",
                        packet_path.parent / "events.jsonl",
                        packet_path.parent / "provider.log",
                        packet_path.parent / "raw-response.json",
                    ]
                    if (
                        result.get("terminal") != "SEED-BATCH-PACKET-MISMATCH"
                        or result.get("provider_exit_code") is not None
                        or any(path.exists() for path in traces)
                    ):
                        raise ServiceError(
                            "unattempted v3 result is not a closed packet mismatch"
                        )
                elif any(
                    (packet_path.parent / name).exists()
                    for name in (
                        "provider-start.json",
                        "events.jsonl",
                        "provider.log",
                        "raw-response.json",
                    )
                ):
                    raise ServiceError("unattempted v3 packet has execution traces")
        records.sort(key=lambda item: int(item.get("charged_ordinal") or 0))
        return records
    records: list[dict[str, Any]] = []
    batches = service_dir / "batches"
    if not batches.exists():
        return records
    for batch_dir in sorted(path for path in batches.iterdir() if path.is_dir()):
        packet_path = batch_dir / "packet.json"
        attempt_path = batch_dir / "attempt.json"
        result_path = batch_dir / "result-receipt.json"
        execution_traces = [
            batch_dir / "provider-start.json",
            batch_dir / "events.jsonl",
            batch_dir / "provider.log",
            batch_dir / "raw-response.json",
        ]
        if attempt_path.is_file() and not packet_path.is_file():
            raise ServiceError(
                f"invocation history has an attempt without a packet: {batch_dir.name}"
            )
        if not packet_path.is_file():
            continue
        try:
            packet = read_json(packet_path, "historical packet")
        except ServiceError as exc:
            raise ServiceError(
                f"invocation history contains an unreadable packet: {batch_dir.name}"
            ) from exc
        if packet.get("protocol") not in RATE_ACCOUNTING_PROTOCOLS:
            continue
        if not attempt_path.is_file():
            if result_path.is_file():
                non_invocation = read_json(
                    result_path, "historical non-invocation result"
                )
                if packet.get("protocol") == PROTOCOL_VERSION:
                    seed_path = batch_dir / "seed-batch.json"
                    if not seed_path.is_file():
                        raise ServiceError(
                            "v3 non-invocation result has no seed batch"
                        )
                    validate_v3_result_receipt(
                        service_dir,
                        result_path,
                        seed_path,
                        read_json(seed_path, "v3 non-invocation seed batch"),
                    )
                if not (
                    packet.get("protocol") == PROTOCOL_VERSION
                    and non_invocation.get("campaign_id")
                    == packet.get("campaign_id")
                    and non_invocation.get("terminal")
                    == "SEED-BATCH-PACKET-MISMATCH"
                    and non_invocation.get("provider_exit_code") is None
                    and not any(path.exists() for path in execution_traces)
                ):
                    raise ServiceError(
                        "invocation history is missing an attempt receipt for "
                        f"{batch_dir.name}"
                    )
                continue
            if any(path.exists() for path in execution_traces):
                raise ServiceError(
                    "invocation history is missing an attempt receipt for "
                    f"{batch_dir.name}"
                )
            continue
        attempt = read_json(attempt_path, "historical attempt")
        if attempt.get("campaign_id") != packet.get("campaign_id"):
            raise ServiceError(
                f"attempt and packet identities differ for {batch_dir.name}"
            )
        started_at = attempt.get("started_at")
        if parse_timestamp(started_at) is None:
            raise ServiceError(
                f"attempt timestamp is invalid for {batch_dir.name}"
            )
        result = None
        if result_path.is_file():
            result = read_json(result_path, "historical result")
            if packet.get("protocol") == PROTOCOL_VERSION:
                seed_path = batch_dir / "seed-batch.json"
                if not seed_path.is_file():
                    raise ServiceError("v3 historical result has no seed batch")
                result = validate_v3_result_receipt(
                    service_dir,
                    result_path,
                    seed_path,
                    read_json(seed_path, "v3 historical seed batch"),
                )
            if result.get("campaign_id") != packet.get("campaign_id"):
                raise ServiceError(
                    f"result and packet identities differ for {batch_dir.name}"
                )
            if not isinstance(result.get("terminal"), str):
                raise ServiceError(
                    f"historical result terminal is missing for {batch_dir.name}"
                )
        records.append(
            {
                "campaign_id": packet.get("campaign_id"),
                "generation_mode": packet.get("generation_mode"),
                "started_at": started_at,
                "result": result,
            }
        )
    records.sort(key=lambda item: str(item.get("started_at") or ""))
    return records


def provider_safety_status(
    service_dir: Path, authorization: dict[str, Any]
) -> dict[str, Any]:
    limits = authorization["limits"]
    accounting = validate_accounting_chain(service_dir, authorization)
    charged_count = int(accounting["charged_count"])
    records = authorized_cycle_records(service_dir, authorization)
    unresolved = [item for item in records if item.get("result") is None]
    completed = [
        item
        for item in records
        if isinstance(item.get("result"), dict)
        and item.get("provider_invoked") is not False
    ]
    consecutive_provider_stops = 0
    consecutive_zero_seed_batches = 0
    for item in reversed(completed):
        result = item["result"]
        if result.get("terminal") == "SEED-BATCH-PACKET-MISMATCH":
            # A stale/mismatched attempted packet is charged but supplies no
            # evidence that the provider-stop circuit recovered.
            continue
        if result.get("terminal") == "SEED-BATCH-PROVIDER-STOP":
            consecutive_provider_stops += 1
        else:
            break
    for item in reversed(completed):
        result = item["result"]
        if result.get("terminal") == "SEED-BATCH-PACKET-MISMATCH":
            # A mismatch is not evidence that novelty production recovered.
            continue
        if (
            result.get("terminal") == "SEED-BATCH-NOVELTY-STOP"
            and int(result.get("seed_count") or 0) == 0
        ):
            consecutive_zero_seed_batches += 1
        else:
            break
    reason = "provider-safety-open"
    allowed = True
    if unresolved:
        reason = "unresolved-attempt-circuit-open"
        allowed = False
    elif charged_count >= int(limits["max_total_invocations"]):
        reason = "standing-total-invocation-cap"
        allowed = False
    elif consecutive_provider_stops >= int(
        limits["max_consecutive_provider_stops"]
    ):
        reason = "provider-stop-circuit-open"
        allowed = False
    elif consecutive_zero_seed_batches >= int(
        limits["max_consecutive_zero_seed_batches"]
    ):
        reason = "zero-seed-circuit-open"
        allowed = False
    return {
        "allowed": allowed,
        "reason": reason,
        "total_invocations": charged_count,
        "consecutive_provider_stops": consecutive_provider_stops,
        "consecutive_zero_seed_batches": consecutive_zero_seed_batches,
        "records": records,
        "unresolved_attempts": len(unresolved),
    }


def generation_gate(
    service_dir: Path, authorization: dict[str, Any]
) -> dict[str, Any]:
    limits = authorization["limits"]
    accounting = validate_accounting_chain(service_dir, authorization)
    reserve = active_reserve(
        service_dir,
        authorization=authorization,
        accounting=accounting,
    )
    unreconciled_seeds = sum(int(item.get("seed_count") or 0) for item in reserve)
    reserved_seed_capacity = pending_reserved_capacity(
        service_dir,
        authorization=authorization,
        accounting=accounting,
    )
    accounted_capacity = unreconciled_seeds + reserved_seed_capacity
    safety = provider_safety_status(service_dir, authorization)
    records = safety["records"]
    current = datetime.now(timezone.utc)
    recent_cutoff = current - timedelta(hours=24)
    recent_calls = sum(
        1
        for item in records
        if (parse_timestamp(item.get("started_at")) or datetime.min.replace(tzinfo=timezone.utc))
        >= recent_cutoff
    )
    gate = {
        "ready": False,
        "reason": "unknown",
        "total_invocations": safety["total_invocations"],
        "calls_last_24h": recent_calls,
        "unreconciled_batches": len(reserve),
        "unreconciled_seeds": unreconciled_seeds,
        "pending_reserved_seed_capacity": reserved_seed_capacity,
        "accounted_seed_capacity": accounted_capacity,
        "consecutive_provider_stops": safety["consecutive_provider_stops"],
        "consecutive_zero_seed_batches": safety[
            "consecutive_zero_seed_batches"
        ],
        "unresolved_attempts": safety.get("unresolved_attempts", 0),
        "next_eligible_at": None,
    }
    gate["ready_seed_target"] = limits["ready_seed_target"]
    gate["seed_deficit"] = max(
        0, int(limits["ready_seed_target"]) - accounted_capacity
    )
    if not safety["allowed"]:
        gate["reason"] = safety["reason"]
        return gate
    if accounted_capacity >= limits["ready_seed_target"]:
        gate["reason"] = "ready-seed-target-met"
        return gate
    gate["ready"] = True
    gate["reason"] = "ready-seed-deficit"
    return gate


def next_campaign_id(service_dir: Path) -> str:
    ordinal = 0
    batches = service_dir / "batches"
    if batches.exists():
        for path in batches.iterdir():
            if not path.is_dir() or "-continuous-seeds-" not in path.name:
                continue
            try:
                ordinal = max(ordinal, int(path.name.rsplit("-", 1)[1]))
            except ValueError:
                continue
    day = datetime.now(timezone.utc).strftime("%Y%m%d")
    return f"{day}-continuous-seeds-{ordinal + 1:03d}"


def prepare_next_cycle(
    service_dir: Path,
    authorization_path: Path,
    authorization: dict[str, Any],
    *,
    state_lock_held: bool = False,
) -> dict[str, Any]:
    gate = generation_gate(service_dir, authorization)
    if not gate["ready"] or int(gate["seed_deficit"]) < 1:
        raise ServiceError("automatic cycle preparation has no unreserved seed deficit")
    requested_seed_count = min(5, int(gate["seed_deficit"]))
    records = authorized_cycle_records(service_dir, authorization)
    modes = authorization["generation_modes"]
    generation_mode = modes[len(records) % len(modes)]
    campaign_id = next_campaign_id(service_dir)
    frozen = freeze_campaign_packet(
        service_dir,
        campaign_id,
        generation_mode,
        authorization_path,
        authorization,
        requested_seed_count,
    )
    packet_path = authenticate_receipt(frozen["packet"], "automatic packet")
    entry = queue_packet(
        service_dir,
        packet_path,
        frozen["packet"]["sha256"],
        frozen["prompt"]["sha256"],
        frozen["task"]["sha256"],
        str(authorization["approval_ref"]),
        state_lock_held=state_lock_held,
    )
    return {
        "campaign_id": campaign_id,
        "generation_mode": generation_mode,
        "requested_seed_count": requested_seed_count,
        "packet": frozen["packet"],
        "queue": file_receipt(
            service_dir / "queue" / f"{campaign_id}.json"
        ),
        "entry": entry,
    }


def command_serve(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    service_dir.mkdir(parents=True, exist_ok=True)
    authorization_path, authorization = active_standing_authorization(service_dir)
    lock_handle = (service_dir / "service.lock").open("a+")
    try:
        fcntl.flock(lock_handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as exc:
        raise ServiceError("another continuous idea-generator daemon holds the lock") from exc
    pid_receipt = {
        "schema_version": 1,
        "protocol": PROTOCOL_VERSION,
        "service_id": args.service_id,
        "supervisor_ref": args.supervisor_ref,
        "implementation_sha256": sha256(Path(__file__).resolve()),
        "standing_authorization": file_receipt(authorization_path),
        "pid": os.getpid(),
        "process_identity": daemon_process_identity(os.getpid()),
        "started_at": now(),
    }
    if pid_receipt["process_identity"] is None:
        raise ServiceError("cannot authenticate the daemon process identity")
    atomic_json(service_dir / "service.pid", pid_receipt)
    stop_flag = {"stop": False}

    def receive_stop(_signum: int, _frame: Any) -> None:
        stop_flag["stop"] = True

    signal.signal(signal.SIGTERM, receive_stop)
    signal.signal(signal.SIGINT, receive_stop)
    state: dict[str, Any] = {
        "schema_version": 1,
        "protocol": PROTOCOL_VERSION,
        "service_id": args.service_id,
        "supervisor_ref": args.supervisor_ref,
        "implementation_sha256": sha256(Path(__file__).resolve()),
        "standing_authorization": file_receipt(authorization_path),
        "service_status": "running",
        "job_status": "idle",
        "campaign_id": None,
        "provider_pid": None,
        "heartbeat_at": now(),
    }
    atomic_json(service_dir / "state.json", state)
    while not stop_flag["stop"] and not stop_requested(service_dir, args.service_id):
        try:
            current_authorization_path, current_authorization = (
                active_standing_authorization(service_dir)
            )
            if (
                current_authorization_path != authorization_path
                or current_authorization != authorization
            ):
                raise ServiceError(
                    "active standing authorization changed while the daemon was live"
                )
        except ServiceError as exc:
            state.update(
                {
                    "service_status": "error",
                    "job_status": "standing-authorization-error",
                    "error": str(exc),
                    "provider_pid": None,
                }
            )
            break
        with locked_service_state(service_dir):
            accounting_transition_preflight(service_dir, authorization)
            reserve = active_reserve(service_dir)
            pending = pending_queue(service_dir)
            gate = generation_gate(service_dir, authorization)
        if pending:
            try:
                result = run_provider(service_dir, pending[0], state, stop_flag)
                with locked_service_state(service_dir):
                    completed_reserve = active_reserve(service_dir)
                    completed_pending_count = len(pending_queue(service_dir))
                state.update(
                    {
                        "job_status": result["terminal"],
                        "campaign_id": result["campaign_id"],
                        "provider_pid": None,
                        "last_result": result,
                        "reserve": completed_reserve,
                        "pending_queue_count": completed_pending_count,
                    }
                )
            except (ServiceError, campaign.CampaignError, OSError, subprocess.SubprocessError) as exc:
                state.update(
                    {
                        "service_status": "error",
                        "job_status": "operational-error",
                        "error": str(exc),
                        "provider_pid": None,
                    }
                )
        elif gate["ready"]:
            try:
                state.update(
                    {
                        "service_status": "running",
                        "job_status": "preparing-next-cycle",
                        "generation_gate": gate,
                        "heartbeat_at": now(),
                    }
                )
                atomic_json(service_dir / "state.json", state)
                with locked_service_state(service_dir):
                    prepared = prepare_next_cycle(
                        service_dir,
                        authorization_path,
                        authorization,
                        state_lock_held=True,
                    )
                    prepared_pending_count = len(pending_queue(service_dir))
                state.update(
                    {
                        "service_status": "running",
                        "job_status": "cycle-prepared",
                        "campaign_id": prepared["campaign_id"],
                        "last_prepared": prepared,
                        "pending_queue_count": prepared_pending_count,
                    }
                )
            except (ServiceError, campaign.CampaignError, OSError, subprocess.SubprocessError) as exc:
                state.update(
                    {
                        "service_status": "error",
                        "job_status": "automatic-prepare-error",
                        "error": str(exc),
                        "provider_pid": None,
                    }
                )
        else:
            state.update(
                {
                    "service_status": "idle",
                    "job_status": gate["reason"],
                    "reserve": reserve,
                    "pending_queue_count": len(pending),
                    "generation_gate": gate,
                    "provider_pid": None,
                }
            )
        state["heartbeat_at"] = now()
        atomic_json(service_dir / "state.json", state)
        if state.get("service_status") == "error":
            break
        time.sleep(10)
    state.update(
        {
            "service_status": "stopped" if stop_flag["stop"] or stop_requested(service_dir, args.service_id) else state.get("service_status"),
            "provider_pid": None,
            "stopped_at": now(),
            "heartbeat_at": now(),
        }
    )
    atomic_json(service_dir / "state.json", state)
    return 1 if state.get("service_status") == "error" else 0


def service_status(service_dir: Path) -> dict[str, Any]:
    pid = daemon_receipt(service_dir)
    state_path = service_dir / "state.json"
    state = read_json(state_path, "state") if state_path.is_file() else None
    queue = sorted((service_dir / "queue").glob("*.json")) if (service_dir / "queue").exists() else []
    authorization_receipt = None
    authorization_pointer_receipt = None
    gate = None
    authorization_error = None
    pointer_path = active_authorization_pointer_path(service_dir)
    if pointer_path.is_file():
        try:
            authorization_path, authorization = active_standing_authorization(
                service_dir
            )
            authorization_receipt = file_receipt(authorization_path)
            authorization_pointer_receipt = file_receipt(pointer_path)
            gate = generation_gate(service_dir, authorization)
        except ServiceError as exc:
            authorization_error = str(exc)
    inventory_error = None
    pending: list[str] | None = None
    reserve: list[dict[str, Any]] | None = None
    try:
        inventory = seed_inventory(service_dir)
        pending = [path.name for path in pending_queue(service_dir)]
        reserve = active_reserve(service_dir)
    except ServiceError as exc:
        inventory = []
        inventory_error = str(exc)
    inventory_counts = {
        state: sum(1 for item in inventory if item["state"] == state)
        for state in (
            "ready",
            "investigating",
            "investigated",
            "legacy_reconciled_investigation_unknown",
        )
    }
    return {
        "protocol": PROTOCOL_VERSION,
        "service_dir": repo_relative(service_dir),
        "daemon_alive": pid is not None,
        "daemon": pid,
        "standing_authorization": authorization_receipt,
        "active_authorization_pointer": authorization_pointer_receipt,
        "standing_authorization_error": authorization_error,
        "inventory_error": inventory_error,
        "generation_gate": gate,
        "state": state,
        "queue_entries": len(queue),
        "pending_queue": pending,
        "active_reserve": reserve,
        "seed_inventory_counts": inventory_counts,
        "investigating_seeds": [
            {
                "campaign_id": item["campaign_id"],
                "seed_id": item["seed_id"],
                "claim": item["claim"],
            }
            for item in inventory
            if item["state"] == "investigating"
        ],
    }


def command_status(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    print(json.dumps(service_status(service_dir), indent=2, sort_keys=True))
    return 0


def command_claim(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    with locked_service_state(service_dir):
        return _command_claim_locked(args, service_dir)


def _command_claim_locked(args: argparse.Namespace, service_dir: Path) -> int:
    safe_leaf_id(args.campaign_id, "campaign_id")
    safe_leaf_id(args.seed_id, "seed_id")
    _authorization_path, authorization = active_standing_authorization(service_dir)
    accounting = validate_accounting_chain(service_dir, authorization)
    seed_path = service_dir / "batches" / args.campaign_id / "seed-batch.json"
    if not seed_path.is_file() or sha256(seed_path) != args.seed_batch_sha256:
        raise ServiceError("claim hash does not authenticate the seed batch")
    batch = read_json(seed_path, "seed batch")
    campaign.validate_seed_batch(batch, authenticate=True)
    matches = [
        seed
        for seed in batch.get("seeds", [])
        if isinstance(seed, dict) and seed.get("seed_id") == args.seed_id
    ]
    if len(matches) != 1:
        raise ServiceError("claim seed_id is not unique in the seed batch")
    selected_seed = matches[0]
    if (service_dir / "consumed" / f"{args.campaign_id}.json").is_file():
        raise ServiceError("legacy-consumed batches cannot acquire v3 claims")
    brief_path = run_artifact_path(args.development_brief)
    if not brief_path.is_file() or sha256(brief_path) != args.development_brief_sha256:
        raise ServiceError("claim hash does not authenticate the development brief")
    task_path = run_artifact_path(args.task_packet)
    if not task_path.is_file() or sha256(task_path) != args.task_packet_sha256:
        raise ServiceError("claim hash does not authenticate the first-test task packet")
    brief = read_json(brief_path, "claimed development brief")
    task = read_json(task_path, "claimed first-test task packet")
    campaign.validate_brief(
        brief,
        brief_path=brief_path,
        task_packet=task,
        authenticate=True,
    )
    execution = task.get("first_test_execution") or {}
    validation = {
        "protocol": "ticket-0119-first-test-validation-v1",
        "approval_ref": campaign.FIRST_TEST_APPROVAL_REF,
        "task_packet": file_receipt(task_path),
        "execution_contract_id": execution.get("contract_id"),
        "guard_component": execution.get("guard_component"),
        "budget": task.get("budget"),
        "write_paths": (task.get("ownership") or {}).get("write_paths"),
        "claims_allowed": task.get("claims_allowed"),
        "decision": "pass",
    }
    deterministic = {
        "seed": {
            "campaign_id": args.campaign_id,
            "seed_id": args.seed_id,
            "seed_batch": file_receipt(seed_path),
        },
        "development_brief": file_receipt(brief_path),
        "task_packet": file_receipt(task_path),
        "first_test_validation": validation,
    }
    path = seed_claim_path(service_dir, args.campaign_id, args.seed_id)
    if path.is_file():
        existing = validate_seed_claim(
            path,
            campaign_id=args.campaign_id,
            seed_id=args.seed_id,
            seed_path=seed_path,
        )
        if any(existing.get(key) != value for key, value in deterministic.items()):
            raise ServiceError("existing claim differs from the exact retry contract")
        print(
            json.dumps(
                {**existing, "claim_receipt": file_receipt(path)},
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    inventory = seed_inventory(
        service_dir,
        authorization=authorization,
        accounting=accounting,
    )
    ready_matches = [
        item
        for item in inventory
        if item.get("campaign_id") == args.campaign_id
        and item.get("seed_id") == args.seed_id
        and item.get("seed_batch") == file_receipt(seed_path)
    ]
    if len(ready_matches) != 1 or ready_matches[0].get("state") != "ready":
        raise ServiceError(
            "claim requires one authenticated seed in exact ready state"
        )
    investigating = [
        item for item in inventory if item.get("state") == "investigating"
    ]
    if len(investigating) >= 4:
        raise ServiceError("four investigations are already active")
    selected_family = (selected_seed.get("mechanism") or {}).get("family_hint")
    same_family = 0
    for item in investigating:
        other_path = authenticate_receipt(
            item.get("seed_batch"), "investigating seed batch"
        )
        other_batch = read_json(other_path, "investigating seed batch")
        other = [
            seed
            for seed in other_batch.get("seeds", [])
            if isinstance(seed, dict) and seed.get("seed_id") == item.get("seed_id")
        ]
        if len(other) != 1:
            raise ServiceError("investigating seed identity is ambiguous")
        if (other[0].get("mechanism") or {}).get("family_hint") == selected_family:
            same_family += 1
    if same_family >= 2:
        raise ServiceError(
            "two investigations from this mechanism family are already active"
        )
    claim = {
        "schema_version": 3,
        "protocol": CLAIM_PROTOCOL,
        "claim_id": f"{args.campaign_id}:{args.seed_id}",
        "claimed_at": now(),
        **deterministic,
        "meaning": (
            "this individual proposal is assigned and no longer counts toward "
            "the ten-item ready queue; it is not admitted proof evidence"
        ),
    }
    write_once(path, claim)
    validate_seed_claim(
        path,
        campaign_id=args.campaign_id,
        seed_id=args.seed_id,
        seed_path=seed_path,
    )
    print(json.dumps({**claim, "claim_receipt": file_receipt(path)}, indent=2, sort_keys=True))
    return 0


def command_reconcile(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    with locked_service_state(service_dir):
        return _command_reconcile_locked(args, service_dir)


def _command_reconcile_locked(args: argparse.Namespace, service_dir: Path) -> int:
    safe_leaf_id(args.campaign_id, "campaign_id")
    safe_leaf_id(args.seed_id, "seed_id")
    _authorization_path, authorization = active_standing_authorization(service_dir)
    accounting = validate_accounting_chain(service_dir, authorization)
    seed_path = service_dir / "batches" / args.campaign_id / "seed-batch.json"
    if not seed_path.is_file() or sha256(seed_path) != args.seed_batch_sha256:
        raise ServiceError("reconciliation hash does not authenticate the seed batch")
    claim_path = seed_claim_path(service_dir, args.campaign_id, args.seed_id)
    if not claim_path.is_file():
        raise ServiceError("cannot reconcile a seed without an authenticated claim")
    claim = validate_seed_claim(
        claim_path,
        campaign_id=args.campaign_id,
        seed_id=args.seed_id,
        seed_path=seed_path,
    )
    investigating = [
        item
        for item in seed_inventory(
            service_dir,
            authorization=authorization,
            accounting=accounting,
        )
        if item.get("campaign_id") == args.campaign_id
        and item.get("seed_id") == args.seed_id
        and item.get("state") == "investigating"
    ]
    if len(investigating) != 1:
        raise ServiceError("reconciliation requires one investigating seed")
    source_path = run_artifact_path(args.feedback)
    if not source_path.is_file() or sha256(source_path) != args.feedback_sha256:
        raise ServiceError("reconciliation hash does not authenticate feedback")
    validate_investigation_feedback(
        source_path,
        claim=claim,
        campaign_id=args.campaign_id,
        seed_id=args.seed_id,
        seed_path=seed_path,
    )
    destination = seed_feedback_path(service_dir, args.campaign_id, args.seed_id)
    payload = read_json(source_path, "investigation feedback")
    if source_path != destination:
        write_once(destination, payload)
    validate_investigation_feedback(
        destination,
        claim=claim,
        campaign_id=args.campaign_id,
        seed_id=args.seed_id,
        seed_path=seed_path,
    )
    result = {
        "schema_version": 1,
        "protocol": PROTOCOL_VERSION,
        "campaign_id": args.campaign_id,
        "seed_id": args.seed_id,
        "feedback": file_receipt(destination),
        "meaning": (
            "root-admitted per-seed learning is available to every subsequently "
            "frozen idea packet; this receipt does not itself admit a route"
        ),
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


def command_import_root_batch(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    if not isinstance(args.approval_ref, str) or not args.approval_ref.strip():
        raise ServiceError("root import approval reference is required")
    source_path = run_artifact_path(args.seed_batch)
    if not source_path.is_file() or sha256(source_path) != args.seed_batch_sha256:
        raise ServiceError("root import hash does not authenticate the seed batch")
    batch = read_json(source_path, "root-origin seed batch")
    campaign.validate_seed_batch(batch, authenticate=True)
    if batch.get("terminal") not in {
        "SEED-BATCH-COMPLETE",
        "SEED-BATCH-NOVELTY-STOP",
    } or not batch.get("seeds"):
        raise ServiceError("root import requires at least one validated proposal seed")
    campaign_id = safe_leaf_id(batch.get("campaign_id"), "root campaign_id")
    if "-root-seeds-" not in campaign_id:
        raise ServiceError("root-origin campaign identity must contain -root-seeds-")
    if "requested_seed_count" not in batch:
        raise ServiceError("root import must state its frozen requested_seed_count")
    requested_seed_count = batch["requested_seed_count"]
    if (
        not isinstance(requested_seed_count, int)
        or isinstance(requested_seed_count, bool)
        or not 1 <= requested_seed_count <= 5
    ):
        raise ServiceError("root import requested_seed_count is invalid")
    snapshot_path = authenticate_receipt(batch.get("snapshot"), "root snapshot")
    snapshot = read_json(snapshot_path, "root snapshot summary")
    snapshot_epoch = snapshot.get("feedback_epoch_sha256")
    snapshot_build_path, snapshot_build = validate_snapshot_build_receipt(
        snapshot_path,
        service_dir=service_dir,
        campaign_id=campaign_id,
        purpose="root_fallback",
        mode="historical",
    )
    prior_registry_path = authenticate_receipt(
        snapshot_build["outputs"]["prior_idea_registry_json"],
        "root prior-idea registry",
    )
    if (
        not isinstance(snapshot_epoch, str)
        or len(snapshot_epoch) != 64
        or not prior_registry_path.is_file()
        or snapshot.get("prior_idea_registry_sha256")
        != sha256(prior_registry_path)
    ):
        raise ServiceError(
            "root import snapshot lacks authenticated current idea/feedback memory"
        )
    semantic_screen_path = run_artifact_path(args.semantic_screen)
    if (
        not semantic_screen_path.is_file()
        or sha256(semantic_screen_path) != args.semantic_screen_sha256
    ):
        raise ServiceError("root import does not authenticate its semantic screen")

    source_run = source_path.parent.resolve()
    service_root = service_dir.resolve()
    if (
        source_run == RUNS_ROOT
        or source_run == service_root
        or service_root in source_run.parents
        or source_run in service_root.parents
    ):
        raise ServiceError(
            "root import source run must be isolated from the service state"
        )
    expected_snapshot = (source_run / "snapshot" / "packet-summary.json").resolve()
    expected_build = (
        source_run
        / "snapshot"
        / build_sol_idea_packet.SNAPSHOT_BUILD_RECEIPT_NAME
    ).resolve()
    expected_admission = (source_run / SNAPSHOT_ADMISSION_NAME).resolve()
    if (
        snapshot_path.resolve() != expected_snapshot
        or snapshot_build_path.resolve() != expected_build
        or snapshot_admission_path(snapshot_path) != expected_admission
    ):
        raise ServiceError("root import snapshot must use its source run layout")
    try:
        semantic_screen_path.resolve().relative_to(source_run)
    except ValueError as exc:
        raise ServiceError("root semantic screen must remain inside its source run") from exc
    if service_root == semantic_screen_path.resolve() or service_root in semantic_screen_path.resolve().parents:
        raise ServiceError("root semantic screen cannot be inside service state")

    with locked_service_state(service_dir):
        authorization_path, authorization, accounting = current_authorized_accounting(
            service_dir
        )
        if args.approval_ref != authorization.get("approval_ref"):
            raise ServiceError(
                "root import approval reference differs from standing authority"
            )
        if pending_reserved_capacity(
            service_dir,
            authorization=authorization,
            accounting=accounting,
        ) != 0:
            raise ServiceError(
                "root fallback import cannot race a pending provider reservation"
            )
        ready_count = sum(
            int(item.get("seed_count") or 0)
            for item in active_reserve(
                service_dir,
                authorization=authorization,
                accounting=accounting,
            )
        )
        if ready_count != 0:
            raise ServiceError("root fallback is authorized only when the ready queue is empty")
        export_path = authenticate_receipt(
            snapshot_build["input_state"]["validated_learning_export"],
            "root validated learning export",
        )
        frozen_export = build_sol_idea_packet.load_validated_learning_export(
            export_path, authenticate_inputs=False
        )
        current_epoch = str(
            snapshot_build["input_state"]["learning_epoch_sha256"]
        )
        if snapshot_epoch != current_epoch:
            raise ServiceError("root import snapshot is stale against current learning")
        current_manifest = build_sol_idea_packet.current_manifest_aggregate_sha256(
            snapshot_path.parent,
            service_dir,
            excluded_campaign_id=campaign_id,
            validated_learning_export=export_path,
        )
        if snapshot.get("manifest_aggregate_sha256") != current_manifest:
            raise ServiceError(
                "root import snapshot is stale against current repository bytes"
            )
        snapshot_admission_path_value = admit_snapshot_build(
            snapshot_path,
            service_dir=service_dir,
            campaign_id=campaign_id,
            purpose="root_fallback",
        )
        validate_root_semantic_screen(
            semantic_screen_path,
            source_seed_path=source_path,
            batch=batch,
            service_dir=service_dir,
            authorization_path=authorization_path,
            snapshot_path=snapshot_path,
            snapshot_build_path=snapshot_build_path,
            prior_registry_path=prior_registry_path,
            feedback_epoch_sha256=current_epoch,
            approval_ref=args.approval_ref,
        )
        filtered, dedup_report = deduplicate_provider_batch(
            service_dir,
            batch,
            requested_seed_count,
            known_memory=frozen_generated_seed_memory(frozen_export),
            source_receipt=file_receipt(source_path),
        )
        if dedup_report["dropped"]:
            raise ServiceError(
                "root import repeats generated seed memory; regenerate from the current snapshot"
            )
        campaign.validate_seed_batch(filtered, authenticate=True)
        batch = filtered
        if len(batch["seeds"]) > int(
            authorization["limits"]["ready_seed_target"]
        ):
            raise ServiceError("root import exceeds the ready-seed target")
        prewrite_authorization_path, prewrite_authorization, prewrite_accounting = (
            current_authorized_accounting(service_dir)
        )
        if (
            file_receipt(prewrite_authorization_path)
            != file_receipt(authorization_path)
            or prewrite_authorization != authorization
        ):
            raise ServiceError("root import authority changed before commit")
        admission = validate_snapshot_admission(
            snapshot_admission_path_value,
            snapshot_path=snapshot_path,
            service_dir=service_dir,
            campaign_id=campaign_id,
            purpose="root_fallback",
        )
        current, reasons = snapshot_currency(
            admission,
            service_dir=service_dir,
            campaign_id=campaign_id,
        )
        if not current:
            raise ServiceError(
                "root import snapshot changed before commit: " + ",".join(reasons)
            )
        batch_dir = service_dir / "batches" / campaign_id
        destination = batch_dir / "seed-batch.json"
        if destination.exists() or batch_dir.exists():
            raise ServiceError("root-origin campaign identity already exists")
        root_packet = {
            "schema_version": 1,
            "protocol": PROTOCOL_VERSION,
            "origin": "root-empty-queue-fallback",
            "campaign_id": campaign_id,
            "created_at": now(),
            "service_dir": repo_relative(service_dir),
            "requested_seed_count": requested_seed_count,
            "feedback_epoch_sha256": current_epoch,
            "standing_authorization": file_receipt(authorization_path),
            "snapshot": file_receipt(snapshot_path),
            "snapshot_build": file_receipt(snapshot_build_path),
            "snapshot_admission": file_receipt(snapshot_admission_path_value),
            "source_seed_batch": file_receipt(source_path),
            "semantic_screen": file_receipt(semantic_screen_path),
            "approval_ref": args.approval_ref,
            "authority": "proposal import only; no route or proof admission",
        }
        write_once(batch_dir / "root-import-packet.json", root_packet)
        write_once(batch_dir / "dedup-report.json", dedup_report)
        write_once(destination, batch)
        postwrite_authorization_path, postwrite_authorization, postwrite_accounting = (
            current_authorized_accounting(service_dir)
        )
        if (
            file_receipt(postwrite_authorization_path)
            != file_receipt(authorization_path)
            or postwrite_authorization != authorization
        ):
            raise ServiceError("root import authority changed during commit")
        current, reasons = snapshot_currency(
            admission,
            service_dir=service_dir,
            campaign_id=campaign_id,
        )
        if not current:
            raise ServiceError(
                "root import snapshot changed during commit: " + ",".join(reasons)
            )
        accounting_head = read_json(
            authenticate_receipt(
                postwrite_accounting["head"], "root commit accounting head"
            ),
            "root commit accounting head",
        )
        accounting_checkpoint = {
            "baseline": postwrite_accounting["baseline"],
            "event_count": postwrite_accounting["event_count"],
            "charged_count": postwrite_accounting["charged_count"],
            "unresolved_attempt_ordinal": postwrite_accounting[
                "unresolved_attempt_ordinal"
            ],
            "last_event": accounting_head["last_event"],
        }
        receipt = {
            "schema_version": 1,
            "protocol": PROTOCOL_VERSION,
            "campaign_id": campaign_id,
            "requested_seed_count": requested_seed_count,
            "feedback_epoch_sha256": current_epoch,
            "started_at": None,
            "finished_at": now(),
            "provider_exit_code": None,
            "terminal": batch["terminal"],
            "seed_count": len(batch["seeds"]),
            "claim_level": "proposal",
            "validation": "scripts/check_research_campaign.py --seed-batch",
            "terminal_reason": "root-origin empty-ready-queue fallback under Ticket 0119",
            "receipts": {
                "root_import_packet": file_receipt(
                    batch_dir / "root-import-packet.json"
                ),
                "standing_authorization": file_receipt(authorization_path),
                "snapshot": file_receipt(snapshot_path),
                "snapshot_build": file_receipt(snapshot_build_path),
                "snapshot_admission": file_receipt(
                    snapshot_admission_path_value
                ),
                "semantic_screen": file_receipt(semantic_screen_path),
                "dedup_report": file_receipt(batch_dir / "dedup-report.json"),
                "seed_batch": file_receipt(destination),
                "source_seed_batch": file_receipt(source_path),
            },
            "route_action": "none",
            "proof_movement": "neutral",
            "origin": "root-empty-queue-fallback",
            "approval_ref": args.approval_ref,
            "root_commit": {
                "schema_version": 1,
                "protocol": "continuous-idea-generator-root-commit-v1",
                "standing_authorization": file_receipt(authorization_path),
                "snapshot_admission": file_receipt(
                    snapshot_admission_path_value
                ),
                "learning_epoch_sha256": current_epoch,
                "workspace_manifest_aggregate_sha256": admission[
                    "workspace_manifest_aggregate_sha256"
                ],
                "accounting_checkpoint": accounting_checkpoint,
                "checks": {
                    "prewrite_current_authority_accounting": "pass",
                    "prewrite_snapshot_currency": "pass",
                    "postwrite_current_authority_accounting": "pass",
                    "postwrite_snapshot_currency": "pass",
                },
            },
        }
        write_once(batch_dir / "result-receipt.json", receipt)
        validate_v3_result_receipt(
            service_dir,
            batch_dir / "result-receipt.json",
            destination,
            batch,
        )
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


def command_consume(args: argparse.Namespace) -> int:
    raise ServiceError(
        "batch-level consume is historical-only under v3; use claim and reconcile per seed"
    )


def command_resolve_prelaunch_stop(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    with locked_service_state(service_dir):
        resolved = resolve_charged_prelaunch_stop(
            service_dir,
            campaign_id=args.campaign_id,
            approval_ref=args.approval_ref,
            reason=args.reason,
        )
    print(json.dumps(resolved, indent=2, sort_keys=True))
    return 0


def command_stop(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    daemon = daemon_receipt(service_dir)
    request = None
    if daemon is not None:
        request = {
            "schema_version": 1,
            "service_id": daemon["service_id"],
            "requested_at": now(),
            "reason": args.reason,
        }
        atomic_json(service_dir / "stop.request.json", request)
    stopped = subprocess.run(
        ["systemctl", "--user", "disable", "--now", SYSTEMD_UNIT_NAME],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if stopped.returncode != 0 and daemon is not None:
        try:
            os.kill(int(daemon["pid"]), signal.SIGTERM)
        except ProcessLookupError:
            pass
    print(
        json.dumps(
            {
                "daemon_alive": daemon is not None,
                "stop_requested": request,
                "unit_disable_returncode": stopped.returncode,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


def add_approval_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--packet", required=True, type=Path)
    parser.add_argument("--packet-sha256", required=True)
    parser.add_argument("--prompt-sha256", required=True)
    parser.add_argument("--task-sha256", required=True)
    parser.add_argument("--approval-ref", required=True)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    configure = subparsers.add_parser(
        "configure", help="freeze one bounded standing generation authorization"
    )
    configure.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    configure.add_argument("--approval-ref", required=True)
    configure.add_argument(
        "--generation-modes",
        nargs="+",
        choices=sorted(SUPPORTED_MODES),
        default=list(DEFAULT_GENERATION_MODES),
    )
    configure.add_argument("--wall-minutes", type=int, default=90)
    configure.add_argument("--ready-seed-target", type=int, default=10)
    configure.add_argument("--max-total-invocations", type=int, default=100)
    configure.add_argument("--max-consecutive-provider-stops", type=int, default=2)
    configure.add_argument("--max-consecutive-zero-seed-batches", type=int, default=2)
    configure.add_argument("--max-inline-bytes", type=int, default=6 * 1024 * 1024)
    configure.set_defaults(function=command_configure)

    prepare = subparsers.add_parser("prepare", help="freeze one provider packet")
    prepare.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    prepare.add_argument("--campaign-id", required=True)
    prepare.add_argument(
        "--generation-mode",
        choices=sorted(SUPPORTED_MODES),
        default="context_rich",
    )
    prepare.add_argument("--requested-seed-count", type=int, default=5)
    prepare.set_defaults(function=command_prepare)

    root_snapshot = subparsers.add_parser(
        "prepare-root-snapshot",
        help="freeze an authenticated empty-queue root proposal snapshot",
    )
    root_snapshot.add_argument(
        "--service-dir", type=Path, default=DEFAULT_SERVICE_DIR
    )
    root_snapshot.add_argument("--campaign-id", required=True)
    root_snapshot.add_argument("--output-dir", required=True, type=Path)
    root_snapshot.set_defaults(function=command_prepare_root_snapshot)

    enqueue = subparsers.add_parser("enqueue", help="queue one exactly approved packet")
    enqueue.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    add_approval_arguments(enqueue)
    enqueue.set_defaults(function=command_enqueue)

    start = subparsers.add_parser(
        "start", help="start the bounded self-refilling daemon"
    )
    start.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    start.add_argument("--authorization", required=True, type=Path)
    start.add_argument("--authorization-sha256", required=True)
    start.set_defaults(function=command_start)

    serve = subparsers.add_parser("serve", help=argparse.SUPPRESS)
    serve.add_argument("--service-dir", type=Path, required=True)
    serve.add_argument("--service-id", required=True)
    serve.add_argument("--supervisor-ref", required=True)
    serve.set_defaults(function=command_serve)

    status = subparsers.add_parser("status", help="show queue, job, and reserve state")
    status.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    status.set_defaults(function=command_status)

    claim = subparsers.add_parser(
        "claim", help="assign one ready seed under an immutable development brief"
    )
    claim.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    claim.add_argument("--campaign-id", required=True)
    claim.add_argument("--seed-id", required=True)
    claim.add_argument("--seed-batch-sha256", required=True)
    claim.add_argument("--development-brief", required=True, type=Path)
    claim.add_argument("--development-brief-sha256", required=True)
    claim.add_argument("--task-packet", required=True, type=Path)
    claim.add_argument("--task-packet-sha256", required=True)
    claim.set_defaults(function=command_claim)

    reconcile = subparsers.add_parser(
        "reconcile", help="record root-admitted learning for one claimed seed"
    )
    reconcile.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    reconcile.add_argument("--campaign-id", required=True)
    reconcile.add_argument("--seed-id", required=True)
    reconcile.add_argument("--seed-batch-sha256", required=True)
    reconcile.add_argument("--feedback", required=True, type=Path)
    reconcile.add_argument("--feedback-sha256", required=True)
    reconcile.set_defaults(function=command_reconcile)

    root_import = subparsers.add_parser(
        "import-root-batch",
        help="import one root-origin proposal batch only when the ready queue is empty",
    )
    root_import.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    root_import.add_argument("--seed-batch", required=True, type=Path)
    root_import.add_argument("--seed-batch-sha256", required=True)
    root_import.add_argument("--semantic-screen", required=True, type=Path)
    root_import.add_argument("--semantic-screen-sha256", required=True)
    root_import.add_argument("--approval-ref", required=True)
    root_import.set_defaults(function=command_import_root_batch)

    consume = subparsers.add_parser(
        "consume", help="historical v2 batch-release command (rejected under v3)"
    )
    consume.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    consume.add_argument("--campaign-id", required=True)
    consume.add_argument("--seed-batch-sha256", required=True)
    consume.add_argument("--reconciliation-ref", required=True)
    consume.set_defaults(function=command_consume)

    resolve_prelaunch = subparsers.add_parser(
        "resolve-prelaunch-stop",
        help="operator-close one charged attempt proven not to have launched",
    )
    resolve_prelaunch.add_argument(
        "--service-dir", type=Path, default=DEFAULT_SERVICE_DIR
    )
    resolve_prelaunch.add_argument("--campaign-id", required=True)
    resolve_prelaunch.add_argument("--approval-ref", required=True)
    resolve_prelaunch.add_argument("--reason", required=True)
    resolve_prelaunch.set_defaults(function=command_resolve_prelaunch_stop)

    stop = subparsers.add_parser("stop", help="gracefully stop daemon and provider child")
    stop.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    stop.add_argument("--reason", required=True)
    stop.set_defaults(function=command_stop)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if getattr(args, "wall_minutes", 1) < 1:
        raise ServiceError("wall-minutes must be positive")
    try:
        return int(args.function(args))
    except (ServiceError, campaign.CampaignError, OSError, subprocess.SubprocessError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
