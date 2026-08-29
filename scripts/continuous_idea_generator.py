#!/usr/bin/env python3
"""Run a bounded, self-refilling, chat-independent research-seed service."""

from __future__ import annotations

import argparse
import copy
from datetime import datetime, timedelta, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
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
PROTOCOL_VERSION = "continuous-idea-generator-v2.1"
RATE_ACCOUNTING_PROTOCOLS = {
    "continuous-idea-generator-v2",
    PROTOCOL_VERSION,
}
WAYFINDER_TICKET = "docs/wayfinder/tickets/0083-continuous-idea-generator-v2.md"
SUPPORTED_MODES = {"context_rich", "failure_dual", "recombination"}
DEFAULT_GENERATION_MODES = ("context_rich", "failure_dual", "recombination")
ACTIVE_AUTHORIZATION_NAME = "active-authorization.json"
AUTHORIZATION_DIRECTORY_NAME = "authorizations"
SYSTEMD_UNIT_NAME = "erdos-szekeres-continuous-idea-generator.service"
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


def atomic_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}-{time.time_ns()}")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    os.replace(temporary, path)


def write_once(path: Path, value: Any) -> None:
    encoded = json.dumps(value, indent=2, sort_keys=True) + "\n"
    if path.exists():
        if path.read_text(encoding="utf-8") != encoded:
            raise ServiceError(f"immutable artifact already exists with other bytes: {path}")
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(encoded, encoding="utf-8")


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
        campaign.SEED_SCHEMA.resolve(),
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
    service_dir: Path, payload: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Drop only deterministic literal repeats; semantic review remains root-only."""
    campaign_id = str(payload.get("campaign_id"))
    known = generated_seed_memory(service_dir, exclude_campaign=campaign_id)
    accepted: list[dict[str, Any]] = []
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
    batch = copy.deepcopy(payload)
    batch["seeds"] = accepted
    batch["terminal"] = (
        "SEED-BATCH-COMPLETE"
        if len(accepted) == 5
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
        "campaign_id": campaign_id,
        "prior_fingerprint_count": len(known),
        "provider_seed_count": len(payload.get("seeds", [])),
        "accepted_seed_count": len(accepted),
        "dropped": dropped,
        "meaning": (
            "deterministic literal duplicate filter only; target-equivalence "
            "and mathematical novelty remain root-review obligations"
        ),
    }
    return batch, report


def authenticate_receipt(value: Any, label: str) -> Path:
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
    if not path.is_file():
        raise ServiceError(f"{label} is missing: {rel}")
    actual = sha256(path)
    if actual != claimed:
        raise ServiceError(f"{label} hash mismatch: {claimed} != {actual}")
    return path


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
) -> str:
    snapshot_dir = batch_dir / "snapshot"
    return f"""# Immutable continuous seed-generation packet

Campaign: `{campaign_id}`
Generation mode: `{generation_mode}`
Snapshot receipt: `{snapshot_receipt['path']}` / `{snapshot_receipt['sha256']}`

You are the read-only Research Question Generator for the exact Erdős--Szekeres
happy-ending project. Authenticate every named receipt before interpreting it.
Read `AGENTS.md`, `docs/agents/research-campaign.md`, and
`docs/agents/profiles/research-question-generator.md`. The complete reconciled
coordinator snapshot is under `{repo_relative(snapshot_dir)}`. In particular,
inspect `packet-summary.json`, `context.md`, `lean-declarations.md`, and the full
`prior-idea-registry.json`; use the repository paths committed by `manifest.json`
when the inline context is insufficient.

The prior registry includes every earlier validated continuous-generator seed,
including unreconciled inbox batches. Those entries are duplicate-avoidance
memory only: never treat their presence as evidence, endorsement, route
admission, or permission to mutate a failed mechanism.

Generate up to five compact, materially different mathematical questions or
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
`SEED-BATCH-COMPLETE` only with exactly five honest seeds. If only zero to four
survive, return `SEED-BATCH-NOVELTY-STOP`; never pad. Set unknown tool, token,
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
            "Generate one evidence-first inbox batch of up to five compact, "
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
        ],
        "success": [
            "SEED-BATCH-COMPLETE: exactly five honest seeds validate.",
            "SEED-BATCH-NOVELTY-STOP: zero to four honest seeds validate without padding.",
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


def active_authorization_pointer_path(service_dir: Path) -> Path:
    return service_dir / ACTIVE_AUTHORIZATION_NAME


def authorization_file_path(
    service_dir: Path, authorization: dict[str, Any]
) -> Path:
    encoded = (json.dumps(authorization, indent=2, sort_keys=True) + "\n").encode(
        "utf-8"
    )
    digest = hashlib.sha256(encoded).hexdigest()
    return service_dir / AUTHORIZATION_DIRECTORY_NAME / f"{digest}.json"


def active_standing_authorization(
    service_dir: Path,
) -> tuple[Path, dict[str, Any]]:
    pointer_path = active_authorization_pointer_path(service_dir)
    pointer = read_json(pointer_path, "active standing-authorization pointer")
    if set(pointer) != {
        "schema_version",
        "protocol",
        "activated_at",
        "authorization",
    } or pointer.get("schema_version") != 1:
        raise ServiceError("active standing-authorization pointer is malformed")
    if pointer.get("protocol") != PROTOCOL_VERSION:
        raise ServiceError("active standing-authorization pointer protocol drifted")
    authorization_path = authenticate_receipt(
        pointer.get("authorization"), "active standing authorization"
    )
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


def verify_standing_authorization(
    path: Path, *, service_dir: Path | None = None
) -> dict[str, Any]:
    value = read_json(path, "standing authorization")
    required = {
        "schema_version",
        "protocol",
        "created_at",
        "approval_ref",
        "service_dir",
        "implementation",
        "supporting_implementation",
        "provider",
        "generation_modes",
        "limits",
        "authority",
    }
    if set(value) != required or value.get("schema_version") != 1:
        raise ServiceError("standing authorization has an unexpected contract")
    if value.get("protocol") != PROTOCOL_VERSION:
        raise ServiceError("standing authorization protocol is unsupported")
    implementation = authenticate_receipt(
        value.get("implementation"), "standing authorization implementation"
    )
    if implementation != Path(__file__).resolve():
        raise ServiceError("standing authorization binds another implementation")
    supporting = value.get("supporting_implementation")
    expected_supporting = [
        file_receipt(path) for path in implementation_component_paths()[1:]
    ]
    if supporting != expected_supporting:
        raise ServiceError(
            "standing authorization helper or schema implementation drifted"
        )
    for index, receipt in enumerate(supporting):
        authenticate_receipt(receipt, f"standing supporting implementation {index}")
    resolved_service = service_directory(Path(str(value.get("service_dir"))))
    if service_dir is not None and resolved_service != service_dir.resolve():
        raise ServiceError("standing authorization binds another service directory")
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
    if not executable_path.is_absolute() or not executable_path.is_file():
        raise ServiceError("standing provider executable is not an absolute file")
    if provider.get("executable_sha256") != sha256(executable_path):
        raise ServiceError("standing provider executable bytes drifted")
    if provider.get("cli_version") != codex_version(executable):
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
    positive_integer_fields = (
        "wall_minutes_per_call",
        "cpu_cores_per_call",
        "memory_gib_per_call",
        "max_calls_per_24h",
        "minimum_cycle_interval_minutes",
        "max_total_invocations",
        "max_unreconciled_batches",
        "max_unreconciled_seeds",
        "max_consecutive_provider_stops",
        "max_consecutive_zero_seed_batches",
        "max_inline_bytes",
    )
    for key in positive_integer_fields:
        if not isinstance(limits.get(key), int) or int(limits[key]) < 1:
            raise ServiceError(f"standing limit must be a positive integer: {key}")
    output_gib = limits.get("output_gib_per_call")
    if not isinstance(output_gib, (int, float)) or not 0 < output_gib <= 0.05:
        raise ServiceError("standing output ceiling must be in (0, 0.05] GiB")
    if limits["cpu_cores_per_call"] > 2 or limits["memory_gib_per_call"] > 4:
        raise ServiceError("standing local resource ceiling exceeds v2 envelope")
    maximums = {
        "wall_minutes_per_call": 90,
        "max_calls_per_24h": 6,
        "max_total_invocations": 100,
        "max_unreconciled_batches": 10,
        "max_unreconciled_seeds": 50,
        "max_consecutive_provider_stops": 2,
        "max_consecutive_zero_seed_batches": 2,
        "max_inline_bytes": 6 * 1024 * 1024,
    }
    for key, maximum in maximums.items():
        if limits[key] > maximum:
            raise ServiceError(f"standing limit exceeds the v2 ceiling: {key}")
    if limits["minimum_cycle_interval_minutes"] < 30:
        raise ServiceError("standing cycle interval is below the v2 floor")
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
        "max_calls_per_24h": 6,
        "max_total_invocations": 100,
        "max_unreconciled_batches": 10,
        "max_unreconciled_seeds": 50,
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
    if (
        not isinstance(args.minimum_cycle_interval_minutes, int)
        or args.minimum_cycle_interval_minutes < 30
    ):
        raise ServiceError("requested standing cycle interval must be at least 30 minutes")
    codex_executable = shutil.which("codex")
    if codex_executable is None:
        raise ServiceError("codex executable is not available")
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
            "max_calls_per_24h": args.max_calls_per_24h,
            "minimum_cycle_interval_minutes": args.minimum_cycle_interval_minutes,
            "max_total_invocations": args.max_total_invocations,
            "max_unreconciled_batches": args.max_unreconciled_batches,
            "max_unreconciled_seeds": args.max_unreconciled_seeds,
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
    if daemon_receipt(service_dir) is not None:
        raise ServiceError("stop the live daemon before rotating standing authority")
    authorization = make_standing_authorization(service_dir, args)
    path = authorization_file_path(service_dir, authorization)
    write_once(path, authorization)
    verify_standing_authorization(path, service_dir=service_dir)
    pointer_path = active_authorization_pointer_path(service_dir)
    atomic_json(
        pointer_path,
        {
            "schema_version": 1,
            "protocol": PROTOCOL_VERSION,
            "activated_at": now(),
            "authorization": file_receipt(path),
        },
    )
    active_path, _ = active_standing_authorization(service_dir)
    if active_path != path:
        raise ServiceError("active authorization pointer did not bind the new receipt")
    print(
        json.dumps(
            {
                "standing_authorization": file_receipt(path),
                "active_authorization_pointer": file_receipt(pointer_path),
                "limits": authorization["limits"],
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
) -> dict[str, Any]:
    if generation_mode not in authorization["generation_modes"]:
        raise ServiceError("generation mode is outside the standing authorization")
    limits = authorization["limits"]
    batch_dir = service_dir / "batches" / campaign_id
    packet_path = batch_dir / "packet.json"
    if packet_path.exists():
        raise ServiceError(f"campaign is already frozen: {packet_path}")
    batch_dir.mkdir(parents=True, exist_ok=True)
    snapshot_dir = batch_dir / "snapshot"
    summary = build_sol_idea_packet.build_packet(
        snapshot_dir, int(limits["max_inline_bytes"])
    )
    snapshot_path = snapshot_dir / "packet-summary.json"
    snapshot = file_receipt(snapshot_path)

    schema_path = batch_dir / "output-schema.json"
    atomic_json(
        schema_path,
        provider_schema(campaign_id, generation_mode, snapshot),
    )
    prompt_path = batch_dir / "prompt.md"
    prompt_path.write_text(
        make_prompt(campaign_id, generation_mode, snapshot, batch_dir),
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
        snapshot_path,
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
        ),
    )
    provider = authorization["provider"]
    packet = {
        "schema_version": 1,
        "protocol": PROTOCOL_VERSION,
        "campaign_id": campaign_id,
        "generation_mode": generation_mode,
        "created_at": now(),
        "service_dir": repo_relative(service_dir),
        "batch_dir": repo_relative(batch_dir),
        "disposition": "standing-authorization-bound",
        "implementation": file_receipt(Path(__file__).resolve()),
        "standing_authorization": file_receipt(authorization_path),
        "snapshot": snapshot,
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
    verify_packet(packet_path)
    return {
        "campaign_id": campaign_id,
        "packet": file_receipt(packet_path),
        "prompt": packet["prompt"],
        "task": packet["task"],
        "snapshot": packet["snapshot"],
        "standing_authorization": packet["standing_authorization"],
        "next": "queue under the standing authorization",
    }


def command_prepare(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    authorization_path, authorization = active_standing_authorization(service_dir)
    result = freeze_campaign_packet(
        service_dir,
        args.campaign_id,
        args.generation_mode,
        authorization_path,
        authorization,
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


def verify_task_inputs(task: dict[str, Any]) -> None:
    inputs = task.get("inputs")
    if not isinstance(inputs, list) or not inputs:
        raise ServiceError("task inputs are missing")
    for index, item in enumerate(inputs):
        authenticate_receipt(item, f"task input {index}")


def verify_packet(packet_path: Path) -> dict[str, Any]:
    packet = read_json(packet_path, "packet")
    required = {
        "schema_version",
        "protocol",
        "campaign_id",
        "generation_mode",
        "created_at",
        "service_dir",
        "batch_dir",
        "disposition",
        "implementation",
        "standing_authorization",
        "snapshot",
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
    for key in (
        "implementation",
        "standing_authorization",
        "snapshot",
        "prompt",
        "task",
        "output_schema",
    ):
        authenticate_receipt(packet[key], f"packet {key}")
    authorization_path = authenticate_receipt(
        packet["standing_authorization"], "packet standing authorization"
    )
    authorization = verify_standing_authorization(
        authorization_path,
        service_dir=service_directory(Path(str(packet["service_dir"]))),
    )
    task_path = authenticate_receipt(packet["task"], "packet task")
    task = read_json(task_path, "task")
    verify_task_inputs(task)
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
    if not process_alive(pid):
        state_path = service_dir / "state.json"
        if not state_path.is_file():
            return None
        try:
            state = read_json(state_path, "state")
            heartbeat = datetime.fromisoformat(str(state["heartbeat_at"]))
            age = (datetime.now(timezone.utc) - heartbeat).total_seconds()
        except (ServiceError, KeyError, TypeError, ValueError):
            return None
        if (
            state.get("service_id") != value.get("service_id")
            or state.get("service_status") in {"stopped", "error"}
            or not 0 <= age <= 30
        ):
            return None
        value = dict(value)
        value["liveness"] = "fresh-heartbeat; PID hidden from current namespace"
    else:
        value = dict(value)
        value["liveness"] = "pid"
    return value


def queue_packet(
    service_dir: Path,
    packet_path: Path,
    packet_sha: str,
    prompt_sha: str,
    task_sha: str,
    approval_ref: str,
) -> dict[str, Any]:
    if sha256(packet_path) != packet_sha:
        raise ServiceError("approved packet hash does not match")
    packet = verify_packet(packet_path)
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
    queue_path = service_dir / "queue" / f"{packet['campaign_id']}.json"
    if queue_path.exists():
        existing = read_json(queue_path, "queue entry")
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


def launch_daemon(service_dir: Path) -> dict[str, Any]:
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
    active_path, authorization = active_standing_authorization(service_dir)
    if authorization_path != active_path:
        raise ServiceError("start must use the service's active standing authorization")
    if sha256(authorization_path) != args.authorization_sha256:
        raise ServiceError("standing authorization hash does not match")
    daemon = launch_daemon(service_dir)
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


def active_reserve(service_dir: Path) -> list[dict[str, Any]]:
    active: list[dict[str, Any]] = []
    batches = service_dir / "batches"
    if not batches.exists():
        return active
    for seed_path in sorted(batches.glob("*/seed-batch.json")):
        try:
            batch = read_json(seed_path, "seed batch")
        except ServiceError:
            continue
        if batch.get("terminal") not in {
            "SEED-BATCH-COMPLETE",
            "SEED-BATCH-NOVELTY-STOP",
        }:
            continue
        campaign_id = batch.get("campaign_id")
        consumed = service_dir / "consumed" / f"{campaign_id}.json"
        if not consumed.exists():
            active.append(
                {
                    "campaign_id": campaign_id,
                    "terminal": batch.get("terminal"),
                    "seed_count": len(batch.get("seeds", [])),
                    "seed_batch": file_receipt(seed_path),
                }
            )
    return active


def pending_queue(service_dir: Path) -> list[Path]:
    queue_dir = service_dir / "queue"
    if not queue_dir.exists():
        return []
    pending: list[Path] = []
    for entry_path in sorted(queue_dir.glob("*.json")):
        entry = read_json(entry_path, "queue entry")
        campaign_id = entry.get("campaign_id")
        if not isinstance(campaign_id, str):
            continue
        batch_dir = service_dir / "batches" / campaign_id
        if not (batch_dir / "seed-batch.json").exists():
            pending.append(entry_path)
    return pending


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
    atomic_json(batch_dir / "seed-batch.json", batch)
    return batch, reason


def finalize_provider(
    batch_dir: Path,
    packet_path: Path,
    packet: dict[str, Any],
    exit_code: int | None,
    stop_reason: str | None,
    started_at: str,
) -> dict[str, Any]:
    raw_path = batch_dir / "raw-response.json"
    terminal_reason = stop_reason
    batch: dict[str, Any]
    if stop_reason is None and exit_code in (0, None) and raw_path.is_file():
        try:
            payload = read_json(raw_path, "provider response")
            campaign.validate_seed_batch(payload, authenticate=True)
            batch, dedup_report = deduplicate_provider_batch(
                batch_dir.parents[1], payload
            )
            campaign.validate_seed_batch(batch, authenticate=True)
            atomic_json(batch_dir / "dedup-report.json", dedup_report)
            atomic_json(batch_dir / "seed-batch.json", batch)
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
            batch_dir, packet, "SEED-BATCH-PROVIDER-STOP", reason
        )
    receipts: dict[str, Any] = {
        "packet": file_receipt(packet_path),
        "standing_authorization": packet["standing_authorization"],
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
    result = {
        "schema_version": 1,
        "protocol": PROTOCOL_VERSION,
        "campaign_id": packet["campaign_id"],
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
    }
    write_once(batch_dir / "result-receipt.json", result)
    return result


def authenticate_queue(entry_path: Path) -> tuple[dict[str, Any], Path, dict[str, Any]]:
    entry = read_json(entry_path, "queue entry")
    packet_path = authenticate_receipt(entry.get("packet"), "queue packet")
    packet = verify_packet(packet_path)
    if entry.get("campaign_id") != packet["campaign_id"]:
        raise ServiceError("queue and packet campaign identities differ")
    if entry.get("standing_authorization") != packet["standing_authorization"]:
        raise ServiceError("queue and packet standing authorizations differ")
    if entry.get("approved_prompt_sha256") != packet["prompt"]["sha256"]:
        raise ServiceError("queued prompt is not the approved prompt")
    if entry.get("approved_task_sha256") != packet["task"]["sha256"]:
        raise ServiceError("queued task is not the approved task")
    if entry.get("provider_invocations_authorized") != 1:
        raise ServiceError("queue entry must authorize exactly one invocation")
    return entry, packet_path, packet


def set_affinity(pid: int, cores: int) -> None:
    if not hasattr(os, "sched_getaffinity"):
        return
    try:
        allowed = sorted(os.sched_getaffinity(0))[:cores]
        if allowed:
            os.sched_setaffinity(pid, allowed)
    except (OSError, ValueError):
        pass


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

    if attempt_path.exists():
        attempt = read_json(attempt_path, "attempt")
        started_at = str(attempt.get("started_at", started_at))
        if not provider_start_path.exists():
            return finalize_provider(
                batch_dir,
                packet_path,
                packet,
                None,
                "prior attempt was recorded without a provider PID; retry is forbidden",
                started_at,
            )
        provider_start = read_json(provider_start_path, "provider start")
        pid = int(provider_start["pid"])
        expected_identity = provider_start.get("process_identity")
        if process_alive(pid) and not process_identity_matches(expected_identity):
            return finalize_provider(
                batch_dir,
                packet_path,
                packet,
                None,
                "prior provider PID is alive but its boot/start identity differs; retry is forbidden",
                started_at,
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
    attempt = {
        "schema_version": 1,
        "protocol": PROTOCOL_VERSION,
        "campaign_id": packet["campaign_id"],
        "started_at": started_at,
        "queue": file_receipt(entry_path),
        "packet": file_receipt(packet_path),
        "command": argv,
        "provider_invocation_ordinal": 1,
        "retry_authority": "none",
    }
    write_once(attempt_path, attempt)
    events_path = batch_dir / "events.jsonl"
    log_path = batch_dir / "provider.log"
    prompt_path = authenticate_receipt(packet["prompt"], "provider prompt")
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
        write_once(
            provider_start_path,
            {
                "schema_version": 1,
                "campaign_id": packet["campaign_id"],
                "pid": process.pid,
                "process_identity": process_identity(process.pid),
                "started_at": now(),
            },
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
                    "local_process_tree_rss_bytes": process_tree_rss_bytes(process.pid),
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
                terminate_provider(process.pid)
                break
            time.sleep(5)
        exit_code = process.poll()
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
    records: list[dict[str, Any]] = []
    batches = service_dir / "batches"
    if not batches.exists():
        return records
    for batch_dir in sorted(path for path in batches.iterdir() if path.is_dir()):
        packet_path = batch_dir / "packet.json"
        attempt_path = batch_dir / "attempt.json"
        if not packet_path.is_file() or not attempt_path.is_file():
            continue
        try:
            packet = read_json(packet_path, "historical packet")
            attempt = read_json(attempt_path, "historical attempt")
        except ServiceError:
            continue
        if packet.get("protocol") not in RATE_ACCOUNTING_PROTOCOLS:
            continue
        result_path = batch_dir / "result-receipt.json"
        result = (
            read_json(result_path, "historical result")
            if result_path.is_file()
            else None
        )
        records.append(
            {
                "campaign_id": packet.get("campaign_id"),
                "generation_mode": packet.get("generation_mode"),
                "started_at": attempt.get("started_at"),
                "result": result,
            }
        )
    records.sort(key=lambda item: str(item.get("started_at") or ""))
    return records


def generation_gate(
    service_dir: Path, authorization: dict[str, Any]
) -> dict[str, Any]:
    limits = authorization["limits"]
    reserve = active_reserve(service_dir)
    unreconciled_seeds = sum(int(item.get("seed_count") or 0) for item in reserve)
    records = authorized_cycle_records(service_dir, authorization)
    current = datetime.now(timezone.utc)
    recent_cutoff = current - timedelta(hours=24)
    recent_calls = sum(
        1
        for item in records
        if (parse_timestamp(item.get("started_at")) or datetime.min.replace(tzinfo=timezone.utc))
        >= recent_cutoff
    )
    completed = [item for item in records if isinstance(item.get("result"), dict)]
    consecutive_provider_stops = 0
    consecutive_zero_seed_batches = 0
    for item in reversed(completed):
        result = item["result"]
        if result.get("terminal") == "SEED-BATCH-PROVIDER-STOP":
            consecutive_provider_stops += 1
        else:
            break
    for item in reversed(completed):
        result = item["result"]
        if (
            result.get("terminal") == "SEED-BATCH-NOVELTY-STOP"
            and int(result.get("seed_count") or 0) == 0
        ):
            consecutive_zero_seed_batches += 1
        else:
            break
    gate = {
        "ready": False,
        "reason": "unknown",
        "total_invocations": len(records),
        "calls_last_24h": recent_calls,
        "unreconciled_batches": len(reserve),
        "unreconciled_seeds": unreconciled_seeds,
        "consecutive_provider_stops": consecutive_provider_stops,
        "consecutive_zero_seed_batches": consecutive_zero_seed_batches,
        "next_eligible_at": None,
    }
    if len(reserve) >= limits["max_unreconciled_batches"]:
        gate["reason"] = "inbox-batch-high-water"
        return gate
    if unreconciled_seeds >= limits["max_unreconciled_seeds"]:
        gate["reason"] = "inbox-seed-high-water"
        return gate
    if len(records) >= limits["max_total_invocations"]:
        gate["reason"] = "standing-total-invocation-cap"
        return gate
    if recent_calls >= limits["max_calls_per_24h"]:
        gate["reason"] = "rolling-24h-call-cap"
        starts = sorted(
            timestamp
            for item in records
            if (timestamp := parse_timestamp(item.get("started_at"))) is not None
            and timestamp >= recent_cutoff
        )
        if starts:
            gate["next_eligible_at"] = (
                starts[0] + timedelta(hours=24)
            ).isoformat()
        return gate
    if consecutive_provider_stops >= limits["max_consecutive_provider_stops"]:
        gate["reason"] = "provider-stop-circuit-open"
        return gate
    if (
        consecutive_zero_seed_batches
        >= limits["max_consecutive_zero_seed_batches"]
    ):
        gate["reason"] = "zero-seed-circuit-open"
        return gate
    if completed:
        finished = parse_timestamp(completed[-1]["result"].get("finished_at"))
        if finished is not None:
            eligible = finished + timedelta(
                minutes=limits["minimum_cycle_interval_minutes"]
            )
            if current < eligible:
                gate["reason"] = "cycle-cooldown"
                gate["next_eligible_at"] = eligible.isoformat()
                return gate
    gate["ready"] = True
    gate["reason"] = "ready"
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
) -> dict[str, Any]:
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
    )
    packet_path = authenticate_receipt(frozen["packet"], "automatic packet")
    entry = queue_packet(
        service_dir,
        packet_path,
        frozen["packet"]["sha256"],
        frozen["prompt"]["sha256"],
        frozen["task"]["sha256"],
        str(authorization["approval_ref"]),
    )
    return {
        "campaign_id": campaign_id,
        "generation_mode": generation_mode,
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
        "started_at": now(),
    }
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
        reserve = active_reserve(service_dir)
        pending = pending_queue(service_dir)
        gate = generation_gate(service_dir, authorization)
        if pending:
            try:
                result = run_provider(service_dir, pending[0], state, stop_flag)
                state.update(
                    {
                        "job_status": result["terminal"],
                        "campaign_id": result["campaign_id"],
                        "provider_pid": None,
                        "last_result": result,
                        "reserve": active_reserve(service_dir),
                        "pending_queue_count": len(pending_queue(service_dir)),
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
                prepared = prepare_next_cycle(
                    service_dir, authorization_path, authorization
                )
                state.update(
                    {
                        "service_status": "running",
                        "job_status": "cycle-prepared",
                        "campaign_id": prepared["campaign_id"],
                        "last_prepared": prepared,
                        "pending_queue_count": len(pending_queue(service_dir)),
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
    return {
        "protocol": PROTOCOL_VERSION,
        "service_dir": repo_relative(service_dir),
        "daemon_alive": pid is not None,
        "daemon": pid,
        "standing_authorization": authorization_receipt,
        "active_authorization_pointer": authorization_pointer_receipt,
        "standing_authorization_error": authorization_error,
        "generation_gate": gate,
        "state": state,
        "queue_entries": len(queue),
        "pending_queue": [path.name for path in pending_queue(service_dir)],
        "active_reserve": active_reserve(service_dir),
    }


def command_status(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    print(json.dumps(service_status(service_dir), indent=2, sort_keys=True))
    return 0


def command_consume(args: argparse.Namespace) -> int:
    service_dir = service_directory(args.service_dir)
    seed_path = service_dir / "batches" / args.campaign_id / "seed-batch.json"
    if not seed_path.is_file() or sha256(seed_path) != args.seed_batch_sha256:
        raise ServiceError("consumption hash does not authenticate the seed batch")
    batch = read_json(seed_path, "seed batch")
    campaign.validate_seed_batch(batch, authenticate=True)
    receipt = {
        "schema_version": 1,
        "protocol": PROTOCOL_VERSION,
        "campaign_id": args.campaign_id,
        "consumed_at": now(),
        "seed_batch": file_receipt(seed_path),
        "reconciliation_ref": args.reconciliation_ref,
        "meaning": "reserve released; this receipt does not admit or schedule any seed",
    }
    write_once(service_dir / "consumed" / f"{args.campaign_id}.json", receipt)
    print(json.dumps(receipt, indent=2, sort_keys=True))
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
    configure.add_argument("--max-calls-per-24h", type=int, default=6)
    configure.add_argument("--minimum-cycle-interval-minutes", type=int, default=30)
    configure.add_argument("--max-total-invocations", type=int, default=100)
    configure.add_argument("--max-unreconciled-batches", type=int, default=10)
    configure.add_argument("--max-unreconciled-seeds", type=int, default=50)
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
    prepare.set_defaults(function=command_prepare)

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

    consume = subparsers.add_parser("consume", help="release an admitted/reconciled reserve")
    consume.add_argument("--service-dir", type=Path, default=DEFAULT_SERVICE_DIR)
    consume.add_argument("--campaign-id", required=True)
    consume.add_argument("--seed-batch-sha256", required=True)
    consume.add_argument("--reconciliation-ref", required=True)
    consume.set_defaults(function=command_consume)

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
