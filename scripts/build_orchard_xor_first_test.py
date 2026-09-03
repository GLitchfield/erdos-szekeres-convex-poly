#!/usr/bin/env python3
"""Freeze the guarded Orchard-XOR first test and its verifier request.

This builder is deliberately non-executing.  ``freeze`` authenticates one
ready service seed and publishes the immutable event template, development
brief, and task packet.  ``freeze-verifier-request`` authenticates a later
claim, guarded PASS envelope, and artifact, derives the event through the
worker's pure event functions, and publishes only the verifier request.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from typing import Any, Sequence

try:
    from scripts import check_orchard_xor_palette as orchard
    from scripts import check_research_campaign as campaign
    from scripts import continuous_idea_generator as generator
    from scripts import run_first_test_guarded as guard
except ModuleNotFoundError:  # Direct ``python3 scripts/...`` execution.
    import check_orchard_xor_palette as orchard
    import check_research_campaign as campaign
    import continuous_idea_generator as generator
    import run_first_test_guarded as guard


ROOT = Path(__file__).resolve().parents[1]
RUNS_AGENTS = (ROOT / "runs" / "agents").resolve()
SEED_ID = "ORCHARD-XOR-PALETTE-V2"
EVENT_TEMPLATE_NAME = "event-template.json"
BRIEF_NAME = "development-brief.json"
TASK_NAME = "task.json"
ARTIFACT_NAME = "terminal-artifact.json"
SEMANTIC_CONTRACT_PATH = (
    "runs/agents/20260831-self-refilling-loop/"
    "orchard-xor-author-v2/semantic-contract.md"
)
SEMANTIC_CONTRACT_SHA256 = (
    "034cf73fbd222717cd1262231608ecdea74e6b6987ccb597a9b4cbb1f59fb2f7"
)
HEX64 = re.compile(r"^[0-9a-f]{64}$")
SAFE_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")


class BuilderError(ValueError):
    """An input, immutable identity, or publication boundary failed."""


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def digest_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def digest(path: Path) -> str:
    return digest_bytes(path.read_bytes())


def encoded_json(value: Any) -> bytes:
    return canonical_bytes(value) + b"\n"


def load_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise BuilderError(f"cannot parse {label} {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise BuilderError(f"{label} must be a JSON object")
    return value


def repository_path(value: str | Path, label: str) -> tuple[str, Path]:
    supplied = Path(value)
    resolved = supplied.resolve() if supplied.is_absolute() else (ROOT / supplied).resolve()
    try:
        relative = resolved.relative_to(ROOT.resolve()).as_posix()
    except ValueError as exc:
        raise BuilderError(f"{label} is outside the repository") from exc
    if not relative or relative == "." or ".." in Path(relative).parts:
        raise BuilderError(f"{label} is not a strict repository file path")
    return relative, resolved


def authenticated_receipt(
    value: str | Path, expected_sha256: str, label: str
) -> tuple[dict[str, str], Path]:
    if not isinstance(expected_sha256, str) or HEX64.fullmatch(expected_sha256) is None:
        raise BuilderError(f"{label} SHA-256 is malformed")
    relative, path = repository_path(value, label)
    if not path.is_file():
        raise BuilderError(f"{label} is absent: {relative}")
    observed = digest(path)
    if observed != expected_sha256:
        raise BuilderError(
            f"{label} hash differs: expected {expected_sha256}, observed {observed}"
        )
    return {"path": relative, "sha256": expected_sha256}, path


def predicted_receipt(path: Path, value: Any) -> dict[str, str]:
    relative, _resolved = repository_path(path, "predicted output")
    return {"path": relative, "sha256": digest_bytes(encoded_json(value))}


def write_once(path: Path, value: Any) -> dict[str, str]:
    data = encoded_json(value)
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o444)
    except FileExistsError as exc:
        raise BuilderError(f"write-once output already exists: {path}") from exc
    try:
        view = memoryview(data)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise BuilderError(f"write made no progress: {path}")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    return guard.file_receipt(path)


def exact_seed(batch: dict[str, Any]) -> dict[str, Any]:
    matches = [seed for seed in batch["seeds"] if seed.get("seed_id") == SEED_ID]
    if len(matches) != 1:
        raise BuilderError(f"seed batch must contain exactly one {SEED_ID}")
    return matches[0]


def authenticate_ready_seed(
    service_dir_value: str | Path,
    *,
    batch_receipt: dict[str, str],
    campaign_id: str,
) -> dict[str, Any]:
    """Authenticate that the imported composite identity is currently ready."""

    service_dir = generator.service_directory(Path(service_dir_value))
    _authorization_path, authorization = generator.active_standing_authorization(
        service_dir
    )
    accounting = generator.validate_accounting_chain(service_dir, authorization)
    inventory = generator.seed_inventory(
        service_dir, authorization=authorization, accounting=accounting
    )
    matches = [
        item
        for item in inventory
        if item.get("campaign_id") == campaign_id
        and item.get("seed_id") == SEED_ID
        and item.get("seed_batch") == batch_receipt
    ]
    if len(matches) != 1 or matches[0].get("state") != "ready":
        raise BuilderError(
            "freeze requires exactly one authenticated ready Orchard-XOR seed identity"
        )
    return matches[0]


def validate_run_directory(value: str | Path) -> tuple[str, Path]:
    relative, path = repository_path(value, "output run directory")
    parts = Path(relative).parts
    if len(parts) != 3 or parts[:2] != ("runs", "agents"):
        raise BuilderError("output run directory must be exactly runs/agents/<run_id>")
    run_id = parts[2]
    if SAFE_ID.fullmatch(run_id) is None:
        raise BuilderError("output run_id is unsafe")
    return run_id, path


def standing_authority() -> dict[str, Any]:
    return {
        "protocol": campaign.FIRST_TEST_PROTOCOL,
        "approval_ref": campaign.FIRST_TEST_APPROVAL_REF,
        "execution_class": "pre_admission_information_gathering",
        "terminal_ceiling": "has_legs_or_earlier",
        "limits": {
            "wall_minutes": 30,
            "cpu_cores": 2,
            "memory_gib": 4,
            "output_gib": 0.1,
        },
        "writes": "exact_ignored_runs_agents_paths_only",
        "provider_calls": 0,
        "service_starts": 0,
        "scheduler_mutations": False,
        "canonical_writes": False,
        "external_writes": False,
        "installations": False,
        "destructive_actions": False,
    }


def evidence_contract(
    seed: dict[str, Any], *, campaign_id: str, batch_sha256: str
) -> dict[str, Any]:
    model = json.loads(json.dumps(seed["model"]))
    model_contract_id = canonical_sha256(model)
    scope = {
        "scope_contract_id": "",
        "candidate": {
            "campaign_id": campaign_id,
            "seed_id": SEED_ID,
            "seed_batch_sha256": batch_sha256,
        },
        "ceiling": "candidate-local",
        "subfamily": None,
    }
    scope["scope_contract_id"] = canonical_sha256(
        {key: value for key, value in scope.items() if key != "scope_contract_id"}
    )
    contract = {
        "contract_id": "",
        "statement": seed["first_test"]["question"],
        "target_ref": seed["target_ref"],
        "model": model,
        "model_contract_id": model_contract_id,
        "scope": scope,
        "theorem": None,
    }
    contract["contract_id"] = canonical_sha256(
        {key: value for key, value in contract.items() if key != "contract_id"}
    )
    return contract


def event_template(contract: dict[str, Any]) -> dict[str, Any]:
    contract_id = contract["contract_id"]
    blueprint = {
        "claim_contract_id": contract_id,
        "primary_contract_id": contract_id,
        "subject": "primary_claim",
        "subject_contract_id": contract_id,
        "model_contract_id": contract["model_contract_id"],
        "scope_contract_id": contract["scope"]["scope_contract_id"],
        "checked_predicate": contract["statement"],
    }
    branches: dict[str, Any] = {}
    for terminal in orchard.TERMINALS:
        kind, gate_branch, polarity, damage = orchard.BRANCH_SEMANTICS[terminal]
        texts: dict[str, str | None]
        if terminal == "ORCHARD-XOR-KILL":
            texts = dict(orchard.KILL_LEARNING_TEXT)
        else:
            texts = {
                "failing_feature": None,
                "strongest_supported_statement": None,
            }
        branches[terminal] = {
            "kind": kind,
            "gate_branch": gate_branch,
            "polarity": polarity,
            "damage_scope_reached": damage,
            "verified_learning_texts": texts,
        }
    value = {
        "schema_version": 1,
        "protocol": orchard.EVENT_TEMPLATE_PROTOCOL,
        "input_role": "event_template",
        "synthetic_only": False,
        "task_id": orchard.TASK_ID,
        "semantic_contract_id": orchard.SEMANTIC_CONTRACT_ID,
        "blueprint": blueprint,
        "branches": branches,
        "template_core_sha256": "",
    }
    value["template_core_sha256"] = canonical_sha256(
        {key: item for key, item in value.items() if key != "template_core_sha256"}
    )
    orchard.validate_event_template(value, synthetic_test_only=False)
    return value


def development_brief(
    seed: dict[str, Any],
    *,
    batch_receipt: dict[str, str],
    panel_receipt: dict[str, str],
    semantic_receipt: dict[str, str],
    template_receipt: dict[str, str],
    contract: dict[str, Any],
) -> dict[str, Any]:
    first_test = seed["first_test"]
    return {
        "schema_version": 3,
        "brief_id": "orchard-xor-palette-v2-first-test-brief-v1",
        "task_id": orchard.TASK_ID,
        "seed": {
            "batch_path": batch_receipt["path"],
            "batch_sha256": batch_receipt["sha256"],
            "seed_id": SEED_ID,
        },
        "target_ref": seed["target_ref"],
        "worker_mode": "independent_replication",
        "evidence_contract": contract,
        "probe": {
            "question": first_test["question"],
            "assumption_refs": [semantic_receipt["path"]],
            "actions": [
                "Authenticate the frozen panel, event template, worker, and semantic contract.",
                "Use the worker's two independent exact implementations to reconstruct every frozen case.",
                "Classify only the predeclared live, kill, no-signal, or semantic-readiness branch.",
            ],
            "live_signal": first_test["live_signal"],
            "kill_signal": first_test["kill_signal"],
            "ceiling_minutes": first_test["ceiling_minutes"],
            "stop_condition": (
                "Stop at the first authenticated terminal; do not widen the panel, "
                "repair a control, or infer a uniform producer theorem."
            ),
        },
        "selected_context": [
            {
                **panel_receipt,
                "purpose": "Frozen actual/control panel; execution reconstructs its predicates independently.",
            },
            {
                **semantic_receipt,
                "purpose": "Exact Orchard-XOR and four-index strong-set semantic contract.",
            },
            {
                **template_receipt,
                "purpose": "Pre-run evidence blueprint and closed terminal semantics without an event hash.",
            },
        ],
        "hostile_controls": [
            {
                "control_id": "relaxed-exact-strong-separation",
                "construction": (
                    "Use the frozen eligible relaxed sign-table controls with the literal "
                    "four-index IsStrongPolygonSet predicate, never circuit balance."
                ),
                "expected_if_mechanism_is_real": (
                    "All realizable actuals pass while at least one eligible relaxed control fails."
                ),
                "expected_if_artifact": (
                    "The actual/control distinction disappears or an actual itself has no passing palette cut."
                ),
                "stop_observation": (
                    "Any actual failure is candidate-local kill; failure to separate controls is no-signal."
                ),
            }
        ],
        "allowed_methods": ["local_python"],
        "lean_policy": {
            "mode": "not_yet",
            "theorem_contract_ref": None,
            "rationale": (
                "This is a pre-admission finite discriminator; it has no theorem-entry memo "
                "or Lean-producing authority."
            ),
        },
        "checkpoint_tool_calls": 1,
        "persistence_instruction": campaign.PERSISTENCE_INSTRUCTION,
        "policies": {
            "persistence": "neutral-v1",
            "serendipity": "scoped-sidecar-v1",
            "claims": "verification-funnel-v1",
            "metrics": "evidence-vector-v1",
        },
        "authority": standing_authority(),
    }


def execution_contract(
    *,
    worker_receipt: dict[str, str],
    panel_receipt: dict[str, str],
    template_receipt: dict[str, str],
    guard_receipt: dict[str, str],
    artifact_path: str,
) -> dict[str, Any]:
    value = {
        "protocol": campaign.FIRST_TEST_EXECUTION_PROTOCOL,
        "contract_id": "",
        "guard_component": guard_receipt,
        "engine": "python_exact",
        "argv_template": [
            "/usr/bin/python3",
            "-B",
            worker_receipt["path"],
            "--input",
            panel_receipt["path"],
            "--input",
            template_receipt["path"],
            "--result-fd",
            "{output_fd:terminal_artifact}",
        ],
        "cwd": ".",
        "input_receipts": [worker_receipt, panel_receipt, template_receipt],
        "outputs": [
            {
                "role": "terminal_artifact",
                "path": artifact_path,
                "media_type": "application/json",
            }
        ],
        "normalized_result_role": "terminal_artifact",
        "process_model": campaign.FIRST_TEST_PROCESS_MODEL,
    }
    value["contract_id"] = canonical_sha256(
        {key: item for key, item in value.items() if key != "contract_id"}
    )
    return value


def task_packet(
    *,
    run_id: str,
    base_revision: str,
    workspace_fingerprint: str,
    inputs: list[dict[str, str]],
    artifact_path: str,
    execution: dict[str, Any],
) -> dict[str, Any]:
    return {
        "schema_version": 2,
        "run_id": run_id,
        "task_id": orchard.TASK_ID,
        "wayfinder_ticket": campaign.TICKET_0119,
        "profile": "orchard-xor-palette-v2-guarded-first-test",
        "base_revision": base_revision,
        "workspace_fingerprint": workspace_fingerprint,
        "objective": (
            "Run exactly the frozen Orchard-XOR v2 panel through the independent "
            "exact worker and emit one canonical terminal artifact."
        ),
        "theorem_contract": None,
        "inputs": inputs,
        "ownership": {
            "read_paths": [item["path"] for item in inputs],
            "write_paths": [artifact_path],
        },
        "budget": {
            "wall_minutes": 30,
            "cpu_cores": 2,
            "memory_gib": 4,
            "output_gib": 0.1,
        },
        "required_checks": [
            "Authenticate the exact seed batch, brief, panel, event template, semantic contract, worker, and guard.",
            "Use only the frozen worker inputs and inherited output descriptor.",
            "Preserve exact four-index strong-set semantics and both independent implementations.",
        ],
        "success": [
            "Emit one canonical terminal artifact at the exact declared output path.",
            "Accept live, kill, no-signal, and semantic-readiness-stop as predeclared mathematical terminals.",
        ],
        "stop": [
            "Stop on any receipt drift, worker disagreement, malformed input, resource violation, or undeclared write.",
            "Do not repair fixtures, substitute a predicate, run Lean, mutate services, or infer route admission.",
        ],
        "deliverables": [artifact_path],
        "claims_allowed": ["proposal", "computational_evidence"],
        "standing_first_test": standing_authority(),
        "first_test_execution": execution,
    }


def freeze(
    *,
    service_dir: str | Path,
    seed_batch: str | Path,
    seed_batch_sha256: str,
    panel: str | Path,
    panel_sha256: str,
    semantic_contract_path: str | Path,
    semantic_contract_sha256: str,
    worker: str | Path,
    worker_sha256: str,
    guard_path: str | Path,
    guard_sha256: str,
    output_run_dir: str | Path,
    base_revision: str,
    workspace_fingerprint: str,
) -> dict[str, Any]:
    batch_receipt, batch_path = authenticated_receipt(
        seed_batch, seed_batch_sha256, "service seed batch"
    )
    panel_receipt, _panel_path = authenticated_receipt(panel, panel_sha256, "panel")
    semantic_receipt, _semantic_path = authenticated_receipt(
        semantic_contract_path, semantic_contract_sha256, "semantic contract"
    )
    worker_receipt, worker_path = authenticated_receipt(
        worker, worker_sha256, "Orchard-XOR worker"
    )
    guard_receipt, guard_file = authenticated_receipt(
        guard_path, guard_sha256, "first-test guard"
    )
    if worker_path != Path(orchard.__file__).resolve() or worker_receipt["path"] != (
        "scripts/check_orchard_xor_palette.py"
    ):
        raise BuilderError("freeze requires the imported current Orchard-XOR worker")
    if semantic_receipt != {
        "path": SEMANTIC_CONTRACT_PATH,
        "sha256": SEMANTIC_CONTRACT_SHA256,
    }:
        raise BuilderError("freeze requires the authenticated Orchard-XOR v2 semantic contract")
    if guard_file != Path(guard.__file__).resolve() or guard_receipt["path"] != (
        "scripts/run_first_test_guarded.py"
    ):
        raise BuilderError("freeze requires the imported current first-test guard")
    if not isinstance(base_revision, str) or not base_revision.strip():
        raise BuilderError("base_revision must be nonempty")
    if not isinstance(workspace_fingerprint, str) or not workspace_fingerprint.strip():
        raise BuilderError("workspace_fingerprint must be nonempty")

    batch = campaign.validate_seed_batch(
        load_json(batch_path, "service seed batch"), authenticate=True
    )
    seed = exact_seed(batch)
    campaign_id = batch["campaign_id"]
    authenticate_ready_seed(
        service_dir,
        batch_receipt=batch_receipt,
        campaign_id=campaign_id,
    )

    run_id, run_dir = validate_run_directory(output_run_dir)
    template_path = run_dir / EVENT_TEMPLATE_NAME
    brief_path = run_dir / BRIEF_NAME
    task_path = run_dir / TASK_NAME
    for path in (template_path, brief_path, task_path):
        if path.exists():
            raise BuilderError(f"write-once output already exists: {path}")

    contract = evidence_contract(
        seed, campaign_id=campaign_id, batch_sha256=batch_receipt["sha256"]
    )
    template = event_template(contract)
    template_receipt = predicted_receipt(template_path, template)
    brief = development_brief(
        seed,
        batch_receipt=batch_receipt,
        panel_receipt=panel_receipt,
        semantic_receipt=semantic_receipt,
        template_receipt=template_receipt,
        contract=contract,
    )
    brief_receipt = predicted_receipt(brief_path, brief)
    artifact_relative, _artifact_path = repository_path(
        run_dir / ARTIFACT_NAME, "terminal artifact"
    )
    execution = execution_contract(
        worker_receipt=worker_receipt,
        panel_receipt=panel_receipt,
        template_receipt=template_receipt,
        guard_receipt=guard_receipt,
        artifact_path=artifact_relative,
    )
    inputs = [
        batch_receipt,
        brief_receipt,
        panel_receipt,
        template_receipt,
        semantic_receipt,
        worker_receipt,
        guard_receipt,
    ]
    task = task_packet(
        run_id=run_id,
        base_revision=base_revision,
        workspace_fingerprint=workspace_fingerprint,
        inputs=inputs,
        artifact_path=artifact_relative,
        execution=execution,
    )
    task_receipt = predicted_receipt(task_path, task)

    # Closed-shape validation before publication catches construction errors.
    campaign.validate_brief(
        brief, brief_path=brief_path, task_packet=task, authenticate=False
    )
    guard.validate_execution_contract(task, authenticate=False)

    template_written = write_once(template_path, template)
    brief_written = write_once(brief_path, brief)
    task_written = write_once(task_path, task)
    if (
        template_written != template_receipt
        or brief_written != brief_receipt
        or task_written != task_receipt
    ):
        raise BuilderError("published output differs from its precomputed receipt")

    # The required authenticated gates are deliberately after bytes exist.
    campaign.validate_brief(
        brief, brief_path=brief_path, task_packet=task, authenticate=True
    )
    guard.validate_execution_contract(task, authenticate=True)
    return {
        "terminal": "BUILDER-READY",
        "mode": "freeze",
        "campaign_id": campaign_id,
        "seed_id": SEED_ID,
        "event_template": template_written,
        "development_brief": brief_written,
        "task_packet": task_written,
        "evidence_contract_id": contract["contract_id"],
        "execution_contract_id": execution["contract_id"],
    }


def authenticate_investigating_claim(
    service_dir_value: str | Path, *, claim_path: Path, claim: dict[str, Any]
) -> tuple[dict[str, Any], Path]:
    seed_identity = claim.get("seed")
    if not isinstance(seed_identity, dict):
        raise BuilderError("claim lacks a composite seed identity")
    campaign_id = seed_identity.get("campaign_id")
    seed_id = seed_identity.get("seed_id")
    seed_receipt = seed_identity.get("seed_batch")
    if not isinstance(campaign_id, str) or seed_id != SEED_ID:
        raise BuilderError("claim does not identify the Orchard-XOR seed")
    _batch_text, seed_path = guard.receipt(seed_receipt, "claimed seed batch")
    generator.validate_seed_claim(
        claim_path, campaign_id=campaign_id, seed_id=seed_id, seed_path=seed_path
    )
    service_dir = generator.service_directory(Path(service_dir_value))
    _authorization_path, authorization = generator.active_standing_authorization(
        service_dir
    )
    accounting = generator.validate_accounting_chain(service_dir, authorization)
    inventory = generator.seed_inventory(
        service_dir, authorization=authorization, accounting=accounting
    )
    claim_receipt = guard.file_receipt(claim_path)
    matches = [
        item
        for item in inventory
        if item.get("campaign_id") == campaign_id
        and item.get("seed_id") == seed_id
        and item.get("seed_batch") == seed_receipt
        and item.get("claim") == claim_receipt
    ]
    if len(matches) != 1 or matches[0].get("state") != "investigating":
        raise BuilderError(
            "verifier request requires one authenticated investigating identity"
        )
    return matches[0], seed_path


def load_claim_dependencies(
    claim: dict[str, Any], claim_path: Path
) -> tuple[dict[str, Any], Path, dict[str, Any], Path, dict[str, Any]]:
    _brief_text, brief_path = guard.receipt(
        claim.get("development_brief"), "claimed development brief"
    )
    _task_text, task_path = guard.receipt(claim.get("task_packet"), "claimed task packet")
    brief = load_json(brief_path, "claimed development brief")
    task = load_json(task_path, "claimed task packet")
    campaign.validate_brief(
        brief, brief_path=brief_path, task_packet=task, authenticate=True
    )
    execution = guard.validate_execution_contract(task, authenticate=True)
    if claim.get("task_packet") != guard.file_receipt(task_path):
        raise BuilderError("claim task receipt changed")
    if claim.get("development_brief") != guard.file_receipt(brief_path):
        raise BuilderError("claim brief receipt changed")
    if claim.get("claim_id") != (
        f"{claim['seed']['campaign_id']}:{claim['seed']['seed_id']}"
    ):
        raise BuilderError("claim ID differs from its seed identity")
    del claim_path  # Identity was authenticated by its caller and the service validator.
    return brief, brief_path, task, task_path, execution


def authenticate_pass_envelope(
    *,
    claim_path: Path,
    claim: dict[str, Any],
    brief_path: Path,
    brief: dict[str, Any],
    task_path: Path,
    task: dict[str, Any],
    execution: dict[str, Any],
) -> tuple[Path, dict[str, Any]]:
    envelope_path = (
        ROOT
        / "runs"
        / "agents"
        / task["run_id"]
        / "root-receipts"
        / f"{task['task_id']}.execution-envelope.json"
    )
    if not envelope_path.is_file():
        raise BuilderError("guarded PASS execution envelope is absent")
    expected_identity = {
        "seed_claim": guard.file_receipt(claim_path),
        "claim_id": claim["claim_id"],
        "development_brief": guard.file_receipt(brief_path),
        "brief_id": brief["brief_id"],
        "task_packet": guard.file_receipt(task_path),
        "task_id": task["task_id"],
        "execution_contract_id": execution["contract_id"],
    }
    envelope = guard.validate_envelope(
        load_json(envelope_path, "first-test execution envelope"),
        expected_identity=expected_identity,
        authenticate_outputs=True,
    )
    guard.validate_first_envelope_contract(envelope, execution, task)
    if envelope["terminal"] != "PASS":
        raise BuilderError("verifier request requires a guarded PASS envelope")
    return envelope_path, envelope


def derive_request(
    *,
    claim_path: Path,
    claim: dict[str, Any],
    task_path: Path,
    task: dict[str, Any],
    execution: dict[str, Any],
    artifact_receipt: dict[str, str],
    artifact_path: Path,
) -> tuple[dict[str, Any], Path]:
    execution_inputs = execution["input_receipts"]
    if len(execution_inputs) != 3:
        raise BuilderError("Orchard-XOR execution must have exactly worker, panel, template")
    checker_receipt, panel_receipt, template_receipt = execution_inputs
    if checker_receipt["path"] != "scripts/check_orchard_xor_palette.py":
        raise BuilderError("execution checker is not the current Orchard-XOR worker")
    _checker_text, checker_path = guard.receipt(
        checker_receipt, "Orchard-XOR checker", authenticate=True
    )
    if checker_path != Path(orchard.__file__).resolve():
        raise BuilderError("imported Orchard-XOR worker differs from frozen checker")
    _panel_text, _panel_path = guard.receipt(panel_receipt, "frozen panel")
    _template_text, template_path = guard.receipt(
        template_receipt, "frozen event template"
    )
    template = load_json(template_path, "frozen event template")
    orchard.validate_event_template(template, synthetic_test_only=False)

    raw = artifact_path.read_bytes()
    if digest_bytes(raw) != artifact_receipt["sha256"]:
        raise BuilderError("artifact changed while deriving its event")
    artifact = load_json(artifact_path, "terminal artifact")
    event = orchard.event_record(artifact_receipt["path"], raw, artifact, template)
    normalized = orchard.normalized_result(event, template)
    binding = event["binding"]
    event_summary = {
        "event_id": event["event_id"],
        "event_core_sha256": normalized["verified_event_core_sha256"],
        "subject_contract_id": binding["subject_contract_id"],
        "model_contract_id": binding["model_contract_id"],
        "scope_contract_id": binding["scope_contract_id"],
        "artifact": artifact_receipt,
    }
    raw_inputs = [panel_receipt, template_receipt]
    argv = [
        "/usr/bin/python3",
        "-B",
        checker_receipt["path"],
        "--verify-event",
        artifact_receipt["path"],
        "--normalized-result-stdout",
    ]
    for item in raw_inputs:
        argv.extend(["--input", item["path"]])
    verifier_core = {
        "verifier_component": checker_receipt,
        "claim_contract_id": normalized["claim_contract_id"],
        "primary_contract_id": normalized["primary_contract_id"],
        "subject_contract_id": normalized["subject_contract_id"],
        "model_contract_id": normalized["model_contract_id"],
        "scope_contract_id": normalized["scope_contract_id"],
        "verified_event_core_sha256": normalized["verified_event_core_sha256"],
        "event_artifact": normalized["event_artifact"],
        "engine": "python_exact",
        "invocation": {"argv": argv, "cwd": "."},
        "input_receipts": [artifact_receipt, *raw_inputs],
    }
    request = {
        "schema_version": 1,
        "protocol": guard.VERIFIER_REQUEST_PROTOCOL,
        "verifier_contract_id": canonical_sha256(verifier_core),
        "guard_component": execution["guard_component"],
        "seed_claim": guard.file_receipt(claim_path),
        "task_packet": guard.file_receipt(task_path),
        "claim_id": claim["claim_id"],
        "task_id": task["task_id"],
        "event": event_summary,
        "checker": checker_receipt,
        "argv_template": argv,
        "input_receipts": [checker_receipt, artifact_receipt, *raw_inputs],
        "expected_normalized_result": normalized,
        "budget": task["budget"],
        "process_model": guard.PROCESS_MODEL,
    }
    request_path = (
        ROOT
        / "runs"
        / "agents"
        / task["run_id"]
        / "root-receipts"
        / f"{event['event_id']}.verification-request.json"
    )
    return request, request_path


def freeze_verifier_request(
    *,
    service_dir: str | Path,
    claim_path_value: str | Path,
    claim_sha256: str,
    artifact_path_value: str | Path,
    artifact_sha256: str,
) -> dict[str, Any]:
    claim_receipt, claim_path = authenticated_receipt(
        claim_path_value, claim_sha256, "seed claim"
    )
    artifact_receipt, artifact_path = authenticated_receipt(
        artifact_path_value, artifact_sha256, "terminal artifact"
    )
    claim = load_json(claim_path, "seed claim")
    authenticate_investigating_claim(service_dir, claim_path=claim_path, claim=claim)
    brief, brief_path, task, task_path, execution = load_claim_dependencies(
        claim, claim_path
    )
    if claim_receipt != guard.file_receipt(claim_path):
        raise BuilderError("claim changed during authentication")
    outputs = execution["outputs"]
    if (
        len(outputs) != 1
        or outputs[0]["role"] != "terminal_artifact"
        or outputs[0]["path"] != artifact_receipt["path"]
        or task["deliverables"] != [artifact_receipt["path"]]
    ):
        raise BuilderError("artifact is not the exact sole task deliverable")
    _envelope_path, envelope = authenticate_pass_envelope(
        claim_path=claim_path,
        claim=claim,
        brief_path=brief_path,
        brief=brief,
        task_path=task_path,
        task=task,
        execution=execution,
    )
    matching_writes = [
        item
        for item in envelope["observation"]["writes"]
        if item["path"] == artifact_receipt["path"]
        and item["sha256"] == artifact_receipt["sha256"]
        and item["materialized"] is True
    ]
    if len(matching_writes) != 1:
        raise BuilderError("PASS envelope does not authenticate the artifact")

    request, request_path = derive_request(
        claim_path=claim_path,
        claim=claim,
        task_path=task_path,
        task=task,
        execution=execution,
        artifact_receipt=artifact_receipt,
        artifact_path=artifact_path,
    )
    if request_path.exists():
        raise BuilderError(f"write-once verifier request already exists: {request_path}")
    # Validate the complete object and current investigating inventory before
    # publishing it.  The validator does not require the request file itself.
    guard.validate_verifier_request(
        request, service_dir_value=service_dir, request_path=request_path
    )
    request_receipt = write_once(request_path, request)
    guard.validate_verifier_request(
        request, service_dir_value=service_dir, request_path=request_path
    )
    return {
        "terminal": "BUILDER-READY",
        "mode": "freeze-verifier-request",
        "event_id": request["event"]["event_id"],
        "event_core_sha256": request["event"]["event_core_sha256"],
        "verifier_contract_id": request["verifier_contract_id"],
        "verification_request": request_receipt,
    }


def parser() -> argparse.ArgumentParser:
    value = argparse.ArgumentParser(description=__doc__)
    subparsers = value.add_subparsers(dest="command", required=True)
    freeze_parser = subparsers.add_parser("freeze")
    freeze_parser.add_argument("--service-dir", required=True)
    freeze_parser.add_argument("--seed-batch", required=True)
    freeze_parser.add_argument("--seed-batch-sha256", required=True)
    freeze_parser.add_argument("--panel", required=True)
    freeze_parser.add_argument("--panel-sha256", required=True)
    freeze_parser.add_argument("--semantic-contract", required=True)
    freeze_parser.add_argument("--semantic-contract-sha256", required=True)
    freeze_parser.add_argument("--worker", required=True)
    freeze_parser.add_argument("--worker-sha256", required=True)
    freeze_parser.add_argument("--guard", required=True)
    freeze_parser.add_argument("--guard-sha256", required=True)
    freeze_parser.add_argument("--output-run-dir", required=True)
    freeze_parser.add_argument("--base-revision", required=True)
    freeze_parser.add_argument("--workspace-fingerprint", required=True)

    verifier_parser = subparsers.add_parser("freeze-verifier-request")
    verifier_parser.add_argument("--service-dir", required=True)
    verifier_parser.add_argument("--claim", required=True)
    verifier_parser.add_argument("--claim-sha256", required=True)
    verifier_parser.add_argument("--artifact", required=True)
    verifier_parser.add_argument("--artifact-sha256", required=True)
    return value


def main(argv: Sequence[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        if args.command == "freeze":
            result = freeze(
                service_dir=args.service_dir,
                seed_batch=args.seed_batch,
                seed_batch_sha256=args.seed_batch_sha256,
                panel=args.panel,
                panel_sha256=args.panel_sha256,
                semantic_contract_path=args.semantic_contract,
                semantic_contract_sha256=args.semantic_contract_sha256,
                worker=args.worker,
                worker_sha256=args.worker_sha256,
                guard_path=args.guard,
                guard_sha256=args.guard_sha256,
                output_run_dir=args.output_run_dir,
                base_revision=args.base_revision,
                workspace_fingerprint=args.workspace_fingerprint,
            )
        else:
            result = freeze_verifier_request(
                service_dir=args.service_dir,
                claim_path_value=args.claim,
                claim_sha256=args.claim_sha256,
                artifact_path_value=args.artifact,
                artifact_sha256=args.artifact_sha256,
            )
    except (
        BuilderError,
        campaign.CampaignError,
        generator.ServiceError,
        guard.GuardError,
        orchard.WorkerError,
        OSError,
    ) as exc:
        print(f"BUILDER-STOP: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
