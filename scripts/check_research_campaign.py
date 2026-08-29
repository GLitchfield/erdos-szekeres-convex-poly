#!/usr/bin/env python3
"""Validate evidence-first research-campaign seeds, briefs, and receipts."""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any


ROOT = Path(__file__).resolve().parents[1]

SEED_SCHEMA = ROOT / "docs/agents/schemas/research-seed-batch.schema.json"
BRIEF_SCHEMA = ROOT / "docs/agents/schemas/research-development-brief.schema.json"
RECEIPT_SCHEMA = ROOT / "docs/agents/schemas/research-development-receipt.schema.json"
SEED_TEMPLATE = ROOT / "templates/research-seed-batch.json"
BRIEF_TEMPLATE = ROOT / "templates/research-development-brief.json"
RECEIPT_TEMPLATE = ROOT / "templates/research-development-receipt.json"
PROTOCOL = ROOT / "docs/agents/research-campaign.md"

REQUIRED_FILE_MARKERS = {
    ROOT / "AGENTS.md": (
        "docs/agents/research-campaign.md",
        "superseded-before-dispatch",
        "pre-admission probes",
    ),
    ROOT / "docs/agents/README.md": (
        "### Evidence-first research campaign",
        "research-campaign.md",
        "immutable-historical-control-only",
    ),
    ROOT / "docs/agents/manifest.toml": (
        'research_campaign_protocol = "docs/agents/research-campaign.md"',
        'research_campaign_checker = ["python3", "scripts/check_research_campaign.py", "--templates"]',
    ),
    ROOT / "Makefile": (
        "python3 scripts/check_research_campaign.py --templates",
        "scripts/check_research_campaign.py",
    ),
    ROOT / "docs/agents/profiles/research-question-generator.md": (
        "up to five compact",
        "never pad",
    ),
    ROOT / "docs/agents/profiles/research-lead-investigator.md": (
        "persistence-neutral instruction",
        "serendipity",
    ),
    ROOT / "docs/agents/profiles/research-card-auditor.md": (
        "two-stage audit boundary",
        "lightweight safety",
    ),
    ROOT / "docs/agents/profiles/principal-orchestrator.md": (
        "full hash-frozen reconciled snapshot",
        "verification funnel",
    ),
    ROOT / "docs/agents/profiles/formal-proof-reviewer.md": (
        "verification funnel",
        "gap-shaped mode",
    ),
}

V3_HISTORICAL_CONTROL = {
    "runs/agents/20260824-continuous-backfill/ready/factory-refresh-v3/prompt.md":
        "28853c782b4b9aafb85ee0794883e51dd2ca37effff49f0b682d182845a35cde",
    "runs/agents/20260824-continuous-backfill/ready/factory-refresh-v3/task.json":
        "dcf5bb3b5282da8868af64121a6bebaba18c7c8c5f3fe6c9c6c828aa5a90aaa6",
}

SEED_TERMINALS = {
    "SEED-BATCH-COMPLETE",
    "SEED-BATCH-NOVELTY-STOP",
    "SEED-BATCH-PROVIDER-STOP",
    "SEED-BATCH-PACKET-MISMATCH",
}
PRIMARY_TERMINALS = {
    "GATE_POSITIVE_SIGNAL",
    "GATE_FALSIFIER",
    "NO_DISCRIMINATING_SIGNAL",
    "OPERATIONAL_STOP",
}
METHODS = {
    "manual_reasoning",
    "local_python",
    "local_lean",
    "local_exact_solver",
    "read_only_sources",
}
LEAN_MODES = {
    "not_yet",
    "fixed_statement_in_loop",
    "post_survival_only",
    "post_discovery_certificate",
}
CLAIM_LEVELS = {"proposal", "computational_evidence", "file_compiles"}
HEX64 = re.compile(r"^[0-9a-f]{64}$")

PERSISTENCE_MARKERS = (
    "The frozen target and conventions may not be weakened or replaced.",
    "Negative, empty, and inconclusive terminals are acceptable.",
    "Effort, prior belief, worker agreement, and failure to find a counterexample are not evidence.",
)
PERSISTENCE_INSTRUCTION = (
    "The frozen target and conventions may not be weakened or replaced. Seek a "
    "proof, exact counterexample, strongest scoped obstruction, or explicitly "
    "inconclusive terminal. Continue only while an undepleted predeclared "
    "discriminating test remains within budget. Negative, empty, and inconclusive "
    "terminals are acceptable. Effort, prior belief, worker agreement, and failure "
    "to find a counterexample are not evidence. Do not infer that the requested "
    "conclusion is true or smuggle it into a premise."
)


class CampaignError(ValueError):
    """A deterministic campaign contract failed."""


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")


def load_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignError(f"cannot parse {label} {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise CampaignError(f"{label} {path} must be a JSON object")
    return value


def exact_keys(value: Any, expected: set[str], label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise CampaignError(f"{label} must be an object")
    actual = set(value)
    if actual != expected:
        missing = sorted(expected - actual)
        extra = sorted(actual - expected)
        raise CampaignError(
            f"{label} keys differ; missing={missing}, extra={extra}"
        )
    return value


def nonempty_string(value: Any, label: str, maximum: int | None = None) -> str:
    if not isinstance(value, str) or not value.strip():
        raise CampaignError(f"{label} must be a nonempty string")
    if maximum is not None and len(value) > maximum:
        raise CampaignError(f"{label} exceeds {maximum} characters")
    return value


def string_list(
    value: Any,
    label: str,
    *,
    minimum: int = 0,
    maximum: int | None = None,
    unique: bool = False,
) -> list[str]:
    if not isinstance(value, list) or not all(
        isinstance(item, str) and item.strip() for item in value
    ):
        raise CampaignError(f"{label} must be an array of nonempty strings")
    if len(value) < minimum or (maximum is not None and len(value) > maximum):
        raise CampaignError(
            f"{label} must contain between {minimum} and {maximum} entries"
        )
    if unique and len(set(value)) != len(value):
        raise CampaignError(f"{label} must contain unique entries")
    return value


def normalize(value: str) -> str:
    return " ".join(value.casefold().split())


def repo_path(value: Any, label: str) -> Path:
    text = nonempty_string(value, label)
    path = Path(text)
    if path.is_absolute() or ".." in path.parts:
        raise CampaignError(f"{label} must be repository-relative")
    return ROOT / path


def validate_file_receipt(
    value: Any, label: str, *, authenticate: bool
) -> tuple[str, str, Path]:
    receipt = exact_keys(value, {"path", "sha256"}, label)
    path_text = nonempty_string(receipt["path"], f"{label}.path")
    claimed = receipt["sha256"]
    if not isinstance(claimed, str) or not HEX64.fullmatch(claimed):
        raise CampaignError(f"{label}.sha256 must be 64 lowercase hex characters")
    path = repo_path(path_text, f"{label}.path")
    if authenticate:
        if not path.is_file():
            raise CampaignError(f"{label}.path does not exist: {path_text}")
        try:
            path.resolve().relative_to(ROOT.resolve())
        except ValueError as exc:
            raise CampaignError(
                f"{label}.path resolves outside the repository: {path_text}"
            ) from exc
        actual = digest(path)
        if actual != claimed:
            raise CampaignError(
                f"{label} hash mismatch for {path_text}: {claimed} != {actual}"
            )
    return path_text, claimed, path


def validate_generation_metrics(value: Any, label: str, seed_count: int) -> None:
    metrics = exact_keys(
        value,
        {
            "private_seed_count",
            "literal_duplicates_removed",
            "target_equivalent_removed",
            "malformed_removed",
            "tool_calls",
            "source_requests",
            "input_tokens",
            "output_tokens",
            "provider_cost_usd",
        },
        label,
    )
    for key in (
        "private_seed_count",
        "literal_duplicates_removed",
        "target_equivalent_removed",
        "malformed_removed",
    ):
        item = metrics[key]
        if not isinstance(item, int) or isinstance(item, bool) or item < 0:
            raise CampaignError(f"{label}.{key} must be a nonnegative integer")
    if metrics["private_seed_count"] < seed_count:
        raise CampaignError(f"{label}.private_seed_count is below exposed seeds")
    for key in ("tool_calls", "source_requests", "input_tokens", "output_tokens"):
        item = metrics[key]
        if item is not None and (
            not isinstance(item, int) or isinstance(item, bool) or item < 0
        ):
            raise CampaignError(f"{label}.{key} must be null or nonnegative integer")
    cost = metrics["provider_cost_usd"]
    if cost is not None and (
        not isinstance(cost, (int, float)) or isinstance(cost, bool) or cost < 0
    ):
        raise CampaignError(f"{label}.provider_cost_usd must be null or nonnegative")


def validate_seed(seed: Any, index: int) -> tuple[str, tuple[str, ...]]:
    label = f"seeds[{index}]"
    item = exact_keys(
        seed,
        {
            "seed_id",
            "target_ref",
            "title",
            "model",
            "mechanism",
            "lineage",
            "nearest_controls",
            "first_test",
            "closest_source_lead",
            "claim_level",
        },
        label,
    )
    if len(canonical_bytes(item)) > 4096:
        raise CampaignError(f"{label} exceeds the 4096-byte canonical ceiling")
    seed_id = nonempty_string(item["seed_id"], f"{label}.seed_id", 120)
    if not re.fullmatch(r"[A-Z0-9][A-Z0-9._-]*", seed_id):
        raise CampaignError(f"{label}.seed_id has invalid characters")
    nonempty_string(item["target_ref"], f"{label}.target_ref", 240)
    nonempty_string(item["title"], f"{label}.title", 120)
    if item["claim_level"] != "proposal":
        raise CampaignError(f"{label}.claim_level must be proposal")

    model = exact_keys(
        item["model"],
        {
            "working_tier",
            "target_tier",
            "transfer_status",
            "bridge_ref",
            "information_at_risk",
        },
        f"{label}.model",
    )
    working = nonempty_string(model["working_tier"], f"{label}.model.working_tier", 600)
    target = nonempty_string(model["target_tier"], f"{label}.model.target_tier", 600)
    status = model["transfer_status"]
    if status not in {"same_tier", "conjectural", "verified_bridge"}:
        raise CampaignError(f"{label}.model.transfer_status is invalid")
    bridge = model["bridge_ref"]
    if bridge is not None:
        nonempty_string(bridge, f"{label}.model.bridge_ref", 240)
    nonempty_string(model["information_at_risk"], f"{label}.model.information_at_risk", 800)
    if status == "same_tier" and (normalize(working) != normalize(target) or bridge is not None):
        raise CampaignError(f"{label} same_tier requires equal tiers and null bridge_ref")
    if status == "verified_bridge" and bridge is None:
        raise CampaignError(f"{label} verified_bridge requires bridge_ref")

    mechanism = exact_keys(
        item["mechanism"],
        {"family_hint", "objects", "operation", "retained_information"},
        f"{label}.mechanism",
    )
    family = nonempty_string(mechanism["family_hint"], f"{label}.mechanism.family_hint", 240)
    objects = nonempty_string(mechanism["objects"], f"{label}.mechanism.objects", 800)
    operation = nonempty_string(mechanism["operation"], f"{label}.mechanism.operation", 800)
    nonempty_string(
        mechanism["retained_information"],
        f"{label}.mechanism.retained_information",
        800,
    )

    lineage = exact_keys(
        item["lineage"],
        {"kind", "parent_refs", "genuinely_new_step"},
        f"{label}.lineage",
    )
    kind = lineage["kind"]
    if kind not in {"de_novo", "mutation", "recombination"}:
        raise CampaignError(f"{label}.lineage.kind is invalid")
    parents = string_list(
        lineage["parent_refs"],
        f"{label}.lineage.parent_refs",
        maximum=2,
        unique=True,
    )
    expected_parents = {"de_novo": 0, "mutation": 1, "recombination": 2}[kind]
    if len(parents) != expected_parents:
        raise CampaignError(f"{label} {kind} requires {expected_parents} parent refs")
    nonempty_string(
        lineage["genuinely_new_step"], f"{label}.lineage.genuinely_new_step", 800
    )

    controls = item["nearest_controls"]
    if not isinstance(controls, list) or not 1 <= len(controls) <= 3:
        raise CampaignError(f"{label}.nearest_controls must contain 1 to 3 entries")
    control_refs: list[str] = []
    for control_index, control in enumerate(controls):
        control_label = f"{label}.nearest_controls[{control_index}]"
        entry = exact_keys(control, {"ref", "material_difference"}, control_label)
        control_refs.append(nonempty_string(entry["ref"], f"{control_label}.ref", 240))
        nonempty_string(entry["material_difference"], f"{control_label}.material_difference", 800)
    if len(set(control_refs)) != len(control_refs):
        raise CampaignError(f"{label}.nearest_controls refs must be unique")

    test = exact_keys(
        item["first_test"],
        {
            "question",
            "live_signal",
            "kill_signal",
            "ceiling_minutes",
            "information_if_live",
            "information_if_killed",
            "information_if_no_signal",
        },
        f"{label}.first_test",
    )
    for key, maximum in (
        ("question", 800),
        ("live_signal", 600),
        ("kill_signal", 600),
        ("information_if_live", 800),
        ("information_if_killed", 800),
        ("information_if_no_signal", 800),
    ):
        nonempty_string(test[key], f"{label}.first_test.{key}", maximum)
    minutes = test["ceiling_minutes"]
    if not isinstance(minutes, int) or isinstance(minutes, bool) or not 1 <= minutes <= 30:
        raise CampaignError(f"{label}.first_test.ceiling_minutes must be 1..30")
    if normalize(test["live_signal"]) == normalize(test["kill_signal"]):
        raise CampaignError(f"{label}.first_test live and kill signals must differ")
    branches = [
        normalize(test["information_if_live"]),
        normalize(test["information_if_killed"]),
        normalize(test["information_if_no_signal"]),
    ]
    if len(set(branches)) != 3:
        raise CampaignError(f"{label}.first_test information branches must differ")

    source = item["closest_source_lead"]
    if source is not None:
        nonempty_string(source, f"{label}.closest_source_lead", 800)
    signature = tuple(
        normalize(value)
        for value in (family, objects, operation, working, target)
    )
    return seed_id, signature


def validate_seed_batch(
    value: Any, *, authenticate: bool = True
) -> dict[str, Any]:
    batch = exact_keys(
        value,
        {
            "schema_version",
            "campaign_id",
            "generation_mode",
            "snapshot",
            "terminal",
            "claim_level",
            "seeds",
            "generation_metrics",
        },
        "seed batch",
    )
    if batch["schema_version"] != 1:
        raise CampaignError("seed batch schema_version must be 1")
    nonempty_string(batch["campaign_id"], "seed batch campaign_id")
    if batch["generation_mode"] not in {
        "context_rich", "representation_escape", "failure_dual", "recombination"
    }:
        raise CampaignError("seed batch generation_mode is invalid")
    validate_file_receipt(batch["snapshot"], "seed batch snapshot", authenticate=authenticate)
    terminal = batch["terminal"]
    if terminal not in SEED_TERMINALS:
        raise CampaignError("seed batch terminal is invalid")
    if batch["claim_level"] != "proposal":
        raise CampaignError("seed batch claim_level must be proposal")
    seeds = batch["seeds"]
    if not isinstance(seeds, list) or len(seeds) > 5:
        raise CampaignError("seed batch seeds must be an array of at most five")
    if terminal == "SEED-BATCH-COMPLETE" and len(seeds) != 5:
        raise CampaignError("SEED-BATCH-COMPLETE requires exactly five seeds")
    if terminal == "SEED-BATCH-NOVELTY-STOP" and len(seeds) >= 5:
        raise CampaignError("SEED-BATCH-NOVELTY-STOP requires zero to four seeds")
    if terminal in {"SEED-BATCH-PROVIDER-STOP", "SEED-BATCH-PACKET-MISMATCH"} and seeds:
        raise CampaignError(f"{terminal} cannot expose seeds")
    ids: list[str] = []
    signatures: list[tuple[str, ...]] = []
    for index, seed in enumerate(seeds):
        seed_id, signature = validate_seed(seed, index)
        ids.append(seed_id)
        signatures.append(signature)
    if len(set(ids)) != len(ids):
        raise CampaignError("seed IDs must be unique")
    if len(set(signatures)) != len(signatures):
        raise CampaignError("exact normalized mechanism signatures must be unique")
    validate_generation_metrics(batch["generation_metrics"], "generation_metrics", len(seeds))
    return batch


def ownership_covers(patterns: list[str], path: str) -> bool:
    return any(fnmatch.fnmatch(path, pattern) for pattern in patterns)


def validate_brief(
    value: Any,
    *,
    brief_path: Path | None = None,
    task_packet: dict[str, Any] | None = None,
    authenticate: bool = True,
) -> dict[str, Any]:
    brief = exact_keys(
        value,
        {
            "schema_version",
            "brief_id",
            "task_id",
            "seed",
            "target_ref",
            "worker_mode",
            "probe",
            "selected_context",
            "hostile_controls",
            "allowed_methods",
            "lean_policy",
            "checkpoint_tool_calls",
            "persistence_instruction",
            "policies",
            "authority",
        },
        "development brief",
    )
    if len(canonical_bytes(brief)) > 12000:
        raise CampaignError("development brief exceeds 12000 canonical bytes")
    if brief["schema_version"] != 1:
        raise CampaignError("development brief schema_version must be 1")
    nonempty_string(brief["brief_id"], "development brief brief_id")
    task_id = nonempty_string(brief["task_id"], "development brief task_id")
    target_ref = nonempty_string(brief["target_ref"], "development brief target_ref", 240)
    if brief["worker_mode"] not in {
        "context_rich", "representation_escape", "failure_dual", "independent_replication"
    }:
        raise CampaignError("development brief worker_mode is invalid")

    seed_ref = exact_keys(
        brief["seed"], {"batch_path", "batch_sha256", "seed_id"}, "development brief seed"
    )
    batch_path, batch_sha, batch_file = validate_file_receipt(
        {"path": seed_ref["batch_path"], "sha256": seed_ref["batch_sha256"]},
        "development brief seed batch",
        authenticate=authenticate,
    )
    seed_id = nonempty_string(seed_ref["seed_id"], "development brief seed.seed_id")
    matched_seed: dict[str, Any] | None = None
    if authenticate:
        batch = validate_seed_batch(load_json(batch_file, "seed batch"), authenticate=True)
        matches = [seed for seed in batch["seeds"] if seed["seed_id"] == seed_id]
        if len(matches) != 1:
            raise CampaignError("development brief seed_id is not unique in seed batch")
        matched_seed = matches[0]
        if matched_seed["target_ref"] != target_ref:
            raise CampaignError("development brief target_ref differs from seed")

    probe = exact_keys(
        brief["probe"],
        {
            "question", "assumption_refs", "actions", "live_signal", "kill_signal",
            "ceiling_minutes", "stop_condition",
        },
        "development brief probe",
    )
    for key, maximum in (
        ("question", 2400), ("live_signal", 800), ("kill_signal", 800), ("stop_condition", 1000)
    ):
        nonempty_string(probe[key], f"development brief probe.{key}", maximum)
    string_list(probe["assumption_refs"], "development brief probe.assumption_refs", maximum=8, unique=True)
    string_list(probe["actions"], "development brief probe.actions", minimum=1, maximum=8)
    if normalize(probe["live_signal"]) == normalize(probe["kill_signal"]):
        raise CampaignError("development brief live and kill signals must differ")
    ceiling_minutes = probe["ceiling_minutes"]
    if (
        not isinstance(ceiling_minutes, int)
        or isinstance(ceiling_minutes, bool)
        or not 1 <= ceiling_minutes <= 30
    ):
        raise CampaignError("development brief probe.ceiling_minutes must be 1..30")
    if (
        matched_seed is not None
        and ceiling_minutes > matched_seed["first_test"]["ceiling_minutes"]
    ):
        raise CampaignError("development brief expands the seed first-test ceiling")

    contexts = brief["selected_context"]
    if not isinstance(contexts, list) or not 1 <= len(contexts) <= 5:
        raise CampaignError("selected_context must contain one to five artifacts")
    context_paths: list[str] = []
    context_hashes: dict[str, str] = {}
    total_bytes = 0
    for index, context in enumerate(contexts):
        label = f"selected_context[{index}]"
        entry = exact_keys(context, {"path", "sha256", "purpose"}, label)
        path_text, claimed, path = validate_file_receipt(
            {"path": entry["path"], "sha256": entry["sha256"]},
            label,
            authenticate=authenticate,
        )
        nonempty_string(entry["purpose"], f"{label}.purpose", 600)
        context_paths.append(path_text)
        context_hashes[path_text] = claimed
        if authenticate:
            total_bytes += path.stat().st_size
    if len(set(context_paths)) != len(context_paths):
        raise CampaignError("selected_context paths must be unique")
    if authenticate and total_bytes > 2_000_000:
        raise CampaignError("selected_context exceeds the 2,000,000-byte ceiling")
    if brief["worker_mode"] == "representation_escape":
        forbidden = ("factory-refresh-context", "prior-idea-registry", "lean-declarations")
        for path in context_paths:
            if any(fragment in path for fragment in forbidden):
                raise CampaignError(
                    "representation_escape context includes a prohibited whole-project artifact"
                )

    controls = brief["hostile_controls"]
    if not isinstance(controls, list) or not 1 <= len(controls) <= 3:
        raise CampaignError("hostile_controls must contain one to three entries")
    control_ids: list[str] = []
    for index, control in enumerate(controls):
        label = f"hostile_controls[{index}]"
        entry = exact_keys(
            control,
            {
                "control_id",
                "construction",
                "expected_if_mechanism_is_real",
                "expected_if_artifact",
                "stop_observation",
            },
            label,
        )
        control_ids.append(nonempty_string(entry["control_id"], f"{label}.control_id", 120))
        for key, maximum in (
            ("construction", 1000),
            ("expected_if_mechanism_is_real", 800),
            ("expected_if_artifact", 800),
            ("stop_observation", 800),
        ):
            nonempty_string(entry[key], f"{label}.{key}", maximum)
        if normalize(entry["expected_if_mechanism_is_real"]) == normalize(entry["expected_if_artifact"]):
            raise CampaignError(f"{label} does not distinguish mechanism from artifact")
    if len(set(control_ids)) != len(control_ids):
        raise CampaignError("hostile control IDs must be unique")

    methods = string_list(
        brief["allowed_methods"], "allowed_methods", minimum=1, unique=True
    )
    if not set(methods) <= METHODS:
        raise CampaignError("allowed_methods contains an unknown method")
    lean = exact_keys(
        brief["lean_policy"], {"mode", "theorem_contract_ref", "rationale"}, "lean_policy"
    )
    mode = lean["mode"]
    if mode not in LEAN_MODES:
        raise CampaignError("lean_policy.mode is invalid")
    theorem_ref = lean["theorem_contract_ref"]
    if theorem_ref is not None:
        nonempty_string(theorem_ref, "lean_policy.theorem_contract_ref", 240)
    nonempty_string(lean["rationale"], "lean_policy.rationale", 800)
    if mode == "fixed_statement_in_loop":
        if theorem_ref is None or "local_lean" not in methods:
            raise CampaignError("fixed_statement_in_loop requires theorem ref and local_lean")
    elif theorem_ref is not None or "local_lean" in methods:
        raise CampaignError(f"{mode} cannot authorize Lean in this development brief")
    checkpoint = brief["checkpoint_tool_calls"]
    if not isinstance(checkpoint, int) or isinstance(checkpoint, bool) or not 1 <= checkpoint <= 10:
        raise CampaignError("checkpoint_tool_calls must be 1..10")
    if brief["persistence_instruction"] != PERSISTENCE_INSTRUCTION:
        raise CampaignError("development brief persistence instruction is not canonical")
    policies = exact_keys(
        brief["policies"], {"persistence", "serendipity", "claims", "metrics"}, "policies"
    )
    expected_policies = {
        "persistence": "neutral-v1",
        "serendipity": "scoped-sidecar-v1",
        "claims": "verification-funnel-v1",
        "metrics": "evidence-vector-v1",
    }
    if policies != expected_policies:
        raise CampaignError("development brief policy versions are not canonical")
    if brief["authority"] != "investigation_only; task_packet_controls_all_actions":
        raise CampaignError("development brief authority is not canonical")

    if task_packet is not None:
        if task_packet.get("task_id") != task_id:
            raise CampaignError("development brief task_id differs from task packet")
        inputs = task_packet.get("inputs")
        if not isinstance(inputs, list):
            raise CampaignError("task packet inputs must be an array")
        task_inputs = {
            entry.get("path"): entry.get("sha256")
            for entry in inputs
            if isinstance(entry, dict)
        }
        for path, claimed in context_hashes.items():
            if task_inputs.get(path) != claimed:
                raise CampaignError(f"selected context is not frozen by task packet: {path}")
        if task_inputs.get(batch_path) != batch_sha:
            raise CampaignError("seed batch is not frozen by task packet")
        if brief_path is not None:
            try:
                rel_brief = str(brief_path.resolve().relative_to(ROOT.resolve()))
            except ValueError as exc:
                raise CampaignError("development brief path is outside repository") from exc
            if authenticate and task_inputs.get(rel_brief) != digest(brief_path):
                raise CampaignError("development brief is not frozen by task packet")
        ownership = task_packet.get("ownership", {})
        patterns = ownership.get("read_paths", []) + ownership.get("write_paths", [])
        if not isinstance(patterns, list):
            raise CampaignError("task ownership paths are invalid")
        for path in [batch_path, *context_paths]:
            if not ownership_covers(patterns, path):
                raise CampaignError(f"task ownership does not cover campaign input: {path}")
        claims = task_packet.get("claims_allowed", [])
        contract = task_packet.get("theorem_contract")
        budget = task_packet.get("budget")
        if not isinstance(budget, dict):
            raise CampaignError("campaign task packet must declare its budget")
        wall_minutes = budget.get("wall_minutes")
        if (
            not isinstance(wall_minutes, int)
            or isinstance(wall_minutes, bool)
            or wall_minutes < ceiling_minutes
        ):
            raise CampaignError(
                "task wall budget must cover the development first-test ceiling"
            )
        if mode == "fixed_statement_in_loop":
            if contract is None or "file_compiles" not in claims:
                raise CampaignError(
                    "fixed_statement_in_loop requires task theorem contract and file_compiles claim"
                )
            if theorem_ref != contract.get("name"):
                raise CampaignError("lean theorem ref differs from task theorem contract")
    return brief


def validate_resource_use(value: Any) -> None:
    resource = exact_keys(
        value,
        {
            "wall_minutes", "active_minutes", "cpu_seconds", "peak_memory_mib",
            "artifact_bytes", "input_tokens", "output_tokens", "tool_calls",
            "source_requests", "experiment_runs", "checker_runs",
        },
        "resource_use",
    )
    integer_keys = {
        "artifact_bytes", "input_tokens", "output_tokens", "tool_calls",
        "source_requests", "experiment_runs", "checker_runs",
    }
    for key, item in resource.items():
        if item is None:
            continue
        if key in integer_keys:
            if not isinstance(item, int) or isinstance(item, bool) or item < 0:
                raise CampaignError(f"resource_use.{key} must be null or nonnegative integer")
        elif not isinstance(item, (int, float)) or isinstance(item, bool) or item < 0:
            raise CampaignError(f"resource_use.{key} must be null or nonnegative number")


def validate_development_receipt(
    value: Any,
    *,
    brief_path: Path | None = None,
    authenticate: bool = True,
) -> dict[str, Any]:
    receipt = exact_keys(
        value,
        {
            "schema_version", "brief_id", "brief_sha256", "terminal",
            "assigned_gate_outcome", "evidence_events", "resource_use",
            "claim_candidate", "serendipity", "route_action", "admission_status",
        },
        "development receipt",
    )
    if receipt["schema_version"] != 1:
        raise CampaignError("development receipt schema_version must be 1")
    brief_id = nonempty_string(receipt["brief_id"], "development receipt brief_id")
    brief_sha = receipt["brief_sha256"]
    if not isinstance(brief_sha, str) or not HEX64.fullmatch(brief_sha):
        raise CampaignError("development receipt brief_sha256 is invalid")
    if brief_path is not None and authenticate:
        if digest(brief_path) != brief_sha:
            raise CampaignError("development receipt brief hash mismatch")
        brief = load_json(brief_path, "development brief")
        if brief.get("brief_id") != brief_id:
            raise CampaignError("development receipt brief_id mismatch")
    if receipt["terminal"] not in PRIMARY_TERMINALS:
        raise CampaignError("development receipt terminal is invalid")
    nonempty_string(receipt["assigned_gate_outcome"], "assigned_gate_outcome", 1600)
    events = receipt["evidence_events"]
    if not isinstance(events, list):
        raise CampaignError("evidence_events must be an array")
    if receipt["terminal"] != "OPERATIONAL_STOP" and not events:
        raise CampaignError("mathematical terminals require at least one evidence event")
    kinds: list[str] = []
    for index, event in enumerate(events):
        label = f"evidence_events[{index}]"
        entry = exact_keys(
            event,
            {"kind", "claim_level", "statement", "scope", "artifact", "replay_or_check"},
            label,
        )
        kind = entry["kind"]
        if kind not in {
            "checked_computation", "exact_falsifier", "authenticated_source_interface",
            "compiling_fixed_statement", "reproducible_unexplained_invariant",
            "claim_refuted", "proposal_only",
        }:
            raise CampaignError(f"{label}.kind is invalid")
        kinds.append(kind)
        if entry["claim_level"] not in CLAIM_LEVELS:
            raise CampaignError(f"{label}.claim_level is invalid")
        nonempty_string(entry["statement"], f"{label}.statement", 1600)
        nonempty_string(entry["scope"], f"{label}.scope", 1200)
        validate_file_receipt(entry["artifact"], f"{label}.artifact", authenticate=authenticate)
        nonempty_string(entry["replay_or_check"], f"{label}.replay_or_check", 1000)
    if receipt["terminal"] == "GATE_FALSIFIER" and not {
        "exact_falsifier", "claim_refuted"
    }.intersection(kinds):
        raise CampaignError("GATE_FALSIFIER requires falsifier or refutation evidence")
    validate_resource_use(receipt["resource_use"])

    claim = receipt["claim_candidate"]
    if claim is not None:
        item = exact_keys(
            claim,
            {
                "statement", "model_tier", "scope_ceiling",
                "evidence_event_indices", "downstream",
            },
            "claim_candidate",
        )
        for key, maximum in (("statement", 2400), ("model_tier", 1200), ("scope_ceiling", 1200)):
            nonempty_string(item[key], f"claim_candidate.{key}", maximum)
        claim_indices = item["evidence_event_indices"]
        if not isinstance(claim_indices, list) or not claim_indices or not all(
            isinstance(index, int)
            and not isinstance(index, bool)
            and 0 <= index < len(events)
            for index in claim_indices
        ):
            raise CampaignError(
                "claim candidate evidence indices must reference evidence events"
            )
        if len(set(claim_indices)) != len(claim_indices):
            raise CampaignError("claim candidate evidence indices must be unique")
        if item["downstream"] != "verification_funnel_required":
            raise CampaignError("claim candidate must require verification funnel")

    serendipity = receipt["serendipity"]
    if serendipity is not None:
        item = exact_keys(
            serendipity,
            {
                "statement_or_observation", "model_tier", "scope_ceiling",
                "relation_to_assigned_probe", "evidence_event_indices",
                "contains_claim_candidate", "downstream",
            },
            "serendipity",
        )
        for key, maximum in (
            ("statement_or_observation", 2400), ("model_tier", 1200),
            ("scope_ceiling", 1200), ("relation_to_assigned_probe", 1200),
        ):
            nonempty_string(item[key], f"serendipity.{key}", maximum)
        indices = item["evidence_event_indices"]
        if not isinstance(indices, list) or not indices or not all(
            isinstance(index, int) and not isinstance(index, bool) and 0 <= index < len(events)
            for index in indices
        ):
            raise CampaignError("serendipity evidence indices must reference evidence events")
        if len(set(indices)) != len(indices):
            raise CampaignError("serendipity evidence indices must be unique")
        if not isinstance(item["contains_claim_candidate"], bool):
            raise CampaignError("serendipity contains_claim_candidate must be boolean")
        if item["contains_claim_candidate"] and claim is None:
            raise CampaignError("serendipitous claim requires claim_candidate sidecar")
        if item["downstream"] != "root_audit_required":
            raise CampaignError("serendipity must require root audit")
    if receipt["route_action"] != "none" or receipt["admission_status"] != "unadmitted":
        raise CampaignError("development receipt cannot take route action or claim admission")
    return receipt


def validate_schema_contract(path: Path, title: str) -> None:
    schema = load_json(path, title)
    if schema.get("$schema") != "https://json-schema.org/draft/2020-12/schema":
        raise CampaignError(f"{title} must use JSON Schema draft 2020-12")
    if schema.get("type") != "object" or schema.get("additionalProperties") is not False:
        raise CampaignError(f"{title} must define a closed object")


def validate_historical_control() -> None:
    for relpath, expected in V3_HISTORICAL_CONTROL.items():
        path = ROOT / relpath
        if not path.is_file():
            raise CampaignError(f"historical Factory v3 control is missing: {relpath}")
        actual = digest(path)
        if actual != expected:
            raise CampaignError(
                f"historical Factory v3 control changed: {relpath}: {actual} != {expected}"
            )


def validate_templates() -> None:
    validate_schema_contract(SEED_SCHEMA, "seed schema")
    validate_schema_contract(BRIEF_SCHEMA, "development brief schema")
    validate_schema_contract(RECEIPT_SCHEMA, "development receipt schema")
    validate_seed_batch(load_json(SEED_TEMPLATE, "seed template"), authenticate=False)
    validate_brief(load_json(BRIEF_TEMPLATE, "brief template"), authenticate=False)
    validate_development_receipt(
        load_json(RECEIPT_TEMPLATE, "receipt template"), authenticate=False
    )
    protocol = PROTOCOL.read_text(encoding="utf-8")
    protocol_text = " ".join(
        line[2:] if line.startswith("> ") else line
        for line in protocol.splitlines()
    )
    for marker in PERSISTENCE_MARKERS:
        if normalize(marker) not in normalize(protocol_text):
            raise CampaignError(f"protocol is missing persistence marker: {marker}")
    for path, markers in REQUIRED_FILE_MARKERS.items():
        try:
            contents = path.read_text(encoding="utf-8")
        except OSError as exc:
            raise CampaignError(f"cannot read wired campaign file {path}: {exc}") from exc
        for marker in markers:
            if marker not in contents:
                relpath = path.relative_to(ROOT)
                raise CampaignError(
                    f"campaign wiring marker is missing from {relpath}: {marker}"
                )
    validate_historical_control()


def resolve_argument(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--templates", action="store_true")
    parser.add_argument("--seed-batch", type=Path)
    parser.add_argument("--development-brief", type=Path)
    parser.add_argument("--task-packet", type=Path)
    parser.add_argument("--development-receipt", type=Path)
    parser.add_argument("--brief", type=Path)
    args = parser.parse_args()

    if not any((args.templates, args.seed_batch, args.development_brief, args.development_receipt)):
        parser.error("select at least one validation target")
    if args.development_brief is not None and args.task_packet is None:
        parser.error("--development-brief requires --task-packet")
    if args.development_receipt is not None and args.brief is None:
        parser.error("--development-receipt requires --brief")

    try:
        if args.templates:
            validate_templates()
        if args.seed_batch is not None:
            path = resolve_argument(args.seed_batch)
            validate_seed_batch(load_json(path, "seed batch"), authenticate=True)
        if args.development_brief is not None:
            brief_path = resolve_argument(args.development_brief)
            task_path = resolve_argument(args.task_packet)
            validate_brief(
                load_json(brief_path, "development brief"),
                brief_path=brief_path,
                task_packet=load_json(task_path, "task packet"),
                authenticate=True,
            )
        if args.development_receipt is not None:
            receipt_path = resolve_argument(args.development_receipt)
            brief_path = resolve_argument(args.brief)
            validate_development_receipt(
                load_json(receipt_path, "development receipt"),
                brief_path=brief_path,
                authenticate=True,
            )
    except (CampaignError, OSError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    print("research campaign contracts OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
