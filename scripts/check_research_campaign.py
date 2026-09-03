#!/usr/bin/env python3
"""Validate evidence-first research-campaign seeds, briefs, and receipts."""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any


ROOT = Path(__file__).resolve().parents[1]

SEED_SCHEMA = ROOT / "docs/agents/schemas/research-seed-batch.schema.json"
BRIEF_SCHEMA = ROOT / "docs/agents/schemas/research-development-brief.schema.json"
RECEIPT_SCHEMA = ROOT / "docs/agents/schemas/research-development-receipt.schema.json"
TASK_SCHEMA = ROOT / "docs/agents/schemas/research-first-test-task.schema.json"
FEEDBACK_SCHEMA = ROOT / "docs/agents/schemas/research-investigation-feedback.schema.json"
ROOT_SCREEN_SCHEMA = ROOT / "docs/agents/schemas/research-root-semantic-screen.schema.json"
SNAPSHOT_BUILD_SCHEMA = ROOT / "docs/agents/schemas/research-snapshot-build-receipt.schema.json"
VALIDATED_LEARNING_EXPORT_SCHEMA = (
    ROOT / "docs/agents/schemas/research-validated-learning-export.schema.json"
)
EVENT_VERIFICATION_SCHEMA = (
    ROOT / "docs/agents/schemas/research-event-verification.schema.json"
)
SEED_TEMPLATE = ROOT / "templates/research-seed-batch.json"
BRIEF_TEMPLATE = ROOT / "templates/research-development-brief.json"
RECEIPT_TEMPLATE = ROOT / "templates/research-development-receipt.json"
PROTOCOL = ROOT / "docs/agents/research-campaign.md"
TICKET_0119 = "docs/wayfinder/tickets/0119-adopt-self-refilling-investigation-loop.md"
FIRST_TEST_PROTOCOL = "ticket-0119-standing-first-test-v1"
FIRST_TEST_APPROVAL_REF = (
    TICKET_0119 + "#approval-and-operational-inventory"
)
FIRST_TEST_EXECUTION_PROTOCOL = "ticket-0119-first-test-execution-v1"
FIRST_TEST_GUARD_PATH = "scripts/run_first_test_guarded.py"
FIRST_TEST_PROCESS_MODEL = "one-filtered-process-no-children-v1"

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
EVENT_CLAIM_LEVELS = {
    "checked_computation": {"computational_evidence"},
    "exact_falsifier": {"computational_evidence", "file_compiles"},
    "authenticated_source_interface": {"proposal"},
    "compiling_fixed_statement": {"file_compiles"},
    "reproducible_unexplained_invariant": {"computational_evidence"},
    "claim_refuted": {"computational_evidence", "file_compiles"},
    "proposal_only": {"proposal"},
}
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


def run_event_verifier(argv: list[str], *, timeout_seconds: int) -> subprocess.CompletedProcess[str]:
    """Replay the exact trusted verifier during root admission."""
    return subprocess.run(
        argv,
        cwd=ROOT,
        text=True,
        capture_output=True,
        timeout=timeout_seconds,
        check=False,
    )


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
    expected_keys = {
        "schema_version",
        "campaign_id",
        "generation_mode",
        "snapshot",
        "terminal",
        "claim_level",
        "seeds",
        "generation_metrics",
    }
    if isinstance(value, dict) and "requested_seed_count" in value:
        expected_keys.add("requested_seed_count")
    batch = exact_keys(
        value,
        expected_keys,
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
    requested_seed_count = batch.get("requested_seed_count", 5)
    if (
        not isinstance(requested_seed_count, int)
        or isinstance(requested_seed_count, bool)
        or not 1 <= requested_seed_count <= 5
    ):
        raise CampaignError("requested_seed_count must be an integer from one to five")
    seeds = batch["seeds"]
    if not isinstance(seeds, list) or len(seeds) > requested_seed_count:
        raise CampaignError(
            "seed batch seeds must not exceed requested_seed_count"
        )
    if terminal == "SEED-BATCH-COMPLETE" and len(seeds) != requested_seed_count:
        raise CampaignError(
            "SEED-BATCH-COMPLETE requires exactly requested_seed_count seeds"
        )
    if terminal == "SEED-BATCH-NOVELTY-STOP" and len(seeds) >= requested_seed_count:
        raise CampaignError(
            "SEED-BATCH-NOVELTY-STOP requires fewer than requested_seed_count seeds"
        )
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


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def validate_first_test_authority(value: Any) -> dict[str, Any]:
    authority = exact_keys(
        value,
        {
            "protocol",
            "approval_ref",
            "execution_class",
            "terminal_ceiling",
            "limits",
            "writes",
            "provider_calls",
            "service_starts",
            "scheduler_mutations",
            "canonical_writes",
            "external_writes",
            "installations",
            "destructive_actions",
        },
        "standing first-test authority",
    )
    limits = exact_keys(
        authority["limits"],
        {"wall_minutes", "cpu_cores", "memory_gib", "output_gib"},
        "standing first-test authority limits",
    )
    expected = {
        "protocol": FIRST_TEST_PROTOCOL,
        "approval_ref": FIRST_TEST_APPROVAL_REF,
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
    if authority != expected or limits != expected["limits"]:
        raise CampaignError("standing first-test authority differs from Ticket 0119")
    return authority


def validate_first_test_execution(
    value: Any,
    *,
    task: dict[str, Any],
    methods: list[str],
    authenticate: bool,
) -> dict[str, Any]:
    execution = exact_keys(
        value,
        {
            "protocol",
            "contract_id",
            "guard_component",
            "engine",
            "argv_template",
            "cwd",
            "input_receipts",
            "outputs",
            "normalized_result_role",
            "process_model",
        },
        "first-test execution contract",
    )
    if execution.get("protocol") != FIRST_TEST_EXECUTION_PROTOCOL:
        raise CampaignError("first-test execution protocol is invalid")
    core = {key: execution[key] for key in execution if key != "contract_id"}
    if execution.get("contract_id") != canonical_sha256(core):
        raise CampaignError("first-test execution contract ID differs")
    guard_text, guard_sha, _guard_path = validate_file_receipt(
        execution.get("guard_component"),
        "first-test guard component",
        authenticate=authenticate,
    )
    if guard_text != FIRST_TEST_GUARD_PATH:
        raise CampaignError("first-test execution names an untrusted guard")
    if authenticate and guard_sha != digest(ROOT / FIRST_TEST_GUARD_PATH):
        raise CampaignError("first-test execution guard is not current")
    engine = execution.get("engine")
    if engine not in {"python_exact", "exact_solver_in_process"}:
        raise CampaignError("standing first-test execution engine is invalid")
    if engine == "python_exact" and "local_python" not in methods:
        raise CampaignError("Python first-test execution lacks local_python authority")
    if engine == "exact_solver_in_process" and "local_exact_solver" not in methods:
        raise CampaignError(
            "exact-solver first-test execution lacks local_exact_solver authority"
        )
    if execution.get("cwd") != "." or execution.get("process_model") != FIRST_TEST_PROCESS_MODEL:
        raise CampaignError("first-test execution working directory or process model differs")

    task_inputs = task.get("inputs")
    if not isinstance(task_inputs, list):
        raise CampaignError("task packet inputs must be an array")
    allowed_inputs = {canonical_sha256(item): item for item in task_inputs}
    execution_inputs = execution.get("input_receipts")
    if not isinstance(execution_inputs, list) or not execution_inputs:
        raise CampaignError("first-test execution inputs must be nonempty")
    input_paths: list[str] = []
    for index, item in enumerate(execution_inputs):
        path_text, _claimed, _path = validate_file_receipt(
            item,
            f"first-test execution input {index}",
            authenticate=authenticate,
        )
        if canonical_sha256(item) not in allowed_inputs:
            raise CampaignError("first-test execution input is not frozen by the task")
        input_paths.append(path_text)
    if len(set(input_paths)) != len(input_paths):
        raise CampaignError("first-test execution input paths must be unique")

    argv = string_list(
        execution.get("argv_template"),
        "first-test execution argv_template",
        minimum=4,
        maximum=64,
    )
    checker = argv[2]
    if (
        argv[:2] != ["/usr/bin/python3", "-B"]
        or checker not in input_paths
        or not checker.startswith("scripts/")
        or not checker.endswith(".py")
    ):
        raise CampaignError("first-test execution must invoke its frozen checker with Python -B")
    for input_path in input_paths:
        if argv.count(input_path) != 1:
            raise CampaignError(
                "first-test execution must consume every frozen execution input exactly once"
            )
    for token in argv[3:]:
        if token in input_paths or token.startswith("-"):
            continue
        if re.fullmatch(r"\{output_fd:[a-z][a-z0-9_]{0,63}\}", token):
            continue
        if "/" in token or token.endswith((".json", ".txt", ".csv", ".bin", ".py")):
            raise CampaignError(
                "first-test execution contains an unfrozen path operand"
            )

    outputs = execution.get("outputs")
    if not isinstance(outputs, list) or not outputs:
        raise CampaignError("first-test execution outputs must be nonempty")
    output_roles: list[str] = []
    output_paths: list[str] = []
    for index, item in enumerate(outputs):
        entry = exact_keys(
            item,
            {"role", "path", "media_type"},
            f"first-test execution output {index}",
        )
        role = nonempty_string(entry.get("role"), f"first-test output {index}.role", 64)
        if re.fullmatch(r"[a-z][a-z0-9_]{0,63}", role) is None:
            raise CampaignError("first-test output role is invalid")
        output_roles.append(role)
        output_paths.append(
            nonempty_string(entry.get("path"), f"first-test output {index}.path")
        )
        nonempty_string(entry.get("media_type"), f"first-test output {index}.media_type", 160)
    if len(set(output_roles)) != len(output_roles) or len(set(output_paths)) != len(output_paths):
        raise CampaignError("first-test execution output roles and paths must be unique")
    task_write_paths = (task.get("ownership") or {}).get("write_paths")
    deliverables = task.get("deliverables")
    if set(output_paths) != set(task_write_paths or []) or set(output_paths) != set(
        deliverables or []
    ):
        raise CampaignError(
            "first-test execution outputs must equal exact task writes and deliverables"
        )
    placeholders = [f"{{output_fd:{role}}}" for role in output_roles]
    for placeholder in placeholders:
        if argv.count(placeholder) != 1:
            raise CampaignError("each first-test output must have one inherited-FD placeholder")
    if any(("{" in item or "}" in item) and item not in placeholders for item in argv):
        raise CampaignError("first-test execution argv contains an unknown placeholder")
    normalized_role = execution.get("normalized_result_role")
    if normalized_role not in output_roles:
        raise CampaignError("normalized result role is not a declared first-test output")
    normalized_output = outputs[output_roles.index(normalized_role)]
    if normalized_output.get("media_type") != "application/json":
        raise CampaignError("normalized first-test result must use application/json")
    return execution


def validate_evidence_contract(
    value: Any,
    *,
    target_ref: str,
    seed_ref: dict[str, Any],
    matched_seed: dict[str, Any] | None,
    probe_question: str,
) -> dict[str, Any]:
    contract = exact_keys(
        value,
        {
            "contract_id",
            "statement",
            "target_ref",
            "model",
            "model_contract_id",
            "scope",
            "theorem",
        },
        "development brief evidence_contract",
    )
    nonempty_string(contract["statement"], "evidence_contract.statement", 4000)
    if contract["statement"] != probe_question or contract["target_ref"] != target_ref:
        raise CampaignError(
            "evidence contract statement/target differs from the frozen probe"
        )
    model = exact_keys(
        contract["model"],
        {
            "working_tier",
            "target_tier",
            "transfer_status",
            "bridge_ref",
            "information_at_risk",
        },
        "evidence_contract.model",
    )
    if contract.get("model_contract_id") != canonical_sha256(model):
        raise CampaignError("evidence contract model ID differs")
    if matched_seed is not None and model != matched_seed.get("model"):
        raise CampaignError("evidence contract model differs from the selected seed")
    scope = exact_keys(
        contract["scope"],
        {"scope_contract_id", "candidate", "ceiling", "subfamily"},
        "evidence_contract.scope",
    )
    candidate = exact_keys(
        scope["candidate"],
        {"campaign_id", "seed_id", "seed_batch_sha256"},
        "evidence_contract.scope.candidate",
    )
    expected_candidate = {
        "campaign_id": None,
        "seed_id": seed_ref["seed_id"],
        "seed_batch_sha256": seed_ref["batch_sha256"],
    }
    if matched_seed is not None:
        batch = load_json(repo_path(seed_ref["batch_path"], "seed batch"), "seed batch")
        expected_candidate["campaign_id"] = batch.get("campaign_id")
    else:
        expected_candidate["campaign_id"] = candidate.get("campaign_id")
        nonempty_string(candidate.get("campaign_id"), "scope.candidate.campaign_id")
    if candidate != expected_candidate:
        raise CampaignError("evidence contract candidate identity differs")
    ceiling = scope.get("ceiling")
    subfamily = scope.get("subfamily")
    if ceiling == "candidate-local":
        if subfamily is not None:
            raise CampaignError("candidate-local evidence contract names a subfamily")
    elif ceiling == "subfamily":
        item = exact_keys(
            subfamily,
            {"subfamily_ref", "shared_premise", "shared_premise_contract_id"},
            "evidence_contract.scope.subfamily",
        )
        nonempty_string(item["subfamily_ref"], "scope.subfamily.subfamily_ref", 240)
        nonempty_string(item["shared_premise"], "scope.subfamily.shared_premise", 2000)
        expected_shared = canonical_sha256(
            {
                "target_ref": target_ref,
                "model_contract_id": contract["model_contract_id"],
                "subfamily_ref": item["subfamily_ref"],
                "shared_premise": item["shared_premise"],
            }
        )
        if item.get("shared_premise_contract_id") != expected_shared:
            raise CampaignError("shared-premise contract ID differs")
    else:
        raise CampaignError("evidence contract scope ceiling is invalid")
    scope_core = {key: scope[key] for key in scope if key != "scope_contract_id"}
    if scope.get("scope_contract_id") != canonical_sha256(scope_core):
        raise CampaignError("evidence scope contract ID differs")
    contract_core = {
        key: contract[key] for key in contract if key != "contract_id"
    }
    if contract.get("contract_id") != canonical_sha256(contract_core):
        raise CampaignError("evidence contract ID differs")
    return contract


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
            "evidence_contract",
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
    if brief["schema_version"] != 3:
        raise CampaignError("development brief schema_version must be 3")
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
    if matched_seed is not None:
        frozen_test = matched_seed["first_test"]
        if any(
            probe[key] != frozen_test[key]
            for key in ("question", "live_signal", "kill_signal")
        ):
            raise CampaignError(
                "development brief changes the selected seed's frozen first test"
            )
    evidence_contract = validate_evidence_contract(
        brief["evidence_contract"],
        target_ref=target_ref,
        seed_ref=seed_ref,
        matched_seed=matched_seed,
        probe_question=probe["question"],
    )

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
    if not set(methods) <= {"local_python", "local_exact_solver"}:
        raise CampaignError(
            "standing first tests allow only local_python or local_exact_solver"
        )
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
        raise CampaignError("standing first tests cannot run a fixed Lean statement")
    if theorem_ref is not None or "local_lean" in methods:
        raise CampaignError("standing first tests cannot authorize Lean")
    if evidence_contract.get("theorem") is not None:
        raise CampaignError("standing first tests cannot carry a theorem contract")
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
    authority = validate_first_test_authority(brief["authority"])

    if task_packet is not None:
        task_keys = {
            "schema_version",
            "run_id",
            "task_id",
            "wayfinder_ticket",
            "profile",
            "base_revision",
            "workspace_fingerprint",
            "objective",
            "theorem_contract",
            "inputs",
            "ownership",
            "budget",
            "required_checks",
            "success",
            "stop",
            "deliverables",
            "claims_allowed",
            "standing_first_test",
            "first_test_execution",
        }
        if set(task_packet) != task_keys or task_packet.get("schema_version") != 2:
            raise CampaignError("standing first-test task has an unexpected contract")
        for key, maximum in (
            ("run_id", 128),
            ("task_id", 240),
            ("profile", 240),
            ("base_revision", 240),
            ("workspace_fingerprint", 240),
            ("objective", 2400),
        ):
            nonempty_string(task_packet.get(key), f"task packet {key}", maximum)
        for key in ("required_checks", "success", "stop", "deliverables"):
            string_list(
                task_packet.get(key),
                f"task packet {key}",
                minimum=1,
                unique=True,
            )
        ownership_object = exact_keys(
            task_packet.get("ownership"),
            {"read_paths", "write_paths"},
            "task packet ownership",
        )
        for key in ("read_paths", "write_paths"):
            string_list(
                ownership_object.get(key),
                f"task packet ownership.{key}",
                unique=True,
            )
        if task_packet.get("task_id") != task_id:
            raise CampaignError("development brief task_id differs from task packet")
        inputs = task_packet.get("inputs")
        if not isinstance(inputs, list):
            raise CampaignError("task packet inputs must be an array")
        task_inputs: dict[str, str] = {}
        for index, entry in enumerate(inputs):
            path_text, claimed, _path = validate_file_receipt(
                entry,
                f"task packet input {index}",
                authenticate=authenticate,
            )
            if path_text in task_inputs:
                raise CampaignError("task packet input paths must be unique")
            task_inputs[path_text] = claimed
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
        ownership = ownership_object
        patterns = ownership.get("read_paths", []) + ownership.get("write_paths", [])
        if not isinstance(patterns, list):
            raise CampaignError("task ownership paths are invalid")
        for path in [batch_path, *context_paths]:
            if not ownership_covers(patterns, path):
                raise CampaignError(f"task ownership does not cover campaign input: {path}")
        claims = task_packet.get("claims_allowed", [])
        contract = task_packet.get("theorem_contract")
        if contract is not None:
            raise CampaignError("standing first-test task cannot carry a theorem contract")
        budget = task_packet.get("budget")
        if task_packet.get("wayfinder_ticket") != TICKET_0119:
            raise CampaignError("standing first test must name Ticket 0119")
        if task_packet.get("standing_first_test") != authority:
            raise CampaignError("task packet does not bind the brief's standing authority")
        if not isinstance(budget, dict) or set(budget) != {
            "wall_minutes",
            "cpu_cores",
            "memory_gib",
            "output_gib",
        }:
            raise CampaignError("campaign task packet must declare its budget")
        wall_minutes = budget.get("wall_minutes")
        if (
            not isinstance(wall_minutes, int)
            or isinstance(wall_minutes, bool)
            or wall_minutes < ceiling_minutes
            or wall_minutes > 30
        ):
            raise CampaignError(
                "task wall budget must cover the probe and remain at most 30 minutes"
            )
        for key, maximum in (("cpu_cores", 2), ("memory_gib", 4)):
            item = budget.get(key)
            if (
                not isinstance(item, int)
                or isinstance(item, bool)
                or not 1 <= item <= maximum
            ):
                raise CampaignError(f"standing first-test {key} exceeds its ceiling")
        output_gib = budget.get("output_gib")
        if (
            not isinstance(output_gib, (int, float))
            or isinstance(output_gib, bool)
            or not 0 < float(output_gib) <= 0.1
        ):
            raise CampaignError("standing first-test output_gib exceeds 0.1 GiB")
        ownership = task_packet.get("ownership") or {}
        write_paths = ownership.get("write_paths")
        run_id = task_packet.get("run_id")
        if (
            not isinstance(run_id, str)
            or re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]{0,127}", run_id) is None
            or not isinstance(write_paths, list)
            or not write_paths
        ):
            raise CampaignError("standing first test lacks exact owned output paths")
        output_root = Path("runs") / "agents" / run_id
        for path_text in write_paths:
            if not isinstance(path_text, str):
                raise CampaignError("standing first-test write path is not a string")
            path_value = Path(path_text)
            if (
                path_value.is_absolute()
                or ".." in path_value.parts
                or any(character in path_text for character in "*?[]")
                or path_value == output_root
                or output_root not in path_value.parents
            ):
                raise CampaignError(
                    "standing first-test writes must be exact descendants of its ignored run"
                )
            git_command = ["git"]
            if (ROOT / ".git-data").is_dir():
                git_command.extend(["--git-dir=.git-data", "--work-tree=."])
            ignored = subprocess.run(
                [*git_command, "check-ignore", "--no-index", "--quiet", path_text],
                cwd=ROOT,
                check=False,
                capture_output=True,
                text=True,
            )
            if ignored.returncode != 0:
                raise CampaignError(
                    f"standing first-test write path is not ignored: {path_text}"
                )
        deliverables = task_packet.get("deliverables")
        if not isinstance(deliverables, list) or not set(deliverables) <= set(
            write_paths
        ):
            raise CampaignError("standing first-test deliverables exceed owned outputs")
        if not isinstance(claims, list) or not set(claims) <= {
            "proposal", "computational_evidence"
        }:
            raise CampaignError("standing first-test claims exceed pre-admission evidence")
        if contract is not None or "file_compiles" in claims:
            raise CampaignError("standing first tests cannot claim compilation")
        validate_first_test_execution(
            task_packet.get("first_test_execution"),
            task=task_packet,
            methods=methods,
            authenticate=authenticate,
        )
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


def validate_execution_envelope(
    value: Any,
    *,
    brief_path: Path,
    brief: dict[str, Any],
    task: dict[str, Any],
    receipt: dict[str, Any],
    authenticate: bool,
) -> dict[str, Any] | None:
    envelope_text, _envelope_sha, envelope_path = validate_file_receipt(
        value, "development execution envelope", authenticate=authenticate
    )
    if not authenticate:
        return None
    run_id = nonempty_string(task.get("run_id"), "execution envelope run_id")
    task_id = nonempty_string(task.get("task_id"), "execution envelope task_id")
    expected_path = (
        Path("runs")
        / "agents"
        / run_id
        / "root-receipts"
        / f"{task_id}.execution-envelope.json"
    )
    if Path(envelope_text) != expected_path:
        raise CampaignError("execution envelope path is not the derived root-owned path")
    worker_paths = {
        *[str(item.get("path")) for item in task.get("inputs", []) if isinstance(item, dict)],
        *((task.get("ownership") or {}).get("read_paths") or []),
        *((task.get("ownership") or {}).get("write_paths") or []),
        *(task.get("deliverables") or []),
    }
    if envelope_text in worker_paths:
        raise CampaignError("execution envelope is visible or writable to the worker")

    envelope = exact_keys(
        load_json(envelope_path, "development execution envelope"),
        {
            "schema_version",
            "protocol",
            "envelope_id",
            "guard_component",
            "identity",
            "launch",
            "enforced_policy",
            "observation",
            "terminal",
        },
        "development execution envelope",
    )
    if (
        envelope.get("schema_version") != 1
        or envelope.get("protocol")
        != "research-first-test-execution-envelope-v1"
    ):
        raise CampaignError("execution envelope protocol is invalid")
    envelope_core = {
        key: envelope[key] for key in envelope if key != "envelope_id"
    }
    if envelope.get("envelope_id") != canonical_sha256(envelope_core):
        raise CampaignError("execution envelope ID differs from its complete core")
    terminal = envelope.get("terminal")
    if terminal not in {"PASS", "VIOLATION", "LAUNCH_STOP"}:
        raise CampaignError("execution envelope terminal is invalid")
    execution = task.get("first_test_execution") or {}
    if envelope.get("guard_component") != execution.get("guard_component"):
        raise CampaignError("execution envelope guard differs from the task contract")
    validate_file_receipt(
        envelope.get("guard_component"),
        "execution envelope guard component",
        authenticate=True,
    )

    identity = exact_keys(
        envelope.get("identity"),
        {
            "seed_claim",
            "claim_id",
            "development_brief",
            "brief_id",
            "task_packet",
            "task_id",
            "execution_contract_id",
        },
        "execution envelope identity",
    )
    brief_receipt = {
        "path": str(brief_path.resolve().relative_to(ROOT.resolve())),
        "sha256": digest(brief_path),
    }
    if (
        identity.get("development_brief") != brief_receipt
        or identity.get("brief_id") != brief.get("brief_id")
        or identity.get("task_id") != task_id
        or identity.get("execution_contract_id") != execution.get("contract_id")
    ):
        raise CampaignError("execution envelope brief/task identity differs")
    _task_text, _task_sha, task_path = validate_file_receipt(
        identity.get("task_packet"), "execution envelope task packet", authenticate=True
    )
    if load_json(task_path, "execution envelope task packet") != task:
        raise CampaignError("execution envelope task packet differs from the admitted task")
    _claim_text, _claim_sha, claim_path = validate_file_receipt(
        identity.get("seed_claim"), "execution envelope seed claim", authenticate=True
    )
    claim = load_json(claim_path, "execution envelope seed claim")
    candidate = ((brief.get("evidence_contract") or {}).get("scope") or {}).get(
        "candidate"
    ) or {}
    expected_claim_id = f"{candidate.get('campaign_id')}:{candidate.get('seed_id')}"
    if (
        identity.get("claim_id") != expected_claim_id
        or claim.get("claim_id") != expected_claim_id
        or claim.get("development_brief") != identity.get("development_brief")
        or claim.get("task_packet") != identity.get("task_packet")
    ):
        raise CampaignError("execution envelope seed-claim identity differs")

    launch = exact_keys(
        envelope.get("launch"),
        {
            "started_at",
            "finished_at",
            "boot_id",
            "outer_pid",
            "sandbox_pid",
            "sandbox_start_ticks",
            "process_group",
            "argv",
            "cwd",
        },
        "execution envelope launch",
    )
    for key in ("started_at", "finished_at", "boot_id"):
        nonempty_string(launch.get(key), f"execution envelope launch.{key}", 240)
    outer_pid = launch.get("outer_pid")
    if not isinstance(outer_pid, int) or isinstance(outer_pid, bool) or outer_pid <= 0:
        raise CampaignError("execution envelope launch.outer_pid is invalid")
    for key in ("sandbox_pid", "sandbox_start_ticks", "process_group"):
        item = launch.get(key)
        if terminal == "PASS":
            valid = isinstance(item, int) and not isinstance(item, bool) and item > 0
        else:
            valid = item is None or (
                isinstance(item, int) and not isinstance(item, bool) and item >= 0
            )
        if not valid:
            raise CampaignError(f"execution envelope launch.{key} is invalid")
    resolved_argv = string_list(
        launch.get("argv"), "execution envelope launch.argv", minimum=4, maximum=64
    )
    template_argv = execution.get("argv_template") or []
    if len(resolved_argv) != len(template_argv):
        raise CampaignError("execution envelope argv length differs from the task")
    for expected, actual in zip(template_argv, resolved_argv, strict=True):
        if re.fullmatch(r"\{output_fd:[a-z][a-z0-9_]{0,63}\}", str(expected)):
            if re.fullmatch(r"[0-9]+", actual) is None:
                raise CampaignError("execution envelope did not resolve an output FD")
        elif actual != expected:
            raise CampaignError("execution envelope argv differs from the task contract")
    if launch.get("cwd") != "/work":
        raise CampaignError("execution envelope launch cwd is not /work")

    policy = exact_keys(
        envelope.get("enforced_policy"),
        {
            "wall_seconds",
            "cpu_affinity",
            "memory_bytes",
            "output_bytes",
            "process_model",
            "network",
            "repository",
            "persistent_writes",
            "seccomp_policy_sha256",
            "namespace_inodes",
        },
        "execution envelope policy",
    )
    budget = task.get("budget") or {}
    expected_output_bytes = int(float(budget.get("output_gib")) * (1024**3))
    affinity = policy.get("cpu_affinity")
    if (
        policy.get("wall_seconds") != int(budget.get("wall_minutes")) * 60
        or not isinstance(affinity, list)
        or not affinity
        or len(affinity) > int(budget.get("cpu_cores"))
        or len(set(affinity)) != len(affinity)
        or any(not isinstance(cpu, int) or isinstance(cpu, bool) or cpu < 0 for cpu in affinity)
        or policy.get("memory_bytes") != int(budget.get("memory_gib")) * (1024**3)
        or policy.get("output_bytes") != expected_output_bytes
        or policy.get("process_model") != FIRST_TEST_PROCESS_MODEL
        or policy.get("network")
        not in {"new-net-namespace-plus-seccomp-kill", "not-observed"}
        or policy.get("repository")
        not in {"sparse-authenticated-inputs-read-only", "not-observed"}
        or policy.get("persistent_writes")
        != [item.get("path") for item in execution.get("outputs", [])]
        or not isinstance(policy.get("seccomp_policy_sha256"), str)
        or HEX64.fullmatch(policy["seccomp_policy_sha256"]) is None
    ):
        raise CampaignError("execution envelope enforced policy differs from the task")
    namespace = exact_keys(
        policy.get("namespace_inodes"),
        {"user", "mount", "pid", "net", "ipc", "uts", "cgroup"},
        "execution envelope namespace inodes",
    )
    valid_namespace = all(
        item is None
        or (isinstance(item, int) and not isinstance(item, bool) and item > 0)
        for item in namespace.values()
    )
    if not valid_namespace:
        raise CampaignError("execution envelope namespace observations are invalid")

    observation = exact_keys(
        envelope.get("observation"),
        {
            "exit_code",
            "signal",
            "wall_seconds",
            "cpu_seconds",
            "peak_aggregate_rss_bytes",
            "worker_output_bytes",
            "writes",
            "stdout",
            "stderr",
            "forbidden_attempts",
            "violations",
        },
        "execution envelope observation",
    )
    for key in ("wall_seconds", "cpu_seconds"):
        item = observation.get(key)
        if not isinstance(item, (int, float)) or isinstance(item, bool) or item < 0:
            raise CampaignError(f"execution envelope observation.{key} is invalid")
    for key in ("peak_aggregate_rss_bytes", "worker_output_bytes"):
        item = observation.get(key)
        if not isinstance(item, int) or isinstance(item, bool) or item < 0:
            raise CampaignError(f"execution envelope observation.{key} is invalid")
    writes = observation.get("writes")
    if not isinstance(writes, list):
        raise CampaignError("execution envelope write manifest must be an array")
    manifest: list[dict[str, Any]] = []
    for index, item in enumerate(writes):
        entry = exact_keys(
            item,
            {"role", "path", "sha256", "bytes", "materialized"},
            f"execution envelope write {index}",
        )
        nonempty_string(entry.get("role"), f"execution envelope write {index}.role", 64)
        nonempty_string(entry.get("path"), f"execution envelope write {index}.path")
        if not isinstance(entry.get("sha256"), str) or HEX64.fullmatch(entry["sha256"]) is None:
            raise CampaignError("execution envelope write digest is invalid")
        if not isinstance(entry.get("bytes"), int) or isinstance(entry.get("bytes"), bool) or entry["bytes"] < 0:
            raise CampaignError("execution envelope write byte count is invalid")
        if not isinstance(entry.get("materialized"), bool):
            raise CampaignError("execution envelope write materialization flag is invalid")
        manifest.append(entry)
    if len({(item["role"], item["path"]) for item in manifest}) != len(manifest):
        raise CampaignError("execution envelope write manifest contains duplicates")
    streams: list[dict[str, Any]] = []
    for key in ("stdout", "stderr"):
        stream = exact_keys(
            observation.get(key), {"sha256", "bytes"}, f"execution envelope {key}"
        )
        if not isinstance(stream.get("sha256"), str) or HEX64.fullmatch(stream["sha256"]) is None:
            raise CampaignError(f"execution envelope {key} digest is invalid")
        if not isinstance(stream.get("bytes"), int) or isinstance(stream.get("bytes"), bool) or stream["bytes"] < 0:
            raise CampaignError(f"execution envelope {key} byte count is invalid")
        streams.append(stream)
    total_bytes = sum(item["bytes"] for item in manifest) + sum(
        item["bytes"] for item in streams
    )
    if observation.get("worker_output_bytes") != total_bytes:
        raise CampaignError("execution envelope complete output total differs")
    violations = observation.get("violations")
    if not isinstance(violations, list) or not all(isinstance(item, str) for item in violations):
        raise CampaignError("execution envelope violations are invalid")
    namespace_observed = all(item is not None for item in namespace.values())
    filter_observed = observation.get("forbidden_attempts") != "not-observed"
    expected_network = (
        "new-net-namespace-plus-seccomp-kill"
        if namespace_observed and filter_observed
        else "not-observed"
    )
    expected_repository = (
        "sparse-authenticated-inputs-read-only"
        if namespace_observed
        else "not-observed"
    )
    if (
        policy.get("network") != expected_network
        or policy.get("repository") != expected_repository
    ):
        raise CampaignError("execution envelope policy claims unobserved controls")

    if terminal == "PASS":
        expected_manifest = [
            (item.get("role"), item.get("path")) for item in execution.get("outputs", [])
        ]
        if (
            observation.get("exit_code") != 0
            or observation.get("signal") is not None
            or observation.get("forbidden_attempts") != "none"
            or violations
            or [(item["role"], item["path"]) for item in manifest] != expected_manifest
            or any(not item["materialized"] for item in manifest)
        ):
            raise CampaignError("PASS execution envelope contains a policy violation")
        if (
            float(observation["wall_seconds"]) > float(policy["wall_seconds"])
            or float(observation["cpu_seconds"])
            > float(policy["wall_seconds"]) * len(affinity)
            or int(observation["peak_aggregate_rss_bytes"]) > int(policy["memory_bytes"])
            or int(observation["worker_output_bytes"]) > int(policy["output_bytes"])
        ):
            raise CampaignError("PASS execution envelope exceeds an enforced limit")
        for item in manifest:
            materialized_path = repo_path(item["path"], "execution envelope output")
            if (
                not materialized_path.is_file()
                or digest(materialized_path) != item["sha256"]
                or materialized_path.stat().st_size != item["bytes"]
            ):
                raise CampaignError("execution envelope output manifest is not authentic")
        event_artifacts = [event.get("artifact") for event in receipt.get("evidence_events", [])]
        for artifact in event_artifacts:
            matches = [
                item
                for item in manifest
                if item["path"] == artifact.get("path")
                and item["sha256"] == artifact.get("sha256")
            ] if isinstance(artifact, dict) else []
            if len(matches) != 1:
                raise CampaignError("event artifact is absent from the complete write manifest")
    else:
        if any(item["materialized"] for item in manifest):
            raise CampaignError("non-PASS execution envelope materialized worker output")
        if (
            receipt.get("terminal") != "OPERATIONAL_STOP"
            or receipt.get("evidence_events") != []
            or receipt.get("claim_candidate") is not None
            or receipt.get("serendipity") is not None
        ):
            raise CampaignError("non-PASS envelope requires a pure operational stop")

    resource = receipt.get("resource_use") or {}
    expected_projection = {
        "wall_minutes": float(observation["wall_seconds"]) / 60,
        "active_minutes": float(observation["wall_seconds"]) / 60,
        "cpu_seconds": observation["cpu_seconds"],
        "peak_memory_mib": float(observation["peak_aggregate_rss_bytes"]) / (1024**2),
        "artifact_bytes": observation["worker_output_bytes"],
        "source_requests": 0,
    }
    if any(resource.get(key) != expected for key, expected in expected_projection.items()):
        raise CampaignError("development resource projection differs from the root envelope")
    return envelope


def validate_verifier_guard_chain(
    receipt: dict[str, Any],
    *,
    event: dict[str, Any],
    normalized: dict[str, Any],
    brief: dict[str, Any],
    task: dict[str, Any],
) -> tuple[list[str], dict[str, Any]]:
    event_id = nonempty_string(event.get("event_id"), "verified event ID")
    run_id = nonempty_string(task.get("run_id"), "verifier task run_id")
    root_receipt_root = Path("runs") / "agents" / run_id / "root-receipts"
    expected_request_path = root_receipt_root / f"{event_id}.verification-request.json"
    expected_envelope_path = root_receipt_root / f"{event_id}.verification-envelope.json"
    request_text, _request_sha, request_path = validate_file_receipt(
        receipt.get("verification_request"),
        "event verifier request",
        authenticate=True,
    )
    envelope_text, _envelope_sha, envelope_path = validate_file_receipt(
        receipt.get("verification_envelope"),
        "event verifier envelope",
        authenticate=True,
    )
    worker_paths = {
        *[str(item.get("path")) for item in task.get("inputs", []) if isinstance(item, dict)],
        *((task.get("ownership") or {}).get("read_paths") or []),
        *((task.get("ownership") or {}).get("write_paths") or []),
        *(task.get("deliverables") or []),
    }
    if (
        Path(request_text) != expected_request_path
        or Path(envelope_text) != expected_envelope_path
        or request_text in worker_paths
        or envelope_text in worker_paths
    ):
        raise CampaignError("event verifier request/envelope is not root-owned")
    request = exact_keys(
        load_json(request_path, "event verifier request"),
        {
            "schema_version",
            "protocol",
            "verifier_contract_id",
            "guard_component",
            "seed_claim",
            "task_packet",
            "claim_id",
            "task_id",
            "event",
            "checker",
            "argv_template",
            "input_receipts",
            "expected_normalized_result",
            "budget",
            "process_model",
        },
        "event verifier request",
    )
    if (
        request.get("schema_version") != 1
        or request.get("protocol") != "ticket-0119-event-verifier-request-v1"
        or request.get("guard_component")
        != (task.get("first_test_execution") or {}).get("guard_component")
        or request.get("checker") != receipt.get("verifier_component")
        or request.get("argv_template") != (receipt.get("invocation") or {}).get("argv")
        or request.get("input_receipts")
        != [request.get("checker"), *(receipt.get("input_receipts") or [])]
        or request.get("expected_normalized_result") != normalized
        or request.get("budget") != task.get("budget")
        or request.get("process_model") != FIRST_TEST_PROCESS_MODEL
        or request.get("task_id") != task.get("task_id")
    ):
        raise CampaignError("event verifier request differs from the admitted contract")
    request_event = exact_keys(
        request.get("event"),
        {
            "event_id",
            "event_core_sha256",
            "subject_contract_id",
            "model_contract_id",
            "scope_contract_id",
            "artifact",
        },
        "event verifier request event",
    )
    if request_event != {
        "event_id": event_id,
        "event_core_sha256": receipt.get("verified_event_core_sha256"),
        "subject_contract_id": receipt.get("subject_contract_id"),
        "model_contract_id": receipt.get("model_contract_id"),
        "scope_contract_id": receipt.get("scope_contract_id"),
        "artifact": event.get("artifact"),
    }:
        raise CampaignError("event verifier request is rebound from the event")
    _guard_text, _guard_sha, _guard_path = validate_file_receipt(
        request.get("guard_component"), "event verifier guard", authenticate=True
    )
    if request.get("guard_component", {}).get("path") != FIRST_TEST_GUARD_PATH:
        raise CampaignError("event verifier request names an untrusted guard")
    _task_text, _task_sha, task_path = validate_file_receipt(
        request.get("task_packet"), "event verifier task packet", authenticate=True
    )
    if load_json(task_path, "event verifier task packet") != task:
        raise CampaignError("event verifier request task packet differs")
    _claim_text, _claim_sha, claim_path = validate_file_receipt(
        request.get("seed_claim"), "event verifier seed claim", authenticate=True
    )
    claim = load_json(claim_path, "event verifier seed claim")
    candidate = ((brief.get("evidence_contract") or {}).get("scope") or {}).get(
        "candidate"
    ) or {}
    expected_claim_id = f"{candidate.get('campaign_id')}:{candidate.get('seed_id')}"
    if request.get("claim_id") != expected_claim_id or claim.get("claim_id") != expected_claim_id:
        raise CampaignError("event verifier request claim identity differs")
    request_core = {
        key: receipt[key]
        for key in (
            "verifier_component",
            "claim_contract_id",
            "primary_contract_id",
            "subject_contract_id",
            "model_contract_id",
            "scope_contract_id",
            "verified_event_core_sha256",
            "event_artifact",
            "engine",
            "invocation",
            "input_receipts",
        )
    }
    if (
        request.get("verifier_contract_id") != canonical_sha256(request_core)
        or receipt.get("verifier_contract_id") != request.get("verifier_contract_id")
    ):
        raise CampaignError("event verifier request contract ID differs")

    envelope = exact_keys(
        load_json(envelope_path, "event verifier envelope"),
        {
            "schema_version",
            "protocol",
            "envelope_id",
            "guard_component",
            "identity",
            "launch",
            "enforced_policy",
            "observation",
            "normalized_result",
            "terminal",
        },
        "event verifier envelope",
    )
    if (
        envelope.get("schema_version") != 1
        or envelope.get("protocol")
        != "research-event-verifier-execution-envelope-v1"
        or envelope.get("guard_component") != request.get("guard_component")
        or envelope.get("terminal") != "PASS"
        or envelope.get("envelope_id")
        != canonical_sha256(
            {key: envelope[key] for key in envelope if key != "envelope_id"}
        )
    ):
        raise CampaignError("event verifier envelope identity or terminal differs")
    identity = exact_keys(
        envelope.get("identity"),
        {
            "verifier_request",
            "verifier_contract_id",
            "seed_claim",
            "claim_id",
            "task_packet",
            "task_id",
            "event_id",
            "event_core_sha256",
            "subject_contract_id",
            "model_contract_id",
            "scope_contract_id",
            "event_artifact",
        },
        "event verifier envelope identity",
    )
    if identity != {
        "verifier_request": receipt.get("verification_request"),
        "verifier_contract_id": request.get("verifier_contract_id"),
        "seed_claim": request.get("seed_claim"),
        "claim_id": request.get("claim_id"),
        "task_packet": request.get("task_packet"),
        "task_id": request.get("task_id"),
        "event_id": event_id,
        "event_core_sha256": request_event.get("event_core_sha256"),
        "subject_contract_id": request_event.get("subject_contract_id"),
        "model_contract_id": request_event.get("model_contract_id"),
        "scope_contract_id": request_event.get("scope_contract_id"),
        "event_artifact": request_event.get("artifact"),
    }:
        raise CampaignError("event verifier envelope is rebound from its request")
    launch = exact_keys(
        envelope.get("launch"),
        {
            "started_at",
            "finished_at",
            "boot_id",
            "outer_pid",
            "sandbox_pid",
            "sandbox_start_ticks",
            "process_group",
            "argv",
            "cwd",
        },
        "event verifier envelope launch",
    )
    if launch.get("argv") != request.get("argv_template") or launch.get("cwd") != "/work":
        raise CampaignError("event verifier envelope launch differs from its request")
    policy = exact_keys(
        envelope.get("enforced_policy"),
        {
            "wall_seconds",
            "cpu_affinity",
            "memory_bytes",
            "output_bytes",
            "process_model",
            "network",
            "repository",
            "persistent_writes",
            "seccomp_policy_sha256",
            "namespace_inodes",
        },
        "event verifier envelope policy",
    )
    budget = task.get("budget") or {}
    affinity = policy.get("cpu_affinity")
    if (
        policy.get("wall_seconds") != int(budget.get("wall_minutes")) * 60
        or not isinstance(affinity, list)
        or not affinity
        or len(affinity) > int(budget.get("cpu_cores"))
        or policy.get("memory_bytes") != int(budget.get("memory_gib")) * (1024**3)
        or policy.get("output_bytes")
        != int(float(budget.get("output_gib")) * (1024**3))
        or policy.get("process_model") != FIRST_TEST_PROCESS_MODEL
        or policy.get("network") != "new-net-namespace-plus-seccomp-kill"
        or policy.get("repository") != "sparse-authenticated-inputs-read-only"
        or policy.get("persistent_writes") != []
        or not isinstance(policy.get("seccomp_policy_sha256"), str)
        or HEX64.fullmatch(policy["seccomp_policy_sha256"]) is None
    ):
        raise CampaignError("event verifier envelope policy differs from its task")
    exact_keys(
        policy.get("namespace_inodes"),
        {"user", "mount", "pid", "net", "ipc", "uts", "cgroup"},
        "event verifier namespace inodes",
    )
    observation = exact_keys(
        envelope.get("observation"),
        {
            "exit_code",
            "signal",
            "wall_seconds",
            "cpu_seconds",
            "peak_aggregate_rss_bytes",
            "worker_output_bytes",
            "writes",
            "stdout",
            "stderr",
            "forbidden_attempts",
            "violations",
        },
        "event verifier envelope observation",
    )
    normalized_bytes = canonical_bytes(normalized) + b"\n"
    normalized_receipt = exact_keys(
        envelope.get("normalized_result"),
        {"sha256", "bytes", "value", "matches_expected"},
        "event verifier envelope normalized result",
    )
    if (
        observation.get("exit_code") != 0
        or observation.get("signal") is not None
        or observation.get("writes") != []
        or observation.get("forbidden_attempts") != "none"
        or observation.get("violations") != []
        or normalized_receipt
        != {
            "sha256": hashlib.sha256(normalized_bytes).hexdigest(),
            "bytes": len(normalized_bytes),
            "value": normalized,
            "matches_expected": True,
        }
        or observation.get("worker_output_bytes") != len(normalized_bytes)
    ):
        raise CampaignError("event verifier envelope did not establish the normalized result")
    claim_parts = Path(request.get("seed_claim", {}).get("path", "")).parts
    service_dir = claim_path.parent
    if "claims" in claim_parts:
        claims_index = claim_parts.index("claims")
        service_dir = ROOT.joinpath(*claim_parts[:claims_index])
    try:
        service_text = str(service_dir.resolve().relative_to(ROOT.resolve()))
    except ValueError as exc:
        raise CampaignError("event verifier service directory is outside repository") from exc
    guarded_argv = [
        "python3",
        FIRST_TEST_GUARD_PATH,
        "verify",
        "--service-dir",
        service_text,
        "--request",
        request_text,
        "--request-sha256",
        digest(request_path),
        "--envelope",
        envelope_text,
    ]
    return guarded_argv, envelope


def validate_event_verification(
    value: Any,
    *,
    event: dict[str, Any],
    claim_contract_id: str,
    brief: dict[str, Any],
    task: dict[str, Any],
    authenticate: bool,
) -> None:
    claim_level = event["claim_level"]
    if claim_level == "proposal":
        if value is not None:
            raise CampaignError("proposal evidence event must not carry verification")
        return
    path_text, _claimed, path = validate_file_receipt(
        value, "event verification receipt", authenticate=authenticate
    )
    if not authenticate:
        return
    run_id = nonempty_string(task.get("run_id"), "event verification task run_id")
    root_receipt_root = Path("runs") / "agents" / run_id / "root-receipts"
    receipt_path_value = Path(path_text)
    task_paths = {
        *[str(item.get("path")) for item in task.get("inputs", []) if isinstance(item, dict)],
        *((task.get("ownership") or {}).get("read_paths") or []),
        *((task.get("ownership") or {}).get("write_paths") or []),
        *(task.get("deliverables") or []),
    }
    if root_receipt_root not in receipt_path_value.parents or path_text in task_paths:
        raise CampaignError("event verification receipt must be root-owned and worker-invisible")
    receipt = exact_keys(
        load_json(path, "event verification receipt"),
        {
            "schema_version",
            "protocol",
            "verifier_contract_id",
            "verification_request",
            "verification_envelope",
            "verifier_component",
            "claim_contract_id",
            "primary_contract_id",
            "subject_contract_id",
            "model_contract_id",
            "scope_contract_id",
            "verified_event_core_sha256",
            "event_artifact",
            "engine",
            "invocation",
            "input_receipts",
            "normalized_result",
            "guarded_runner",
            "makefile",
            "theorem_audit",
            "exit_code",
            "terminal",
        },
        "event verification receipt",
    )
    binding = event.get("binding") or {}
    event_core_sha256 = canonical_sha256(
        {
            key: event[key]
            for key in event
            if key not in {"event_id", "verification_receipt"}
        }
    )
    if (
        receipt.get("schema_version") != 3
        or receipt.get("protocol") != "research-event-verification-v3"
        or receipt.get("claim_contract_id") != claim_contract_id
        or receipt.get("primary_contract_id") != binding.get("primary_contract_id")
        or receipt.get("subject_contract_id") != binding.get("subject_contract_id")
        or receipt.get("model_contract_id") != binding.get("model_contract_id")
        or receipt.get("scope_contract_id") != binding.get("scope_contract_id")
        or receipt.get("verified_event_core_sha256") != event_core_sha256
        or receipt.get("event_artifact") != event.get("artifact")
        or receipt.get("exit_code") != 0
        or receipt.get("terminal") != "PASS"
    ):
        raise CampaignError("event verification receipt identity or terminal differs")
    verifier_text, _verifier_sha, verifier_path = validate_file_receipt(
        receipt.get("verifier_component"),
        "event verifier component",
        authenticate=True,
    )
    invocation = exact_keys(
        receipt.get("invocation"), {"argv", "cwd"}, "event verification invocation"
    )
    argv = string_list(
        invocation.get("argv"), "event verification argv", minimum=1, maximum=32
    )
    if invocation.get("cwd") != ".":
        raise CampaignError("event verification cwd must be the repository root")
    inputs = receipt.get("input_receipts")
    if not isinstance(inputs, list) or not inputs:
        raise CampaignError("event verification input receipts must be nonempty")
    input_paths: list[str] = []
    for index, item in enumerate(inputs):
        input_text, _input_sha, _input_path = validate_file_receipt(
            item, f"event verification input {index}", authenticate=True
        )
        input_paths.append(input_text)
    if len(set(input_paths)) != len(input_paths):
        raise CampaignError("event verification input paths must be unique")
    engine = receipt.get("engine")
    if engine not in {
        "python_exact",
        "exact_solver",
        "lean_native_decide",
        "lean_kernel",
    }:
        raise CampaignError("event verification engine is invalid")
    verifier_contract_core = {
        key: receipt[key]
        for key in (
            "verifier_component",
            "claim_contract_id",
            "primary_contract_id",
            "subject_contract_id",
            "model_contract_id",
            "scope_contract_id",
            "verified_event_core_sha256",
            "event_artifact",
            "engine",
            "invocation",
            "input_receipts",
        )
    }
    normalized = exact_keys(
        receipt.get("normalized_result"),
        {
            "schema_version",
            "protocol",
            "verified_event_core_sha256",
            "event_artifact",
            "claim_contract_id",
            "primary_contract_id",
            "subject_contract_id",
            "model_contract_id",
            "scope_contract_id",
            "kind",
            "gate_branch",
            "polarity",
            "damage_scope_reached",
            "observation_sha256",
            "checked_predicate",
            "result",
            "verified_learning",
        },
        "event normalized result",
    )
    expected_normalized = {
        "schema_version": 1,
        "protocol": "research-event-normalized-result-v1",
        "verified_event_core_sha256": event_core_sha256,
        "event_artifact": event.get("artifact"),
        "claim_contract_id": claim_contract_id,
        "primary_contract_id": binding.get("primary_contract_id"),
        "subject_contract_id": binding.get("subject_contract_id"),
        "model_contract_id": binding.get("model_contract_id"),
        "scope_contract_id": binding.get("scope_contract_id"),
        "kind": event.get("kind"),
        "gate_branch": event.get("gate_branch"),
        "polarity": binding.get("polarity"),
        "damage_scope_reached": binding.get("damage_scope_reached"),
        "observation_sha256": hashlib.sha256(
            str(event.get("observation")).encode("utf-8")
        ).hexdigest(),
        "checked_predicate": (brief.get("probe") or {}).get("question"),
        "result": binding.get("polarity"),
        "verified_learning": normalized.get("verified_learning"),
    }
    if normalized != expected_normalized:
        raise CampaignError("normalized verifier result differs from the event contract")
    verified_learning = exact_keys(
        normalized.get("verified_learning"),
        {"failing_feature", "strongest_supported_statement"},
        "normalized verified learning",
    )
    falsifier = (
        event.get("kind") in {"exact_falsifier", "claim_refuted"}
        and event.get("gate_branch") == "kill"
        and binding.get("polarity") == "refutes"
    )
    for role in ("failing_feature", "strongest_supported_statement"):
        item = verified_learning.get(role)
        if falsifier:
            claim = exact_keys(
                item,
                {"learning_claim_id", "text", "subject_contract_id"},
                f"normalized verified learning {role}",
            )
            nonempty_string(claim.get("text"), f"normalized verified learning {role}.text", 2000)
            if claim.get("subject_contract_id") != binding.get("subject_contract_id"):
                raise CampaignError("normalized learning subject differs from the event")
            learning_core = {
                "role": role,
                "text": claim.get("text"),
                "subject_contract_id": claim.get("subject_contract_id"),
                "model_contract_id": binding.get("model_contract_id"),
                "scope_contract_id": binding.get("scope_contract_id"),
                "verified_event_core_sha256": event_core_sha256,
            }
            if claim.get("learning_claim_id") != canonical_sha256(learning_core):
                raise CampaignError("normalized learning-claim ID differs")
        elif item is not None:
            raise CampaignError("non-falsifier event cannot verify negative learning prose")
    expected_guard = {
        "path": "scripts/run_lean_guarded.py",
        "sha256": digest(ROOT / "scripts/run_lean_guarded.py"),
    }
    expected_makefile = {"path": "Makefile", "sha256": digest(ROOT / "Makefile")}
    lean_engine = engine in {"lean_native_decide", "lean_kernel"}
    if task.get("standing_first_test") is not None and lean_engine:
        raise CampaignError("standing first tests cannot use a Lean verification engine")
    if lean_engine:
        if (
            receipt.get("verification_request") is not None
            or receipt.get("verification_envelope") is not None
            or receipt.get("verifier_contract_id")
            != canonical_sha256(verifier_contract_core)
        ):
            raise CampaignError("later Lean verification has an invalid global contract")
    elif (
        receipt.get("verification_request") is None
        or receipt.get("verification_envelope") is None
    ):
        raise CampaignError("Python evidence lacks its guarded verifier receipts")
    if claim_level == "file_compiles":
        if engine != "lean_kernel" or event.get("kind") not in {
            "compiling_fixed_statement",
            "exact_falsifier",
            "claim_refuted",
        }:
            raise CampaignError("file-compiles evidence must be a kernel Lean event")
        if (
            receipt.get("verifier_component") != expected_guard
            or receipt.get("guarded_runner") != expected_guard
            or receipt.get("makefile") != expected_makefile
            or argv != ["make", "test"]
        ):
            raise CampaignError("Lean compilation did not use the guarded Makefile gate")
    else:
        if engine == "lean_kernel":
            raise CampaignError("kernel compilation cannot be relabeled as computation")
        if engine == "lean_native_decide":
            if (
                receipt.get("verifier_component") != expected_guard
                or receipt.get("guarded_runner") != expected_guard
                or receipt.get("makefile") != expected_makefile
                or argv != ["make", "test"]
            ):
                raise CampaignError(
                    "native_decide evidence must remain computational and use the guarded Makefile gate"
                )
        elif engine in {"python_exact", "exact_solver"} and any(
            receipt.get(key) is not None
            for key in ("guarded_runner", "makefile", "theorem_audit")
        ):
            raise CampaignError(
                "non-Lean computational verification cannot carry Lean gate receipts"
            )

    if lean_engine:
        theorem = (brief.get("evidence_contract") or {}).get("theorem")
        if not isinstance(theorem, dict):
            raise CampaignError("Lean evidence lacks a frozen theorem contract")
        _audit_text, _audit_sha, audit_path = validate_file_receipt(
            receipt.get("theorem_audit"),
            "Lean declaration audit",
            authenticate=True,
        )
        audit = exact_keys(
            load_json(audit_path, "Lean declaration audit"),
            {
                "schema_version",
                "protocol",
                "claim_contract_id",
                "verified_event_core_sha256",
                "source",
                "declaration_name",
                "statement_sha256",
                "proof_mode",
                "axiom_report",
                "terminal",
            },
            "Lean declaration audit",
        )
        expected_mode = "native_decide" if engine == "lean_native_decide" else "kernel"
        if (
            audit.get("schema_version") != 1
            or audit.get("protocol") != "research-lean-declaration-audit-v1"
            or audit.get("claim_contract_id") != claim_contract_id
            or audit.get("verified_event_core_sha256")
            != receipt.get("verified_event_core_sha256")
            or audit.get("source") != event.get("artifact")
            or audit.get("declaration_name") != theorem.get("name")
            or audit.get("statement_sha256")
            != hashlib.sha256(str(theorem.get("statement")).encode("utf-8")).hexdigest()
            or audit.get("proof_mode") != expected_mode
            or audit.get("terminal") != "PASS"
        ):
            raise CampaignError("Lean declaration audit differs from the frozen theorem")
        _source_text, _source_sha, source_path = validate_file_receipt(
            audit.get("source"), "Lean audited source", authenticate=True
        )
        if source_path.suffix != ".lean":
            raise CampaignError("Lean evidence artifact must be a Lean source file")
        source = source_path.read_text(encoding="utf-8")
        declaration = str(theorem.get("name"))
        if re.search(rf"\b(?:theorem|lemma)\s+{re.escape(declaration)}\b", source) is None:
            raise CampaignError("Lean audited declaration is absent from its source")
        if engine == "lean_native_decide":
            if audit.get("axiom_report") is not None or "native_decide" not in source:
                raise CampaignError("native_decide audit lacks its exact computational source")
        else:
            if re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", source):
                raise CampaignError("kernel theorem source contains a forbidden trust token")
            _axiom_text, _axiom_sha, axiom_path = validate_file_receipt(
                audit.get("axiom_report"), "Lean axiom report", authenticate=True
            )
            axiom_text = axiom_path.read_text(encoding="utf-8")
            if declaration not in axiom_text or any(
                token in axiom_text for token in ("sorryAx", "unsafe", "admit")
            ):
                raise CampaignError("Lean axiom report does not clear the frozen declaration")
    else:
        if engine not in {"python_exact", "exact_solver"}:
            raise CampaignError("unsupported checked-evidence engine")
        if engine == "exact_solver":
            raise CampaignError(
                "exact_solver evidence requires a separately pinned certificate and independent checker"
            )
        execution = task.get("first_test_execution")
        if not isinstance(execution, dict):
            raise CampaignError("Python evidence lacks its frozen first-test execution contract")
        execution_inputs = execution.get("input_receipts") or []
        checker_receipts = [
            item
            for item in execution_inputs
            if isinstance(item, dict) and item.get("path") == verifier_text
        ]
        if len(checker_receipts) != 1 or receipt.get("verifier_component") != checker_receipts[0]:
            raise CampaignError("event verifier differs from the task-frozen checker")
        raw_inputs = [item for item in execution_inputs if item != checker_receipts[0]]
        expected_inputs = [event.get("artifact"), *raw_inputs]
        if inputs != expected_inputs:
            raise CampaignError(
                "event verifier must consume the exact artifact and all frozen raw inputs"
            )
        expected_argv = [
            "/usr/bin/python3",
            "-B",
            verifier_text,
            "--verify-event",
            str(event.get("artifact", {}).get("path")),
            "--normalized-result-stdout",
        ]
        for item in raw_inputs:
            expected_argv.extend(["--input", str(item.get("path"))])
        if argv != expected_argv:
            raise CampaignError("event verifier invocation differs from its closed contract")

    replay_argv = argv
    expected_replay_envelope: dict[str, Any] | None = None
    if not lean_engine:
        replay_argv, expected_replay_envelope = validate_verifier_guard_chain(
            receipt,
            event=event,
            normalized=normalized,
            brief=brief,
            task=task,
        )

    timeout_seconds = min(1800, int(task["budget"]["wall_minutes"]) * 60)
    try:
        replay = run_event_verifier(replay_argv, timeout_seconds=timeout_seconds)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise CampaignError(f"trusted event verifier did not complete: {exc}") from exc
    if replay.returncode != 0:
        tail = (replay.stderr or replay.stdout or "")[-1000:]
        raise CampaignError(f"trusted event verifier rejected the event: {tail}")
    if not lean_engine:
        try:
            replayed = json.loads(replay.stdout)
        except (TypeError, json.JSONDecodeError) as exc:
            raise CampaignError("trusted event verifier returned no normalized JSON") from exc
        if (
            not isinstance(replayed, dict)
            or expected_replay_envelope is None
            or canonical_bytes(replayed) != canonical_bytes(expected_replay_envelope)
        ):
            raise CampaignError("guarded event verifier envelope differs on exact replay")


def validate_development_receipt(
    value: Any,
    *,
    brief_path: Path | None = None,
    task_packet: dict[str, Any] | None = None,
    authenticate: bool = True,
) -> dict[str, Any]:
    receipt = exact_keys(
        value,
        {
            "schema_version", "brief_id", "brief_sha256", "terminal",
            "execution_envelope", "assigned_gate_outcome", "evidence_events", "resource_use",
            "claim_candidate", "serendipity", "route_action", "admission_status",
        },
        "development receipt",
    )
    if receipt["schema_version"] != 3:
        raise CampaignError("development receipt schema_version must be 3")
    brief_id = nonempty_string(receipt["brief_id"], "development receipt brief_id")
    brief_sha = receipt["brief_sha256"]
    if not isinstance(brief_sha, str) or not HEX64.fullmatch(brief_sha):
        raise CampaignError("development receipt brief_sha256 is invalid")
    brief: dict[str, Any] | None = None
    task: dict[str, Any] | None = None
    if brief_path is not None and authenticate:
        if task_packet is None:
            raise CampaignError(
                "authenticated development receipt requires its task packet"
            )
        if digest(brief_path) != brief_sha:
            raise CampaignError("development receipt brief hash mismatch")
        brief = validate_brief(
            load_json(brief_path, "development brief"),
            brief_path=brief_path,
            task_packet=task_packet,
            authenticate=True,
        )
        task = task_packet
        if brief.get("brief_id") != brief_id:
            raise CampaignError("development receipt brief_id mismatch")
    if receipt["terminal"] not in PRIMARY_TERMINALS:
        raise CampaignError("development receipt terminal is invalid")
    if task is not None and brief is not None and brief_path is not None:
        validate_execution_envelope(
            receipt.get("execution_envelope"),
            brief_path=brief_path,
            brief=brief,
            task=task,
            receipt=receipt,
            authenticate=True,
        )
    else:
        validate_file_receipt(
            receipt.get("execution_envelope"),
            "development execution envelope",
            authenticate=False,
        )
    nonempty_string(receipt["assigned_gate_outcome"], "assigned_gate_outcome", 1600)
    events = receipt["evidence_events"]
    if not isinstance(events, list):
        raise CampaignError("evidence_events must be an array")
    if receipt["terminal"] != "OPERATIONAL_STOP" and not events:
        raise CampaignError("mathematical terminals require at least one evidence event")
    kinds: list[str] = []
    event_ids: list[str] = []
    event_artifact_paths: list[Path] = []
    for index, event in enumerate(events):
        label = f"evidence_events[{index}]"
        entry = exact_keys(
            event,
            {
                "event_id",
                "kind",
                "claim_level",
                "gate_branch",
                "binding",
                "artifact",
                "verification_receipt",
                "observation",
            },
            label,
        )
        kind = entry["kind"]
        if kind not in EVENT_CLAIM_LEVELS:
            raise CampaignError(f"{label}.kind is invalid")
        if task is not None and kind == "authenticated_source_interface":
            raise CampaignError(
                "standing first-test evidence cannot use an authenticated-source event"
            )
        kinds.append(kind)
        if entry["claim_level"] not in CLAIM_LEVELS:
            raise CampaignError(f"{label}.claim_level is invalid")
        if task is not None and entry["claim_level"] == "file_compiles":
            raise CampaignError("standing first-test evidence cannot claim file compilation")
        if entry["claim_level"] not in EVENT_CLAIM_LEVELS[kind]:
            raise CampaignError(
                f"{label}.claim_level is inconsistent with {kind}"
            )
        event_core = {
            key: entry[key]
            for key in entry
            if key not in {"event_id", "verification_receipt"}
        }
        if entry.get("event_id") != canonical_sha256(event_core):
            raise CampaignError(f"{label}.event_id differs from its event")
        event_ids.append(entry["event_id"])
        if entry.get("gate_branch") not in {"live", "kill", "no_signal", "sidecar"}:
            raise CampaignError(f"{label}.gate_branch is invalid")
        binding = exact_keys(
            entry.get("binding"),
            {
                "primary_contract_id",
                "subject",
                "subject_contract_id",
                "model_contract_id",
                "scope_contract_id",
                "polarity",
                "damage_scope_reached",
            },
            f"{label}.binding",
        )
        if binding.get("subject") not in {"primary_claim", "shared_premise"}:
            raise CampaignError(f"{label}.binding.subject is invalid")
        if binding.get("polarity") not in {"supports", "refutes", "observes"}:
            raise CampaignError(f"{label}.binding.polarity is invalid")
        if binding.get("damage_scope_reached") not in {
            "candidate-local",
            "subfamily",
        }:
            raise CampaignError(f"{label}.binding damage scope is invalid")
        artifact_text, _artifact_sha, artifact_path = validate_file_receipt(
            entry["artifact"], f"{label}.artifact", authenticate=authenticate
        )
        event_artifact_paths.append(artifact_path)
        if task is not None:
            write_paths = (task.get("ownership") or {}).get("write_paths") or []
            if artifact_text not in write_paths:
                raise CampaignError(
                    f"{label}.artifact is not an exact task-owned output"
                )
        nonempty_string(entry["observation"], f"{label}.observation", 2000)
        if brief is not None:
            contract = brief["evidence_contract"]
            scope = contract["scope"]
            subfamily = scope.get("subfamily")
            expected_subject = contract["contract_id"]
            if binding.get("subject") == "shared_premise":
                if not isinstance(subfamily, dict):
                    raise CampaignError(f"{label} names an absent shared premise")
                expected_subject = subfamily["shared_premise_contract_id"]
            if (
                binding.get("primary_contract_id") != contract["contract_id"]
                or binding.get("subject_contract_id") != expected_subject
                or binding.get("model_contract_id") != contract["model_contract_id"]
                or binding.get("scope_contract_id") != scope["scope_contract_id"]
            ):
                raise CampaignError(f"{label} is not bound to the development claim")
            if binding.get("damage_scope_reached") == "subfamily" and not (
                scope.get("ceiling") == "subfamily"
                and binding.get("subject") == "shared_premise"
                and binding.get("polarity") == "refutes"
                and entry.get("gate_branch") == "kill"
                and kind in {"exact_falsifier", "claim_refuted"}
            ):
                raise CampaignError(f"{label} does not authenticate subfamily coverage")
            validate_event_verification(
                entry.get("verification_receipt"),
                event=entry,
                claim_contract_id=expected_subject,
                brief=brief,
                task=task,
                authenticate=authenticate,
            )
        elif entry["claim_level"] == "proposal":
            if entry.get("verification_receipt") is not None:
                raise CampaignError("proposal template event must have null verification")
        elif entry.get("verification_receipt") is None:
            raise CampaignError("checked evidence event must name verification")
    if len(set(event_ids)) != len(event_ids):
        raise CampaignError("development receipt event IDs must be unique")
    terminal = receipt["terminal"]
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
    if terminal != "OPERATIONAL_STOP" and len(primary_events) != 1:
        raise CampaignError(
            "development terminal requires exactly one semantically bound primary event"
        )
    validate_resource_use(receipt["resource_use"])
    if task is not None:
        resource = receipt["resource_use"]
        budget = task["budget"]
        required_observations = {
            "wall_minutes",
            "active_minutes",
            "cpu_seconds",
            "peak_memory_mib",
            "artifact_bytes",
            "source_requests",
        }
        if any(resource.get(key) is None for key in required_observations):
            raise CampaignError(
                "authenticated development receipt lacks enforced resource observations"
            )
        if (
            float(resource["wall_minutes"]) > float(budget["wall_minutes"])
            or float(resource["active_minutes"]) > float(budget["wall_minutes"])
            or float(resource["cpu_seconds"])
            > float(budget["wall_minutes"]) * 60 * int(budget["cpu_cores"])
            or float(resource["peak_memory_mib"])
            > float(budget["memory_gib"]) * 1024
            or int(resource["artifact_bytes"])
            > float(budget["output_gib"]) * (1024**3)
            or int(resource["source_requests"]) != 0
        ):
            raise CampaignError("development receipt exceeds its standing task envelope")
        actual_artifact_bytes = sum(
            path.stat().st_size for path in set(event_artifact_paths)
        )
        if int(resource["artifact_bytes"]) < actual_artifact_bytes:
            raise CampaignError(
                "development receipt understates authenticated artifact bytes"
            )

    claim = receipt["claim_candidate"]
    if claim is not None:
        item = exact_keys(
            claim,
            {
                "contract_id",
                "model_contract_id",
                "scope_contract_id",
                "evidence_event_ids",
                "downstream",
            },
            "claim_candidate",
        )
        claim_ids = item["evidence_event_ids"]
        if (
            not isinstance(claim_ids, list)
            or not claim_ids
            or any(event_id not in event_ids for event_id in claim_ids)
        ):
            raise CampaignError(
                "claim candidate event IDs must reference evidence events"
            )
        if len(set(claim_ids)) != len(claim_ids):
            raise CampaignError("claim candidate event IDs must be unique")
        selected = [event for event in events if event["event_id"] in claim_ids]
        if all(event["claim_level"] == "proposal" for event in selected):
            raise CampaignError(
                "claim candidate cannot be supported only by proposal evidence"
            )
        if not any(
            event.get("binding", {}).get("polarity") == "supports"
            and event.get("binding", {}).get("subject") == "primary_claim"
            and event.get("claim_level") != "proposal"
            for event in selected
        ):
            raise CampaignError(
                "claim candidate lacks supporting checked primary evidence"
            )
        if brief is not None:
            contract = brief["evidence_contract"]
            if (
                item.get("contract_id") != contract["contract_id"]
                or item.get("model_contract_id") != contract["model_contract_id"]
                or item.get("scope_contract_id")
                != contract["scope"]["scope_contract_id"]
                or any(
                    event["binding"]["primary_contract_id"]
                    != contract["contract_id"]
                    for event in selected
                )
            ):
                raise CampaignError("claim candidate is rebound from its brief contract")
        if item["downstream"] != "verification_funnel_required":
            raise CampaignError("claim candidate must require verification funnel")

    serendipity = receipt["serendipity"]
    if serendipity is not None:
        item = exact_keys(
            serendipity,
            {
                "statement_or_observation", "model_tier", "scope_ceiling",
                "relation_to_assigned_probe", "evidence_event_ids",
                "contains_claim_candidate", "downstream",
            },
            "serendipity",
        )
        for key, maximum in (
            ("statement_or_observation", 2400), ("model_tier", 1200),
            ("scope_ceiling", 1200), ("relation_to_assigned_probe", 1200),
        ):
            nonempty_string(item[key], f"serendipity.{key}", maximum)
        selected_ids = item["evidence_event_ids"]
        if not isinstance(selected_ids, list) or not selected_ids or not all(
            event_id in event_ids for event_id in selected_ids
        ):
            raise CampaignError("serendipity event IDs must reference evidence events")
        if len(set(selected_ids)) != len(selected_ids):
            raise CampaignError("serendipity event IDs must be unique")
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
    validate_schema_contract(TASK_SCHEMA, "task packet schema")
    validate_schema_contract(EVENT_VERIFICATION_SCHEMA, "event verification schema")
    validate_schema_contract(FEEDBACK_SCHEMA, "investigation feedback schema")
    validate_schema_contract(ROOT_SCREEN_SCHEMA, "root semantic-screen schema")
    validate_schema_contract(SNAPSHOT_BUILD_SCHEMA, "snapshot-build schema")
    validate_schema_contract(
        VALIDATED_LEARNING_EXPORT_SCHEMA, "validated-learning export schema"
    )
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
    if args.development_receipt is not None and (
        args.brief is None or args.task_packet is None
    ):
        parser.error("--development-receipt requires --brief and --task-packet")

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
            task_path = resolve_argument(args.task_packet)
            validate_development_receipt(
                load_json(receipt_path, "development receipt"),
                brief_path=brief_path,
                task_packet=load_json(task_path, "task packet"),
                authenticate=True,
            )
    except (CampaignError, OSError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    print("research campaign contracts OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
