#!/usr/bin/env python3
"""Validate the repository's dependency-free multi-agent protocol."""

from __future__ import annotations

import argparse
import fnmatch
import json
from pathlib import Path
import sys
import tomllib
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "docs/agents/manifest.toml"
TASK_SCHEMA_PATH = ROOT / "docs/agents/schemas/task-packet.schema.json"
RESULT_SCHEMA_PATH = ROOT / "docs/agents/schemas/result.schema.json"
TASK_TEMPLATE_PATH = ROOT / "templates/agent-task-packet.json"
RESULT_TEMPLATE_PATH = ROOT / "templates/agent-result.json"

PROFILE_SECTIONS = (
    "## Mission",
    "## Temperament",
    "## Operating principles",
    "## Invoke when",
    "## Default boundaries",
    "## Required output",
    "## Failure modes",
)
PROFILE_KINDS = {"orchestrator", "specialist", "builder", "reviewer"}
DEFAULT_MODES = {"orchestrator", "read_only", "owned_files"}
CHECK_OUTCOMES = {"passed", "failed", "not_run"}


def load_json(path: Path, errors: list[str]) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        errors.append(f"cannot parse {path.relative_to(ROOT)}: {exc}")
        return {}


def require_keys(
    value: Any, required: list[str], label: str, errors: list[str]
) -> None:
    if not isinstance(value, dict):
        errors.append(f"{label} must be a JSON object")
        return
    missing = sorted(set(required) - value.keys())
    if missing:
        errors.append(f"{label} is missing keys: {', '.join(missing)}")


def as_string_list(value: Any, label: str, errors: list[str]) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        errors.append(f"{label} must be an array of strings")
        return []
    return value


def validate_manifest(errors: list[str]) -> dict[str, Any]:
    try:
        manifest = tomllib.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as exc:
        errors.append(f"cannot parse docs/agents/manifest.toml: {exc}")
        return {}

    if manifest.get("schema_version") != 1:
        errors.append("manifest schema_version must be 1")
    policy = manifest.get("policy")
    if not isinstance(policy, dict):
        errors.append("manifest must contain a [policy] table")
        policy = {}
    for key in (
        "max_parallel_workers",
        "max_parallel_specialists",
        "max_parallel_builders",
        "max_delegation_depth",
        "default_wall_minutes",
        "default_cpu_cores",
        "default_memory_gib",
        "default_output_gib",
    ):
        if not isinstance(policy.get(key), int) or policy.get(key, 0) < 1:
            errors.append(f"policy.{key} must be a positive integer")

    profiles = manifest.get("profiles")
    if not isinstance(profiles, list) or not profiles:
        errors.append("manifest must register at least one profile")
        return manifest

    ids: list[str] = []
    orchestrators: list[str] = []
    for index, profile in enumerate(profiles):
        label = f"profiles[{index}]"
        if not isinstance(profile, dict):
            errors.append(f"{label} must be a table")
            continue
        require_keys(
            profile, ["id", "display_name", "kind", "path", "default_mode"], label, errors
        )
        profile_id = profile.get("id")
        if not isinstance(profile_id, str) or not profile_id:
            errors.append(f"{label}.id must be a nonempty string")
            continue
        ids.append(profile_id)
        if profile.get("kind") not in PROFILE_KINDS:
            errors.append(f"{label}.kind is not recognized")
        if profile.get("default_mode") not in DEFAULT_MODES:
            errors.append(f"{label}.default_mode is not recognized")
        if profile.get("kind") == "orchestrator":
            orchestrators.append(profile_id)
        relpath = profile.get("path")
        if not isinstance(relpath, str) or not relpath.startswith("docs/agents/profiles/"):
            errors.append(f"{label}.path must be under docs/agents/profiles/")
            continue
        path = ROOT / relpath
        try:
            body = path.read_text(encoding="utf-8")
        except OSError as exc:
            errors.append(f"cannot read profile {relpath}: {exc}")
            continue
        if f"Profile ID: `{profile_id}`" not in body:
            errors.append(f"{relpath} does not declare Profile ID `{profile_id}`")
        for section in PROFILE_SECTIONS:
            if section not in body:
                errors.append(f"{relpath} is missing section {section}")

    duplicates = sorted({item for item in ids if ids.count(item) > 1})
    if duplicates:
        errors.append(f"duplicate profile IDs: {', '.join(duplicates)}")
    if orchestrators != [manifest.get("orchestrator")]:
        errors.append("manifest must name its single registered orchestrator")
    return manifest


def validate_schema(path: Path, expected_required: set[str], errors: list[str]) -> dict[str, Any]:
    schema = load_json(path, errors)
    label = str(path.relative_to(ROOT))
    if schema.get("$schema") != "https://json-schema.org/draft/2020-12/schema":
        errors.append(f"{label} must use JSON Schema draft 2020-12")
    if schema.get("type") != "object" or schema.get("additionalProperties") is not False:
        errors.append(f"{label} must describe a closed object")
    required = schema.get("required")
    if not isinstance(required, list) or set(required) != expected_required:
        errors.append(f"{label} has an unexpected required-field contract")
    return schema


def validate_task(packet: Any, manifest: dict[str, Any], label: str, errors: list[str]) -> None:
    schema = load_json(TASK_SCHEMA_PATH, errors)
    required = schema.get("required", [])
    require_keys(packet, required, label, errors)
    if not isinstance(packet, dict):
        return
    if packet.get("schema_version") != 1:
        errors.append(f"{label}.schema_version must be 1")

    profiles = {p.get("id"): p for p in manifest.get("profiles", []) if isinstance(p, dict)}
    profile = profiles.get(packet.get("profile"))
    if profile is None:
        errors.append(f"{label}.profile is not registered")

    ownership = packet.get("ownership")
    require_keys(ownership, ["read_paths", "write_paths"], f"{label}.ownership", errors)
    if isinstance(ownership, dict):
        reads = as_string_list(ownership.get("read_paths"), f"{label}.ownership.read_paths", errors)
        writes = as_string_list(ownership.get("write_paths"), f"{label}.ownership.write_paths", errors)
        overlap = sorted(set(reads) & set(writes))
        if overlap:
            errors.append(f"{label} has overlapping read/write paths: {', '.join(overlap)}")
        if profile and profile.get("default_mode") == "read_only" and writes:
            errors.append(f"{label} gives write paths to a read-only profile")
        if profile and profile.get("kind") != "orchestrator":
            protected = manifest.get("policy", {}).get("orchestrator_owned", [])
            for write_path in writes:
                if any(fnmatch.fnmatch(write_path, pattern) for pattern in protected):
                    errors.append(f"{label} assigns orchestrator-owned path {write_path}")

    claims = as_string_list(packet.get("claims_allowed"), f"{label}.claims_allowed", errors)
    allowed_claims = set(manifest.get("policy", {}).get("claim_levels", []))
    unknown_claims = sorted(set(claims) - allowed_claims)
    if unknown_claims:
        errors.append(f"{label} has unknown claim levels: {', '.join(unknown_claims)}")

    budget = packet.get("budget")
    require_keys(
        budget, ["wall_minutes", "cpu_cores", "memory_gib", "output_gib"], f"{label}.budget", errors
    )
    if isinstance(budget, dict):
        for key in ("wall_minutes", "cpu_cores", "memory_gib"):
            if not isinstance(budget.get(key), int) or budget.get(key, 0) < 1:
                errors.append(f"{label}.budget.{key} must be a positive integer")
        output = budget.get("output_gib")
        if not isinstance(output, (int, float)) or isinstance(output, bool) or output <= 0:
            errors.append(f"{label}.budget.output_gib must be positive")

    contract = packet.get("theorem_contract")
    if contract is not None:
        require_keys(contract, ["name", "statement", "statement_may_change"], f"{label}.theorem_contract", errors)
        if isinstance(contract, dict) and contract.get("statement_may_change") is not False:
            errors.append(f"{label}.theorem_contract.statement_may_change must be false")

    inputs = packet.get("inputs")
    if not isinstance(inputs, list):
        errors.append(f"{label}.inputs must be an array")
    else:
        for index, item in enumerate(inputs):
            item_label = f"{label}.inputs[{index}]"
            require_keys(item, ["path", "sha256"], item_label, errors)
            if isinstance(item, dict):
                digest = item.get("sha256")
                if not isinstance(digest, str) or len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest):
                    errors.append(f"{item_label}.sha256 must be 64 lowercase hexadecimal characters")
                if isinstance(ownership, dict) and isinstance(item.get("path"), str):
                    declared = reads + writes
                    if not any(fnmatch.fnmatch(item["path"], pattern) for pattern in declared):
                        errors.append(f"{item_label}.path is outside declared ownership")

    for key in ("required_checks", "success", "stop", "deliverables"):
        values = as_string_list(packet.get(key), f"{label}.{key}", errors)
        if not values:
            errors.append(f"{label}.{key} must not be empty")


def validate_result(result: Any, manifest: dict[str, Any], label: str, errors: list[str]) -> None:
    schema = load_json(RESULT_SCHEMA_PATH, errors)
    required = schema.get("required", [])
    require_keys(result, required, label, errors)
    if not isinstance(result, dict):
        return
    if result.get("schema_version") != 1:
        errors.append(f"{label}.schema_version must be 1")
    statuses = set(manifest.get("policy", {}).get("result_statuses", []))
    if result.get("status") not in statuses:
        errors.append(f"{label}.status is not registered")
    claims = set(manifest.get("policy", {}).get("claim_levels", []))
    if result.get("claim_level") not in claims:
        errors.append(f"{label}.claim_level is not registered")
    for key in ("supports", "does_not_support", "changes", "evidence", "limitations"):
        values = as_string_list(result.get(key), f"{label}.{key}", errors)
        if key in {"supports", "does_not_support"} and not values:
            errors.append(f"{label}.{key} must not be empty")
    checks = result.get("checks")
    if not isinstance(checks, list):
        errors.append(f"{label}.checks must be an array")
    else:
        for index, check in enumerate(checks):
            check_label = f"{label}.checks[{index}]"
            require_keys(check, ["command", "outcome"], check_label, errors)
            if isinstance(check, dict) and check.get("outcome") not in CHECK_OUTCOMES:
                errors.append(f"{check_label}.outcome is not recognized")


def validate_pair(packet: Any, result: Any, label: str, errors: list[str]) -> None:
    """Check authority and evidence promotion across a task/result pair."""
    if not isinstance(packet, dict) or not isinstance(result, dict):
        return
    if packet.get("task_id") != result.get("task_id"):
        errors.append(f"{label} task IDs do not match")
    if result.get("claim_level") not in packet.get("claims_allowed", []):
        errors.append(f"{label} promotes a claim not allowed by its task packet")

    ownership = packet.get("ownership", {})
    writes = ownership.get("write_paths", []) if isinstance(ownership, dict) else []
    changes = result.get("changes", [])
    if isinstance(changes, list) and isinstance(writes, list):
        for changed in changes:
            if isinstance(changed, str) and not any(fnmatch.fnmatch(changed, pattern) for pattern in writes):
                errors.append(f"{label} reports out-of-ownership change {changed}")

    passed = {
        check.get("command")
        for check in result.get("checks", [])
        if isinstance(check, dict) and check.get("outcome") == "passed"
    }
    claim = result.get("claim_level")
    if claim == "file_compiles" and not any("lean" in command for command in passed if isinstance(command, str)):
        errors.append(f"{label} claims file_compiles without a passed Lean check")
    if claim == "project_builds" and not any("lake build" in command for command in passed if isinstance(command, str)):
        errors.append(f"{label} claims project_builds without a passed lake build")
    if claim == "repository_tests_pass" and not any("make test" in command for command in passed if isinstance(command, str)):
        errors.append(f"{label} claims repository_tests_pass without a passed make test")
    if claim == "kernel_checked_counterexample":
        if result.get("status") != "refuted":
            errors.append(f"{label} kernel_checked_counterexample must have status refuted")
        if not any("lean" in command or "lake build" in command for command in passed if isinstance(command, str)):
            errors.append(f"{label} claims a kernel-checked counterexample without a passed Lean gate")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--task-packet", type=Path, help="also validate a concrete task packet")
    parser.add_argument("--result", type=Path, help="also validate a concrete agent result")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    errors: list[str] = []
    manifest = validate_manifest(errors)

    task_required = {
        "schema_version", "run_id", "task_id", "wayfinder_ticket", "profile",
        "base_revision", "workspace_fingerprint", "objective", "theorem_contract",
        "inputs", "ownership", "budget", "required_checks", "success", "stop",
        "deliverables", "claims_allowed",
    }
    result_required = {
        "schema_version", "task_id", "status", "claim_level", "summary", "supports",
        "does_not_support", "changes", "checks", "evidence", "limitations", "blocked_by",
    }
    validate_schema(TASK_SCHEMA_PATH, task_required, errors)
    validate_schema(RESULT_SCHEMA_PATH, result_required, errors)
    task_template = load_json(TASK_TEMPLATE_PATH, errors)
    result_template = load_json(RESULT_TEMPLATE_PATH, errors)
    validate_task(task_template, manifest, "task template", errors)
    validate_result(result_template, manifest, "result template", errors)
    validate_pair(task_template, result_template, "template pair", errors)

    agents_text = (ROOT / "AGENTS.md").read_text(encoding="utf-8")
    if "docs/agents/README.md" not in agents_text:
        errors.append("AGENTS.md must point to docs/agents/README.md")

    task_packet = load_json(args.task_packet, errors) if args.task_packet else None
    agent_result = load_json(args.result, errors) if args.result else None
    if args.task_packet:
        validate_task(task_packet, manifest, str(args.task_packet), errors)
    if args.result:
        validate_result(agent_result, manifest, str(args.result), errors)
    if args.task_packet and args.result:
        validate_pair(task_packet, agent_result, "runtime task/result pair", errors)

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print(
        f"agent orchestration OK: {len(manifest.get('profiles', []))} profiles, "
        "task/result contracts valid"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
