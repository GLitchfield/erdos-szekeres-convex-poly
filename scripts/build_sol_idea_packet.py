#!/usr/bin/env python3
"""Build a deterministic whole-project evidence packet for Sol ideation.

The packet is deliberately an index plus a bounded inline corpus.  Every
selected file is hash-committed in the manifest, while large Lean and machine
artifacts remain available to a repository-local agent through their paths.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive)\s+([^\s:{(]+)"
)
RUN_NAMES = {
    "result.json",
    "summary.md",
    "static-audit.md",
    "root-admission.md",
    "REPORT.md",
}
CORE_PATHS = {
    "README.md",
    "docs/formalization_plan.md",
    "docs/research_log.md",
    "docs/literature_review.md",
    "docs/bibliography.md",
    "docs/wayfinder/map.md",
    "docs/wayfinder/frontier-portfolio.md",
}
LARGE_INDEXED_PATHS = {
    "runs/agents/20260818-research-factory-v1/substrate/interface-graph.json",
    "runs/agents/20260818-open-world-research-ecology-v01/atlas/"
    "machinery-atlas.json",
    "runs/agents/20260818-open-world-research-ecology-v01/atlas/"
    "representation-graph.json",
}
IDEA_SOURCE_PATHS = {
    "runs/agents/20260818-research-factory-v1/generation/proof_graph/"
    "validated.json",
    "runs/agents/20260818-research-factory-v1/generation/"
    "representation_geometry/validated.json",
    "runs/agents/20260818-research-factory-v1/generation/"
    "transferred_machinery/validated.json",
    "runs/agents/20260818-evolutionary-lead-lab-v01/generation-v2/"
    "generation0.json",
    "runs/agents/20260818-evolutionary-lead-lab-v01/probes/near-route/"
    "batch-g0.json",
    "runs/agents/20260818-evolutionary-lead-lab-v01/probes/exploratory/"
    "batch-g0.json",
    "runs/agents/20260818-open-world-research-ecology-v01/atlas/"
    "machinery-atlas.json",
}
SNAPSHOT_BUILD_PROTOCOL = "sol-idea-snapshot-build-v1"
SNAPSHOT_BUILD_RECEIPT_NAME = "snapshot-build-receipt.json"
VALIDATED_LEARNING_EXPORT_PROTOCOL = (
    "continuous-idea-generator-validated-learning-export-v1"
)


def digest_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def selected_paths(
    output_dir: Path,
    continuous_service_dir: Path | None = None,
    *,
    excluded_campaign_id: str | None = None,
    validated_learning_export: Path | None = None,
) -> list[Path]:
    paths: set[Path] = set()
    for path in (ROOT / "docs").rglob("*.md"):
        if path.is_file():
            paths.add(path)
    for name in ("README.md", "AGENTS.md", "lakefile.toml", "lean-toolchain"):
        path = ROOT / name
        if path.is_file():
            paths.add(path)
    for path in (ROOT / "ErdosSzekeres").rglob("*.lean"):
        if path.is_file():
            paths.add(path)
    for base in (
        ROOT / "runs" / "agents",
        ROOT / "runs" / "experiments",
        ROOT / "runs" / "reviews",
    ):
        if not base.exists():
            continue
        for path in base.rglob("*"):
            if path.is_file() and path.name in RUN_NAMES:
                if output_dir not in path.parents:
                    paths.add(path)
    for name in LARGE_INDEXED_PATHS | IDEA_SOURCE_PATHS:
        path = ROOT / name
        if path.is_file():
            paths.add(path)
    agent_runs = ROOT / "runs" / "agents"
    if agent_runs.exists():
        for path in agent_runs.glob("*-sol-idea-loop/batch-*/ideas.md"):
            if path.is_file() and output_dir not in path.parents:
                paths.add(path)
        if validated_learning_export is not None:
            export_path = validated_learning_export.resolve()
            export = load_validated_learning_export(export_path)
            paths.add(export_path)
            for index, receipt in enumerate(export["input_receipts"]):
                paths.add(
                    authenticate_file_receipt(
                        receipt, f"validated learning input {index}"
                    )
                )
        else:
            service_dir = (
                continuous_service_dir.resolve()
                if continuous_service_dir is not None
                else (agent_runs / "continuous-idea-generator").resolve()
            )
            try:
                service_dir.relative_to(agent_runs.resolve())
            except ValueError as exc:
                raise ValueError(
                    "continuous idea-generator service must be under runs/agents"
                ) from exc
            for path in service_dir.glob("batches/*/seed-batch.json"):
                if (
                    path.is_file()
                    and output_dir not in path.parents
                    and path.parent.name != excluded_campaign_id
                ):
                    paths.add(path)
            for pattern in (
                "claims/*/*.json",
                "feedback/*/*.json",
            ):
                for path in service_dir.glob(pattern):
                    if path.is_file() and output_dir not in path.parents:
                        paths.add(path)
    ledger = ROOT / "runs" / "idea-factory" / "idea-ledger.md"
    if ledger.is_file() and output_dir not in ledger.parents:
        paths.add(ledger)
    return sorted(paths, key=relative)


def load_json(name: str) -> object:
    return json.loads((ROOT / name).read_text(encoding="utf-8"))


def authenticate_file_receipt(value: object, label: str) -> Path:
    if not isinstance(value, dict) or set(value) != {"path", "sha256"}:
        raise ValueError(f"{label} is not a closed file receipt")
    path_value = value.get("path")
    hash_value = value.get("sha256")
    if not isinstance(path_value, str) or not isinstance(hash_value, str):
        raise ValueError(f"{label} has invalid path/hash fields")
    path = (ROOT / path_value).resolve()
    try:
        path.relative_to(ROOT.resolve())
    except ValueError as exc:
        raise ValueError(f"{label} escapes the repository") from exc
    if not path.is_file() or digest_bytes(path.read_bytes()) != hash_value:
        raise ValueError(f"{label} does not authenticate current bytes")
    return path


def load_validated_learning_export(
    path: Path, *, authenticate_inputs: bool = True
) -> dict[str, object]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read validated learning export: {exc}") from exc
    expected = {
        "schema_version",
        "protocol",
        "service_dir",
        "excluded_campaign_id",
        "standing_authorization",
        "accounting_checkpoint",
        "validator_components",
        "continuous_entries",
        "learning_receipts",
        "input_receipts",
        "learning_epoch_sha256",
        "current_input_fingerprint_sha256",
        "export_core_sha256",
    }
    if not isinstance(value, dict) or set(value) != expected:
        raise ValueError("validated learning export has an unexpected closed contract")
    if (
        value.get("schema_version") != 1
        or value.get("protocol") != VALIDATED_LEARNING_EXPORT_PROTOCOL
        or not isinstance(value.get("continuous_entries"), list)
        or not isinstance(value.get("learning_receipts"), list)
        or not isinstance(value.get("input_receipts"), list)
    ):
        raise ValueError("validated learning export identity or arrays are invalid")
    validator_components = value.get("validator_components")
    expected_validator_components = {
        "generator",
        "campaign",
        "first_test_guard",
        "seed_schema",
        "brief_schema",
        "task_schema",
        "development_receipt_schema",
        "event_verification_schema",
        "first_test_execution_envelope_schema",
        "feedback_schema",
    }
    if (
        not isinstance(validator_components, dict)
        or set(validator_components) != expected_validator_components
    ):
        raise ValueError("validated learning validator components are malformed")
    for name in sorted(expected_validator_components):
        receipt = validator_components[name]
        if authenticate_inputs:
            authenticate_file_receipt(
                receipt, f"validated learning validator component {name}"
            )
        elif (
            not isinstance(receipt, dict)
            or set(receipt) != {"path", "sha256"}
            or not isinstance(receipt.get("path"), str)
            or not isinstance(receipt.get("sha256"), str)
            or re.fullmatch(r"[0-9a-f]{64}", str(receipt.get("sha256"))) is None
            or Path(str(receipt.get("path"))).is_absolute()
            or ".." in Path(str(receipt.get("path"))).parts
        ):
            raise ValueError(
                f"validated learning validator component {name} is malformed"
            )
    core = {key: item for key, item in value.items() if key != "export_core_sha256"}
    if value.get("export_core_sha256") != digest_bytes(
        json.dumps(
            core,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ):
        raise ValueError("validated learning export core digest differs")
    learning = value["learning_receipts"]
    if value.get("learning_epoch_sha256") != digest_bytes(
        json.dumps(
            learning,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ):
        raise ValueError("validated learning export epoch differs")
    inputs = value["input_receipts"]
    if value.get("current_input_fingerprint_sha256") != digest_bytes(
        json.dumps(
            inputs,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ):
        raise ValueError("validated learning export input fingerprint differs")
    for index, receipt in enumerate(inputs):
        if authenticate_inputs:
            authenticate_file_receipt(receipt, f"validated learning input {index}")
        elif (
            not isinstance(receipt, dict)
            or set(receipt) != {"path", "sha256"}
            or not isinstance(receipt.get("path"), str)
            or not isinstance(receipt.get("sha256"), str)
            or re.fullmatch(r"[0-9a-f]{64}", str(receipt.get("sha256"))) is None
            or Path(str(receipt.get("path"))).is_absolute()
            or ".." in Path(str(receipt.get("path"))).parts
        ):
            raise ValueError(f"validated learning input {index} is malformed")
    entries = value["continuous_entries"]
    registry_ids: list[str] = []
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict) or set(entry) != {
            "campaign_id",
            "seed_id",
            "ordinal",
            "state",
            "seed_batch",
            "result",
            "claim",
            "feedback",
            "feedback_core_sha256",
            "registry",
        }:
            raise ValueError(f"validated learning entry {index} is malformed")
        registry = entry.get("registry")
        if not isinstance(registry, dict):
            raise ValueError(f"validated learning entry {index} lacks its registry")
        registry_id = registry.get("registry_id")
        if not isinstance(registry_id, str) or registry_id in registry_ids:
            raise ValueError("validated learning registry identities are invalid")
        registry_ids.append(registry_id)
    if registry_ids != sorted(registry_ids):
        raise ValueError("validated learning entries are not sorted")
    return value


def prior_idea_registry(
    continuous_service_dir: Path | None = None,
    *,
    excluded_campaign_id: str | None = None,
    validated_continuous_entries: list[dict[str, object]] | None = None,
) -> list[dict[str, object]]:
    registry: list[dict[str, object]] = []
    audit_by_id: dict[str, dict[str, object]] = {}
    audit_root = ROOT / "runs/agents/20260818-research-factory-v1/audit"
    if audit_root.exists():
        for path in sorted(audit_root.glob("*/review.json")):
            payload = json.loads(path.read_text(encoding="utf-8"))
            for review in payload.get("reviews", []):
                audit_by_id[review["id"]] = {
                    "audited_classification": review.get("audited_classification"),
                    "investigation_eligible": review.get("investigation_eligible"),
                    "verdict": review.get("verdict"),
                    "reason": review.get("smallest_exact_reason"),
                }

    factory_sources = sorted(
        name for name in IDEA_SOURCE_PATHS if name.endswith("validated.json")
    )
    for name in factory_sources:
        payload = load_json(name)
        assert isinstance(payload, dict)
        for case in payload.get("cases", []):
            case_id = case["id"]
            registry.append(
                {
                    "registry_id": f"rfv1:{case_id}",
                    "origin": "research_factory_v1",
                    "source_path": name,
                    "original_id": case_id,
                    "mechanism_family": case.get("mechanism_family"),
                    "model_tier": case.get("source_model_tier"),
                    "question": case.get("literal_statement_skeleton"),
                    "idea": case.get("invariant_or_relation"),
                    "cheapest_probe": case.get("cheapest_falsifier")
                    or case.get("bounded_test"),
                    "prior_audit": audit_by_id.get(case_id),
                    "investigation_status": "generated_not_mathematically_probed",
                }
            )

    generation_name = (
        "runs/agents/20260818-evolutionary-lead-lab-v01/generation-v2/"
        "generation0.json"
    )
    generation = load_json(generation_name)
    assert isinstance(generation, dict)
    for lead in generation.get("leads", []):
        statement = lead.get("statement", {})
        probe = lead.get("probe_recipe", {})
        registry.append(
            {
                "registry_id": f"ell:{lead['id']}",
                "origin": "evolutionary_lead_lab",
                "source_path": generation_name,
                "original_id": lead["id"],
                "mechanism_family": lead.get("mechanism_family"),
                "model_tier": statement.get("model_tier"),
                "question": statement.get("literal_question"),
                "idea": {
                    "premises": statement.get("premises"),
                    "conclusion": statement.get("conclusion"),
                    "operator_trace": lead.get("operator_trace"),
                },
                "cheapest_probe": probe.get("exact_question"),
                "investigation_status": "generated_not_mathematically_probed",
            }
        )

    for name in sorted(
        n for n in IDEA_SOURCE_PATHS if n.endswith("batch-g0.json")
    ):
        payload = load_json(name)
        assert isinstance(payload, dict)
        leads = payload.get("leads") or payload.get("batch") or payload.get("records")
        if leads is None:
            leads = []
        for lead in leads:
            registry.append(
                {
                    "registry_id": f"ell-public:{lead.get('id', lead.get('lead_id'))}",
                    "origin": "evolutionary_lead_lab_public_batch",
                    "source_path": name,
                    "original_id": lead.get("id", lead.get("lead_id")),
                    "mechanism_family": lead.get("mechanism_family"),
                    "model_tier": lead.get("model_tier"),
                    "question": lead.get("exact_question")
                    or lead.get("literal_question"),
                    "idea": lead.get("statement") or lead,
                    "cheapest_probe": lead.get("probe_recipe"),
                    "investigation_status": "selected_but_semantically_ungrounded",
                }
            )

    atlas_name = (
        "runs/agents/20260818-open-world-research-ecology-v01/atlas/"
        "machinery-atlas.json"
    )
    atlas = load_json(atlas_name)
    assert isinstance(atlas, dict)
    for dossier in atlas.get("dossiers", []):
        registry.append(
            {
                "registry_id": f"atlas:{dossier['id']}",
                "origin": "open_world_machinery_atlas",
                "source_path": atlas_name,
                "original_id": dossier["id"],
                "mechanism_family": dossier.get("area"),
                "model_tier": dossier.get("objects_and_dimensions"),
                "question": dossier.get("title"),
                "idea": dossier.get("proposed_bridge"),
                "cheapest_probe": dossier.get("cheapest_falsifier"),
                "investigation_status": "authenticated_transfer_uninvestigated",
                }
            )

    if validated_continuous_entries is not None:
        registry.extend(
            dict(entry["registry"]) for entry in validated_continuous_entries
        )
        return registry

    service_dir = (
        continuous_service_dir.resolve()
        if continuous_service_dir is not None
        else (ROOT / "runs" / "agents" / "continuous-idea-generator").resolve()
    )
    agents_root = (ROOT / "runs" / "agents").resolve()
    try:
        service_dir.relative_to(agents_root)
    except ValueError as exc:
        raise ValueError(
            "continuous idea-generator service must be under runs/agents"
        ) from exc
    continuous_root = service_dir / "batches"
    consumed_root = service_dir / "consumed"
    claims_root = service_dir / "claims"
    feedback_root = service_dir / "feedback"
    if continuous_root.exists():
        for seed_path in sorted(continuous_root.glob("*/seed-batch.json")):
            try:
                payload = json.loads(seed_path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue
            if payload.get("terminal") not in {
                "SEED-BATCH-COMPLETE",
                "SEED-BATCH-NOVELTY-STOP",
            }:
                continue
            campaign_id = payload.get("campaign_id")
            if not isinstance(campaign_id, str):
                continue
            if campaign_id == excluded_campaign_id:
                continue
            consumed = (consumed_root / f"{campaign_id}.json").is_file()
            for seed in payload.get("seeds", []):
                if not isinstance(seed, dict):
                    continue
                seed_id = seed.get("seed_id")
                model = seed.get("model") or {}
                mechanism = seed.get("mechanism") or {}
                first_test = seed.get("first_test") or {}
                claim_path = claims_root / campaign_id / f"{seed_id}.json"
                feedback_path = feedback_root / campaign_id / f"{seed_id}.json"
                admitted_feedback = None
                claim_receipt = None
                if feedback_path.is_file() and not claim_path.is_file():
                    raise ValueError(
                        f"feedback exists without claim for {campaign_id}:{seed_id}"
                    )
                if claim_path.is_file():
                    claim = json.loads(claim_path.read_text(encoding="utf-8"))
                    claim_seed = claim.get("seed") or {}
                    if (
                        claim_seed.get("campaign_id") != campaign_id
                        or claim_seed.get("seed_id") != seed_id
                        or claim_seed.get("seed_batch")
                        != {
                            "path": relative(seed_path),
                            "sha256": digest_bytes(seed_path.read_bytes()),
                        }
                    ):
                        raise ValueError(
                            f"claim seed receipt differs for {campaign_id}:{seed_id}"
                        )
                    authenticate_file_receipt(
                        claim.get("development_brief"),
                        f"development brief for {campaign_id}:{seed_id}",
                    )
                    claim_receipt = {
                        "path": relative(claim_path),
                        "sha256": digest_bytes(claim_path.read_bytes()),
                    }
                if feedback_path.is_file():
                    feedback = json.loads(feedback_path.read_text(encoding="utf-8"))
                    expected_feedback_id = f"{campaign_id}:{seed_id}"
                    if feedback.get("feedback_id") != expected_feedback_id:
                        raise ValueError(
                            f"feedback identity differs for {expected_feedback_id}"
                        )
                    feedback_seed = feedback.get("seed") or {}
                    if (
                        feedback_seed.get("campaign_id") != campaign_id
                        or feedback_seed.get("seed_id") != seed_id
                        or feedback_seed.get("seed_batch")
                        != {
                            "path": relative(seed_path),
                            "sha256": digest_bytes(seed_path.read_bytes()),
                        }
                    ):
                        raise ValueError(
                            f"feedback seed receipt differs for {expected_feedback_id}"
                        )
                    investigation = feedback.get("investigation") or {}
                    authenticate_file_receipt(
                        investigation.get("development_receipt"),
                        f"development receipt for {expected_feedback_id}",
                    )
                    root_admission = feedback.get("root_admission") or {}
                    authenticate_file_receipt(
                        root_admission.get("reconciliation"),
                        f"root reconciliation for {expected_feedback_id}",
                    )
                    admitted_feedback = {
                        "receipt": {
                            "path": relative(feedback_path),
                            "sha256": digest_bytes(feedback_path.read_bytes()),
                        },
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
                elif claim_path.is_file():
                    investigation_status = "in_flight"
                elif consumed:
                    investigation_status = (
                        "legacy_reconciled_investigation_unknown"
                    )
                else:
                    investigation_status = "queued_uninvestigated"
                registry.append(
                    {
                        "registry_id": f"continuous:{campaign_id}:{seed_id}",
                        "origin": "continuous_idea_generator",
                        "source_path": relative(seed_path),
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
                )
    return registry


def feedback_receipts_from_registry(
    ideas: list[dict[str, object]],
) -> list[dict[str, object]]:
    return sorted(
        (
            idea["admitted_feedback"]["receipt"]
            for idea in ideas
            if isinstance(idea.get("admitted_feedback"), dict)
        ),
        key=lambda receipt: str(receipt["path"]),
    )


def claim_receipts_from_registry(
    ideas: list[dict[str, object]],
) -> list[dict[str, object]]:
    return sorted(
        (
            idea["claim_receipt"]
            for idea in ideas
            if isinstance(idea.get("claim_receipt"), dict)
        ),
        key=lambda receipt: str(receipt["path"]),
    )


def learning_state_receipts(
    ideas: list[dict[str, object]],
) -> list[dict[str, object]]:
    receipts = [
        {"kind": "claim", "receipt": receipt}
        for receipt in claim_receipts_from_registry(ideas)
    ]
    receipts.extend(
        {"kind": "feedback", "receipt": receipt}
        for receipt in feedback_receipts_from_registry(ideas)
    )
    # Failure genomes and broader shared-cause reviews live in existing canonical
    # route records, not in a second tracker.  Commit those records into the same
    # learning epoch so a later canonical review cannot be invisible to either
    # the provider or root's duplicate/failure-memory screen.
    canonical_paths = [ROOT / "docs/wayfinder/frontier-portfolio.md"]
    idea_ledger = ROOT / "runs/idea-factory/idea-ledger.md"
    if idea_ledger.is_file():
        canonical_paths.append(idea_ledger)
    tickets = ROOT / "docs/wayfinder/tickets"
    if tickets.exists():
        canonical_paths.extend(sorted(path for path in tickets.glob("*.md") if path.is_file()))
    receipts.extend(
        {
            "kind": "canonical_failure_memory",
            "receipt": {
                "path": relative(path),
                "sha256": digest_bytes(path.read_bytes()),
            },
        }
        for path in canonical_paths
        if path.is_file()
    )
    return sorted(
        receipts,
        key=lambda item: (str(item["kind"]), str(item["receipt"]["path"])),
    )


def current_feedback_epoch_sha256(
    continuous_service_dir: Path | None = None,
    *,
    excluded_campaign_id: str | None = None,
    validated_learning_export: Path | None = None,
) -> str:
    if validated_learning_export is not None:
        export = load_validated_learning_export(validated_learning_export)
        return str(export["learning_epoch_sha256"])
    receipts = learning_state_receipts(
        prior_idea_registry(
            continuous_service_dir,
            excluded_campaign_id=excluded_campaign_id,
        )
    )
    return digest_bytes(
        json.dumps(receipts, sort_keys=True, separators=(",", ":")).encode("utf-8")
    )


def category(name: str) -> str:
    if name.endswith(".lean"):
        return "lean_source"
    if name.startswith("docs/wayfinder/tickets/"):
        return "wayfinder_ticket"
    if name.startswith("docs/experiments/"):
        return "experiment_note"
    if name.startswith("docs/") or name in {"README.md", "AGENTS.md"}:
        return "project_document"
    if name.startswith("runs/"):
        return "checked_or_proposed_run_artifact"
    return "build_or_environment"


def inline_priority(name: str) -> tuple[int, str]:
    if name in CORE_PATHS:
        return (0, name)
    if name.startswith("docs/wayfinder/tickets/"):
        return (1, name)
    if name.startswith("docs/experiments/"):
        return (2, name)
    if name.startswith("runs/") and Path(name).name in {"summary.md", "result.json"}:
        return (3, name)
    if name.startswith("docs/"):
        return (4, name)
    return (9, name)


def current_manifest_aggregate_sha256(
    output_dir: Path,
    continuous_service_dir: Path | None = None,
    *,
    excluded_campaign_id: str | None = None,
    validated_learning_export: Path | None = None,
) -> str:
    entries: list[dict[str, object]] = []
    for path in selected_paths(
        output_dir,
        continuous_service_dir,
        excluded_campaign_id=excluded_campaign_id,
        validated_learning_export=validated_learning_export,
    ):
        data = path.read_bytes()
        name = relative(path)
        entries.append(
            {
                "path": name,
                "sha256": digest_bytes(data),
                "bytes": len(data),
                "category": category(name),
            }
        )
    return digest_bytes(
        json.dumps(entries, sort_keys=True, separators=(",", ":")).encode("utf-8")
    )


def build_packet(
    output_dir: Path,
    max_inline_bytes: int,
    continuous_service_dir: Path | None = None,
    *,
    campaign_id: str = "unscoped-snapshot",
    purpose: str = "root_fallback",
    validated_learning_export: Path | None = None,
) -> dict[str, object]:
    if purpose not in {"provider_generation", "root_fallback"}:
        raise ValueError("snapshot purpose is unsupported")
    if not isinstance(campaign_id, str) or not campaign_id.strip():
        raise ValueError("snapshot campaign_id must be nonempty")
    if continuous_service_dir is not None and validated_learning_export is None:
        raise ValueError(
            "continuous service snapshots require a validated learning export"
        )
    export = (
        load_validated_learning_export(validated_learning_export.resolve())
        if validated_learning_export is not None
        else None
    )
    if export is not None:
        if export.get("excluded_campaign_id") != campaign_id:
            raise ValueError("validated learning export exclusion differs")
        service_path = continuous_service_dir.resolve() if continuous_service_dir else None
        if service_path is None or export.get("service_dir") != relative(service_path):
            raise ValueError("validated learning export names another service")
    build_started_at = datetime.now(timezone.utc).isoformat()
    output_dir.mkdir(parents=True, exist_ok=True)
    paths = selected_paths(
        output_dir,
        continuous_service_dir,
        excluded_campaign_id=campaign_id,
        validated_learning_export=validated_learning_export,
    )
    entries: list[dict[str, object]] = []
    data_by_name: dict[str, bytes] = {}
    for path in paths:
        name = relative(path)
        data = path.read_bytes()
        data_by_name[name] = data
        entries.append(
            {
                "path": name,
                "sha256": digest_bytes(data),
                "bytes": len(data),
                "category": category(name),
            }
        )

    manifest_payload = json.dumps(entries, sort_keys=True, separators=(",", ":"))
    aggregate = digest_bytes(manifest_payload.encode("utf-8"))

    inline_names: list[str] = []
    used = 0
    candidates = sorted(data_by_name, key=inline_priority)
    for name in candidates:
        if name.endswith(".lean") or name in LARGE_INDEXED_PATHS:
            continue
        data = data_by_name[name]
        try:
            data.decode("utf-8")
        except UnicodeDecodeError:
            continue
        if used + len(data) > max_inline_bytes:
            continue
        inline_names.append(name)
        used += len(data)

    manifest = {
        "schema_version": 1,
        "aggregate_sha256": aggregate,
        "entry_count": len(entries),
        "inline_entry_count": len(inline_names),
        "inline_bytes": used,
        "max_inline_bytes": max_inline_bytes,
        "entries": entries,
    }
    (output_dir / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    context_lines = [
        "# Whole-project Sol ideation context",
        "",
        f"Manifest aggregate SHA-256: `{aggregate}`",
        "",
        "This is a bounded inline view. The manifest commits every selected",
        "project document, ticket, experiment note, run summary/result/static",
        "audit, Lean source file, interface graph, and machinery-atlas file.",
        "A repository-local reviewer may inspect any indexed path directly.",
        "",
    ]
    for name in inline_names:
        text = data_by_name[name].decode("utf-8")
        context_lines.extend(
            [
                f"## BEGIN `{name}`",
                "",
                text.rstrip(),
                "",
                f"## END `{name}`",
                "",
            ]
        )
    (output_dir / "context.md").write_text(
        "\n".join(context_lines), encoding="utf-8"
    )

    decl_lines = [
        "# Lean declaration index",
        "",
        f"Manifest aggregate SHA-256: `{aggregate}`",
        "",
    ]
    declaration_count = 0
    for name in sorted(n for n in data_by_name if n.endswith(".lean")):
        text = data_by_name[name].decode("utf-8")
        for line_no, line in enumerate(text.splitlines(), start=1):
            match = DECL_RE.match(line)
            if match:
                declaration_count += 1
                decl_lines.append(
                    f"- `{name}:{line_no}` {match.group(1)} `{match.group(2)}`"
                )
    (output_dir / "lean-declarations.md").write_text(
        "\n".join(decl_lines) + "\n", encoding="utf-8"
    )

    ideas = prior_idea_registry(
        continuous_service_dir,
        excluded_campaign_id=campaign_id,
        validated_continuous_entries=(
            list(export["continuous_entries"]) if export is not None else []
        ),
    )
    continuous_ideas = [
        idea for idea in ideas if idea.get("origin") == "continuous_idea_generator"
    ]
    queued_seed_count = sum(
        1
        for idea in continuous_ideas
        if idea.get("investigation_status") == "queued_uninvestigated"
    )
    in_flight_seed_count = sum(
        1
        for idea in continuous_ideas
        if idea.get("investigation_status") == "in_flight"
    )
    investigated_seed_count = sum(
        1
        for idea in continuous_ideas
        if str(idea.get("investigation_status") or "").startswith("investigated_")
    )
    feedback_receipts = feedback_receipts_from_registry(ideas)
    claim_receipts = claim_receipts_from_registry(ideas)
    state_receipts = (
        list(export["learning_receipts"])
        if export is not None
        else learning_state_receipts(ideas)
    )
    learning_manifest = {
        "schema_version": 1,
        "purpose": "complete authenticated claim, feedback, and canonical failure-memory epoch",
        "entries": state_receipts,
    }
    (output_dir / "learning-state-manifest.json").write_text(
        json.dumps(learning_manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    feedback_epoch_sha256 = digest_bytes(
        json.dumps(
            state_receipts, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
    )
    ideas_payload = {
        "schema_version": 1,
        "purpose": "duplicate avoidance; entries are not endorsements",
        "idea_count": len(ideas),
        "feedback_epoch_sha256": feedback_epoch_sha256,
        "ideas": ideas,
    }
    (output_dir / "prior-idea-registry.json").write_text(
        json.dumps(ideas_payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    registry_lines = [
        "# Prior factory and atlas idea registry",
        "",
        "These entries prevent duplicate generation. They are not endorsements,",
        "and most have never reached a mathematically grounded probe.",
        "",
    ]
    for idea in ideas:
        question = str(idea.get("question") or "").replace("\n", " ")
        registry_lines.append(
            f"- `{idea['registry_id']}` [{idea.get('investigation_status')}] "
            f"{question}"
        )
        feedback = idea.get("admitted_feedback")
        if isinstance(feedback, dict):
            learned = feedback.get("learned") or {}
            failing = learned.get("failing_feature") or {}
            surviving = learned.get("surviving_structure") or {}
            if failing.get("status") == "verified":
                registry_lines.append(
                    "  VERIFIED CONSTRAINT: " + str(failing.get("text"))
                )
            if surviving.get("status") == "inferred":
                registry_lines.append(
                    "  INFERRED RESIDUE (not positive evidence): "
                    + str(surviving.get("text"))
                )
    (output_dir / "prior-idea-registry.md").write_text(
        "\n".join(registry_lines) + "\n", encoding="utf-8"
    )

    summary = {
        "manifest_aggregate_sha256": aggregate,
        "entries": len(entries),
        "inline_entries": len(inline_names),
        "inline_bytes": used,
        "lean_declarations": declaration_count,
        "prior_ideas": len(ideas),
        "queued_seeds": queued_seed_count,
        "in_flight_seeds": in_flight_seed_count,
        "investigated_seeds": investigated_seed_count,
        "claim_receipts": len(claim_receipts),
        "feedback_receipts": len(feedback_receipts),
        "feedback_epoch_sha256": feedback_epoch_sha256,
        "manifest_sha256": digest_bytes((output_dir / "manifest.json").read_bytes()),
        "context_sha256": digest_bytes((output_dir / "context.md").read_bytes()),
        "lean_index_sha256": digest_bytes(
            (output_dir / "lean-declarations.md").read_bytes()
        ),
        "prior_idea_registry_sha256": digest_bytes(
            (output_dir / "prior-idea-registry.json").read_bytes()
        ),
    }
    (output_dir / "packet-summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    service_dir = (
        continuous_service_dir.resolve()
        if continuous_service_dir is not None
        else (ROOT / "runs" / "agents" / "continuous-idea-generator").resolve()
    )
    try:
        service_dir_text = relative(service_dir)
    except ValueError as exc:
        raise ValueError(
            "continuous idea-generator service must be inside the repository"
        ) from exc
    end_epoch = current_feedback_epoch_sha256(
        service_dir,
        excluded_campaign_id=campaign_id,
        validated_learning_export=validated_learning_export,
    )
    if end_epoch != feedback_epoch_sha256:
        raise ValueError(
            "claim, feedback, or canonical failure-memory state changed during snapshot build"
        )
    output_receipts = {
        name.replace("-", "_").replace(".", "_"): {
            "path": relative(output_dir / name),
            "sha256": digest_bytes((output_dir / name).read_bytes()),
        }
        for name in (
            "manifest.json",
            "context.md",
            "lean-declarations.md",
            "prior-idea-registry.json",
            "prior-idea-registry.md",
            "learning-state-manifest.json",
            "packet-summary.json",
        )
    }
    output_aggregate = digest_bytes(
        json.dumps(output_receipts, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    )
    receipt = {
        "schema_version": 1,
        "protocol": SNAPSHOT_BUILD_PROTOCOL,
        "campaign_id": campaign_id,
        "purpose": purpose,
        "started_at": build_started_at,
        "finished_at": datetime.now(timezone.utc).isoformat(),
        "terminal": "SNAPSHOT-BUILD-COMPLETE",
        "builder_component": {
            "path": relative(Path(__file__).resolve()),
            "sha256": digest_bytes(Path(__file__).resolve().read_bytes()),
        },
        "invocation": {
            "service_dir": service_dir_text,
            "output_dir": relative(output_dir),
            "max_inline_bytes": max_inline_bytes,
            "excluded_campaign_id": campaign_id,
        },
        "input_state": {
            "validated_learning_export": (
                {
                    "path": relative(validated_learning_export.resolve()),
                    "sha256": digest_bytes(
                        validated_learning_export.resolve().read_bytes()
                    ),
                }
                if validated_learning_export is not None
                else None
            ),
            "validated_learning_export_core_sha256": (
                export["export_core_sha256"] if export is not None else None
            ),
            "current_input_fingerprint_sha256": (
                export["current_input_fingerprint_sha256"]
                if export is not None
                else None
            ),
            "learning_state_manifest": output_receipts[
                "learning_state_manifest_json"
            ],
            "learning_epoch_sha256": feedback_epoch_sha256,
            "workspace_manifest_aggregate_sha256": aggregate,
        },
        "outputs": output_receipts,
        "output_aggregate_sha256": output_aggregate,
        "meaning": (
            "closed attestation that the current builder produced this exact "
            "snapshot for the selected continuous-generator service"
        ),
    }
    (output_dir / SNAPSHOT_BUILD_RECEIPT_NAME).write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--max-inline-bytes", type=int, default=6 * 1024 * 1024)
    parser.add_argument("--service-dir", type=Path)
    parser.add_argument("--campaign-id", default="unscoped-snapshot")
    parser.add_argument(
        "--purpose",
        choices=("provider_generation", "root_fallback"),
        default="root_fallback",
    )
    parser.add_argument("--validated-learning-export", type=Path)
    args = parser.parse_args()
    output_dir = args.output_dir
    if not output_dir.is_absolute():
        output_dir = ROOT / output_dir
    service_dir = args.service_dir
    if service_dir is not None and not service_dir.is_absolute():
        service_dir = ROOT / service_dir
    summary = build_packet(
        output_dir.resolve(),
        args.max_inline_bytes,
        service_dir.resolve() if service_dir is not None else None,
        campaign_id=args.campaign_id,
        purpose=args.purpose,
        validated_learning_export=(
            (ROOT / args.validated_learning_export).resolve()
            if args.validated_learning_export is not None
            and not args.validated_learning_export.is_absolute()
            else args.validated_learning_export.resolve()
            if args.validated_learning_export is not None
            else None
        ),
    )
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
