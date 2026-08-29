#!/usr/bin/env python3
"""Build a deterministic whole-project evidence packet for Sol ideation.

The packet is deliberately an index plus a bounded inline corpus.  Every
selected file is hash-committed in the manifest, while large Lean and machine
artifacts remain available to a repository-local agent through their paths.
"""

from __future__ import annotations

import argparse
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


def digest_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def selected_paths(output_dir: Path) -> list[Path]:
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
        for path in agent_runs.glob(
            "continuous-idea-generator/batches/*/seed-batch.json"
        ):
            if path.is_file() and output_dir not in path.parents:
                paths.add(path)
    ledger = ROOT / "runs" / "idea-factory" / "idea-ledger.md"
    if ledger.is_file() and output_dir not in ledger.parents:
        paths.add(ledger)
    return sorted(paths, key=relative)


def load_json(name: str) -> object:
    return json.loads((ROOT / name).read_text(encoding="utf-8"))


def prior_idea_registry() -> list[dict[str, object]]:
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

    continuous_root = (
        ROOT / "runs" / "agents" / "continuous-idea-generator" / "batches"
    )
    consumed_root = (
        ROOT / "runs" / "agents" / "continuous-idea-generator" / "consumed"
    )
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
            consumed = (consumed_root / f"{campaign_id}.json").is_file()
            for seed in payload.get("seeds", []):
                if not isinstance(seed, dict):
                    continue
                seed_id = seed.get("seed_id")
                model = seed.get("model") or {}
                mechanism = seed.get("mechanism") or {}
                first_test = seed.get("first_test") or {}
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
                        "investigation_status": (
                            "generated_reconciled"
                            if consumed
                            else "generated_unreconciled"
                        ),
                    }
                )
    return registry


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


def build_packet(output_dir: Path, max_inline_bytes: int) -> dict[str, object]:
    output_dir.mkdir(parents=True, exist_ok=True)
    paths = selected_paths(output_dir)
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

    ideas = prior_idea_registry()
    ideas_payload = {
        "schema_version": 1,
        "purpose": "duplicate avoidance; entries are not endorsements",
        "idea_count": len(ideas),
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
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--max-inline-bytes", type=int, default=6 * 1024 * 1024)
    args = parser.parse_args()
    output_dir = args.output_dir
    if not output_dir.is_absolute():
        output_dir = ROOT / output_dir
    summary = build_packet(output_dir.resolve(), args.max_inline_bytes)
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
