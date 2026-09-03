#!/usr/bin/env python3
"""Freeze a root-origin proposal batch and its explicit semantic screen.

The builder is deliberately mechanical.  Root supplies the proposal and every
judgment rationale in one immutable JSON specification; this program binds
those bytes to the current Ticket-0119 authorization and root snapshot, then
uses the canonical campaign validators before reporting either output.
"""

from __future__ import annotations

import argparse
from datetime import datetime
import json
from pathlib import Path
from typing import Any

try:
    from scripts import check_research_campaign as campaign
    from scripts import continuous_idea_generator as generator
except ModuleNotFoundError:  # Direct ``python3 scripts/...`` execution.
    import check_research_campaign as campaign
    import continuous_idea_generator as generator


ROOT = Path(__file__).resolve().parents[1]
PROTOCOL = "research-root-proposal-spec-v1"
JUDGMENT_KEYS = (
    "semantic_duplicate_absent",
    "target_equivalence_screened",
    "model_tier_and_return_status_explicit",
    "failure_memory_respected",
    "novelty_or_source_status_reviewed",
    "family_correlation_reviewed",
    "no_padding",
)


class RootBundleError(ValueError):
    """The proposal specification or current root snapshot is not admissible."""


def exact_object(value: Any, keys: set[str], label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != keys:
        raise RootBundleError(f"{label} has an unexpected closed contract")
    return value


def validate_timestamp(value: Any) -> str:
    if not isinstance(value, str) or not value.strip():
        raise RootBundleError("screened-at must be a nonempty ISO timestamp")
    try:
        datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError as exc:
        raise RootBundleError("screened-at is not an ISO timestamp") from exc
    return value


def load_spec(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise RootBundleError(f"cannot parse proposal specification: {exc}") from exc
    spec = exact_object(
        value,
        {
            "schema_version",
            "protocol",
            "campaign_id",
            "generation_mode",
            "requested_seed_count",
            "seeds",
            "reviews",
        },
        "root proposal specification",
    )
    if spec["schema_version"] != 1 or spec["protocol"] != PROTOCOL:
        raise RootBundleError("root proposal specification version differs")
    campaign_id = generator.safe_leaf_id(spec["campaign_id"], "root campaign_id")
    if "-root-seeds-" not in campaign_id:
        raise RootBundleError("root campaign identity lacks -root-seeds-")
    if spec["generation_mode"] not in {
        "context_rich",
        "representation_escape",
        "failure_dual",
        "recombination",
    }:
        raise RootBundleError("root proposal generation mode is invalid")
    requested = spec["requested_seed_count"]
    seeds = spec["seeds"]
    reviews = spec["reviews"]
    if (
        not isinstance(requested, int)
        or isinstance(requested, bool)
        or not 1 <= requested <= 5
        or not isinstance(seeds, list)
        or not 1 <= len(seeds) <= requested
        or not isinstance(reviews, list)
        or len(reviews) != len(seeds)
    ):
        raise RootBundleError("root proposal seed/review cardinality is invalid")
    seed_ids = [seed.get("seed_id") for seed in seeds if isinstance(seed, dict)]
    if len(seed_ids) != len(seeds) or len(set(seed_ids)) != len(seeds):
        raise RootBundleError("root proposal seed identities are missing or duplicated")
    review_ids: list[Any] = []
    for index, review_value in enumerate(reviews):
        review = exact_object(
            review_value,
            {"seed_id", "rationale", "judgments"},
            f"root review {index}",
        )
        if not isinstance(review["rationale"], str) or not review["rationale"].strip():
            raise RootBundleError(f"root review {index} lacks a rationale")
        judgments = exact_object(
            review["judgments"], set(JUDGMENT_KEYS), f"root review {index} judgments"
        )
        for name in JUDGMENT_KEYS:
            judgment = exact_object(
                judgments[name], {"rationale", "record_refs"},
                f"root review {index} judgment {name}",
            )
            if not isinstance(judgment["rationale"], str) or not judgment["rationale"].strip():
                raise RootBundleError(
                    f"root review {index} judgment {name} lacks a rationale"
                )
            if not isinstance(judgment["record_refs"], list):
                raise RootBundleError(
                    f"root review {index} judgment {name} refs are not an array"
                )
            for ref_index, receipt in enumerate(judgment["record_refs"]):
                generator.authenticate_receipt(
                    receipt,
                    f"root review {index} judgment {name} ref {ref_index}",
                )
        review_ids.append(review["seed_id"])
    if review_ids != seed_ids:
        raise RootBundleError("root reviews must match seed order and identities exactly")
    return spec


def build_seed_batch(spec: dict[str, Any], snapshot: dict[str, str]) -> dict[str, Any]:
    seeds = spec["seeds"]
    requested = spec["requested_seed_count"]
    return {
        "schema_version": 1,
        "campaign_id": spec["campaign_id"],
        "generation_mode": spec["generation_mode"],
        "requested_seed_count": requested,
        "snapshot": snapshot,
        "terminal": (
            "SEED-BATCH-COMPLETE"
            if len(seeds) == requested
            else "SEED-BATCH-NOVELTY-STOP"
        ),
        "claim_level": "proposal",
        "seeds": seeds,
        "generation_metrics": {
            "private_seed_count": len(seeds),
            "literal_duplicates_removed": 0,
            "target_equivalent_removed": 0,
            "malformed_removed": 0,
            "tool_calls": 0,
            "source_requests": 0,
            "input_tokens": None,
            "output_tokens": None,
            "provider_cost_usd": None,
        },
    }


def build_semantic_screen(
    *,
    spec: dict[str, Any],
    screened_at: str,
    approval_ref: str,
    authorization: dict[str, str],
    seed_batch: dict[str, str],
    snapshot: dict[str, str],
    snapshot_build: dict[str, str],
    prior_registry: dict[str, str],
    feedback_epoch_sha256: str,
) -> dict[str, Any]:
    reviews_by_id = {review["seed_id"]: review for review in spec["reviews"]}
    reviews = []
    for seed in spec["seeds"]:
        source = reviews_by_id[seed["seed_id"]]
        judgments = {
            name: {
                "status": "pass",
                "rationale": source["judgments"][name]["rationale"],
                "record_refs": source["judgments"][name]["record_refs"],
            }
            for name in JUDGMENT_KEYS
        }
        reviews.append(
            {
                "seed_id": seed["seed_id"],
                "seed_sha256": generator.canonical_json_sha256(seed),
                "working_model_tier": seed["model"]["working_tier"],
                "machine_checks": {
                    "schema_valid": "pass",
                    "identity_bound": "pass",
                    "snapshot_bound": "pass",
                    "proposal_only": "pass",
                    "literal_duplicate_absent": "pass",
                    "first_test_within_30_minutes": "pass",
                },
                "root_judgment_checks": judgments,
                "decision": "pass",
                "rationale": source["rationale"],
            }
        )
    return {
        "schema_version": 1,
        "protocol": "research-root-semantic-screen-v1",
        "screen_id": (
            f"root-screen:{spec['campaign_id']}:"
            f"{seed_batch['sha256'][:16]}"
        ),
        "screened_at": screened_at,
        "reviewer": "root",
        "authority": "proposal_queue_screen_only",
        "campaign_id": spec["campaign_id"],
        "approval_ref": approval_ref,
        "standing_authorization": authorization,
        "seed_batch": seed_batch,
        "snapshot": snapshot,
        "snapshot_build": snapshot_build,
        "prior_idea_registry": prior_registry,
        "feedback_epoch_sha256": feedback_epoch_sha256,
        "seed_reviews": reviews,
        "overall_decision": "pass",
        "claim_level": "proposal",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--service-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--proposal", type=Path, required=True)
    parser.add_argument("--approval-ref", required=True)
    parser.add_argument("--screened-at", required=True)
    args = parser.parse_args()

    screened_at = validate_timestamp(args.screened_at)
    service_dir = generator.service_directory(args.service_dir)
    output_dir = generator.run_artifact_path(args.output_dir)
    proposal_path = generator.run_artifact_path(args.proposal)
    if proposal_path.parent != output_dir or proposal_path.name != "root-proposal.json":
        raise RootBundleError("proposal must be OUTPUT_DIR/root-proposal.json")
    if output_dir == service_dir or service_dir in output_dir.parents:
        raise RootBundleError("root proposal output must remain outside service state")
    spec = load_spec(proposal_path)
    campaign_id = spec["campaign_id"]
    snapshot_path = output_dir / "snapshot" / "packet-summary.json"
    if not snapshot_path.is_file():
        raise RootBundleError("root proposal snapshot is absent")

    with generator.locked_service_state(service_dir):
        authorization_path, authorization, _accounting = (
            generator.current_authorized_accounting(service_dir)
        )
        if authorization.get("approval_ref") != args.approval_ref:
            raise RootBundleError("approval reference differs from active authority")
        build_path, build = generator.validate_snapshot_build_receipt(
            snapshot_path,
            service_dir=service_dir,
            campaign_id=campaign_id,
            purpose="root_fallback",
            mode="current",
        )
        admission_path = generator.snapshot_admission_path(snapshot_path)
        admission = generator.validate_snapshot_admission(
            admission_path,
            snapshot_path=snapshot_path,
            service_dir=service_dir,
            campaign_id=campaign_id,
            purpose="root_fallback",
        )
        current, reasons = generator.snapshot_currency(
            admission, service_dir=service_dir, campaign_id=campaign_id
        )
        if not current:
            raise RootBundleError("root proposal snapshot is stale: " + ",".join(reasons))
        prior_path = generator.authenticate_receipt(
            build["outputs"]["prior_idea_registry_json"], "root prior registry"
        )
        batch = build_seed_batch(spec, generator.file_receipt(snapshot_path))
        campaign.validate_seed_batch(batch, authenticate=True)
        seed_path = output_dir / "seed-batch.json"
        generator.write_once(seed_path, batch)
        seed_receipt = generator.file_receipt(seed_path)
        screen = build_semantic_screen(
            spec=spec,
            screened_at=screened_at,
            approval_ref=args.approval_ref,
            authorization=generator.file_receipt(authorization_path),
            seed_batch=seed_receipt,
            snapshot=generator.file_receipt(snapshot_path),
            snapshot_build=generator.file_receipt(build_path),
            prior_registry=generator.file_receipt(prior_path),
            feedback_epoch_sha256=build["input_state"]["learning_epoch_sha256"],
        )
        screen_path = output_dir / "semantic-screen.json"
        generator.write_once(screen_path, screen)
        generator.validate_root_semantic_screen(
            screen_path,
            source_seed_path=seed_path,
            batch=batch,
            service_dir=service_dir,
            authorization_path=authorization_path,
            snapshot_path=snapshot_path,
            snapshot_build_path=build_path,
            prior_registry_path=prior_path,
            feedback_epoch_sha256=build["input_state"]["learning_epoch_sha256"],
            approval_ref=args.approval_ref,
        )

    print(
        json.dumps(
            {
                "campaign_id": campaign_id,
                "proposal": generator.file_receipt(proposal_path),
                "seed_batch": generator.file_receipt(seed_path),
                "semantic_screen": generator.file_receipt(screen_path),
                "snapshot": generator.file_receipt(snapshot_path),
                "authority": "proposal queue screen only",
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
