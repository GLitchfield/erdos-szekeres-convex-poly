#!/usr/bin/env python3
"""Regression tests for the evidence-first research-campaign contracts."""

from __future__ import annotations

import copy
import json
from pathlib import Path
import tempfile
import unittest

from scripts import check_research_campaign as campaign


def template(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


class ResearchCampaignContractTests(unittest.TestCase):
    def setUp(self) -> None:
        self.seed_batch = template(campaign.SEED_TEMPLATE)
        self.brief = template(campaign.BRIEF_TEMPLATE)
        self.receipt = template(campaign.RECEIPT_TEMPLATE)

    def assert_campaign_error(self, function, *args, **kwargs) -> None:
        with self.assertRaises(campaign.CampaignError):
            function(*args, **kwargs)

    def test_templates_and_historical_control_validate(self) -> None:
        campaign.validate_templates()

    def test_seed_complete_requires_five_honest_seeds(self) -> None:
        self.seed_batch["terminal"] = "SEED-BATCH-COMPLETE"
        self.assert_campaign_error(
            campaign.validate_seed_batch, self.seed_batch, authenticate=False
        )

    def test_seed_lineage_arity_is_enforced(self) -> None:
        self.seed_batch["seeds"][0]["lineage"]["kind"] = "mutation"
        self.assert_campaign_error(
            campaign.validate_seed_batch, self.seed_batch, authenticate=False
        )

    def test_seed_outcome_branches_must_discriminate(self) -> None:
        first_test = self.seed_batch["seeds"][0]["first_test"]
        first_test["information_if_no_signal"] = first_test["information_if_killed"]
        self.assert_campaign_error(
            campaign.validate_seed_batch, self.seed_batch, authenticate=False
        )

    def test_brief_rejects_more_than_five_context_artifacts(self) -> None:
        context = self.brief["selected_context"][0]
        self.brief["selected_context"] = [copy.deepcopy(context) for _ in range(6)]
        self.assert_campaign_error(
            campaign.validate_brief, self.brief, authenticate=False
        )

    def test_hostile_control_must_have_different_predictions(self) -> None:
        control = self.brief["hostile_controls"][0]
        control["expected_if_artifact"] = control["expected_if_mechanism_is_real"]
        self.assert_campaign_error(
            campaign.validate_brief, self.brief, authenticate=False
        )

    def test_lean_cannot_be_enabled_without_a_fixed_contract(self) -> None:
        self.brief["allowed_methods"].append("local_lean")
        self.assert_campaign_error(
            campaign.validate_brief, self.brief, authenticate=False
        )

    def test_persistence_instruction_cannot_be_tilted(self) -> None:
        self.brief["persistence_instruction"] += " Assume the conjecture is true."
        self.assert_campaign_error(
            campaign.validate_brief, self.brief, authenticate=False
        )

    def make_authenticated_brief(self, directory: Path) -> tuple[Path, dict, dict]:
        source_rel = "docs/agents/research-campaign.md"
        source_path = campaign.ROOT / source_rel

        batch = copy.deepcopy(self.seed_batch)
        batch["campaign_id"] = "test-campaign"
        batch["snapshot"] = {
            "path": source_rel,
            "sha256": campaign.digest(source_path),
        }
        batch_path = directory / "seed-batch.json"
        batch_path.write_text(json.dumps(batch), encoding="utf-8")
        batch_rel = str(batch_path.relative_to(campaign.ROOT))

        brief = copy.deepcopy(self.brief)
        brief["brief_id"] = "test-campaign-S01-probe"
        brief["task_id"] = "test-campaign-S01-probe"
        brief["seed"] = {
            "batch_path": batch_rel,
            "batch_sha256": campaign.digest(batch_path),
            "seed_id": "S01",
        }
        brief["selected_context"] = [
            {
                "path": source_rel,
                "sha256": campaign.digest(source_path),
                "purpose": "Authenticate the campaign boundary under test.",
            }
        ]
        brief_path = directory / "development-brief.json"
        brief_path.write_text(json.dumps(brief), encoding="utf-8")
        brief_rel = str(brief_path.relative_to(campaign.ROOT))

        task = {
            "task_id": brief["task_id"],
            "inputs": [
                {"path": batch_rel, "sha256": campaign.digest(batch_path)},
                {"path": source_rel, "sha256": campaign.digest(source_path)},
                {"path": brief_rel, "sha256": campaign.digest(brief_path)},
            ],
            "ownership": {
                "read_paths": [batch_rel, source_rel, brief_rel],
                "write_paths": [],
            },
            "claims_allowed": ["proposal", "computational_evidence"],
            "theorem_contract": None,
            "budget": {
                "wall_minutes": 30,
                "cpu_cores": 1,
                "memory_gib": 1,
                "output_gib": 0.01,
            },
        }
        return brief_path, brief, task

    def test_authenticated_brief_and_task_packet_validate(self) -> None:
        runs = campaign.ROOT / "runs"
        runs.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            brief_path, brief, task = self.make_authenticated_brief(Path(raw_directory))
            campaign.validate_brief(
                brief,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )

    def test_context_must_be_frozen_by_task_packet(self) -> None:
        runs = campaign.ROOT / "runs"
        runs.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            brief_path, brief, task = self.make_authenticated_brief(Path(raw_directory))
            context_path = brief["selected_context"][0]["path"]
            task["inputs"] = [
                entry for entry in task["inputs"] if entry["path"] != context_path
            ]
            self.assert_campaign_error(
                campaign.validate_brief,
                brief,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )

    def test_development_cannot_expand_seed_test_ceiling(self) -> None:
        runs = campaign.ROOT / "runs"
        runs.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=runs) as raw_directory:
            brief_path, brief, task = self.make_authenticated_brief(Path(raw_directory))
            brief["probe"]["ceiling_minutes"] = 21
            brief_path.write_text(json.dumps(brief), encoding="utf-8")
            brief_rel = str(brief_path.relative_to(campaign.ROOT))
            for entry in task["inputs"]:
                if entry["path"] == brief_rel:
                    entry["sha256"] = campaign.digest(brief_path)
            self.assert_campaign_error(
                campaign.validate_brief,
                brief,
                brief_path=brief_path,
                task_packet=task,
                authenticate=True,
            )

    def test_serendipity_must_reference_real_evidence(self) -> None:
        self.receipt["serendipity"] = {
            "statement_or_observation": "An unrelated pattern appeared.",
            "model_tier": "the frozen finite control",
            "scope_ceiling": "one control",
            "relation_to_assigned_probe": "Not needed for its primary terminal.",
            "evidence_event_indices": [4],
            "contains_claim_candidate": False,
            "downstream": "root_audit_required",
        }
        self.assert_campaign_error(
            campaign.validate_development_receipt,
            self.receipt,
            authenticate=False,
        )

    def test_claim_candidate_must_reference_frozen_evidence(self) -> None:
        self.receipt["claim_candidate"] = {
            "statement": "The observed finite identity holds uniformly.",
            "model_tier": "sweep-realizable planar triple colorings",
            "scope_ceiling": "all finite carriers",
            "evidence_event_indices": [2],
            "downstream": "verification_funnel_required",
        }
        self.assert_campaign_error(
            campaign.validate_development_receipt,
            self.receipt,
            authenticate=False,
        )

    def test_worker_receipt_cannot_take_route_action(self) -> None:
        self.receipt["route_action"] = "promote"
        self.assert_campaign_error(
            campaign.validate_development_receipt,
            self.receipt,
            authenticate=False,
        )


if __name__ == "__main__":
    unittest.main()
