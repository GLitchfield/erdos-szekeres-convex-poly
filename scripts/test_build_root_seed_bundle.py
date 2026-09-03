from __future__ import annotations

import copy
import json
from pathlib import Path
import tempfile
import unittest

from scripts import build_root_seed_bundle as builder


def example_seed() -> dict:
    template = json.loads(
        (builder.ROOT / "templates/research-seed-batch.json").read_text(
            encoding="utf-8"
        )
    )
    return template["seeds"][0]


def example_spec() -> dict:
    seed = example_seed()
    judgments = {
        name: {"rationale": f"Checked {name}.", "record_refs": []}
        for name in builder.JUDGMENT_KEYS
    }
    return {
        "schema_version": 1,
        "protocol": builder.PROTOCOL,
        "campaign_id": "20990101-root-seeds-test-001",
        "generation_mode": "context_rich",
        "requested_seed_count": 1,
        "seeds": [seed],
        "reviews": [
            {
                "seed_id": seed["seed_id"],
                "rationale": "The test seed is admitted to the proposal queue only.",
                "judgments": judgments,
            }
        ],
    }


class RootSeedBundleBuilderTests(unittest.TestCase):
    def test_closed_spec_and_ordered_reviews_validate(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "root-proposal.json"
            path.write_text(json.dumps(example_spec()), encoding="utf-8")
            self.assertEqual(builder.load_spec(path)["requested_seed_count"], 1)

    def test_batch_is_complete_only_when_requested_count_is_met(self) -> None:
        spec = example_spec()
        receipt = {"path": "runs/agents/test/snapshot.json", "sha256": "a" * 64}
        batch = builder.build_seed_batch(spec, receipt)
        self.assertEqual(batch["terminal"], "SEED-BATCH-COMPLETE")
        spec["requested_seed_count"] = 2
        batch = builder.build_seed_batch(spec, receipt)
        self.assertEqual(batch["terminal"], "SEED-BATCH-NOVELTY-STOP")

    def test_screen_binds_explicit_judgments_without_inventing_rationales(self) -> None:
        spec = example_spec()
        receipt = {"path": "runs/agents/test/value.json", "sha256": "b" * 64}
        screen = builder.build_semantic_screen(
            spec=spec,
            screened_at="2099-01-01T00:00:00+00:00",
            approval_ref="ticket#approval",
            authorization=receipt,
            seed_batch=receipt,
            snapshot=receipt,
            snapshot_build=receipt,
            prior_registry=receipt,
            feedback_epoch_sha256="c" * 64,
        )
        review = screen["seed_reviews"][0]
        for name in builder.JUDGMENT_KEYS:
            self.assertEqual(
                review["root_judgment_checks"][name]["rationale"],
                f"Checked {name}.",
            )
        self.assertEqual(review["decision"], "pass")

    def test_missing_judgment_is_rejected(self) -> None:
        spec = example_spec()
        del spec["reviews"][0]["judgments"][builder.JUDGMENT_KEYS[0]]
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "root-proposal.json"
            path.write_text(json.dumps(spec), encoding="utf-8")
            with self.assertRaises(builder.RootBundleError):
                builder.load_spec(path)

    def test_review_order_must_match_seed_order(self) -> None:
        spec = example_spec()
        second = copy.deepcopy(spec["seeds"][0])
        second["seed_id"] = "S02"
        spec["seeds"].append(second)
        spec["requested_seed_count"] = 2
        second_review = copy.deepcopy(spec["reviews"][0])
        second_review["seed_id"] = "S02"
        spec["reviews"].append(second_review)
        spec["reviews"].reverse()
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "root-proposal.json"
            path.write_text(json.dumps(spec), encoding="utf-8")
            with self.assertRaises(builder.RootBundleError):
                builder.load_spec(path)


if __name__ == "__main__":
    unittest.main()
