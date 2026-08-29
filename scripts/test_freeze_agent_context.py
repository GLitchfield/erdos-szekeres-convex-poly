import copy
import json
from pathlib import Path
import tempfile
import unittest

import freeze_agent_context as capsule


class FreezeAgentContextTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        (self.root / "docs").mkdir()
        (self.root / "docs/map.md").write_text("map v1\n", encoding="utf-8")
        (self.root / "docs/portfolio.md").write_text(
            "portfolio v1\n", encoding="utf-8"
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def snapshot(self) -> dict:
        return capsule.build_snapshot(
            root=self.root,
            snapshot_id="wave-1",
            base_revision="abc123",
            sources=["docs/portfolio.md", "docs/map.md"],
        )

    def test_capsule_is_sorted_and_deterministic(self) -> None:
        first = self.snapshot()
        second = capsule.build_snapshot(
            root=self.root,
            snapshot_id="wave-1",
            base_revision="abc123",
            sources=["docs/map.md", "docs/portfolio.md"],
        )
        self.assertEqual(first, second)
        self.assertEqual(
            [entry["path"] for entry in first["source_entries"]],
            ["docs/map.md", "docs/portfolio.md"],
        )
        self.assertEqual(capsule.validate_snapshot(first), [])

    def test_internal_verification_survives_live_reconciliation(self) -> None:
        snapshot = self.snapshot()
        (self.root / "docs/map.md").write_text("map v2\n", encoding="utf-8")
        self.assertEqual(capsule.validate_snapshot(snapshot), [])
        self.assertEqual(
            capsule.validate_snapshot(
                snapshot, root=self.root, compare_live=True
            ),
            ["live source drift: docs/map.md"],
        )

    def test_content_and_aggregate_corruptions_reject(self) -> None:
        snapshot = self.snapshot()
        changed_content = copy.deepcopy(snapshot)
        changed_content["source_entries"][0]["content"] = "tampered\n"
        errors = capsule.validate_snapshot(changed_content)
        self.assertIn("source_entries[0].sha256 mismatch", errors)
        self.assertIn("aggregate_sha256 mismatch", errors)

        changed_aggregate = copy.deepcopy(snapshot)
        changed_aggregate["aggregate_sha256"] = "0" * 64
        self.assertEqual(
            capsule.validate_snapshot(changed_aggregate),
            ["aggregate_sha256 mismatch"],
        )

    def test_duplicate_escape_and_overwrite_reject(self) -> None:
        with self.assertRaisesRegex(capsule.SnapshotError, "duplicate source"):
            capsule.build_snapshot(
                root=self.root,
                snapshot_id="duplicate",
                base_revision="abc123",
                sources=["docs/map.md", "docs/map.md"],
            )
        with self.assertRaisesRegex(capsule.SnapshotError, "escapes"):
            capsule.build_snapshot(
                root=self.root,
                snapshot_id="escape",
                base_revision="abc123",
                sources=["../outside.md"],
            )

        output = self.root / "snapshot.json"
        capsule.write_new(output, self.snapshot())
        self.assertEqual(json.loads(output.read_text()), self.snapshot())
        with self.assertRaisesRegex(capsule.SnapshotError, "overwrite"):
            capsule.write_new(output, self.snapshot())


if __name__ == "__main__":
    unittest.main()
