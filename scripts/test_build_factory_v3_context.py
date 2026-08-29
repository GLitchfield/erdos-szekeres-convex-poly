from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

from build_factory_v3_context import (
    BATCH012_ATTRITION,
    BATCH012_SOURCE_PATHS,
    ContextError,
    REQUIRED_SUBSTRATE_ROLES,
    build_context,
    render_lean_declaration_index,
    render_ticket_source_inventory,
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


HASH1 = "1" * 64
HASH2 = "2" * 64

BULLET = f"""- **Failure-genome subject:** `B001-I01` / `family-one` / exact model;
  terminal `TERMINAL-ONE`; evidence `runs/result.json` SHA-256
  `{HASH1}`.
- **Verified failing feature:** a frozen feature fails.
- **Strongest supported statement:** only the exact card is rejected.
- **Evidence level:** `proposal`.
- **Damage scope:** `candidate-local`.
- **Representation blindness (`verified`):** it forgets order.
- **Candidate discriminator (`inferred`):** preserve order.
- **Mutation directions (`not-established`):** none established.
- **Anti-duplication warning (`verified`):** do not rename it.
- **Cheapest falsifier (`inferred`):** one exact control.
"""

TABLE = f"""| Field | Value |
| --- | --- |
| Subject | `FP-17` / `family-two` / abstract model; terminal `TERMINAL-TWO`; evidence `runs/result-two.json`, SHA-256 `{HASH2}` |
| Verified failing feature | one selector fails. |
| Strongest supported statement | only the selector subfamily is rejected. |
| Evidence level | `proposal`. |
| Damage scope | `subfamily`. |
| Representation blindness | `verified`: no ambient growth. |
| Candidate discriminator | `inferred`: detect growth. |
| Mutation directions | `not-established`: none established. |
| Anti-duplication warning | `verified`: do not rename selectors. |
| Cheapest falsifier | `inferred`: one frozen window. |
"""


class ContextFixture:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.ledger_path = root / "runs/idea-factory/idea-ledger.md"
        self.portfolio_path = root / "docs/wayfinder/frontier-portfolio.md"
        ledger = """# Ledger

```text
- **Failure-genome subject:** this is only the documented template.
```

## Actual

""" + BULLET + "\n## After\n"
        portfolio = "# Portfolio\n\n## Genome\n\n" + TABLE + "\n## Next\n"
        write(self.ledger_path, ledger)
        write(self.portfolio_path, portfolio)

        fixed_text = {
            "AGENTS.md": "# Model and proof-distance rules\n",
            "README.md": "# Destination state\n",
            "docs/wayfinder/map.md": "# Dependency map\n",
            "docs/literature_review.md": "# Literature\n",
            "docs/bibliography.md": "# Bibliography\n",
        }
        for path, text in fixed_text.items():
            write(root / path, text)
        write(root / "ErdosSzekeres.lean", "def rootDeclaration : Nat := 1\n")
        write(root / "ErdosSzekeres/Example.lean", "theorem exampleTheorem : True := by trivial\n")
        lean_index_path = "derived/lean-declarations.md"
        write(root / lean_index_path, render_lean_declaration_index(root))
        for index, baseline_source in enumerate(BATCH012_SOURCE_PATHS):
            write(root / baseline_source, f"aggregate-only source {index}\n")
        baseline_path = "derived/batch012-aggregate-baseline.json"
        baseline = {
            "schema_version": 1,
            "terminal": "FACTORY-NOVELTY-STOP",
            "private_raw_count": 80,
            "exposed_idea_count": 0,
            "source_chain_count": 13,
            "evidence_level": "proposal",
            "damage_scope": "operational-only",
            "admitted_genome_count": 0,
            "new_route_count": 0,
            "dependency_edge_change_count": 0,
            "contains_candidate_text": False,
            "attrition": BATCH012_ATTRITION,
            "sources": [
                {
                    "path": baseline_source,
                    "sha256": digest((root / baseline_source).read_bytes()),
                }
                for baseline_source in BATCH012_SOURCE_PATHS
            ],
        }
        write(root / baseline_path, json.dumps(baseline, indent=2, sort_keys=True) + "\n")
        ticket_inventory_path = "derived/ticket-genome-sources.json"
        write(root / ticket_inventory_path, render_ticket_source_inventory(root))

        role_paths = {
            "readme": "README.md",
            "wayfinder_map": "docs/wayfinder/map.md",
            "frontier_portfolio": "docs/wayfinder/frontier-portfolio.md",
            "literature_review": "docs/literature_review.md",
            "bibliography": "docs/bibliography.md",
            "model_proof_distance_rules": "AGENTS.md",
            "lean_declaration_index": lean_index_path,
            "batch012_aggregate_baseline": baseline_path,
        }

        substrates = []
        required = []
        for role in sorted(REQUIRED_SUBSTRATE_ROLES):
            path = role_paths[role]
            data = (root / path).read_bytes()
            substrates.append({"role": role, "path": path, "sha256": digest(data)})
            required.append(path)

        self.allowlist = {
            "schema_version": 1,
            "required_substrate_paths": required,
            "private_globs": ["runs/agents/batch013/private/**"],
            "excluded_globs": [],
            "substrate": substrates,
            "authorized_genome_sources": [
                {"path": "runs/idea-factory/idea-ledger.md", "sha256": digest(ledger.encode())},
                {"path": "docs/wayfinder/frontier-portfolio.md", "sha256": digest(portfolio.encode())},
            ],
            "ticket_genome_source_inventory": {
                "path": ticket_inventory_path,
                "sha256": digest((root / ticket_inventory_path).read_bytes()),
            },
            "genomes": [
                self.genome(
                    "B001-I01", "runs/idea-factory/idea-ledger.md", ledger,
                    "- **Failure-genome subject:** `B001-I01`", "\n## After", BULLET,
                    ["B001-I01", "family-one", "exact model"], "proposal", "candidate-local",
                ),
                self.genome(
                    "FP-17", "docs/wayfinder/frontier-portfolio.md", portfolio,
                    "| Subject | `FP-17`", "\n## Next", TABLE,
                    ["FP-17", "family-two", "abstract model"], "proposal", "subfamily",
                ),
            ],
        }
        self.allowlist_path = root / "allowlist.json"
        self.save()

    @staticmethod
    def genome(
        genome_id: str,
        path: str,
        source: str,
        start: str,
        end: str,
        _expected_block: str,
        terms: list[str],
        evidence: str,
        scope: str,
    ) -> dict[str, object]:
        begin = source.index(start)
        finish = source.index(end)
        block = source[begin:finish].rstrip() + "\n"
        return {
            "id": genome_id,
            "path": path,
            "source_sha256": digest(source.encode()),
            "start_marker": start,
            "end_marker": end,
            "block_sha256": digest(block.encode()),
            "subject_terms": terms,
            "evidence_level": evidence,
            "damage_scope": scope,
        }

    def save(self) -> None:
        self.allowlist_path.write_text(
            json.dumps(self.allowlist, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

    def insert_adjacent_ledger_text(self, inserted: str) -> None:
        source = self.ledger_path.read_text()
        boundary = "\n\n## After\n"
        if source.count(boundary) != 1:
            raise AssertionError("fixture must have one exact post-genome boundary")
        source = source.replace(boundary, "\n" + inserted + "## After\n")
        write(self.ledger_path, source)
        source_hash = digest(source.encode())
        self.allowlist["authorized_genome_sources"][0]["sha256"] = source_hash
        for genome in self.allowlist["genomes"]:
            if genome["path"] == "runs/idea-factory/idea-ledger.md":
                genome["source_sha256"] = source_hash
                begin = source.index(genome["start_marker"])
                finish = source.index(genome["end_marker"])
                genome["block_sha256"] = digest(
                    (source[begin:finish].rstrip() + "\n").encode()
                )
        self.save()


class BuildContextTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.fixture = ContextFixture(self.root)

    def tearDown(self) -> None:
        self.temp.cleanup()

    def test_valid_projection_is_complete_and_does_not_echo_private_pattern(self) -> None:
        summary = build_context(self.root, self.fixture.allowlist_path, self.root / "out")
        self.assertEqual(summary["genomes"], 2)
        manifest_text = (self.root / "out/manifest.json").read_text()
        context_text = (self.root / "out/context.md").read_text()
        self.assertNotIn("batch013/private", manifest_text)
        self.assertIn("TERMINAL-ONE", context_text)
        self.assertIn("TERMINAL-TWO", context_text)
        self.assertNotIn("documented template", context_text)

    def test_omitted_admitted_genome_fails_completeness(self) -> None:
        self.fixture.allowlist["genomes"] = self.fixture.allowlist["genomes"][:1]
        self.fixture.save()
        with self.assertRaisesRegex(ContextError, "completeness mismatch"):
            build_context(self.root, self.fixture.allowlist_path, self.root / "out")

    def test_duplicate_genome_fails(self) -> None:
        duplicate = dict(self.fixture.allowlist["genomes"][0])
        duplicate["id"] = "duplicate-id"
        self.fixture.allowlist["genomes"].append(duplicate)
        self.fixture.save()
        with self.assertRaisesRegex(ContextError, "covered twice|duplicate genome block"):
            build_context(self.root, self.fixture.allowlist_path, self.root / "out")

    def test_partial_or_malformed_genome_fails(self) -> None:
        item = self.fixture.allowlist["genomes"][0]
        item["end_marker"] = "- **Cheapest falsifier"
        source = self.fixture.ledger_path.read_text()
        block = source[source.index(item["start_marker"]):source.index(item["end_marker"])].rstrip() + "\n"
        item["block_sha256"] = digest(block.encode())
        self.fixture.save()
        with self.assertRaisesRegex(ContextError, "field order|cheapest falsifier"):
            build_context(self.root, self.fixture.allowlist_path, self.root / "out")

    def test_prior_ideas_cannot_be_whole_substrate(self) -> None:
        self.fixture.allowlist["excluded_globs"] = ["README.md"]
        self.fixture.save()
        with self.assertRaisesRegex(ContextError, "excluded path"):
            build_context(self.root, self.fixture.allowlist_path, self.root / "out")

    def test_stale_lean_projection_fails(self) -> None:
        entry = next(
            item for item in self.fixture.allowlist["substrate"]
            if item["role"] == "lean_declaration_index"
        )
        path = self.root / entry["path"]
        write(path, path.read_text() + "- stale declaration\n")
        entry["sha256"] = digest(path.read_bytes())
        self.fixture.save()
        with self.assertRaisesRegex(ContextError, "complete deterministic"):
            build_context(self.root, self.fixture.allowlist_path, self.root / "out")

    def test_batch012_candidate_text_flag_fails(self) -> None:
        entry = next(
            item for item in self.fixture.allowlist["substrate"]
            if item["role"] == "batch012_aggregate_baseline"
        )
        path = self.root / entry["path"]
        baseline = json.loads(path.read_text())
        baseline["contains_candidate_text"] = True
        write(path, json.dumps(baseline, indent=2, sort_keys=True) + "\n")
        entry["sha256"] = digest(path.read_bytes())
        self.fixture.save()
        with self.assertRaisesRegex(ContextError, "scalar contract"):
            build_context(self.root, self.fixture.allowlist_path, self.root / "out")

    def test_batch012_extra_candidate_prose_fails(self) -> None:
        entry = next(
            item for item in self.fixture.allowlist["substrate"]
            if item["role"] == "batch012_aggregate_baseline"
        )
        path = self.root / entry["path"]
        baseline = json.loads(path.read_text())
        baseline["candidate_text"] = "synthetic private sentinel must not enter context"
        write(path, json.dumps(baseline, indent=2, sort_keys=True) + "\n")
        entry["sha256"] = digest(path.read_bytes())
        self.fixture.save()
        with self.assertRaisesRegex(ContextError, "scalar contract"):
            build_context(self.root, self.fixture.allowlist_path, self.root / "out")

    def test_batch012_duplicate_json_key_fails(self) -> None:
        entry = next(
            item for item in self.fixture.allowlist["substrate"]
            if item["role"] == "batch012_aggregate_baseline"
        )
        path = self.root / entry["path"]
        text = path.read_text()
        text = text.replace(
            "{\n",
            "{\n  \"terminal\": \"synthetic candidate prose sentinel\",\n",
            1,
        )
        write(path, text)
        entry["sha256"] = digest(path.read_bytes())
        self.fixture.save()
        with self.assertRaisesRegex(ContextError, "duplicate JSON key"):
            build_context(self.root, self.fixture.allowlist_path, self.root / "out")

    def test_overlong_genome_extract_fails(self) -> None:
        sentinel = "synthetic adjacent idea prose must not enter the genome\n"
        self.fixture.insert_adjacent_ledger_text(sentinel)
        with self.assertRaisesRegex(ContextError, "trailing or unscoped prose"):
            build_context(self.root, self.fixture.allowlist_path, self.root / "out")

    def test_indented_markdown_after_genome_fails(self) -> None:
        self.fixture.insert_adjacent_ledger_text(
            "  ### synthetic nested section\n  adjacent idea prose must not enter\n"
        )
        with self.assertRaisesRegex(ContextError, "trailing or unscoped prose"):
            build_context(self.root, self.fixture.allowlist_path, self.root / "out")

    def test_adjacent_thematic_break_after_genome_fails(self) -> None:
        self.fixture.insert_adjacent_ledger_text(
            "  ---\n  synthetic candidate sentinel\n"
        )
        with self.assertRaisesRegex(ContextError, "trailing or unscoped prose"):
            build_context(self.root, self.fixture.allowlist_path, self.root / "out")

    def test_adjacent_html_block_after_genome_fails(self) -> None:
        self.fixture.insert_adjacent_ledger_text(
            "  <details>\n  synthetic candidate sentinel\n  </details>\n"
        )
        with self.assertRaisesRegex(ContextError, "trailing or unscoped prose"):
            build_context(self.root, self.fixture.allowlist_path, self.root / "out")

    def test_adjacent_unclosed_html_block_tag_after_genome_fails(self) -> None:
        self.fixture.insert_adjacent_ledger_text(
            "  <details\n  synthetic candidate sentinel\n"
        )
        with self.assertRaisesRegex(ContextError, "trailing or unscoped prose"):
            build_context(self.root, self.fixture.allowlist_path, self.root / "out")

    def test_adjacent_empty_list_and_no_space_quote_markers_fail(self) -> None:
        insertions = (
            "  *\n  synthetic candidate sentinel\n",
            "  +\n  synthetic candidate sentinel\n",
            "  1.\n  synthetic candidate sentinel\n",
            "  1)\n  synthetic candidate sentinel\n",
            "  >\n  synthetic candidate sentinel\n",
            "  >synthetic candidate sentinel\n",
        )
        for inserted in insertions:
            with self.subTest(marker=inserted.splitlines()[0]):
                with tempfile.TemporaryDirectory() as directory:
                    root = Path(directory)
                    fixture = ContextFixture(root)
                    fixture.insert_adjacent_ledger_text(inserted)
                    with self.assertRaisesRegex(ContextError, "trailing or unscoped prose"):
                        build_context(root, fixture.allowlist_path, root / "out")

    def test_new_ticket_genome_requires_inventory_refresh_and_extract(self) -> None:
        ticket = self.root / "docs/wayfinder/tickets/9999.md"
        write(ticket, "# Ticket\n\n" + BULLET)
        with self.assertRaisesRegex(ContextError, "ticket genome source inventory is stale"):
            build_context(self.root, self.fixture.allowlist_path, self.root / "out")


if __name__ == "__main__":
    unittest.main()
