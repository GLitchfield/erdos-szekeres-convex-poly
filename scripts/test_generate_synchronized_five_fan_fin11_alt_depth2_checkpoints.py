#!/usr/bin/env python3
"""Corruption and determinism tests for the frozen Fin11 checkpoint renderer."""

from __future__ import annotations

from dataclasses import replace
import hashlib
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

import generate_synchronized_five_fan_fin11_alt_depth2_checkpoints as renderer


REPO_ROOT = Path(__file__).resolve().parents[1]


def synthetic_analysis() -> renderer.ProofAnalysis:
    imported = [set() for _ in range(renderer.SEGMENT_COUNT)]
    exported = [set() for _ in range(renderer.SEGMENT_COUNT)]
    additions = [0] * renderer.SEGMENT_COUNT
    deletions = [0] * renderer.SEGMENT_COUNT
    crossing = [0] * renderer.SEGMENT_COUNT
    imported[20].add(20_000)
    exported[0].add(20_000)
    additions[0] = 1
    additions[-1] = 1
    crossing[0] = 1
    return renderer.ProofAnalysis(
        size=100,
        introduced={20_000: 0, 20_001: renderer.SEGMENT_COUNT - 1},
        imported_by_segment=imported,
        exported_by_segment=exported,
        additions_by_segment=additions,
        deletions_by_segment=deletions,
        hint_edges=1,
        final_empty_id=20_001,
        final_empty_segment=renderer.SEGMENT_COUNT - 1,
        crossing_width_by_segment=crossing,
    )


def toy_validation_pair() -> tuple[renderer.BranchSpec, renderer.ProofAnalysis]:
    branch = replace(
        renderer.RIGHT_LEFT,
        core_variables=2,
        original_clauses=2,
        learned_additions=2,
        hint_edges=1,
        minimum_additions_per_segment=0,
        maximum_additions_per_segment=1,
        maximum_crossing_width=1,
        maximum_crossing_after_segment=0,
        unique_exported_clauses=1,
        final_empty_id=4,
        peak_imported_clauses=1,
        peak_import_segment=1,
        peak_carry_input_bytes=5,
        peak_carry_input_segment=1,
        total_carry_input_bytes=5,
    )
    imported = [set() for _ in range(renderer.SEGMENT_COUNT)]
    exported = [set() for _ in range(renderer.SEGMENT_COUNT)]
    additions = [0] * renderer.SEGMENT_COUNT
    deletions = [0] * renderer.SEGMENT_COUNT
    crossing = [0] * renderer.SEGMENT_COUNT
    imported[1].add(3)
    exported[0].add(3)
    additions[0] = 1
    additions[-1] = 1
    crossing[0] = 1
    analysis = renderer.ProofAnalysis(
        size=10,
        introduced={3: 0, 4: renderer.SEGMENT_COUNT - 1},
        imported_by_segment=imported,
        exported_by_segment=exported,
        additions_by_segment=additions,
        deletions_by_segment=deletions,
        hint_edges=1,
        final_empty_id=4,
        final_empty_segment=renderer.SEGMENT_COUNT - 1,
        crossing_width_by_segment=crossing,
    )
    return branch, analysis


class FrozenContractTest(unittest.TestCase):
    def test_exact_branches_stems_and_raw_declarations(self) -> None:
        self.assertEqual(
            tuple(branch.key for branch in renderer.BRANCHES),
            ("v015-0_v111-1", "v015-1_v111-1"),
        )
        self.assertEqual(
            renderer.RIGHT_LEFT.stem,
            "SynchronizedFiveFanFin11AltDepth2RightLeft",
        )
        self.assertEqual(
            renderer.LEFT_LEFT.stem,
            "SynchronizedFiveFanFin11AltDepth2LeftLeft",
        )
        self.assertEqual(
            renderer.RIGHT_LEFT.raw_declaration,
            "synchronizedFiveFanFin11_"
            "SynchronizedFiveFanFin11AltDepth2RightLeft_lrat_unsat",
        )
        self.assertEqual(
            renderer.LEFT_LEFT.raw_declaration,
            "synchronizedFiveFanFin11_"
            "SynchronizedFiveFanFin11AltDepth2LeftLeft_lrat_unsat",
        )

    def test_exact_clause_units_and_resource_ledger(self) -> None:
        self.assertEqual(renderer.RIGHT_LEFT.original_clauses, 14816)
        self.assertEqual(renderer.LEFT_LEFT.original_clauses, 14911)
        self.assertEqual(renderer.RIGHT_LEFT.units, (-15, 111))
        self.assertEqual(renderer.LEFT_LEFT.units, (15, 111))
        self.assertEqual(renderer.RIGHT_LEFT.peak_imported_clauses, 1763)
        self.assertEqual(renderer.LEFT_LEFT.peak_imported_clauses, 1736)
        self.assertEqual(renderer.RIGHT_LEFT.peak_carry_input_bytes, 145159)
        self.assertEqual(renderer.LEFT_LEFT.peak_carry_input_bytes, 141110)
        self.assertLessEqual(
            max(branch.maximum_additions_per_segment for branch in renderer.BRANCHES),
            renderer.MAX_ADDITIONS_PER_SEGMENT,
        )

    def test_only_two_frozen_representations_exist(self) -> None:
        self.assertEqual(renderer.MODES, ("ordinary", "prefix-aggregate"))
        with self.assertRaisesRegex(ValueError, "unsupported"):
            renderer.segment_import_names(
                renderer.RIGHT_LEFT, 1, [0], "unfrozen-repair"
            )


class CorruptionTest(unittest.TestCase):
    def test_artifact_hash_and_size_corruptions_are_rejected(self) -> None:
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / "toy.bin"
            path.write_bytes(b"good")
            digest = hashlib.sha256(b"good").hexdigest()
            artifact = renderer.ArtifactSpec("toy", "toy.bin", 4, digest)
            self.assertEqual(renderer.authenticate_artifact(root, artifact), path)
            path.write_bytes(b"evil")
            with self.assertRaisesRegex(ValueError, "SHA-256"):
                renderer.authenticate_artifact(root, artifact)
            path.write_bytes(b"short")
            with self.assertRaisesRegex(ValueError, "byte mismatch"):
                renderer.authenticate_artifact(root, artifact)

    def test_clause_count_and_branch_unit_corruptions_are_rejected(self) -> None:
        branch = replace(
            renderer.RIGHT_LEFT,
            core_variables=111,
            original_clauses=2,
            units=(-15, 111),
        )
        with TemporaryDirectory() as temporary:
            path = Path(temporary) / "core.cnf"
            path.write_bytes(b"p cnf 111 2\n-15 0\n111 0\n")
            renderer.validate_core_cnf(path, branch)
            path.write_bytes(b"p cnf 111 3\n-15 0\n111 0\n")
            with self.assertRaisesRegex(ValueError, "clause count"):
                renderer.validate_core_cnf(path, branch)
            path.write_bytes(b"p cnf 111 2\n15 0\n111 0\n")
            with self.assertRaisesRegex(ValueError, "branch units"):
                renderer.validate_core_cnf(path, branch)

    def test_segment_count_import_and_final_empty_corruptions_are_rejected(
        self,
    ) -> None:
        branch, analysis = toy_validation_pair()
        renderer.validate_analysis(analysis, branch)
        short = replace(
            analysis,
            additions_by_segment=analysis.additions_by_segment[:-1],
        )
        with self.assertRaisesRegex(ValueError, "exactly 256"):
            renderer.validate_analysis(short, branch)

        oversized_imports = [set() for _ in range(renderer.SEGMENT_COUNT)]
        oversized_imports[1] = set(range(renderer.MAX_IMPORTED_CLAUSES + 1))
        import_analysis = replace(
            analysis,
            imported_by_segment=oversized_imports,
        )
        import_branch = replace(
            branch,
            peak_imported_clauses=renderer.MAX_IMPORTED_CLAUSES + 1,
        )
        with self.assertRaisesRegex(ValueError, "ceiling"):
            renderer.validate_analysis(import_analysis, import_branch)

        displaced_empty = replace(analysis, final_empty_segment=254)
        with self.assertRaisesRegex(ValueError, "placement"):
            renderer.validate_analysis(displaced_empty, branch)

    def test_carry_corruptions_are_rejected(self) -> None:
        branch, _ = toy_validation_pair()
        values = [0] * renderer.SEGMENT_COUNT
        values[1] = 5
        renderer.validate_carry_input_bytes(values, branch)
        with self.assertRaisesRegex(ValueError, "exactly 256"):
            renderer.validate_carry_input_bytes(values[:-1], branch)
        oversized = [0] * renderer.SEGMENT_COUNT
        oversized[1] = renderer.MAX_CARRY_INPUT_BYTES + 1
        oversized_branch = replace(
            branch,
            peak_carry_input_bytes=renderer.MAX_CARRY_INPUT_BYTES + 1,
            total_carry_input_bytes=renderer.MAX_CARRY_INPUT_BYTES + 1,
        )
        with self.assertRaisesRegex(ValueError, "ceiling"):
            renderer.validate_carry_input_bytes(oversized, oversized_branch)

    def test_source_and_output_envelope_corruptions_are_rejected(self) -> None:
        renderer.validate_lean_source("theorem tiny : True := by trivial\n")
        corruptions = (
            "theorem bad : True := by sorry\n",
            "set_option maxHeartbeats 0\n",
            "theorem trailing : True := by trivial \n",
            "x" * (renderer.MAX_LEAN_COLUMNS + 1) + "\n",
        )
        for source in corruptions:
            with self.subTest(source=source[:30]):
                with self.assertRaises(ValueError):
                    renderer.validate_lean_source(source)
        renderer.validate_render_envelope(renderer.MAX_RENDER_BYTES)
        with self.assertRaisesRegex(ValueError, "byte envelope"):
            renderer.validate_render_envelope(renderer.MAX_RENDER_BYTES + 1)

    def test_output_path_escape_is_rejected(self) -> None:
        safe = renderer.owned_branch_root(
            REPO_ROOT, renderer.RIGHT_LEFT, "ordinary"
        )
        owner = (REPO_ROOT / renderer.STAGING_RELATIVE).resolve()
        self.assertIn(owner, safe.parents)
        with patch.object(renderer, "STAGING_RELATIVE", Path("../escape")):
            with self.assertRaisesRegex(ValueError, "escapes"):
                renderer.owned_branch_root(
                    REPO_ROOT, renderer.RIGHT_LEFT, "ordinary"
                )


class LeanSourceShapeTest(unittest.TestCase):
    def test_owned_render_passes_an_absent_atomic_target(self) -> None:
        with TemporaryDirectory() as temporary:
            root = Path(temporary)

            def fake_render(
                _repo_root: Path,
                branch_root: Path,
                _branch: renderer.BranchSpec,
                _mode: str,
            ) -> Path:
                self.assertFalse(branch_root.exists())
                branch_root.mkdir(parents=True)
                manifest = branch_root / "manifest.json"
                manifest.write_text("{}\n", encoding="utf-8")
                return manifest

            with (
                patch.object(renderer, "STAGING_RELATIVE", Path("owned")),
                patch.object(
                    renderer,
                    "render_branch_to_new_root",
                    side_effect=fake_render,
                ),
            ):
                manifest = renderer.render_owned_branch(
                    root, renderer.RIGHT_LEFT, "ordinary"
                )
            self.assertEqual(
                manifest,
                root
                / "owned/ordinary/v015-0_v111-1/manifest.json",
            )
            self.assertTrue(manifest.is_file())

    def test_ordinary_and_prefix_module_shapes_are_exact(self) -> None:
        analysis = synthetic_analysis()
        expected_counts = {"ordinary": 258, "prefix-aggregate": 274}
        for branch in renderer.BRANCHES:
            for mode in renderer.MODES:
                with self.subTest(branch=branch.key, mode=mode):
                    with TemporaryDirectory() as temporary:
                        lean_dir = Path(temporary) / "ErdosSzekeres"
                        metadata = renderer.render_lean_modules(
                            lean_dir, branch, analysis, mode
                        )
                        sources = sorted(lean_dir.glob("*.lean"))
                        self.assertEqual(len(sources), expected_counts[mode])
                        names = {path.name for path in sources}
                        prefix = branch.checkpoint_prefix
                        self.assertIn(f"{prefix}Context.lean", names)
                        self.assertIn(f"{prefix}Segment000.lean", names)
                        self.assertIn(f"{prefix}Segment255.lean", names)
                        self.assertIn(f"{prefix}Leaf.lean", names)
                        leaf = (lean_dir / f"{prefix}Leaf.lean").read_text()
                        self.assertIn(branch.raw_declaration, leaf)
                        self.assertNotIn("maxHeartbeats 0", leaf)
                        if mode == "prefix-aggregate":
                            self.assertEqual(
                                len(metadata["prefix_aggregate_modules"]), 16
                            )
                            self.assertIn(
                                f"{prefix}PrefixAggregate255.lean", names
                            )
                        else:
                            self.assertEqual(
                                metadata["prefix_aggregate_modules"], []
                            )
                        for path in sources:
                            source = path.read_text(encoding="utf-8")
                            self.assertLessEqual(
                                renderer.maximum_columns(source),
                                renderer.MAX_LEAN_COLUMNS,
                            )

    def test_prefix_mode_uses_only_previous_aggregate_and_same_block(self) -> None:
        branch = renderer.RIGHT_LEFT
        names = renderer.segment_import_names(
            branch,
            34,
            [0, 12, 16, 31, 32, 33],
            "prefix-aggregate",
        )
        self.assertEqual(
            names,
            [
                f"{branch.checkpoint_prefix}PrefixAggregate031",
                f"{branch.checkpoint_prefix}Segment032",
                f"{branch.checkpoint_prefix}Segment033",
            ],
        )


class FrozenArtifactIntegrationTest(unittest.TestCase):
    def test_two_render_determinism_and_manifest_contract(self) -> None:
        for branch in renderer.BRANCHES:
            with self.subTest(branch=branch.key):
                with (
                    TemporaryDirectory() as first,
                    TemporaryDirectory() as second,
                    TemporaryDirectory() as aggregate,
                ):
                    first_root = Path(first) / branch.key
                    second_root = Path(second) / branch.key
                    aggregate_root = Path(aggregate) / branch.key
                    first_manifest = renderer.render_branch_to_new_root(
                        REPO_ROOT, first_root, branch, "ordinary"
                    )
                    second_manifest = renderer.render_branch_to_new_root(
                        REPO_ROOT, second_root, branch, "ordinary"
                    )
                    aggregate_manifest = renderer.render_branch_to_new_root(
                        REPO_ROOT,
                        aggregate_root,
                        branch,
                        "prefix-aggregate",
                    )
                    self.assertEqual(
                        first_manifest.read_bytes(), second_manifest.read_bytes()
                    )
                    manifest = json.loads(first_manifest.read_text())
                    aggregate_data = json.loads(aggregate_manifest.read_text())
                    self.assertEqual(manifest["branch"], branch.key)
                    self.assertEqual(manifest["branch_units"], list(branch.units))
                    self.assertEqual(manifest["segments"], renderer.SEGMENT_COUNT)
                    self.assertEqual(
                        manifest["original_clauses"], branch.original_clauses
                    )
                    self.assertEqual(
                        manifest["raw_lrat_declaration"], branch.raw_declaration
                    )
                    self.assertEqual(manifest["final_empty_segment"], 255)
                    self.assertEqual(
                        manifest["reconstructed_lrat_sha256"],
                        branch.artifact("core_lrat").sha256,
                    )
                    self.assertEqual(len(manifest["artifact_ledger"]), 4)
                    for key in (
                        "artifact_ledger",
                        "segment_sha256",
                        "carry_input_sha256",
                        "carry_output_sha256",
                        "reconstructed_lrat_sha256",
                    ):
                        self.assertEqual(manifest[key], aggregate_data[key])
                    self.assertEqual(
                        len(
                            aggregate_data["module_metadata"][
                                "prefix_aggregate_modules"
                            ]
                        ),
                        16,
                    )
                    self.assertLessEqual(
                        max(manifest["imports_by_segment"]),
                        renderer.MAX_IMPORTED_CLAUSES,
                    )
                    self.assertLessEqual(
                        max(manifest["carry_input_bytes"]),
                        renderer.MAX_CARRY_INPUT_BYTES,
                    )
                    self.assertLessEqual(
                        max(manifest["additions_by_segment"]),
                        renderer.MAX_ADDITIONS_PER_SEGMENT,
                    )


if __name__ == "__main__":
    unittest.main()
