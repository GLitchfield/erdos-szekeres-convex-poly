#!/usr/bin/env python3

import unittest

from generate_e3_state566_lean import (
    balanced_tree,
    balanced_or_injection,
    checkpoint_refutation_term,
    chunk_imports,
    refined_chunks,
    restored_refinement_terms,
)
from generate_e3_state466_lean import balanced_join


class ChunkImportsTest(unittest.TestCase):
    def test_first_lane_level_imports_only_encoding(self) -> None:
        for index in range(5):
            imports = chunk_imports(index)
            self.assertIn("E3State566Encoding", imports)
            self.assertNotIn("Checkpoint", imports)
            self.assertTrue(imports.startswith("module\n\npublic import "))

    def test_five_bounded_dependency_lanes(self) -> None:
        self.assertEqual(
            chunk_imports(5),
            "module\n\npublic import ErdosSzekeres.E3State566Encoding\n"
            "import ErdosSzekeres.E3State566CNFChunk000",
        )
        self.assertEqual(
            chunk_imports(17),
            "module\n\npublic import ErdosSzekeres.E3State566Encoding\n"
            "import ErdosSzekeres.E3State566CNFChunk012",
        )

    def test_refined_tail_uses_six_lanes_without_changing_prefix(self) -> None:
        self.assertIn("CNFChunk080", chunk_imports(85))
        self.assertIn("CNFChunk084", chunk_imports(89))
        self.assertIn("CNFChunk079", chunk_imports(90))
        self.assertIn("CNFChunk085", chunk_imports(91))


class RefinedChunksTest(unittest.TestCase):
    def test_preserves_prefix_and_refines_only_tail(self) -> None:
        items = [str(index) for index in range(64)]
        base = refined_chunks(items, 8, 8, 1)
        refined = refined_chunks(items, 8, 3, 4)

        self.assertEqual(refined[:3], base[:3])
        self.assertEqual([item for chunk in refined for item in chunk], items)
        self.assertEqual(len(refined), 3 + (8 - 3) * 4)

    def test_rejects_invalid_refinement_boundary(self) -> None:
        with self.assertRaises(ValueError):
            refined_chunks(["a", "b", "c", "d"], 2, 3, 1)

    def test_restoration_preserves_original_balanced_tree(self) -> None:
        items = [str(index) for index in range(64)]
        chunks = refined_chunks(items, 8, 3, 4)
        restored = restored_refinement_terms(
            len(chunks), 8, 3, 4,
            lambda index: balanced_join(chunks[index], "∨"),
            lambda names: balanced_join(names, "∨"),
        )

        self.assertEqual(
            balanced_join(restored, "∨"),
            balanced_join(items, "∨"),
        )

    def test_restoration_uses_distinct_refutation_combiner(self) -> None:
        restored = restored_refinement_terms(
            23, 8, 3, 4,
            lambda index: f"h{index}",
            lambda names: f"refute({' '.join(names)})",
        )

        self.assertEqual(restored[:4], ["h0", "h1", "h2", "refute(h3 h4 h5 h6)"])

    def test_checkpoint_refutation_is_scrutinee_directed(self) -> None:
        self.assertEqual(
            checkpoint_refutation_term(balanced_tree([0, 1, 2, 3])),
            "(Or.elim hbad (fun hbad ↦ (Or.elim hbad (fun hbad ↦ h0 hbad) "
            "(fun hbad ↦ h1 hbad))) (fun hbad ↦ (Or.elim hbad "
            "(fun hbad ↦ h2 hbad) (fun hbad ↦ h3 hbad))))",
        )

    def test_balanced_or_injection_follows_rendered_tree(self) -> None:
        self.assertEqual(balanced_or_injection(0, 4), "Or.inl (Or.inl (hbad))")
        self.assertEqual(balanced_or_injection(1, 4), "Or.inl (Or.inr (hbad))")
        self.assertEqual(balanced_or_injection(2, 4), "Or.inr (Or.inl (hbad))")
        self.assertEqual(balanced_or_injection(3, 4), "Or.inr (Or.inr (hbad))")


if __name__ == "__main__":
    unittest.main()
