#!/usr/bin/env python3
"""Source-level reconstruction test for the frozen Fin11 semantic generator."""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import runpy
import sys
import unittest


ROOT = Path(__file__).resolve().parents[1]
GENERATOR = ROOT / "scripts/generate_synchronized_five_fan_fin11_semantic.py"
PREFLIGHT_RUN = ROOT / "runs/agents/20260820-fin11-com-slate/fin11"
EXPECTED_PREFLIGHT_SHA256 = (
    "83934c82ea05b30daced2b856bcad7d97294215ee9333401a63d72c0cae3c3e4"
)
EXPECTED_SEMANTIC_SHA256 = (
    "3d3edcd0824781ccac596e15609796f79a21cd6f54f62fcf71d90b09f9213def"
)
EXPECTED_THEOREM = " ".join(
    """theorem synchronizedFiveFanSideAtSixFinEleven_of_selectedCube
    (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hcube : SynchronizedFiveFanFin11SelectedCube chi) :
    SynchronizedFiveFanFin11Conclusion chi""".split()
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class SemanticGeneratorTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        sys.dont_write_bytecode = True
        cls.module = runpy.run_path(str(GENERATOR), run_name="fin11_semantic_generator")
        cls.core = cls.module["semantic_core"](ROOT)
        cls.outputs_a = cls.module["generated_outputs"](ROOT)
        cls.outputs_b = cls.module["generated_outputs"](ROOT)

    def test_frozen_preflight(self) -> None:
        producer_data = (PREFLIGHT_RUN / "preflight-producer.json").read_bytes()
        checker_data = (PREFLIGHT_RUN / "preflight-checker.json").read_bytes()
        self.assertEqual(producer_data, checker_data)
        self.assertEqual(sha256(producer_data), EXPECTED_PREFLIGHT_SHA256)
        preflight = json.loads(producer_data)
        self.assertEqual(preflight["status"], "pass")
        self.assertEqual(preflight["semantic_sha256"], EXPECTED_SEMANTIC_SHA256)
        self.assertEqual(
            preflight["corruptions_rejected"],
            ["literal_sign", "omitted_family_member", "family_index_substitution"],
        )

    def test_exact_reconstruction(self) -> None:
        entries = self.core["entries"]
        units = self.core["units"]
        expected_families = self.module["EXPECTED_FAMILIES"]
        expected_units = self.module["EXPECTED_UNITS"]
        self.assertEqual(len(entries), 9175)
        self.assertEqual(len(units), 6)
        self.assertEqual(Counter(entry["family"] for entry in entries), expected_families)
        self.assertEqual(
            tuple(unit["literal"] for unit in units),
            tuple(unit[0] for unit in expected_units),
        )
        self.assertEqual(
            tuple(entry["core_id"] for entry in self.core["all_entries"]),
            tuple(range(1, 9182)),
        )

    def test_frozen_corruptions_are_detected(self) -> None:
        entries = self.core["entries"]
        first = entries[0]
        sign_corruption = (-first["literals"][0], *first["literals"][1:])
        self.assertNotEqual(sign_corruption, first["literals"])
        self.assertNotEqual(len(entries[:-1]), 9175)
        changed = Counter(entry["family"] for entry in entries)
        changed[first["family"]] -= 1
        changed["strong_quad_definition"] += 1
        self.assertNotEqual(changed, self.module["EXPECTED_FAMILIES"])

    def test_generation_is_deterministic(self) -> None:
        self.assertEqual(self.outputs_a, self.outputs_b)
        expected_outputs = (
            6
            + self.module["SUPPORT_SEGMENT_COUNT"]
            + self.module["CLAUSE_SEGMENT_COUNT"]
        )
        self.assertEqual(len(self.outputs_a), expected_outputs)
        total = sum(len(data) for data in self.outputs_a.values())
        self.assertLess(total, 2 * 1024 * 1024 * 1024)

    def test_generated_lean_static_contract(self) -> None:
        expected_outputs = (
            6
            + self.module["SUPPORT_SEGMENT_COUNT"]
            + self.module["CLAUSE_SEGMENT_COUNT"]
        )
        lean_outputs = {
            path: data.decode()
            for path, data in self.outputs_a.items()
            if path.suffix == ".lean"
        }
        self.assertEqual(len(lean_outputs), expected_outputs - 1)
        banned = (
            re.compile(r"\bsorry\b"),
            re.compile(r"\badmit\b"),
            re.compile(r"\baxiom\s+"),
            re.compile(r"\bunsafe\b"),
            re.compile(r"\bnative_decide\b"),
            re.compile(r"maxHeartbeats\s+0\b"),
        )
        for path, text in lean_outputs.items():
            for line_number, line in enumerate(text.splitlines(), 1):
                self.assertLessEqual(len(line), 100, f"{path}:{line_number}")
            for pattern in banned:
                self.assertIsNone(pattern.search(text), f"{path}: {pattern.pattern}")

    def test_public_surface_and_exact_endpoint(self) -> None:
        interface = self.outputs_a[
            Path("ErdosSzekeres/SynchronizedFiveFanFin11SemanticInterface.lean")
        ].decode()
        final = self.outputs_a[
            Path("ErdosSzekeres/SynchronizedFiveFanFin11SemanticReflection.lean")
        ].decode()
        self.assertEqual(len(re.findall(r"^def ", interface, re.MULTILINE)), 2)
        self.assertEqual(len(re.findall(r"^theorem ", final, re.MULTILINE)), 1)
        public_imports = re.findall(r"^public import (.+)$", final, re.MULTILINE)
        self.assertEqual(
            public_imports,
            ["ErdosSzekeres.SynchronizedFiveFanFin11SemanticInterface"],
        )
        normalized = " ".join(final.split())
        self.assertIn(EXPECTED_THEOREM, normalized)
        self.assertNotIn("semanticClause", EXPECTED_THEOREM)
        self.assertNotIn("valuation", EXPECTED_THEOREM)
        self.assertNotIn("certificate", EXPECTED_THEOREM)

    def test_all_core_clause_lemmas_are_partitioned_once(self) -> None:
        names = []
        segment_sizes = []
        clause_segment_count = self.module["CLAUSE_SEGMENT_COUNT"]
        for index in range(clause_segment_count):
            path = Path(
                f"ErdosSzekeres/SynchronizedFiveFanFin11SemanticSegment{index:03d}.lean"
            )
            text = self.outputs_a[path].decode()
            found = re.findall(
                r"^theorem synchronizedFiveFanFin11Semantic_clause(\d{5})",
                text,
                re.MULTILINE,
            )
            names.extend(map(int, found))
            segment_sizes.append(len(found))
        self.assertEqual(names, list(range(1, 9182)))
        quotient, remainder = divmod(9181, clause_segment_count)
        self.assertEqual(
            segment_sizes,
            [quotient + 1] * remainder
            + [quotient] * (clause_segment_count - remainder),
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
