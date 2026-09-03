from __future__ import annotations

import copy
import unittest
from unittest import mock

from scripts import build_orchard_xor_panel as panel_builder


class OrchardXorPanelBuilderTests(unittest.TestCase):
    def test_authenticated_panel_has_exact_closed_identity(self) -> None:
        panel = panel_builder.build_panel()
        self.assertEqual(panel["schema_version"], 2)
        self.assertEqual(panel["protocol"], panel_builder.PANEL_PROTOCOL)
        self.assertEqual(panel["input_role"], "panel")
        self.assertEqual(panel["task_id"], panel_builder.TASK_ID)
        self.assertEqual(panel["source_bindings"], panel_builder.SOURCE_BINDINGS)
        self.assertEqual(
            [case["case_id"] for case in panel["cases"]],
            [
                "fin8-record-1654",
                "fin9-record-936",
                "ticket-0037-affine-bad-n13",
                "pascal-row-d4-equality16-v1",
                "ticket-0037-affine-bad-n13::fd008-relaxed",
                "pascal-row-d4-equality16-v1::fd008-relaxed",
            ],
        )

    def test_each_actual_matches_its_compact_coordinate_digest(self) -> None:
        panel = panel_builder.build_panel()
        for case in panel["cases"][:4]:
            expected = panel_builder.EXPECTED_ACTUALS[case["case_id"]]
            self.assertEqual(len(case["points"]), expected[0])
            self.assertEqual(case["target_k"], expected[1])
            self.assertEqual(panel_builder.canonical_sha256(case["points"]), expected[2])

    def test_each_control_is_reconstructed_from_parent_and_exact_flips(self) -> None:
        panel = panel_builder.build_panel()
        by_id = {case["case_id"]: case for case in panel["cases"]}
        for case_id, spec in panel_builder.CONTROL_SPECS.items():
            case = by_id[case_id]
            parent = by_id[str(spec["parent"])]
            signs = panel_builder.increasing_signs(parent["points"])
            triples = list(
                __import__("itertools").combinations(range(len(parent["points"])), 3)
            )
            index = {triple: offset for offset, triple in enumerate(triples)}
            for triple in spec["flips"]:
                signs[index[tuple(triple)]] *= -1
            self.assertEqual(case["increasing_signs"], signs)
            self.assertEqual(case["reported_source_sign_sha256"], spec["source_hash"])

    def test_source_hash_drift_stops_before_panel_construction(self) -> None:
        altered = copy.deepcopy(panel_builder.SOURCE_BINDINGS)
        altered["AGENTS.md"] = "0" * 64
        with mock.patch.object(panel_builder, "SOURCE_BINDINGS", altered):
            with self.assertRaises(panel_builder.PanelBuildError):
                panel_builder.build_panel()


if __name__ == "__main__":
    unittest.main()
