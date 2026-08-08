#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts/check_signotope_state_witness.py"


class SignotopeStateWitnessCheckerTest(unittest.TestCase):
    def run_checker(self, literal: int) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            manifest = directory / "manifest.json"
            solution = directory / "solution.txt"
            manifest.write_text(json.dumps({
                "n": 3,
                "cap": 4,
                "cup": 4,
                "strong": 4,
                "forced_blocks": [[0, 1, 2]],
            }))
            solution.write_text(f"s SATISFIABLE\nv {literal} 0\n")
            return subprocess.run(
                [sys.executable, str(CHECKER), str(manifest), str(solution)],
                text=True,
                capture_output=True,
                check=False,
            )

    def test_accepts_forced_cup_block(self) -> None:
        result = self.run_checker(1)
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        self.assertTrue(report["checks"]["forced_cup_blocks"])
        self.assertTrue(report["ok"])

    def test_rejects_non_cup_forced_block(self) -> None:
        result = self.run_checker(-1)
        self.assertEqual(result.returncode, 1)
        report = json.loads(result.stdout)
        self.assertFalse(report["checks"]["forced_cup_blocks"])
        self.assertFalse(report["ok"])


if __name__ == "__main__":
    unittest.main()
