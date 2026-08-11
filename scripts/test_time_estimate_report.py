import tempfile
import unittest
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

import time_estimate_report as report


HEADER = (
    "id,estimated_at,started_at,finished_at,category,description,"
    "forecast_low_minutes,forecast_high_minutes,actual_wall_minutes,"
    "paused_minutes,status,outcome,error_ratio,notes\n"
)


class TimeEstimateReportTests(unittest.TestCase):
    def test_summary_uses_active_wall_and_rewrites_only_completed_ratios(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "ledger.csv"
            path.write_text(
                HEADER
                + "done,e,s,f,review,d,10,20,18,3,completed,proved,9.999,n\n"
                + "live,e,s,,review,d,10,20,,,in_progress,,,n\n",
                encoding="utf-8",
            )

            rows = report.load_completed(path)
            self.assertEqual(len(rows), 1)
            self.assertEqual(rows[0].active_wall, 15)
            self.assertEqual(rows[0].ratio, 1)
            self.assertTrue(rows[0].inside_forecast)
            self.assertEqual(len(report.ratio_mismatches(rows)), 1)

            self.assertEqual(report.rewrite_ratios(path), 1)
            rewritten = report.load_completed(path)
            self.assertEqual(report.ratio_mismatches(rewritten), [])
            self.assertIn(",1.000,n\n", path.read_text(encoding="utf-8"))

    def test_report_separates_categories(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "ledger.csv"
            path.write_text(
                HEADER
                + "a,e,s,f,review,d,10,20,15,0,completed,proved,1.000,n\n"
                + "b,e,s,f,integration,d,20,40,15,0,completed,proved,0.500,n\n",
                encoding="utf-8",
            )
            result = report.build_report(report.load_completed(path))
            self.assertEqual(result["overall"]["count"], 2)
            self.assertEqual(result["categories"]["review"]["count"], 1)
            self.assertEqual(result["categories"]["integration"]["count"], 1)


if __name__ == "__main__":
    unittest.main()
