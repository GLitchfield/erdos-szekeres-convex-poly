from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "scripts/run_lean_guarded.py"


class GuardedRunnerTests(unittest.TestCase):
    def run_guard(self, *arguments: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(RUNNER), *arguments],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )

    def test_success_propagates_exit_zero(self) -> None:
        completed = self.run_guard(
            "--timeout-seconds", "5",
            "--max-rss-mib", "256",
            "--heartbeat-seconds", "1",
            "--poll-seconds", "0.02",
            "--", sys.executable, "-c", "print('guard-ok')",
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("guard-ok", completed.stdout)
        self.assertIn("guard: exit=0", completed.stderr)

    def test_timeout_stops_process_group(self) -> None:
        completed = self.run_guard(
            "--timeout-seconds", "0.1",
            "--max-rss-mib", "256",
            "--heartbeat-seconds", "1",
            "--poll-seconds", "0.02",
            "--grace-seconds", "0.1",
            "--", sys.executable, "-c", "import time; time.sleep(10)",
        )
        self.assertEqual(completed.returncode, 124, completed.stderr)
        self.assertIn("guard: timeout", completed.stderr)

    def test_rss_cap_stops_process_group(self) -> None:
        completed = self.run_guard(
            "--timeout-seconds", "5",
            "--max-rss-mib", "1",
            "--heartbeat-seconds", "1",
            "--poll-seconds", "0.02",
            "--grace-seconds", "0.1",
            "--", sys.executable, "-c", "import time; time.sleep(10)",
        )
        self.assertEqual(completed.returncode, 125, completed.stderr)
        self.assertIn("aggregate RSS cap exceeded", completed.stderr)

    def test_lean_process_cap_stops_process_group(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fake_lean = Path(directory) / "lean"
            os.symlink(sys.executable, fake_lean)
            parent = (
                "import subprocess,sys,time; "
                "children=[subprocess.Popen([sys.argv[1],'-c',"
                "'import time; time.sleep(10)']) for _ in range(2)]; "
                "time.sleep(10)"
            )
            completed = self.run_guard(
                "--timeout-seconds", "5",
                "--max-rss-mib", "256",
                "--max-lean-processes", "1",
                "--heartbeat-seconds", "1",
                "--poll-seconds", "0.02",
                "--grace-seconds", "0.1",
                "--", sys.executable, "-c", parent, str(fake_lean),
            )
        self.assertEqual(completed.returncode, 125, completed.stderr)
        self.assertIn("Lean process cap exceeded", completed.stderr)


if __name__ == "__main__":
    unittest.main()
