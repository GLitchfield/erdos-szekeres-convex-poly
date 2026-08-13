#!/usr/bin/env python3
"""Determinism and raw-string safety tests for the state-556 generator."""

from __future__ import annotations

import hashlib
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GENERATOR = ROOT / "scripts/generate_pascal556_witness_reuse_fin14_lean.py"
BUILDER = ROOT / "runs/agents/20260812-frontier-cycle/pascal-556-builder"
PROMOTION = ROOT / "runs/agents/20260812-promotion-wave/pascal556-lean"


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="pascal556-generator-") as directory:
        root = Path(directory)
        cnf = root / "tiny.cnf"
        lrat = root / "tiny.lrat"
        first = root / "first.lean"
        second = root / "second.lean"
        cnf.write_text("p cnf 1 2\n1 0\n-1 0\n")
        lrat.write_text("3 0 1 2 0\n")
        command = [
            "python3", str(GENERATOR), "--cnf", str(cnf), "--lrat", str(lrat),
            "--theorem", "tinyRefutation", "--output",
        ]
        subprocess.run(command + [str(first)], check=True, capture_output=True, text=True)
        subprocess.run(command + [str(second)], check=True, capture_output=True, text=True)
        if first.read_bytes() != second.read_bytes():
            raise AssertionError("generator is nondeterministic")
        body = first.read_text()
        if "p cnf 1 2" not in body or "3 0 1 2 0" not in body:
            raise AssertionError("certificate payload missing")

        checkpoint_cnf = root / "checkpoint.cnf"
        checkpoint_lrat = root / "checkpoint.lrat"
        checkpoint_cnf.write_text("p cnf 2 3\n1 2 0\n-1 0\n-2 0\n")
        checkpoint_lrat.write_text("4 2 0 2 1 0\n5 0 4 3 0\n")
        checkpoint_digests = []
        for run in range(2):
            data = root / f"data-{run}"
            lean = root / f"lean-{run}"
            subprocess.run([
                "python3", str(GENERATOR), "--cnf", str(checkpoint_cnf),
                "--lrat", str(checkpoint_lrat), "--checkpoint-prefix",
                "Pascal556WitnessReuseFin14Test", "--checkpoint-dir", str(data),
                "--lean-dir", str(lean), "--original-clauses", "3", "--segments", "2",
                "--bundle-size", "2",
            ], check=True, capture_output=True, text=True)
            checkpoint_digests.append([
                hashlib.sha256(path.read_bytes()).hexdigest()
                for path in sorted(lean.glob("*.lean"))
            ])
        if checkpoint_digests[0] != checkpoint_digests[1]:
            raise AssertionError("checkpoint generation is nondeterministic")

        semantic_digests = []
        for run in range(2):
            semantic = root / f"semantic-{run}.lean"
            subprocess.run([
                "python3", str(GENERATOR),
                "--cnf", str(PROMOTION / "two-core.cnf"),
                "--lrat", str(PROMOTION / "two-core.lrat"),
                "--semantic-builder", str(BUILDER),
                "--semantic-map", str(BUILDER / "formula-map.json"),
                "--semantic-origin", str(PROMOTION / "two-core-origin.txt"),
                "--semantic-eliminator-index", "0", "--semantic-chunk-size", "1024",
                "--output", str(semantic),
            ], check=True, capture_output=True, text=True)
            semantic_digests.append(hashlib.sha256(semantic.read_bytes()).hexdigest())
        if semantic_digests[0] != semantic_digests[1]:
            raise AssertionError("semantic generation is nondeterministic")
        print("generator tests passed:", hashlib.sha256(first.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
