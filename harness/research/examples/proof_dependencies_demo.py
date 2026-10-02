"""Run through es job run; preserve raw trace and classified identity receipt."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess

from es.config import load_config
from es.proof_dependencies import lean_command, receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", default="ErdosSzekeres.StructuralChargingCore")
    parser.add_argument("--declaration", default="ErdosSzekeres.TurnSequenceAllowed.all_eq_of_outer_eq")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if not os.environ.get("ES_JOB_ID") or os.environ.get("ES_IN_GUARDED_STAGE") != "1":
        parser.error("run this example inside es job run")
    cfg = load_config()
    out = (cfg.root / args.out).resolve()
    if not any(out.is_relative_to(cfg.root / directory) for directory in ("runs", "data")):
        parser.error("output must be under project runs/ or data/")
    out.mkdir(parents=True, exist_ok=True)
    raw = out / "trace.json"
    subprocess.run(lean_command(cfg, args.module, args.declaration, raw), cwd=cfg.root, check=True)
    result = receipt(cfg, raw)
    (out / "receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in (
        "root", "root_module", "reachable_constants", "generated_modules",
        "certificate_modules", "unknown_project_modules", "nonstandard_axioms",
        "unsafe_constants", "semantics")}))


if __name__ == "__main__":
    main()
