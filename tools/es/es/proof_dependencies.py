"""Observational type/value dependency receipts; never theorem acceptance.

The Lean traversal is run separately through ``es job run``. This module only
constructs its argv, validates the raw trace, and classifies names through the
existing module catalog. Source hashes identify the declaration's owner, not
merely the module used to import it. Original-source checks remain necessary.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from es.artifact_cache import sha256_file
from es.config import load_config
from es.errors import UsageError
from es.modules import module_to_path, scan_modules


RAW_SEMANTICS = "transitive type-and-value constant closure; observational"
RECEIPT_SEMANTICS = (
    "Observational transitive type/value dependency trace classified by the "
    "harness module catalog; hashes identify the root declaration's owner; "
    "no theorem acceptance or fresh-frontier claim"
)
LEAN_REL = Path("tools/es/lean/TraceProofDependencies.lean")


def lean_command(cfg, module: str, declaration: str, output: Path) -> list[str]:
    """Return an argv to submit through guarded ``es job run``; execute nothing."""
    return [cfg.lake, "env", "lean", "--run", str(cfg.root / LEAN_REL),
            module, declaration, str(output)]


def _names(trace: dict, key: str) -> list[str]:
    value = trace.get(key)
    if not isinstance(value, list) or not all(isinstance(x, str) and x for x in value):
        raise UsageError(f"dependency trace {key} must be a list of names")
    return sorted(set(value))


def classify_trace(cfg, trace: dict, *, modules=None) -> dict:
    """Classify a validated raw trace, including unknown project modules.

    This accepts observational data, not an attested proof receipt. Importing a
    certificate is different from referencing one in a declaration's closure.
    Unknown names under *every configured layer prefix* remain explicit.
    """
    if (not isinstance(trace, dict) or type(trace.get("schema_version")) is not int
            or trace["schema_version"] != 1):
        raise UsageError("dependency trace schema_version must be 1")
    if trace.get("semantics") != RAW_SEMANTICS:
        raise UsageError("dependency trace semantics mismatch")
    for key in ("module", "root"):
        if not isinstance(trace.get(key), str) or not trace[key]:
            raise UsageError(f"dependency trace {key} must be a name")
    owner = trace.get("root_module")
    if owner is not None and (not isinstance(owner, str) or not owner):
        raise UsageError("dependency trace root_module must be a name or null")
    if "root_module" not in trace:
        raise UsageError("dependency trace predates declaration-owner capture")
    count = trace.get("reachable_constants")
    upper = trace.get("imported_constant_upper_bound")
    if type(count) is not int or count <= 0 or type(upper) is not int or upper < count:
        raise UsageError("dependency trace requires a positive count and valid upper bound")
    names = _names(trace, "modules")
    axioms = _names(trace, "axioms")
    unsafe = _names(trace, "unsafe_constants")
    if owner is not None and owner not in names:
        raise UsageError("root declaration owner is absent from reachable modules")
    mods = scan_modules(cfg) if modules is None else modules
    prefixes = {prefix for layer in cfg.layers() for prefix in layer.prefixes}
    project = [name for name in names if any(
        name == prefix or name.startswith(prefix + ".") for prefix in prefixes)]
    return {
        "schema_version": 1,
        "root": trace["root"],
        "import_module": trace["module"],
        "root_module": owner,
        "reachable_constants": count,
        "generated_modules": [name for name in project if name in mods and mods[name].generated],
        "certificate_modules": [name for name in project if name in mods and
                                cfg.certificates_layer is not None and
                                mods[name].layer == cfg.certificates_layer],
        "unknown_project_modules": [name for name in project if name not in mods],
        "axioms": axioms,
        "nonstandard_axioms": sorted(set(axioms) - set(cfg.standard_axioms)),
        "unsafe_constants": unsafe,
        "semantics": RECEIPT_SEMANTICS,
    }


def receipt(cfg, trace_path: Path, *, modules=None) -> dict:
    """Pin a project declaration's raw trace, owner source and compiled olean.

    Hashes are observations of existing files. They neither attest that the
    source was compiled into that olean nor replace a kernel check. Stdlib
    traces can be classified with ``classify_trace`` but have no project source
    identity and therefore cannot produce this project receipt.
    """
    mods = scan_modules(cfg) if modules is None else modules
    trace = json.loads(trace_path.read_text())
    result = classify_trace(cfg, trace, modules=mods)
    owner = result["root_module"]
    if owner not in mods:
        raise UsageError("root declaration owner is not a configured project module")
    source = cfg.root / mods[owner].path
    olean = cfg.root / ".lake/build/lib/lean" / module_to_path(owner).with_suffix(".olean")
    if not source.resolve().is_relative_to(cfg.root.resolve()):
        raise UsageError("root declaration source is outside the project")
    for path in (source, olean):
        if not path.is_file():
            raise UsageError(f"dependency receipt identity file is missing: {path}")
    result.update({
        "trace_sha256": sha256_file(trace_path),
        "source_path": source.relative_to(cfg.root).as_posix(),
        "source_sha256": sha256_file(source),
        "olean_path": olean.relative_to(cfg.root).as_posix(),
        "olean_sha256": sha256_file(olean),
    })
    return result


def main(argv=None) -> int:
    """Classify/hash an existing trace; do not launch Lean or grant acceptance."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path)
    parser.add_argument("--trace", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        cfg = load_config(args.root)
        result = receipt(cfg, args.trace)
        args.out.write_text(json.dumps(result, indent=2) + "\n")
    except (UsageError, OSError, json.JSONDecodeError) as exc:
        parser.exit(2, f"{exc}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
