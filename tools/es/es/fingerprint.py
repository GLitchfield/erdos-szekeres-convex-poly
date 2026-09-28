"""Input fingerprints of the extracted index, so `nodes.json` can be verified and updated
without loading the whole Lean environment.

A node's extractor record (statement, sorry, axioms, dependencies, docstring tags) is a
function of the sources in its import closure, of the extractor itself and of the extract
configuration. The fingerprints split those inputs in two:

* ``core``: everything outside the blueprint node modules — the core and certificate
  libraries, the destinations, the toolchain and Lake manifest, the extractor template and
  the extract-relevant configuration. It is computed from git trees plus uncommitted
  changes (`gitutil.tree_hash`), so it costs a few git calls, not a pass over the
  certificate sources. When it changes, only a full `es extract` is trusted.
* ``blueprint``: for every blueprint module reachable from the blueprint root, a digest of
  the blueprint sources in its import closure. When only these change, re-extracting the
  changed modules (a targeted, closure-sized extractor run) reproduces exactly the records
  a full extraction would, and the rest of the index carries over.
"""

from __future__ import annotations

import hashlib
import json

from es.config import Config
from es.gitutil import tree_hash
from es.modules import Module, scan_modules

# Files outside the layer prefixes whose content changes extractor output.
TOOLCHAIN_FILES = ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean")
# Configuration sections the extractor or the record grouping reads.
EXTRACT_CONFIG_SECTIONS = ("project", "layers", "audit", "extract", "certificates")


def _blueprint_prefix(cfg: Config) -> str:
    return cfg.blueprint_namespace + "."


def blueprint_closure(cfg: Config, mods: dict[str, Module], roots: list[str]) -> set[str]:
    """Blueprint modules in the import closure of ``roots``.

    Only blueprint imports are followed: the layering (`es layers`) forbids core and
    certificate modules from importing the blueprint, so no blueprint module is reachable
    through them, and the walk stays proportional to the blueprint."""
    prefix = _blueprint_prefix(cfg)
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        m = stack.pop()
        if m in seen or m not in mods:
            continue
        seen.add(m)
        stack.extend(i for i in mods[m].imports if i.startswith(prefix))
    return {m for m in seen if m.startswith(prefix)}


def blueprint_modules(cfg: Config, mods: dict[str, Module]) -> set[str]:
    """Blueprint modules reachable from the blueprint root (the root itself excluded)."""
    root = cfg.blueprint_namespace
    if root not in mods:
        return set()
    return blueprint_closure(cfg, mods, [i for i in mods[root].imports if i.startswith(_blueprint_prefix(cfg))])


def module_digests(cfg: Config, mods: dict[str, Module], names: set[str]) -> dict[str, str]:
    out: dict[str, str] = {}
    for name in names:
        mod = mods.get(name)
        path = cfg.root / mod.path if mod else None
        if path is None or not path.is_file():
            out[name] = "absent"
            continue
        out[name] = hashlib.sha256(path.read_bytes()).hexdigest()
    return out


def closure_fingerprint(cfg: Config, mods: dict[str, Module], module: str, digests: dict[str, str]) -> str:
    """Digest of the blueprint sources in ``module``'s import closure."""
    h = hashlib.sha256()
    for name in sorted(blueprint_closure(cfg, mods, [module])):
        h.update(name.encode())
        h.update(b"\0")
        h.update(digests.get(name, "absent").encode())
        h.update(b"\n")
    return h.hexdigest()[:16]


def core_dirs(cfg: Config) -> list[str]:
    """The extract state paths (see `commands.extract.state_dirs`) minus the blueprint's own."""
    from es.commands.extract import state_dirs

    bp_dir = cfg.blueprint_namespace
    bp_root = str(cfg.blueprint_root.relative_to(cfg.root))
    dirs = [d for d in state_dirs(cfg) if d not in (bp_dir, bp_root) and not d.startswith(bp_dir + "/")]
    dirs += [f for f in TOOLCHAIN_FILES if (cfg.root / f).exists()]
    return sorted(set(dirs))


def core_fingerprint(cfg: Config) -> str:
    h = hashlib.sha256()
    h.update(tree_hash(cfg, core_dirs(cfg)).encode())
    template = cfg.extract_template
    if template.exists():
        h.update(hashlib.sha256(template.read_bytes()).hexdigest().encode())
    sections = {s: cfg.get(s) for s in EXTRACT_CONFIG_SECTIONS}
    h.update(json.dumps(sections, sort_keys=True, default=str).encode())
    return h.hexdigest()[:16]


def current(cfg: Config, mods: dict[str, Module] | None = None) -> dict:
    """``{"core": ..., "blueprint": {module: closure fingerprint}}`` for the working tree."""
    mods = mods if mods is not None else scan_modules(cfg)
    names = blueprint_modules(cfg, mods)
    digests = module_digests(cfg, mods, blueprint_closure(cfg, mods, sorted(names)))
    return {
        "core": core_fingerprint(cfg),
        "blueprint": {name: closure_fingerprint(cfg, mods, name, digests) for name in sorted(names)},
    }


def diff(recorded: dict | None, now: dict) -> tuple[str | None, set[str], set[str]]:
    """Compare recorded fingerprints with the current ones.

    Returns ``(reason, stale, removed)``: ``reason`` is set when only a full extraction can
    be trusted (no recorded fingerprints, or the core inputs changed); otherwise ``stale``
    holds the blueprint modules to re-extract and ``removed`` those no longer reachable."""
    if not recorded or "core" not in recorded or "blueprint" not in recorded:
        return "nodes.json carries no input fingerprints (written before incremental indexing); run a full `es extract` once", set(), set()
    if recorded["core"] != now["core"]:
        return ("core, certificate, toolchain, extractor or extract-configuration inputs changed since nodes.json "
                "was written; run a full `es extract`"), set(), set()
    old = recorded["blueprint"]
    stale = {m for m, fp in now["blueprint"].items() if old.get(m) != fp}
    removed = set(old) - set(now["blueprint"])
    return None, stale, removed
