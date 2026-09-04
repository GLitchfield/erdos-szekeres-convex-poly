"""Layer checks: import direction, allowlists, blueprint root completeness."""

from __future__ import annotations

from dataclasses import dataclass

from es.config import Config
from es.modules import Module, read_name_list, scan_modules


@dataclass
class Violation:
    kind: str
    module: str
    detail: str

    def __str__(self) -> str:
        return f"{self.kind}: {self.module}: {self.detail}"


def check_layers(cfg: Config, mods: dict[str, Module] | None = None) -> list[Violation]:
    layers = cfg.layers()
    mods = mods if mods is not None else scan_modules(cfg, layers)
    order = {layer.name: i for i, layer in enumerate(layers)}
    rules = {(r.from_layer, r.to_layer): r for r in cfg.layer_rules()}
    lists: dict[str, set[str]] = {}
    for r in cfg.layer_rules():
        if r.file:
            lists[r.file] = set(read_name_list(cfg.root / r.file))
    out: list[Violation] = []
    for m in sorted(mods.values(), key=lambda x: x.name):
        if m.layer is None:
            out.append(Violation("unclassified", m.name, "module belongs to no configured layer"))
            continue
        for imp in m.imports:
            target = mods.get(imp)
            if target is None or target.layer is None:
                continue  # external (mathlib etc.) or unclassified (reported once above)
            if target.layer == m.layer:
                continue
            rule = rules.get((m.layer, target.layer))
            if rule is None:
                allowed = order[m.layer] > order[target.layer]
                if not allowed:
                    out.append(Violation("layer-order", m.name, f"{m.layer} may not import {target.layer} ({imp})"))
                continue
            if rule.allow == "any":
                continue
            if rule.allow == "none":
                out.append(Violation("layer-rule", m.name, f"{m.layer} -> {target.layer} forbidden ({imp})"))
                continue
            allow = lists.get(rule.file or "", set())
            subject = m.name if rule.allow == "importers" else imp
            if subject not in allow:
                out.append(
                    Violation(
                        "layer-allowlist",
                        m.name,
                        f"imports {imp} ({target.layer}); {subject} is not listed in {rule.file}",
                    )
                )
    out.extend(check_blueprint_root(cfg, mods))
    return out


def blueprint_node_modules(cfg: Config, mods: dict[str, Module]) -> list[str]:
    layer = cfg.layer(cfg.blueprint_layer)
    root_name = cfg.blueprint_namespace
    excluded = set(layer.exclude_from_root)
    return sorted(
        m.name
        for m in mods.values()
        if m.layer == layer.name and m.name != root_name and m.name not in excluded
    )


def check_blueprint_root(cfg: Config, mods: dict[str, Module]) -> list[Violation]:
    root_name = cfg.blueprint_namespace
    root = mods.get(root_name)
    if root is None:
        return [Violation("blueprint-root", root_name, f"{cfg.blueprint_root} is missing")]
    imported = set(root.imports)
    out = []
    for name in blueprint_node_modules(cfg, mods):
        if name not in imported:
            out.append(Violation("blueprint-root", name, f"not imported by {root_name}"))
    return out


def derive_allowlists(cfg: Config, mods: dict[str, Module] | None = None) -> dict[str, list[str]]:
    """For every allowlist rule, the names the current import graph would require."""
    mods = mods if mods is not None else scan_modules(cfg)
    result: dict[str, list[str]] = {}
    for r in cfg.layer_rules():
        if r.allow not in ("importers", "imported") or not r.file:
            continue
        names: set[str] = set()
        for m in mods.values():
            if m.layer != r.from_layer:
                continue
            for imp in m.imports:
                t = mods.get(imp)
                if t is not None and t.layer == r.to_layer:
                    names.add(m.name if r.allow == "importers" else imp)
        result[r.file] = sorted(names)
    return result
