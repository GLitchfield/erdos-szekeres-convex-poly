"""Enumerate Lean modules of the project, parse imports, classify by layer."""

from __future__ import annotations

import fnmatch
import re
from dataclasses import dataclass, field
from pathlib import Path

from es.config import Config, Layer

IMPORT_RE = re.compile(
    r"^[ \t]*(?:public[ \t]+)?(?:private[ \t]+)?import[ \t]+(?:all[ \t]+)?([A-Za-z_À-￿][\w.À-￿«»]*)",
    re.M,
)


@dataclass
class Module:
    name: str
    path: Path  # relative to project root
    layer: str | None
    imports: list[str] = field(default_factory=list)
    generated: bool = False

    @property
    def is_root(self) -> bool:
        return "." not in self.name


def module_to_path(name: str) -> Path:
    return Path(*name.split(".")).with_suffix(".lean")


def path_to_module(rel: Path) -> str:
    return ".".join(rel.with_suffix("").parts)


def parse_imports(text: str) -> list[str]:
    # stop at the first non-import, non-comment, non-module-header line to avoid
    # matching `import` inside docstrings
    out: list[str] = []
    for m in IMPORT_RE.finditer(text):
        out.append(m.group(1).strip("«»"))
    return out


def _generated_matcher(cfg: Config):
    patterns = cfg.generated_patterns
    marker = re.compile(cfg.generated_marker, re.I) if cfg.generated_marker else None
    lines = cfg.generated_marker_lines

    def is_generated(rel_under_prefix: str, text_head: str) -> bool:
        if any(fnmatch.fnmatchcase(rel_under_prefix, p) for p in patterns):
            return True
        if marker is not None:
            head = "\n".join(text_head.splitlines()[:lines])
            if marker.search(head):
                return True
        return False

    return is_generated


def classify(cfg: Config, layers: list[Layer], name: str, rel_under_prefix: str | None, head: str) -> tuple[str | None, bool]:
    """Return (layer name, generated?) for a module name."""
    is_gen = _generated_matcher(cfg)
    generated = rel_under_prefix is not None and is_gen(rel_under_prefix, head)
    gen_layers = [layer for layer in layers if layer.generated]
    plain = [layer for layer in layers if not layer.generated]
    if generated:
        for layer in gen_layers:
            if any(name == p or name.startswith(p + ".") for p in layer.prefixes):
                return layer.name, True
    for layer in plain:
        if any(name == p or name.startswith(p + ".") for p in layer.prefixes):
            return layer.name, generated
    return None, generated


def _rel_under_prefix(name: str, prefixes: tuple[str, ...]) -> str | None:
    for p in prefixes:
        if name == p:
            return ""
        if name.startswith(p + "."):
            return name[len(p) + 1 :].replace(".", "/")
    return None


def scan_modules(cfg: Config, layers: list[Layer] | None = None) -> dict[str, Module]:
    """All modules under every layer's prefixes, keyed by module name."""
    layers = layers or cfg.layers()
    root = cfg.root
    seen: dict[str, Module] = {}
    all_prefixes: tuple[str, ...] = tuple(sorted({p for layer in layers for p in layer.prefixes}))
    for prefix in all_prefixes:
        base = root / module_to_path(prefix)
        candidates: list[Path] = []
        if base.exists():
            candidates.append(base)
        pdir = base.with_suffix("")
        if pdir.is_dir():
            candidates.extend(sorted(pdir.rglob("*.lean")))
        for path in candidates:
            rel = path.relative_to(root)
            name = path_to_module(rel)
            if name in seen:
                continue
            try:
                text = path.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            head = text[:4000]
            layer_name, generated = classify(cfg, layers, name, _rel_under_prefix(name, all_prefixes), head)
            seen[name] = Module(name=name, path=rel, layer=layer_name, imports=parse_imports(text), generated=generated)
    return seen


def transitive_closure(mods: dict[str, Module], roots: list[str]) -> set[str]:
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        m = stack.pop()
        if m in seen or m not in mods:
            continue
        seen.add(m)
        stack.extend(mods[m].imports)
    return seen


def topological(mods: dict[str, Module], names: set[str]) -> list[str]:
    """Dependencies first."""
    order: list[str] = []
    state: dict[str, int] = {}

    def visit(n: str) -> None:
        if state.get(n) == 2 or n not in mods or n not in names:
            return
        if state.get(n) == 1:
            return  # cycle; Lean would reject it anyway
        state[n] = 1
        for d in mods[n].imports:
            visit(d)
        state[n] = 2
        order.append(n)

    for n in sorted(names):
        visit(n)
    return order


def read_name_list(path: Path) -> list[str]:
    if not path.exists():
        return []
    out = []
    for line in path.read_text().splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            out.append(line)
    return out


def write_name_list(path: Path, names: list[str], header: str | None = None) -> None:
    lines = []
    if header:
        lines.extend(f"# {h}" for h in header.splitlines())
    lines.extend(sorted(set(names)))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n")
