"""Project configuration: ``harness/config.toml`` plus discovery of the project root."""

from __future__ import annotations

import os
import shutil
import tomllib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from es.errors import ConfigError

CONFIG_REL = Path("harness") / "config.toml"


def primary_root(root: Path) -> Path:
    """The main checkout for a git worktree (`.git` is a file naming `<main>/<gitdir>/worktrees/<name>`),
    else ``root`` itself.  Harness state is shared per primary checkout, not per worktree."""
    gitfile = root / ".git"
    try:
        if gitfile.is_file():
            text = gitfile.read_text().strip()
            if text.startswith("gitdir:"):
                gd = Path(text[len("gitdir:"):].strip())
                gd = gd if gd.is_absolute() else (root / gd).resolve()
                if gd.parent.name == "worktrees":
                    return gd.parent.parent.parent
    except OSError:
        pass
    return root


def find_root(start: Path | None = None) -> Path:
    env = os.environ.get("ES_PROJECT_ROOT")
    if env:
        root = Path(env).resolve()
        if (root / CONFIG_REL).exists():
            return root
        raise ConfigError(f"ES_PROJECT_ROOT={env} has no {CONFIG_REL}")
    start = (start or Path.cwd()).resolve()
    for cand in (start, *start.parents):
        if (cand / CONFIG_REL).exists():
            return cand
    raise ConfigError(f"no {CONFIG_REL} found in {start} or any parent (set ES_PROJECT_ROOT)")


@dataclass(frozen=True)
class LayerRule:
    from_layer: str
    to_layer: str
    allow: str  # "importers" | "imported" | "any" | "none"
    file: str | None = None


@dataclass(frozen=True)
class Layer:
    name: str
    prefixes: tuple[str, ...]
    generated: bool = False  # claims only modules meeting the [certificates] criteria
    exclude_from_root: tuple[str, ...] = ()
    inputs_of: str | None = None  # claims the hand-written modules directly imported by that layer's modules
    members_file: str | None = None  # pinned member list (committed); the computed set must match it
    frozen_closure: bool = False  # the whole hand-written import closure of `inputs_of` may not change without a rebuild marker


@dataclass
class Config:
    root: Path
    raw: dict[str, Any] = field(default_factory=dict)

    # ---- generic accessors -------------------------------------------------
    def get(self, *keys: str, default: Any = None) -> Any:
        cur: Any = self.raw
        for k in keys:
            if not isinstance(cur, dict) or k not in cur:
                return default
            cur = cur[k]
        return cur

    def require(self, *keys: str) -> Any:
        val = self.get(*keys, default=None)
        if val is None:
            raise ConfigError(f"config.toml is missing [{'.'.join(keys[:-1])}] {keys[-1]}")
        return val

    def path(self, *keys: str, default: str | None = None) -> Path:
        val = self.get(*keys, default=default)
        if val is None:
            raise ConfigError(f"config.toml is missing path [{'.'.join(keys[:-1])}] {keys[-1]}")
        return self.root / val

    # ---- project -----------------------------------------------------------
    @property
    def project_id(self) -> str:
        return str(self.require("project", "id"))

    @property
    def blueprint_namespace(self) -> str:
        return str(self.require("project", "blueprint_namespace"))

    @property
    def blueprint_root(self) -> Path:
        return self.path("project", "blueprint_root", default=f"{self.blueprint_namespace}.lean")

    @property
    def core_namespace(self) -> str:
        return str(self.require("project", "core_namespace"))

    @property
    def core_root_module(self) -> str:
        return str(self.get("project", "core_root_module", default=self.core_namespace))

    @property
    def closed_target_default(self) -> str:
        return str(self.get("project", "closed_target_default", default=f"{self.core_namespace}.Closed"))

    @property
    def workstreams(self) -> list[str]:
        return [str(w) for w in self.require("project", "workstreams")]

    @property
    def declaration_namespace(self) -> str:
        """Lean namespace node declarations live in (default: the core namespace)."""
        return str(self.get("project", "declaration_namespace", default=self.core_namespace))

    # ---- git ---------------------------------------------------------------
    @property
    def git_dir(self) -> Path | None:
        val = self.get("git", "git_dir")
        if not val:
            return None
        # A linked worktree's .git file names its worktree-specific metadata
        # directory.  Reusing a configured path relative to the primary
        # checkout would either be absent here or, if symlinked, select the
        # primary checkout's HEAD instead of this worktree's branch.
        gitfile = self.root / ".git"
        try:
            if gitfile.is_file():
                text = gitfile.read_text().strip()
                if text.startswith("gitdir:"):
                    path = Path(text[len("gitdir:"):].strip())
                    return path if path.is_absolute() else (self.root / path).resolve()
        except OSError:
            pass
        path = Path(str(val))
        return path if path.is_absolute() else self.root / path

    @property
    def default_branch(self) -> str:
        return str(self.get("git", "default_branch", default="main"))

    @property
    def git_remote(self) -> str:
        return str(self.get("git", "remote", default="origin"))

    # ---- layers ------------------------------------------------------------
    @property
    def layer_order(self) -> list[str]:
        return [str(x) for x in self.require("layers", "order")]

    def layers(self) -> list[Layer]:
        out = []
        for name in self.layer_order:
            spec = self.get("layers", name)
            if not isinstance(spec, dict):
                raise ConfigError(f"[layers.{name}] table missing")
            out.append(
                Layer(
                    name=name,
                    prefixes=tuple(str(p) for p in spec.get("prefixes", [])),
                    generated=bool(spec.get("generated", False)),
                    exclude_from_root=tuple(str(x) for x in spec.get("exclude_from_root", [])),
                    inputs_of=spec.get("inputs_of"),
                    members_file=spec.get("members_file"),
                    frozen_closure=bool(spec.get("frozen_closure", False)),
                )
            )
        return out

    def layer(self, name: str) -> Layer:
        for layer in self.layers():
            if layer.name == name:
                return layer
        raise ConfigError(f"unknown layer {name}")

    def layer_rules(self) -> list[LayerRule]:
        rules = self.get("layers", "rules", default=[]) or []
        out = []
        for r in rules:
            out.append(
                LayerRule(
                    from_layer=str(r["from"]),
                    to_layer=str(r["to"]),
                    allow=str(r.get("allow", "any")),
                    file=r.get("file"),
                )
            )
        return out

    @property
    def blueprint_layer(self) -> str:
        return str(self.get("layers", "blueprint", default=self.blueprint_namespace))

    @property
    def core_layer(self) -> str:
        return str(self.get("layers", "core", default="ESCore"))

    @property
    def certificates_layer(self) -> str | None:
        val = self.get("layers", "certificates")
        return str(val) if val else None

    # ---- certificates ------------------------------------------------------
    @property
    def generated_patterns(self) -> list[str]:
        return [str(p) for p in self.get("certificates", "generated_patterns", default=[])]

    @property
    def generated_marker(self) -> str | None:
        return self.get("certificates", "generated_marker")

    @property
    def generated_marker_lines(self) -> int:
        return int(self.get("certificates", "marker_lines", default=12))

    # ---- audit -------------------------------------------------------------
    @property
    def standard_axioms(self) -> list[str]:
        return [str(a) for a in self.get("audit", "standard_axioms", default=[])]

    @property
    def destinations_file(self) -> Path:
        return self.path("audit", "destinations_file", default="harness/destinations.txt")

    @property
    def allowlist_file(self) -> Path:
        return self.path("audit", "allowlist_file", default="harness/allowlist.json")

    # ---- harness files -----------------------------------------------------
    @property
    def harness_dir(self) -> Path:
        return self.root / "harness"

    @property
    def lock_file(self) -> Path:
        return self.path("harness", "lock_file", default="harness/statements.lock")

    @property
    def restatements_file(self) -> Path:
        return self.path("harness", "restatements_file", default="harness/restatements.md")

    @property
    def retired_file(self) -> Path:
        return self.path("harness", "retired_file", default="harness/retired.md")

    @property
    def nodes_json(self) -> Path:
        return self.path("harness", "nodes_json", default="harness/nodes.json")

    @property
    def index_json(self) -> Path:
        return self.path("harness", "index_json", default="harness/index.json")

    @property
    def status_md(self) -> Path:
        return self.path("harness", "status_md", default="harness/status.md")

    @property
    def notes_dir(self) -> Path:
        return self.path("harness", "notes_dir", default="docs/notes")

    # ---- build -------------------------------------------------------------
    @property
    def lake(self) -> str:
        configured = str(self.get("build", "lake", default="lake"))
        # User services may omit elan's bin directory from PATH. Honor custom
        # executables and PATH first; the standard elan shim remains portable
        # across user home directories and selects this checkout's toolchain.
        if configured == "lake" and shutil.which(configured) is None:
            shim = Path.home() / ".elan" / "bin" / "lake"
            if shim.is_file() and os.access(shim, os.X_OK):
                return str(shim)
        return configured

    @property
    def core_budget_min(self) -> int:
        return int(self.get("build", "core_budget_min", default=10))

    @property
    def build_guard(self) -> bool:
        return bool(self.get("build", "guard", default=True))

    @property
    def build_memory_max(self) -> str:
        return str(self.get("build", "memory_max", default="20G"))

    @property
    def build_elaborate_memory_base(self) -> str:
        """Fixed part of the cap for building one small module (see `elaboration_memory_max`)."""
        return str(self.get("build", "elaborate_memory_base", default="3G"))

    @property
    def build_elaborate_memory_per_olean_gib(self) -> float:
        """GiB of cap per GiB of project oleans in the module's import closure."""
        return float(self.get("build", "elaborate_memory_per_olean_gib", default=4))

    @property
    def build_elaborate_memory_min(self) -> str:
        return str(self.get("build", "elaborate_memory_min", default="4G"))

    @property
    def build_nobuild_memory_max(self) -> str:
        """Cap for `lake build --no-build` (is the closure current?); measured peak about 0.85 GiB."""
        return str(self.get("build", "nobuild_memory_max", default="2G"))

    @property
    def jobs_review_after_min(self) -> int:
        """Minutes a job runs before its first progress review (`es job review`); a review
        checkpoint never stops the job.  0 disables checkpoints."""
        return int(self.get("jobs", "review_after_min", default=20))

    @property
    def commit_memory_max(self) -> str:
        """Reservation for a queued `es node commit` job (git only)."""
        return str(self.get("jobs", "commit_memory_max", default="1G"))

    @property
    def build_cpu_quota(self) -> int:
        return int(self.get("build", "cpu_quota_cores", default=0))

    @property
    def build_threads(self) -> int:
        return int(self.get("build", "lean_threads", default=0))

    @property
    def build_serial_missing(self) -> bool:
        return bool(self.get("build", "serial_missing", default=True))

    def build_targets(self, kind: str) -> list[str]:
        val = self.get("build", "targets", kind)
        if val is None:
            raise ConfigError(f"[build.targets] {kind} not configured")
        return [str(x) for x in val]

    @property
    def build_log_dir(self) -> Path:
        return self.es_home / "logs"

    @property
    def build_setup_cleanup_enabled(self) -> bool:
        return bool(self.get("build", "setup_metadata_cleanup", "enabled", default=False))

    @property
    def build_setup_cleanup_ir_dir(self) -> Path:
        value = str(self.get("build", "setup_metadata_cleanup", "ir_dir", default=".lake/build/ir"))
        return Path(value)

    @property
    def build_setup_cleanup_toolchain(self) -> str:
        return str(self.get("build", "setup_metadata_cleanup", "toolchain", default="leanprover/lean4:v4.29.1"))

    @property
    def build_artifact_cache_enabled(self) -> bool:
        return bool(self.get("build", "artifact_cache", "enabled", default=False))

    @property
    def build_artifact_cache_root(self) -> Path | None:
        value = self.get("build", "artifact_cache", "root")
        if value is None or not str(value).strip():
            return None
        path = Path(str(value)).expanduser()
        return path if path.is_absolute() else self.root / path

    # ---- extract -----------------------------------------------------------
    @property
    def extract_template(self) -> Path:
        val = self.get("extract", "template")
        if val:
            return self.root / val
        return Path(__file__).resolve().parent.parent / "lean" / "Extract.lean.tmpl"

    @property
    def extract_script(self) -> Path:
        return self.path("extract", "script", default=f"{self.blueprint_namespace}/Extract.lean")

    @property
    def extract_memory_max(self) -> str:
        # ES_EXTRACT_MEMORY_MAX overrides the configured cap for one invocation (the guard
        # needs cap + 6 GiB available; the extractor's measured peak is logged as an "extract" event).
        env = os.environ.get("ES_EXTRACT_MEMORY_MAX")
        return env if env else str(self.get("extract", "memory_max", default="36G"))

    @property
    def extract_full_memory_max(self) -> str:
        """Sized first-attempt cap for a full extract. Over ~120 recorded full extracts the steady-state
        peak (cgroup memory.peak, page cache included) was about 5.3 GiB; the rare cold runs that
        rebuild heavy modules reached the full cap. An OOM kill under this cap is retried once at
        `extract_memory_max`. ES_EXTRACT_MEMORY_MAX pins both attempts to one cap."""
        env = os.environ.get("ES_EXTRACT_MEMORY_MAX")
        return env if env else str(self.get("extract", "full_memory_max", default="12G"))

    @property
    def extract_budget_min(self) -> int:
        return int(self.get("extract", "budget_min", default=120))

    @property
    def extract_targeted_memory_max(self) -> str:
        """Cap for a targeted extract (one node module and its import closure only)."""
        return str(self.get("extract", "targeted_memory_max", default="12G"))

    @property
    def extract_targeted_memory_base(self) -> str:
        """Fixed part of a targeted extract's sized cap (measured peak about 2.2 GiB over a thin closure)."""
        return str(self.get("extract", "targeted_memory_base", default="3G"))

    @property
    def extract_targeted_memory_per_olean_gib(self) -> float:
        return float(self.get("extract", "targeted_memory_per_olean_gib", default=2))

    @property
    def extract_targeted_memory_min(self) -> str:
        return str(self.get("extract", "targeted_memory_min", default="4G"))

    @property
    def extract_targeted_max_olean_gib(self) -> float:
        """Largest import closure (project olean bytes) a targeted extract may attempt under that cap."""
        return float(self.get("extract", "targeted_max_olean_gib", default=4))

    @property
    def extract_index_layers(self) -> list[str]:
        return [str(x) for x in self.get("extract", "index_layers", default=[self.core_layer])]

    @property
    def extract_import_modules(self) -> list[str]:
        return [str(x) for x in self.get("extract", "imports", default=[self.blueprint_namespace, self.core_root_module])]

    @property
    def taint_dir(self) -> Path:
        val = self.get("extract", "taint_dir")
        return Path(val).expanduser() if val else self.es_home / "taint"

    # ---- claims / falsify / jobs / node ------------------------------------
    @property
    def claim_ttl_hours(self) -> float:
        return float(self.get("claims", "ttl_hours", default=12))

    @property
    def falsifiers_dir(self) -> Path:
        return self.path("falsify", "falsifiers_dir", default="harness/falsifiers")

    @property
    def dataset_dir(self) -> Path:
        return self.path("falsify", "dataset_dir", default="harness/dataset")

    @property
    def falsify_results_dir(self) -> Path:
        return self.path("falsify", "results_dir", default="harness/falsify")

    @property
    def falsify_timeout_min(self) -> int:
        return int(self.get("falsify", "timeout_min", default=60))

    @property
    def falsify_memory_max(self) -> str | None:
        """cgroup MemoryMax for falsifier runs (e.g. "8G"); empty or missing = unguarded."""
        value = self.get("falsify", "memory_max", default="")
        return str(value) or None

    @property
    def max_parallel_builds(self) -> int:
        primary = primary_root(self.root)
        if primary != self.root:
            return load_config(primary).max_parallel_builds
        return int(self.get("jobs", "max_parallel_builds", default=1))

    @property
    def claims_require_why(self) -> bool:
        """`es claim` needs --why (what the agent intends to do)."""
        return bool(self.get("claims", "require_why", default=True))

    @property
    def jobs_memory_budget(self) -> str:
        """Sum of the memory caps of live jobs (queued or running) may not exceed this."""
        primary = primary_root(self.root)
        if primary != self.root:
            return load_config(primary).jobs_memory_budget
        return str(self.get("jobs", "memory_budget", default="30G"))

    @property
    def jobs_default_memory_max(self) -> str:
        return str(self.get("jobs", "default_memory_max", default="2G"))

    @property
    def jobs_run_margin_gib(self) -> float:
        """`es job run` needs cap + margin GiB available at submission."""
        return float(self.get("jobs", "run_margin_gib", default=2))

    @property
    def jobs_output_roots(self) -> list[str]:
        """Directories (relative to the root) under which `es job run --out` paths must lie."""
        return [str(x) for x in self.get("jobs", "output_roots", default=["runs", "data"])]

    @property
    def node_default_import(self) -> str:
        return str(self.get("node", "default_import", default=self.core_root_module))

    @property
    def node_template(self) -> Path:
        val = self.get("node", "template")
        if val:
            return self.root / val
        return Path(__file__).resolve().parent.parent / "templates" / "node.lean.tmpl"

    # ---- home --------------------------------------------------------------
    @property
    def es_home(self) -> Path:
        """Where the database, logs, extract cache and taint cache live: ES_HOME, else
        `[project] es_home` (relative to the root, so a sandboxed agent that may only write
        the checkout can write it), else ~/.es; always suffixed with the project id."""
        base = os.environ.get("ES_HOME")
        if base:
            home = Path(base).expanduser()
        else:
            val = self.get("project", "es_home")
            # relative to the primary checkout: a worktree shares the state of the checkout it belongs to
            home = (primary_root(self.root) / str(val)).resolve() if val else Path.home() / ".es"
        return home / self.project_id

    @property
    def db_path(self) -> Path:
        return self.es_home / "es.db"


def load_config(root: Path | None = None) -> Config:
    root = root or find_root()
    path = root / CONFIG_REL
    try:
        raw = tomllib.loads(path.read_text())
    except (OSError, tomllib.TOMLDecodeError) as exc:
        raise ConfigError(f"cannot read {path}: {exc}") from exc
    cfg = Config(root=root, raw=raw)
    validate(cfg)
    return cfg


def validate(cfg: Config) -> list[str]:
    problems: list[str] = []
    for key in (("project", "id"), ("project", "blueprint_namespace"), ("project", "core_namespace"),
                ("project", "workstreams"), ("layers", "order")):
        if cfg.get(*key) is None:
            problems.append(f"missing [{key[0]}] {key[1]}")
    if not problems:
        names = {layer.name for layer in cfg.layers()}
        for rule in cfg.layer_rules():
            for side in (rule.from_layer, rule.to_layer):
                if side not in names:
                    problems.append(f"layer rule refers to unknown layer {side}")
            if rule.allow not in ("importers", "imported", "any", "none"):
                problems.append(f"layer rule {rule.from_layer}->{rule.to_layer}: bad allow={rule.allow}")
            if rule.allow in ("importers", "imported") and not rule.file:
                problems.append(f"layer rule {rule.from_layer}->{rule.to_layer} needs a file")
        if cfg.blueprint_layer not in names:
            problems.append(f"[layers] blueprint={cfg.blueprint_layer} is not a layer")
        if cfg.core_layer not in names:
            problems.append(f"[layers] core={cfg.core_layer} is not a layer")
    ir_dir = cfg.build_setup_cleanup_ir_dir
    if ir_dir.is_absolute() or not ir_dir.parts or any(part in ("", ".", "..") for part in ir_dir.parts):
        problems.append("[build.setup_metadata_cleanup] ir_dir must be a normalized relative path")
    if cfg.build_setup_cleanup_enabled and not cfg.build_setup_cleanup_toolchain.strip():
        problems.append("[build.setup_metadata_cleanup] toolchain must be nonempty when enabled")
    if problems:
        raise ConfigError("; ".join(problems))
    return problems
