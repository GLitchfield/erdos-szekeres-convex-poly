#!/usr/bin/env python3
"""Build a deterministic genomes-only Factory v3 divergence context.

The allowlist is deliberately explicit.  Whole files may enter only through
``substrate``; failure genomes enter as individually hash-committed extracts
from their durable homes.  In particular, lowering an inline-size limit on the
whole-project packet is not an implementation of this projection.
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import re
from pathlib import Path, PurePosixPath
from typing import Any


class ContextError(ValueError):
    """A frozen context contract is malformed or does not authenticate."""


CORE_FIELDS = (
    "verified failing feature",
    "strongest supported statement",
    "evidence level",
    "damage scope",
    "representation blindness",
    "candidate discriminator",
    "mutation directions",
    "anti-duplication warning",
    "cheapest falsifier",
)
TAGGED_FIELDS = CORE_FIELDS[4:]
TAGS = ("verified", "inferred", "not-established")
REQUIRED_EXCLUDED_GLOBS = (
    "**/prior-idea-registry.json",
    "**/prior-idea-registry.md",
    "**/ideas.md",
    "runs/idea-factory/idea-ledger.md",
    "**/transcript.txt",
    "**/transcript.md",
    "**/*-transcript.txt",
    "**/*-transcript.md",
    "**/provider-output.*",
    "**/provider-response.*",
    "**/raw-response.*",
    "**/raw-review.*",
)
BASE_GENOME_SOURCES = (
    "runs/idea-factory/idea-ledger.md",
    "docs/wayfinder/frontier-portfolio.md",
)
REQUIRED_SUBSTRATE_ROLES = {
    "readme",
    "wayfinder_map",
    "frontier_portfolio",
    "lean_declaration_index",
    "literature_review",
    "bibliography",
    "model_proof_distance_rules",
    "batch012_aggregate_baseline",
}
FIXED_ROLE_PATHS = {
    "readme": "README.md",
    "wayfinder_map": "docs/wayfinder/map.md",
    "frontier_portfolio": "docs/wayfinder/frontier-portfolio.md",
    "literature_review": "docs/literature_review.md",
    "bibliography": "docs/bibliography.md",
    "model_proof_distance_rules": "AGENTS.md",
}
DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive)\s+([^\s:{(]+)"
)
BATCH012_ATTRITION = {
    "collision": 31,
    "target_or_producer": 15,
    "missing_consumer_or_two_transfer": 13,
    "source_or_model": 9,
    "invalid_gate": 8,
    "final": 4,
}
BATCH012_SOURCE_PATHS = (
    "docs/wayfinder/tickets/0068-run-post-batch011-factory-refresh.md",
    "runs/agents/20260822-sol-idea-loop/batch-012-v2-process-memory-audit/report.md",
    "runs/agents/20260822-sol-idea-loop/batch-012-v2-process-memory-audit/result.json",
)
BATCH012_BASELINE_KEYS = {
    "schema_version", "terminal", "private_raw_count", "exposed_idea_count",
    "source_chain_count", "evidence_level", "damage_scope",
    "admitted_genome_count", "new_route_count", "dependency_edge_change_count",
    "contains_candidate_text", "attrition", "sources",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def compact_hash(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"))
    return sha256(payload.encode("utf-8"))


def unique_json_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, child in pairs:
        if key in value:
            raise ContextError("duplicate JSON key is forbidden")
        value[key] = child
    return value


def lean_sources(root: Path) -> list[Path]:
    sources: set[Path] = set()
    root_source = root / "ErdosSzekeres.lean"
    if root_source.is_file():
        sources.add(root_source)
    source_dir = root / "ErdosSzekeres"
    if source_dir.is_dir():
        sources.update(path for path in source_dir.rglob("*.lean") if path.is_file())
    return sorted(sources, key=lambda path: path.relative_to(root).as_posix())


def render_lean_declaration_index(root: Path) -> str:
    sources = lean_sources(root)
    if not sources:
        raise ContextError("the repository has no Lean sources to index")
    source_rows: list[dict[str, Any]] = []
    declaration_lines: list[str] = []
    for path in sources:
        name = path.relative_to(root).as_posix()
        data = path.read_bytes()
        source_rows.append({"path": name, "sha256": sha256(data), "bytes": len(data)})
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise ContextError(f"Lean source is not UTF-8: {name}") from exc
        for line_no, line in enumerate(text.splitlines(), start=1):
            match = DECL_RE.match(line)
            if match:
                declaration_lines.append(
                    f"- `{name}:{line_no}` {match.group(1)} `{match.group(2)}`"
                )
    lines = [
        "# Complete Lean declaration index",
        "",
        f"Source inventory SHA-256: `{compact_hash(source_rows)}`",
        f"Source count: {len(source_rows)}",
        f"Declaration count: {len(declaration_lines)}",
        "",
        "## Authenticated sources",
        "",
        *(
            f"- `{row['path']}` SHA-256 `{row['sha256']}` bytes `{row['bytes']}`"
            for row in source_rows
        ),
        "",
        "## Declarations",
        "",
        *declaration_lines,
        "",
    ]
    return "\n".join(lines)


def ticket_source_rows(root: Path) -> list[dict[str, Any]]:
    ticket_dir = root / "docs/wayfinder/tickets"
    paths = sorted(
        (path for path in ticket_dir.glob("*.md") if path.is_file()),
        key=lambda path: path.relative_to(root).as_posix(),
    ) if ticket_dir.is_dir() else []
    return [
        {
            "path": path.relative_to(root).as_posix(),
            "sha256": sha256(path.read_bytes()),
        }
        for path in paths
    ]


def render_ticket_source_inventory(root: Path) -> str:
    rows = ticket_source_rows(root)
    return json.dumps({
        "schema_version": 1,
        "purpose": "extraction-only fallback homes for admitted failure genomes",
        "entry_count": len(rows),
        "aggregate_sha256": compact_hash(rows),
        "entries": rows,
    }, indent=2, sort_keys=True) + "\n"


def validate_batch012_baseline(root: Path, data: bytes) -> None:
    try:
        value = json.loads(data.decode("utf-8"), object_pairs_hook=unique_json_object)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ContextError("Batch012 aggregate baseline must be UTF-8 JSON") from exc
    expected_scalars = {
        "schema_version": 1,
        "terminal": "FACTORY-NOVELTY-STOP",
        "private_raw_count": 80,
        "exposed_idea_count": 0,
        "source_chain_count": 13,
        "evidence_level": "proposal",
        "damage_scope": "operational-only",
        "admitted_genome_count": 0,
        "new_route_count": 0,
        "dependency_edge_change_count": 0,
        "contains_candidate_text": False,
    }
    if (
        not isinstance(value, dict)
        or set(value) != BATCH012_BASELINE_KEYS
        or any(value.get(key) != expected for key, expected in expected_scalars.items())
    ):
        raise ContextError("Batch012 aggregate baseline scalar contract mismatch")
    if value.get("attrition") != BATCH012_ATTRITION or sum(BATCH012_ATTRITION.values()) != 80:
        raise ContextError("Batch012 aggregate baseline attrition mismatch")
    sources = value.get("sources")
    if not isinstance(sources, list) or len(sources) != len(BATCH012_SOURCE_PATHS):
        raise ContextError("Batch012 aggregate baseline must authenticate its exact sources")
    if [item.get("path") for item in sources if isinstance(item, dict)] != list(BATCH012_SOURCE_PATHS):
        raise ContextError("Batch012 aggregate baseline source-path contract mismatch")
    for index, item in enumerate(sources):
        if not isinstance(item, dict) or set(item) != {"path", "sha256"}:
            raise ContextError(f"Batch012 baseline sources[{index}] is malformed")
        _, source_path = repo_path(root, item["path"], f"Batch012 baseline sources[{index}]")
        if sha256(source_path.read_bytes()) != item["sha256"]:
            raise ContextError(f"Batch012 baseline source hash mismatch at index {index}")


def load_object(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=unique_json_object
        )
    except (OSError, json.JSONDecodeError) as exc:
        raise ContextError(f"cannot parse {label} {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise ContextError(f"{label} must be a JSON object")
    return value


def repo_path(root: Path, value: Any, label: str) -> tuple[str, Path]:
    if not isinstance(value, str) or not value:
        raise ContextError(f"{label} must be a nonempty repository-relative path")
    relative = PurePosixPath(value)
    if relative.is_absolute() or ".." in relative.parts:
        raise ContextError(f"{label} must stay inside the repository: {value}")
    path = root.joinpath(*relative.parts)
    if not path.is_file():
        raise ContextError(f"{label} does not exist: {value}")
    return relative.as_posix(), path


def matches(path: str, patterns: list[str]) -> bool:
    pure = PurePosixPath(path)
    return any(fnmatch.fnmatch(path, pattern) or pure.match(pattern) for pattern in patterns)


def unique_field_line(block: str, field: str) -> str:
    found = [line for line in block.splitlines() if field in line.casefold()]
    if len(found) != 1:
        raise ContextError(
            f"failure genome must contain exactly one {field!r} field; found {len(found)}"
        )
    return found[0]


def genome_field_name(line: str) -> str | None:
    folded = line.casefold()
    if "failure-genome subject" in folded or (
        line.lstrip().startswith("|") and "| subject |" in folded
    ):
        return "subject"
    for field in CORE_FIELDS:
        if field in folded:
            return field
    return None


def markdown_block_starter(stripped: str) -> bool:
    """Reject block syntax that cannot be a wrapped genome-field sentence."""
    if re.match(
        r"^(?:#{1,6}(?:\s|$)|[-*+](?:\s|$)|\d{1,9}[.)](?:\s|$)|>|```|~~~|\||\[[^\]]+\]:)",
        stripped,
    ):
        return True
    if re.fullmatch(r"(?:[-*_]\s*){3,}", stripped) or re.fullmatch(r"[=-]+", stripped):
        return True
    return re.match(
        r"^<(?:/?[A-Za-z][A-Za-z0-9-]*(?:\s|/?>|$)|!--|!\[CDATA\[|![A-Z]|\?)",
        stripped,
    ) is not None


def validate_exact_genome_shape(block: str) -> None:
    lines = block.rstrip("\n").splitlines()
    expected = ["subject", *CORE_FIELDS]
    if not lines:
        raise ContextError("failure genome is empty")
    if lines[0].startswith("- **Failure-genome subject:**"):
        seen: list[str] = []
        for line in lines:
            if line.startswith("- **"):
                field = genome_field_name(line)
                if field is None:
                    raise ContextError("failure genome has an extra top-level bullet field")
                seen.append(field)
            else:
                stripped = line.strip()
                if (
                    not line.startswith("  ")
                    or line.startswith("    ")
                    or not stripped
                    or markdown_block_starter(stripped)
                ):
                    raise ContextError("failure genome has trailing or unscoped prose")
        if seen != expected:
            raise ContextError(f"failure-genome bullet field order mismatch: {seen}")
        return
    if lines[0].lstrip().startswith("| Subject |"):
        if len(lines) != len(expected):
            raise ContextError("failure-genome table must contain exactly ten field rows")
        seen = []
        for line in lines:
            if not line.startswith("|") or not line.endswith("|"):
                raise ContextError("failure-genome table has trailing or unscoped prose")
            field = genome_field_name(line)
            if field is None:
                raise ContextError("failure-genome table has an extra field row")
            seen.append(field)
        if seen != expected:
            raise ContextError(f"failure-genome table field order mismatch: {seen}")
        return
    raise ContextError("failure genome must start at its subject bullet or table row")


def validate_genome(block: str, entry: dict[str, Any]) -> None:
    validate_exact_genome_shape(block)
    subject_lines = [
        line for line in block.splitlines()
        if "failure-genome subject" in line.casefold()
        or (line.lstrip().startswith("|") and "| subject |" in line.casefold())
    ]
    if len(subject_lines) != 1:
        raise ContextError("failure genome must contain exactly one subject field")
    subject_index = block.splitlines().index(subject_lines[0])
    block_lines = block.splitlines()
    subject_parts: list[str] = []
    for line in block_lines[subject_index:]:
        if subject_parts and (
            "verified failing feature" in line.casefold()
            or (line.lstrip().startswith("|") and "| verified failing feature |" in line.casefold())
        ):
            break
        subject_parts.append(line)
    subject = " ".join(part.strip() for part in subject_parts)
    if "terminal" not in subject.casefold() or "sha-256" not in subject.casefold():
        raise ContextError("failure-genome subject must name a terminal and SHA-256 evidence")
    if re.search(r"(?<![0-9a-f])[0-9a-f]{64}(?![0-9a-f])", subject) is None:
        raise ContextError("failure-genome subject lacks a lowercase 64-hex evidence hash")

    terms = entry.get("subject_terms")
    if not isinstance(terms, list) or len(terms) < 3 or not all(
        isinstance(term, str) and term for term in terms
    ):
        raise ContextError("each genome requires at least three nonempty subject_terms")
    for term in terms:
        if term not in subject:
            raise ContextError(f"failure-genome subject omits committed term {term!r}")

    field_lines = {field: unique_field_line(block, field) for field in CORE_FIELDS}
    for field in TAGGED_FIELDS:
        line = field_lines[field].casefold()
        tags = [tag for tag in TAGS if tag in line]
        if len(tags) != 1:
            raise ContextError(f"{field} must carry exactly one verified/inferred/not-established tag")

    for key, field in (("evidence_level", "evidence level"), ("damage_scope", "damage scope")):
        expected = entry.get(key)
        if not isinstance(expected, str) or not expected:
            raise ContextError(f"genome {key} must be a nonempty string")
        if expected not in field_lines[field]:
            raise ContextError(f"genome {field} does not match committed {key} {expected!r}")


def extract_block(text: str, entry: dict[str, Any]) -> str:
    start = entry.get("start_marker")
    end = entry.get("end_marker")
    if not isinstance(start, str) or not start:
        raise ContextError("genome start_marker must be nonempty")
    if not isinstance(end, str) or not end:
        raise ContextError("genome end_marker must be nonempty")
    if text.count(start) != 1:
        raise ContextError(f"start_marker must occur exactly once: {start!r}")
    if text.count(end) != 1:
        raise ContextError(f"end_marker must occur exactly once: {end!r}")
    begin = text.index(start)
    finish = text.index(end)
    if finish <= begin:
        raise ContextError("genome end_marker must follow start_marker")
    return text[begin:finish].rstrip() + "\n"


def admitted_genome_anchors(text: str) -> list[int]:
    """Locate canonical admitted-genome subjects, ignoring fenced examples."""
    anchors: list[int] = []
    fenced = False
    offset = 0
    for line in text.splitlines(keepends=True):
        stripped = line.lstrip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            fenced = not fenced
        elif not fenced and (
            re.match(r"^- \*\*Failure-genome subject:\*\*", line) is not None
            or re.match(r"^\| Subject \|", line) is not None
        ):
            anchors.append(offset)
        offset += len(line)
    if fenced:
        raise ContextError("authorized genome source has an unterminated Markdown fence")
    return anchors


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def build_context(repo_root: Path, allowlist_path: Path, output_dir: Path) -> dict[str, Any]:
    root = repo_root.resolve()
    allowlist = load_object(allowlist_path, "allowlist")
    if allowlist.get("schema_version") != 1:
        raise ContextError("allowlist schema_version must be 1")

    substrate = allowlist.get("substrate")
    genomes = allowlist.get("genomes")
    authorized_sources = allowlist.get("authorized_genome_sources")
    ticket_inventory_ref = allowlist.get("ticket_genome_source_inventory")
    required = allowlist.get("required_substrate_paths")
    private_globs = allowlist.get("private_globs")
    extra_excluded = allowlist.get("excluded_globs", [])
    if not isinstance(substrate, list) or not substrate:
        raise ContextError("allowlist substrate must be a nonempty array")
    if not isinstance(genomes, list) or not genomes:
        raise ContextError("allowlist genomes must be a nonempty array")
    if not isinstance(authorized_sources, list):
        raise ContextError("authorized_genome_sources must be an array")
    if len(authorized_sources) != len(BASE_GENOME_SOURCES):
        raise ContextError("authorized_genome_sources has the wrong cardinality")
    authorized_by_path: dict[str, dict[str, Any]] = {}
    for index, item in enumerate(authorized_sources):
        if not isinstance(item, dict) or set(item) != {"path", "sha256"}:
            raise ContextError(
                f"authorized_genome_sources[{index}] must contain exactly path and sha256"
            )
        name = item["path"]
        if name in authorized_by_path:
            raise ContextError(f"duplicate authorized genome source: {name}")
        authorized_by_path[name] = item
    if set(authorized_by_path) != set(BASE_GENOME_SOURCES):
        raise ContextError(
            "authorized genome homes must be exactly the idea ledger and frontier portfolio"
        )
    if not isinstance(ticket_inventory_ref, dict) or set(ticket_inventory_ref) != {"path", "sha256"}:
        raise ContextError(
            "ticket_genome_source_inventory must contain exactly path and sha256"
        )
    ticket_inventory_name, ticket_inventory_path = repo_path(
        root, ticket_inventory_ref["path"], "ticket_genome_source_inventory"
    )
    ticket_inventory_data = ticket_inventory_path.read_bytes()
    if sha256(ticket_inventory_data) != ticket_inventory_ref["sha256"]:
        raise ContextError("ticket genome source inventory hash mismatch")
    expected_ticket_inventory = render_ticket_source_inventory(root)
    if ticket_inventory_data.decode("utf-8") != expected_ticket_inventory:
        raise ContextError("ticket genome source inventory is stale or incomplete")
    ticket_inventory = load_object(ticket_inventory_path, "ticket genome source inventory")
    ticket_rows = ticket_inventory.get("entries")
    if not isinstance(ticket_rows, list):
        raise ContextError("ticket genome source inventory entries must be an array")
    for index, item in enumerate(ticket_rows):
        if not isinstance(item, dict) or set(item) != {"path", "sha256"}:
            raise ContextError(f"ticket genome source inventory entries[{index}] is malformed")
        name = item["path"]
        if name in authorized_by_path:
            raise ContextError(f"duplicate authorized genome source: {name}")
        authorized_by_path[name] = item
    authorized_source_names = [*BASE_GENOME_SOURCES, *(item["path"] for item in ticket_rows)]
    if not isinstance(required, list) or not all(isinstance(x, str) and x for x in required):
        raise ContextError("required_substrate_paths must be an array of nonempty strings")
    if not isinstance(private_globs, list) or not private_globs or not all(
        isinstance(x, str) and x for x in private_globs
    ):
        raise ContextError("private_globs must explicitly name at least one private subtree")
    if not isinstance(extra_excluded, list) or not all(isinstance(x, str) and x for x in extra_excluded):
        raise ContextError("excluded_globs must be an array of nonempty strings")
    excluded = list(dict.fromkeys([*REQUIRED_EXCLUDED_GLOBS, *private_globs, *extra_excluded]))

    entries: list[dict[str, Any]] = []
    context_parts: list[str] = []
    substrate_paths: list[str] = []
    for index, item in enumerate(substrate):
        if not isinstance(item, dict) or set(item) != {"role", "path", "sha256"}:
            raise ContextError(f"substrate[{index}] must contain exactly role, path, and sha256")
        role = item["role"]
        if not isinstance(role, str) or role not in REQUIRED_SUBSTRATE_ROLES:
            raise ContextError(f"substrate[{index}] has an unknown required role")
        name, path = repo_path(root, item["path"], f"substrate[{index}]")
        fixed_path = FIXED_ROLE_PATHS.get(role)
        if fixed_path is not None and name != fixed_path:
            raise ContextError(f"substrate role {role} must use {fixed_path}")
        if role == "lean_declaration_index" and PurePosixPath(name).name != "lean-declarations.md":
            raise ContextError("Lean declaration index must use basename lean-declarations.md")
        if (
            role == "batch012_aggregate_baseline"
            and PurePosixPath(name).name != "batch012-aggregate-baseline.json"
        ):
            raise ContextError(
                "Batch012 aggregate baseline must use basename batch012-aggregate-baseline.json"
            )
        if name in substrate_paths:
            raise ContextError(f"duplicate substrate path: {name}")
        if matches(name, excluded):
            raise ContextError(f"excluded path cannot enter genomes-only substrate: {name}")
        data = path.read_bytes()
        digest = sha256(data)
        if digest != item["sha256"]:
            raise ContextError(f"substrate hash mismatch: {name}")
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise ContextError(f"substrate is not UTF-8: {name}") from exc
        if role == "lean_declaration_index" and text != render_lean_declaration_index(root):
            raise ContextError(
                "Lean declaration index is not the complete deterministic repository projection"
            )
        if role == "batch012_aggregate_baseline":
            validate_batch012_baseline(root, data)
        substrate_paths.append(name)
        entries.append({
            "kind": "substrate", "role": role, "path": name,
            "sha256": digest, "bytes": len(data),
        })
        context_parts.extend([f"## SUBSTRATE `{name}`", "", text.rstrip(), ""])

    if set(substrate_paths) != set(required):
        missing = sorted(set(required) - set(substrate_paths))
        extra = sorted(set(substrate_paths) - set(required))
        raise ContextError(f"substrate allowlist mismatch; missing={missing}, extra={extra}")
    roles = [item["role"] for item in substrate]
    if len(roles) != len(set(roles)) or set(roles) != REQUIRED_SUBSTRATE_ROLES:
        missing = sorted(REQUIRED_SUBSTRATE_ROLES - set(roles))
        extra = sorted(set(roles) - REQUIRED_SUBSTRATE_ROLES)
        raise ContextError(
            f"substrate role completeness mismatch; missing={missing}, extra={extra}, "
            f"duplicates={sorted(role for role in set(roles) if roles.count(role) > 1)}"
        )

    source_texts: dict[str, str] = {}
    source_anchors: dict[str, list[int]] = {}
    for source_name in authorized_source_names:
        _, source_path = repo_path(root, source_name, "authorized genome source")
        source_data = source_path.read_bytes()
        if sha256(source_data) != authorized_by_path[source_name]["sha256"]:
            raise ContextError(f"authorized genome source hash mismatch: {source_name}")
        try:
            source_texts[source_name] = source_data.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise ContextError(f"authorized genome source is not UTF-8: {source_name}") from exc
        source_anchors[source_name] = admitted_genome_anchors(source_texts[source_name])

    genome_ids: set[str] = set()
    genome_hashes: set[str] = set()
    covered_anchors: dict[str, set[int]] = {name: set() for name in authorized_source_names}
    for index, item in enumerate(genomes):
        if not isinstance(item, dict):
            raise ContextError(f"genomes[{index}] must be an object")
        expected_keys = {
            "id", "path", "source_sha256", "start_marker", "end_marker",
            "block_sha256", "subject_terms", "evidence_level", "damage_scope",
        }
        if set(item) != expected_keys:
            raise ContextError(f"genomes[{index}] must contain exactly {sorted(expected_keys)}")
        genome_id = item["id"]
        if not isinstance(genome_id, str) or not genome_id:
            raise ContextError(f"genomes[{index}].id must be nonempty")
        if genome_id in genome_ids:
            raise ContextError(f"duplicate genome id: {genome_id}")
        genome_ids.add(genome_id)
        source_name, source_path = repo_path(root, item["path"], f"genomes[{index}]")
        if source_name not in source_texts:
            raise ContextError(f"genome source is not an authorized durable home: {source_name}")
        if matches(source_name, private_globs):
            raise ContextError(f"private path cannot be a genome source: {source_name}")
        source_data = source_path.read_bytes()
        if sha256(source_data) != item["source_sha256"]:
            raise ContextError(f"genome source hash mismatch: {source_name}")
        try:
            source_text = source_data.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise ContextError(f"genome source is not UTF-8: {source_name}") from exc
        block = extract_block(source_text, item)
        block_start = source_text.index(item["start_marker"])
        block_end = source_text.index(item["end_marker"])
        contained = [
            anchor for anchor in source_anchors[source_name]
            if block_start <= anchor < block_end
        ]
        if len(contained) != 1:
            raise ContextError(
                f"genome extract {genome_id} must cover exactly one admitted subject anchor"
            )
        anchor = contained[0]
        if anchor in covered_anchors[source_name]:
            raise ContextError(f"admitted genome anchor covered twice: {genome_id}")
        covered_anchors[source_name].add(anchor)
        block_data = block.encode("utf-8")
        block_digest = sha256(block_data)
        if block_digest != item["block_sha256"]:
            raise ContextError(f"genome block hash mismatch: {genome_id}")
        if block_digest in genome_hashes:
            raise ContextError(f"duplicate genome block: {genome_id}")
        genome_hashes.add(block_digest)
        validate_genome(block, item)
        virtual_path = f"failure-genomes/{genome_id}.md"
        entries.append({
            "kind": "failure_genome",
            "id": genome_id,
            "path": virtual_path,
            "source_path": source_name,
            "source_sha256": item["source_sha256"],
            "sha256": block_digest,
            "bytes": len(block_data),
            "evidence_level": item["evidence_level"],
            "damage_scope": item["damage_scope"],
        })
        context_parts.extend([
            f"## FAILURE GENOME `{genome_id}`",
            "",
            f"Durable source: `{source_name}`  ",
            f"Extract SHA-256: `{block_digest}`",
            "",
            block.rstrip(),
            "",
        ])

    for source_name, anchors in source_anchors.items():
        missing = sorted(set(anchors) - covered_anchors[source_name])
        extra = sorted(covered_anchors[source_name] - set(anchors))
        if missing or extra:
            raise ContextError(
                f"failure-genome completeness mismatch in {source_name}; "
                f"missing_offsets={missing}, extra_offsets={extra}"
            )

    for entry in entries:
        if matches(entry["path"], excluded):
            raise ContextError(f"excluded path entered output manifest: {entry['path']}")

    aggregate = compact_hash(entries)
    header = [
        "# Factory v3 genomes-only divergence context",
        "",
        f"Manifest aggregate SHA-256: `{aggregate}`",
        "",
        "This context is an explicit projection. Failure-genome extracts are",
        "duplicate-avoidance constraints, not positive leads or route state.",
        "",
    ]
    context = "\n".join([*header, *context_parts]).rstrip() + "\n"
    manifest = {
        "schema_version": 1,
        "mode": "genomes-only",
        "aggregate_sha256": aggregate,
        "entry_count": len(entries),
        "substrate_count": len(substrate_paths),
        "genome_count": len(genome_ids),
        "exclusion_policy": (
            "prior-registry+prior-ideas+ledger-prose+review-provider-transcripts+private-subtrees"
        ),
        "exclusion_policy_sha256": compact_hash(sorted(excluded)),
        "excluded_pattern_count": len(excluded),
        "excluded_entry_count": 0,
        "entries": entries,
    }
    output_dir.mkdir(parents=True, exist_ok=True)
    write_json(output_dir / "manifest.json", manifest)
    (output_dir / "context.md").write_text(context, encoding="utf-8")
    summary = {
        "schema_version": 1,
        "mode": "genomes-only",
        "aggregate_sha256": aggregate,
        "entries": len(entries),
        "substrate": len(substrate_paths),
        "genomes": len(genome_ids),
        "manifest_sha256": sha256((output_dir / "manifest.json").read_bytes()),
        "context_sha256": sha256((output_dir / "context.md").read_bytes()),
    }
    write_json(output_dir / "packet-summary.json", summary)
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", required=True, type=Path)
    parser.add_argument("--allowlist", type=Path)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument(
        "--emit-lean-index",
        type=Path,
        help="write the complete authenticated Lean declaration projection and exit",
    )
    parser.add_argument(
        "--emit-ticket-source-inventory",
        type=Path,
        help="write the complete extraction-only decision-ticket inventory and exit",
    )
    args = parser.parse_args()
    root = args.repo_root.resolve()
    emit_modes = [
        value for value in (args.emit_lean_index, args.emit_ticket_source_inventory)
        if value is not None
    ]
    if emit_modes:
        if len(emit_modes) != 1 or args.allowlist is not None or args.output_dir is not None:
            parser.error("exactly one emit mode may be used without --allowlist/--output-dir")
        emit_path = emit_modes[0]
        output = (
            emit_path if emit_path.is_absolute() else root / emit_path
        )
        output.parent.mkdir(parents=True, exist_ok=True)
        content = (
            render_lean_declaration_index(root)
            if args.emit_lean_index is not None
            else render_ticket_source_inventory(root)
        )
        output.write_text(content, encoding="utf-8")
        print(json.dumps({
            "path": output.relative_to(root).as_posix(),
            "sha256": sha256(output.read_bytes()),
        }, sort_keys=True))
        return 0
    if args.allowlist is None or args.output_dir is None:
        parser.error("--allowlist and --output-dir are required unless an emit mode is used")
    allowlist = args.allowlist if args.allowlist.is_absolute() else root / args.allowlist
    output = args.output_dir if args.output_dir.is_absolute() else root / args.output_dir
    try:
        summary = build_context(root, allowlist.resolve(), output.resolve())
    except (ContextError, OSError) as exc:
        print(f"ERROR: {exc}")
        return 1
    print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
