#!/usr/bin/env python3
"""Validate the canonical Wayfinder frontier-portfolio registry."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import date
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
PORTFOLIO_PATH = ROOT / "docs/wayfinder/frontier-portfolio.md"
MAP_PATH = ROOT / "docs/wayfinder/map.md"

FRONT_MATTER = {
    "title",
    "artifact",
    "schema_version",
    "status",
    "last_updated",
}
REQUIRED_SECTIONS = (
    "# Frontier portfolio",
    "## Formal definition",
    "## Record schema",
    "## Frontier execution cycle",
    "## How to use the portfolio",
    "## How to update the portfolio",
    "## Current registry",
    "## Current subthreads",
    "## Historical register",
)
REQUIRED_FIELDS = (
    "Contribution",
    "Mechanism family",
    "Named destination dependency",
    "Strategic role",
    "State",
    "Model tier",
    "Scope ceiling",
    "Best evidence",
    "Missing generalization bridge",
    "Last forward result",
    "Downstream consumer",
    "Open obstruction",
    "Next discriminating gate",
    "Success payoff",
    "Expiry or revival gate",
    "Children",
)
REQUIRED_CYCLE_STEPS = (
    "Close and integrate the previous run",
    "Reconcile this portfolio",
    "Select an execution slate of size `N`",
    "Plan the entire slate",
    "Execute the approved slate",
)
ALLOWED_ROLES = {
    "direct",
    "bridge",
    "generalization",
    "hedge",
    "fallback",
    "discovery",
    "research-system",
}
ALLOWED_STATES = {
    "advancing",
    "gated",
    "parked",
    "suspended",
    "merged",
    "completed",
    "retired",
}
ALLOWED_MECHANISM_FAMILIES = {
    "predecessor-half",
    "decomposable-pascal",
    "normalization-descent",
    "quantitative-cup-cap",
    "finite-exact-upper",
    "route-discovery",
    "research-system",
}
ENTRY_HEADING = re.compile(r"^### (FP-(\d{2})) — (.+)$", re.MULTILINE)
FIELD = re.compile(r"^- \*\*([^*]+):\*\*\s*(.*)$", re.MULTILINE)


@dataclass(frozen=True)
class FrontierEntry:
    identifier: str
    title: str
    fields: dict[str, str]


def _front_matter(lines: list[str], path: Path) -> tuple[dict[str, str], int]:
    if not lines or lines[0] != "---":
        raise ValueError(f"{path}: missing opening front-matter delimiter")
    try:
        end = lines.index("---", 1)
    except ValueError as error:
        raise ValueError(f"{path}: missing closing front-matter delimiter") from error

    metadata: dict[str, str] = {}
    for line in lines[1:end]:
        if ": " not in line:
            raise ValueError(f"{path}: invalid front-matter line {line!r}")
        key, value = line.split(": ", 1)
        if key in metadata:
            raise ValueError(f"{path}: duplicate front-matter field {key!r}")
        metadata[key] = value
    if set(metadata) != FRONT_MATTER:
        raise ValueError(
            f"{path}: front matter must contain exactly {sorted(FRONT_MATTER)}"
        )
    if metadata["artifact"] != "frontier-portfolio":
        raise ValueError(f"{path}: artifact must be 'frontier-portfolio'")
    if metadata["schema_version"] != "2":
        raise ValueError(f"{path}: schema_version must be 2")
    if metadata["status"] != "canonical":
        raise ValueError(f"{path}: status must be 'canonical'")
    try:
        date.fromisoformat(metadata["last_updated"])
    except ValueError as error:
        raise ValueError(f"{path}: last_updated must be an ISO date") from error
    return metadata, end + 1


def read_frontier_portfolio(path: Path = PORTFOLIO_PATH) -> list[FrontierEntry]:
    """Parse and validate a frontier portfolio, returning its main entries."""
    lines = path.read_text(encoding="utf-8").splitlines()
    _, body_start = _front_matter(lines, path)
    body = "\n".join(lines[body_start:])

    for section in REQUIRED_SECTIONS:
        if section not in body:
            raise ValueError(f"{path}: missing required section {section!r}")
    for step in REQUIRED_CYCLE_STEPS:
        if step not in body:
            raise ValueError(f"{path}: frontier execution cycle is missing {step!r}")
    if "E ⊆" not in body or "execution slate" not in body.lower():
        raise ValueError(
            f"{path}: must formally distinguish the portfolio from an execution slate"
        )

    registry_start = body.index("## Current registry")
    registry_end = body.index("## Current subthreads", registry_start)
    registry = body[registry_start:registry_end]
    matches = list(ENTRY_HEADING.finditer(registry))
    if not matches:
        raise ValueError(f"{path}: current registry has no FP-NN entries")

    entries: list[FrontierEntry] = []
    for index, match in enumerate(matches):
        start = match.end()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(registry)
        entry_body = registry[start:end]
        fields: dict[str, str] = {}
        for field_match in FIELD.finditer(entry_body):
            name, value = field_match.groups()
            if name in fields:
                raise ValueError(f"{path}: {match.group(1)} duplicates field {name!r}")
            fields[name] = value.strip()
        missing = sorted(set(REQUIRED_FIELDS) - fields.keys())
        extra = sorted(set(fields) - set(REQUIRED_FIELDS))
        if missing or extra:
            details: list[str] = []
            if missing:
                details.append(f"missing {', '.join(missing)}")
            if extra:
                details.append(f"unexpected {', '.join(extra)}")
            raise ValueError(f"{path}: {match.group(1)} " + "; ".join(details))
        empty = sorted(name for name, value in fields.items() if not value)
        if empty:
            raise ValueError(
                f"{path}: {match.group(1)} has empty first line for {', '.join(empty)}"
            )

        role = fields["Strategic role"].removesuffix(".")
        state = fields["State"].removesuffix(".")
        mechanism_family = fields["Mechanism family"].removesuffix(".")
        if role not in ALLOWED_ROLES:
            raise ValueError(f"{path}: {match.group(1)} has invalid role {role!r}")
        if state not in ALLOWED_STATES:
            raise ValueError(f"{path}: {match.group(1)} has invalid state {state!r}")
        if mechanism_family not in ALLOWED_MECHANISM_FAMILIES:
            raise ValueError(
                f"{path}: {match.group(1)} has invalid mechanism family "
                f"{mechanism_family!r}"
            )
        if state == "advancing" and fields["Last forward result"].lower().startswith(
            "none"
        ):
            raise ValueError(
                f"{path}: {match.group(1)} cannot be advancing without a last "
                "forward result"
            )
        entries.append(
            FrontierEntry(identifier=match.group(1), title=match.group(3), fields=fields)
        )

    identifiers = [entry.identifier for entry in entries]
    if len(set(identifiers)) != len(identifiers):
        raise ValueError(f"{path}: duplicate frontier identifier")
    expected = [f"FP-{index:02d}" for index in range(1, len(entries) + 1)]
    if identifiers != expected:
        raise ValueError(
            f"{path}: main identifiers must be contiguous and ordered; "
            f"expected {expected}, got {identifiers}"
        )

    subthreads = body[body.index("## Current subthreads"):]
    declared_children = {
        child
        for entry in entries
        for child in re.findall(r"FP-\d{2}\.[A-Z]", entry.fields["Children"])
    }
    for child in sorted(declared_children):
        if f"**{child} —" not in subthreads:
            raise ValueError(f"{path}: declared child {child} has no subthread entry")

    map_body = MAP_PATH.read_text(encoding="utf-8")
    if "## Load-bearing dependency ledger" not in map_body:
        raise ValueError(f"{MAP_PATH}: missing load-bearing dependency ledger")
    for edge in (
        "`D-LOWER`",
        "`D-MODEL`",
        "`D-UPPER`",
        "`D-HALF`",
        "`D-DECOMP`",
        "`D-NORMALIZE`",
        "`D-ASSEMBLE`",
    ):
        if edge not in map_body:
            raise ValueError(f"{MAP_PATH}: dependency ledger is missing {edge}")
    return entries


def main() -> None:
    entries = read_frontier_portfolio()
    states: dict[str, int] = {}
    for entry in entries:
        state = entry.fields["State"].removesuffix(".")
        states[state] = states.get(state, 0) + 1
    summary = ", ".join(f"{state}={count}" for state, count in sorted(states.items()))
    print(f"frontier portfolio OK: {len(entries)} threads ({summary})")


if __name__ == "__main__":
    main()
