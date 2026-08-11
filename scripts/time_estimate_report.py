#!/usr/bin/env python3
"""Summarize and validate the work-time estimation ledger."""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import statistics
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


DEFAULT_LEDGER = Path("docs/agents/time-estimates.csv")


@dataclass(frozen=True)
class CompletedEstimate:
    row_number: int
    task_id: str
    category: str
    forecast_low: float
    forecast_high: float
    actual_wall: float
    paused: float
    stored_ratio: float
    notes: str

    @property
    def active_wall(self) -> float:
        return self.actual_wall - self.paused

    @property
    def midpoint(self) -> float:
        return (self.forecast_low + self.forecast_high) / 2

    @property
    def ratio(self) -> float:
        return self.active_wall / self.midpoint

    @property
    def inside_forecast(self) -> bool:
        return self.forecast_low <= self.active_wall <= self.forecast_high

    @property
    def miss_score(self) -> float:
        if self.ratio <= 0:
            return math.inf
        return abs(math.log2(self.ratio))


def _number(row: dict[str, str], field: str, row_number: int) -> float:
    try:
        return float(row[field])
    except (KeyError, ValueError) as exc:
        raise ValueError(f"row {row_number}: invalid {field!r}") from exc


def load_completed(path: Path) -> list[CompletedEstimate]:
    completed: list[CompletedEstimate] = []
    with path.open(newline="", encoding="utf-8") as handle:
        for row_number, row in enumerate(csv.DictReader(handle), start=2):
            if row.get("status") != "completed":
                continue
            item = CompletedEstimate(
                row_number=row_number,
                task_id=row["id"],
                category=row["category"],
                forecast_low=_number(row, "forecast_low_minutes", row_number),
                forecast_high=_number(row, "forecast_high_minutes", row_number),
                actual_wall=_number(row, "actual_wall_minutes", row_number),
                paused=_number(row, "paused_minutes", row_number),
                stored_ratio=_number(row, "error_ratio", row_number),
                notes=row.get("notes", ""),
            )
            if item.forecast_low < 0 or item.forecast_high < item.forecast_low:
                raise ValueError(f"row {row_number}: invalid forecast interval")
            if item.active_wall < 0 or item.midpoint <= 0:
                raise ValueError(f"row {row_number}: invalid active wall time or midpoint")
            completed.append(item)
    return completed


def _summary(rows: Iterable[CompletedEstimate]) -> dict[str, object]:
    items = list(rows)
    if not items:
        return {"count": 0, "median_error_ratio": None, "inside_fraction": None}
    largest = max(items, key=lambda item: item.miss_score)
    return {
        "count": len(items),
        "median_error_ratio": statistics.median(item.ratio for item in items),
        "inside_fraction": sum(item.inside_forecast for item in items) / len(items),
        "largest_miss": {
            "id": largest.task_id,
            "error_ratio": largest.ratio,
            "active_wall_minutes": largest.active_wall,
            "forecast_low_minutes": largest.forecast_low,
            "forecast_high_minutes": largest.forecast_high,
            "notes": largest.notes,
        },
    }


def build_report(rows: list[CompletedEstimate]) -> dict[str, object]:
    categories = sorted({item.category for item in rows})
    return {
        "overall": _summary(rows),
        "categories": {
            category: _summary(item for item in rows if item.category == category)
            for category in categories
        },
    }


def ratio_mismatches(rows: Iterable[CompletedEstimate]) -> list[dict[str, object]]:
    mismatches = []
    for item in rows:
        expected = round(item.ratio, 3)
        if abs(item.stored_ratio - expected) > 0.0005:
            mismatches.append(
                {
                    "row": item.row_number,
                    "id": item.task_id,
                    "stored": item.stored_ratio,
                    "expected": expected,
                }
            )
    return mismatches


def rewrite_ratios(path: Path) -> int:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        fieldnames = reader.fieldnames
        if fieldnames is None:
            raise ValueError("ledger has no header")
        raw_rows = list(reader)
    completed = {item.row_number: item for item in load_completed(path)}
    changed = 0
    for row_number, row in enumerate(raw_rows, start=2):
        item = completed.get(row_number)
        if item is None:
            continue
        expected = f"{item.ratio:.3f}"
        if row["error_ratio"] != expected:
            row["error_ratio"] = expected
            changed += 1
    with tempfile.NamedTemporaryFile(
        "w", newline="", encoding="utf-8", dir=path.parent, delete=False
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        writer.writerows(raw_rows)
        temporary = Path(handle.name)
    os.replace(temporary, path)
    return changed


def _percent(value: object) -> str:
    return "n/a" if value is None else f"{100 * float(value):.1f}%"


def _ratio(value: object) -> str:
    return "n/a" if value is None else f"{float(value):.3f}"


def render_markdown(report: dict[str, object], mismatches: list[dict[str, object]]) -> str:
    overall = report["overall"]
    assert isinstance(overall, dict)
    lines = [
        "# Time-estimate calibration",
        "",
        f"Completed rows: {overall['count']}",
        f"Median error ratio: {_ratio(overall['median_error_ratio'])}",
        f"Inside forecast range: {_percent(overall['inside_fraction'])}",
        "",
        "## Categories",
        "",
        "| Category | Rows | Median ratio | Inside range |",
        "|---|---:|---:|---:|",
    ]
    categories = report["categories"]
    assert isinstance(categories, dict)
    for category, raw in categories.items():
        assert isinstance(raw, dict)
        lines.append(
            f"| {category} | {raw['count']} | {_ratio(raw['median_error_ratio'])} | "
            f"{_percent(raw['inside_fraction'])} |"
        )
    largest = overall.get("largest_miss")
    if isinstance(largest, dict):
        lines.extend(
            [
                "",
                "## Largest miss",
                "",
                f"`{largest['id']}`: ratio {_ratio(largest['error_ratio'])}; "
                f"active {largest['active_wall_minutes']:.0f} min versus "
                f"{largest['forecast_low_minutes']:.0f}–{largest['forecast_high_minutes']:.0f} min.",
                "",
                str(largest["notes"]),
            ]
        )
    lines.extend(["", "## Ledger validation", ""])
    if mismatches:
        lines.append(f"Stored error-ratio mismatches: {len(mismatches)}")
        for mismatch in mismatches:
            lines.append(
                f"- Row {mismatch['row']} `{mismatch['id']}`: "
                f"stored {mismatch['stored']:.3f}, expected {mismatch['expected']:.3f}"
            )
    else:
        lines.append("Stored error ratios agree with active wall time and forecast midpoints.")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("ledger", nargs="?", type=Path, default=DEFAULT_LEDGER)
    parser.add_argument("--json", action="store_true", help="emit JSON instead of Markdown")
    parser.add_argument(
        "--check-ratios",
        action="store_true",
        help="exit nonzero when a stored completed-row ratio is inconsistent",
    )
    parser.add_argument(
        "--rewrite-ratios",
        action="store_true",
        help="mechanically update completed-row ratios before reporting",
    )
    args = parser.parse_args()

    if args.rewrite_ratios:
        changed = rewrite_ratios(args.ledger)
        print(f"updated {changed} stored error ratios", file=sys.stderr)
    rows = load_completed(args.ledger)
    mismatches = ratio_mismatches(rows)
    report = build_report(rows)
    if args.json:
        print(json.dumps({**report, "ratio_mismatches": mismatches}, indent=2, sort_keys=True))
    else:
        print(render_markdown(report, mismatches), end="")
    return 1 if args.check_ratios and mismatches else 0


if __name__ == "__main__":
    raise SystemExit(main())
