#!/usr/bin/env python3
from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from check_frontier_portfolio import read_frontier_portfolio


FIELDS = """- **Contribution:** advance a live theorem.
- **Strategic role:** direct.
- **State:** advancing.
- **Model tier:** exact test model.
- **Best evidence:** proposal.
- **Downstream consumer:** a named theorem.
- **Open obstruction:** one obstruction.
- **Next discriminating gate:** one bounded gate.
- **Success payoff:** one payoff.
- **Expiry or revival gate:** one expiry condition.
- **Children:** none.
"""


def portfolio(entries: list[tuple[str, str]]) -> str:
    registry = "\n".join(
        f"### {identifier} — {title}\n\n{FIELDS}" for identifier, title in entries
    )
    return f"""---
title: Test frontier portfolio
artifact: frontier-portfolio
schema_version: 1
status: canonical
last_updated: 2026-08-12
---

# Frontier portfolio

## Formal definition

The execution slate obeys `E ⊆ P` and is separate from the registry.

## Record schema

Required fields.

## How to use the portfolio

Select a temporary execution slate.

## How to update the portfolio

Update evidence in place.

## Current registry

{registry}

## Current subthreads

None.

## Historical register

History.
"""


class FrontierPortfolioTest(unittest.TestCase):
    def write(self, text: str) -> tuple[tempfile.TemporaryDirectory[str], Path]:
        temporary = tempfile.TemporaryDirectory()
        path = Path(temporary.name) / "frontier-portfolio.md"
        path.write_text(text, encoding="utf-8")
        return temporary, path

    def test_reads_valid_portfolio(self) -> None:
        temporary, path = self.write(
            portfolio([("FP-01", "First route"), ("FP-02", "Second route")])
        )
        with temporary:
            entries = read_frontier_portfolio(path)
        self.assertEqual([entry.identifier for entry in entries], ["FP-01", "FP-02"])

    def test_rejects_missing_required_field(self) -> None:
        text = portfolio([("FP-01", "First route")]).replace(
            "- **Open obstruction:** one obstruction.\n", ""
        )
        temporary, path = self.write(text)
        with temporary, self.assertRaisesRegex(ValueError, "missing Open obstruction"):
            read_frontier_portfolio(path)

    def test_rejects_invalid_state(self) -> None:
        text = portfolio([("FP-01", "First route")]).replace(
            "- **State:** advancing.", "- **State:** fashionable."
        )
        temporary, path = self.write(text)
        with temporary, self.assertRaisesRegex(ValueError, "invalid state"):
            read_frontier_portfolio(path)

    def test_rejects_noncontiguous_identifiers(self) -> None:
        temporary, path = self.write(portfolio([("FP-02", "Second route")]))
        with temporary, self.assertRaisesRegex(ValueError, "contiguous and ordered"):
            read_frontier_portfolio(path)


if __name__ == "__main__":
    unittest.main()
