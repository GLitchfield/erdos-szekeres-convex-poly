#!/usr/bin/env python3
from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from check_frontier_portfolio import read_frontier_portfolio


FIELDS = """- **Contribution:** advance a live theorem.
- **Mechanism family:** predecessor-half.
- **Named destination dependency:** `D-HALF`.
- **Strategic role:** direct.
- **State:** advancing.
- **Model tier:** exact test model.
- **Scope ceiling:** one exact finite test model; no uniform theorem.
- **Best evidence:** proposal.
- **Missing generalization bridge:** lift the finite statement uniformly.
- **Last forward result:** a compiling producer interface.
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
schema_version: 2
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

## Frontier execution cycle

1. **Close and integrate the previous run.** Verify results.
2. **Reconcile this portfolio.** Update evidence.
3. **Select an execution slate of size `N`.** Choose work.
4. **Plan the entire slate.** Branch on outcomes.
5. **Execute the approved slate.** Run work.

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

    def test_rejects_invalid_mechanism_family(self) -> None:
        text = portfolio([("FP-01", "First route")]).replace(
            "- **Mechanism family:** predecessor-half.",
            "- **Mechanism family:** perpetual-motion.",
        )
        temporary, path = self.write(text)
        with temporary, self.assertRaisesRegex(ValueError, "invalid mechanism family"):
            read_frontier_portfolio(path)

    def test_rejects_advancing_without_forward_result(self) -> None:
        text = portfolio([("FP-01", "First route")]).replace(
            "- **Last forward result:** a compiling producer interface.",
            "- **Last forward result:** none on the load-bearing ledger.",
        )
        temporary, path = self.write(text)
        with temporary, self.assertRaisesRegex(
            ValueError, "cannot be advancing without a last forward result"
        ):
            read_frontier_portfolio(path)

    def test_rejects_noncontiguous_identifiers(self) -> None:
        temporary, path = self.write(portfolio([("FP-02", "Second route")]))
        with temporary, self.assertRaisesRegex(ValueError, "contiguous and ordered"):
            read_frontier_portfolio(path)

    def test_rejects_missing_cycle_step(self) -> None:
        text = portfolio([("FP-01", "First route")]).replace(
            "5. **Execute the approved slate.** Run work.\n", ""
        )
        temporary, path = self.write(text)
        with temporary, self.assertRaisesRegex(ValueError, "execution cycle is missing"):
            read_frontier_portfolio(path)


if __name__ == "__main__":
    unittest.main()
