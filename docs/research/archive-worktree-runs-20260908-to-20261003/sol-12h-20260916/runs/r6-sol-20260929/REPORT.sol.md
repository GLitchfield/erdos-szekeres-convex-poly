# R6 Sol report

Closed the exact theorem
`ErdosSzekeres.ctx_bound_additive_single_run_of_run_contraction_and_alternating`.
Proof commit: `0613cea1565ddb9ba7186c373ce37e2d05d755de` on
`node/CtxBoundAdditiveSingleRunOfRunContractionAndAlternating`.
The locked type is unchanged (`8a8e1b43f96a9e11`), with no sorry and only
`propext`, `Classical.choice`, `Quot.sound`. Both orientations and arbitrary keep lists,
including duplicates, are covered under explicit C1 and C3 hypotheses.

- Exact scratch proof: `20260929-212539-aec410`, rc=0, 6.9 s, peak 592 MiB.
- Reviewed scratch cleanup: `20260929-212807-066210`, rc=0, standard axioms only.
- Targeted registration: `20260930-015047-f6d4f9`, rc=0, 203.5 s, peak 2481 MiB.
- Registered targeted check: `20260930-015830-a40734`, rc=0, 98.5 s, peak 2344 MiB;
  targeted/incremental extraction, locked type preserved, no nonstandard/uncovered axioms.
- Guarded proof commit: `20260930-020442-cd2bc6`, rc=0; five proof/metadata files.

The proof compresses equal neighboring Boolean partition labels using C1 and closed
external-letter contraction in complementary parts, preserves the parent base via closed
child-letter contraction, and applies C3 to the remaining parity partition.

Claims released: conditional glue node closed; original unconditional single-run node
partial and still open here. This run does not prove C1, C3, unconditional additivity or
the full happy-ending conjecture. No merge, push, full extract, primary-checkout source
edit, other statement edit or delegation occurred. No further trial is authorized.
The safest next action is review of this branch and separate work on C1/C3.

Evidence: `targeted-check.log`, `receipt-targeted-check.json`, `NODE.closed.json`,
`module-before-check.sha256`, `receipt-proof-commit.json`; detailed proof and failed work:
`MATHEMATICAL-HANDOFF.md`. Memory/bus refusals and the worker's missing-rg preflight failure
are preserved and logged; neither produced theorem credit.

The native goal remains active for the fixed consolidation/reporting contract. Consolidate
at 2026-09-30T10:40:47.215813Z; completion/report no earlier than 11:10:47.215813Z.
