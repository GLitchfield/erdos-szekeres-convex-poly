# R1: reduce single-run additivity to combs (Claude run, 29 Sept 2026)

Approved by Gavin as round R1 of `runs/next-round-proposal-20260929/PROPOSAL.md` §4.
Claim: `ErdosSzekeres.ctx_bound_additive_single_run` (claude-code:22c8132f…, until 30 Sept 03:41Z).
Research window `window-f12ebdc29b9f446e`. Budget about 8 h wall; jobs ≤ 4 GiB; no Lean until a
statement survives the probes.

## Statements under test (not registered)

- **C1, multi-run uniform-separator contraction.** If every letter strictly inside the child span
  of a well-formed σ is a child letter or `ext 1 s` for one side s, shortening every child run to
  one letter leaves `σ.bound` unchanged (a, u, k and maxima fixed). ≥ is
  `ctx_bound_child_letter_expansion`; the content is ≤. Two runs = `ctx_bound_uniform_separator_contraction`.
- **C2, comb reduction** (C1 + `ctx_bound_external_letter_contraction`): for single-run σ and any
  keep set, both parts have the C1 shape, so the partition's value equals that of the alternating
  singleton partition with the same block pattern.
- **C3, comb inequality.** Single-run additivity on alternating singleton partitions of runs of
  every length.
- **P3 law (exploratory).** How far a child run can be shortened without lowering the bound, as a
  function of the levels with letters inside the child span.

## Probes

- P1 `p1_multirun_usc.py`: C1 falsifier, random + extreme-maxima sampling, j = 2–3 runs, run
  lengths ≤ 3, separators 1–2, optional end level-1 letters, older letters outside the span.
- P2 `p2_comb_c3.py`: for single-run σ with 0–2 older levels outside, every alternating partition
  of runs of length n (up to 10 at k = 5), both start patterns, both orientations, every d:
  value ≤ bound σ; records comb part bounds by tooth count (saturation in j).
- P3: designed after P1/P2.

Kill criteria: C1 counterexample (log, fall back to the two-run statement); C3 violation
(counterexample to single_run: escalate); no P3 law at k ≤ 6 (hand off).
All results diagnostic (Python evaluator `harness.research.recursive`, semantics
`context-bound-zero-children-v1`), not Lean-certified.
