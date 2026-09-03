---
title: Incubate the placement-13 common-anchor obstruction
type: research
mode: HITL
status: closed
claim: common-anchor-gap13-lsp-elaborated-neutral-2026-09-01
blocked_by: none
---

# Ticket 0125: incubate the placement-13 common-anchor obstruction

## Question

Does the exact premise-minimal placement-`13` active-clique declaration
elaborate in the current common-anchor source without premise repair?

## Decision criteria

1. Preserve the exact Ticket-0122 theorem contract and five-field entry memo.
2. Reuse only the ten authenticated middle-determination reductions and six
   literal actual-edge factorizations.
3. Run one declaration-region Lean language-server diagnostic pass; do not run
   a Make/Lake project build or repository tests in this incubation.
4. Stop on any reduction or edge-rewrite mismatch rather than add a premise or
   change the theorem statement.
5. Treat an LSP-clean declaration as proposal-level source evidence until a
   later guarded project build admits it.

## Approved packet

`runs/agents/20260901-ticket0125-gap13-source-incubation/task.md`

## Resolution

The exact declaration was added at source line 1867 and the first authorized
declaration-scoped LSP call returned success with no errors, no timeout, and no
failed dependencies.  It reported five unused-`simp`-argument linter warnings,
so the terminal is `GAP13-LSP-ELABORATED-WITH-LINTER-WARNINGS`, not zero
diagnostics.  The checked source SHA-256 is
`17ebe8718f977b2c0d69640e3c8d5bb6fa3edb55c06b957bd26bd768797a971d`.

The theorem retains exactly four placement inequalities and two strong-owner
hypotheses.  Its ten middle-determination reductions produce the six
active-clique edge equivalences, and existing theorem
`not_perfectMatching_activeClique` closes the contradiction.  No premise,
statement, helper API, axiom, or computational evidence was added.  Root did
not perform cosmetic warning cleanup because the immutable packet authorized
one diagnostic pass only.

## Evidence

- Frozen task SHA-256:
  `c8ca2666f379df49385c61bf7142748498159e1ed61e61d54691bdd437c930d9`.
- Entry-audit SHA-256:
  `dce09ee7662dc58486c1cae3ea708075194393c4b8990cefa5202b6119b31d4d`.
- Frozen source SHA-256:
  `00fbe8f26e0e83370a7a05abeef6542293b742f1f211bb8a5b87c274424bc728`.
- Result source SHA-256:
  `17ebe8718f977b2c0d69640e3c8d5bb6fa3edb55c06b957bd26bd768797a971d`.
- Terminal report SHA-256:
  `2adcaaebb23891be37a4495522dda421acab9e6dce184c771eae967e62f1466c`.

## Proof-distance accounting

- **Net proof movement:** `neutral`.
- **Evidence:** proposal-level LSP elaboration success with five cosmetic
  warnings; no guarded build.
- **Damage scope:** `candidate-local` scope ceiling only; no admitted negative.
- **Difficulty displaced:** unadmitted actual-placement source leaves decrease
  `5 -> 4` and contradiction leaves `2 -> 1`; all admitted downstream
  obligations remain unchanged.
- **Counterfactual test:** the interleaved exact statement now survives its
  first elaboration check without premise repair, but admitted proof depth is
  unchanged until the guarded project gate.
- **Planning consequence:** preserve the candidate, retain `FP-01` and
  `FP-03` as `gated`, and reconcile before selecting `14` or `24`; do not run a
  build merely for this theorem.
- **Load-bearing ledger edge changed:** none.

Terminal report:
`runs/agents/20260901-ticket0125-gap13-source-incubation/result.md`.
No failure genome is created.  The lane used approximately 1 minute 47 seconds
wall time; CPU and peak RSS were not instrumented.
