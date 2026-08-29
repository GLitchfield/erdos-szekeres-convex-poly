---
title: Reconcile Fin15 semantics and select the post-Ticket0096 slate
type: research
mode: HITL
status: closed
claim: post-ticket0096-semantic-reconciliation-and-slate-selection-2026-08-28
blocked_by: none
---

# Ticket 0097: reconcile Fin15 semantics and select the post-Ticket0096 slate

## Question

Before planning Ticket 0096's proposed semantic-reflection successor, verify
that the checked Fin15 Boolean formula uses the project's exact
`IsStrongPolygonSet` semantics, reconcile any model gap, and select the next
honest temporary rolling slate from the resulting frontier.

## Decision criteria

1. Test atom meaning and polarity before spending resources on a large Lean
   certificate reflection.
2. Preserve Ticket 0096's exact checked-UNSAT result while refusing any
   implication not supported by its literal predicates.
3. If the old reflection fails, vary the mathematical information by using the
   exact pair-equality strong-quad law; do not merely trim, kernelize, or rerun
   the old certificate.
4. Select only ready theorem contracts or bounded hostile gates, keep campaign
   mutations at proposal level, and do not pad the slate to four.
5. Treat this as reconciliation plus cycle step 3 only.  It authorizes no
   solver run, Lean edit in the project import tree, delegation, retry,
   provider call, route admission, or execution.

## Evidence

### Reconciled starting point

- Base revision: `e1751075e5632c93a7b406136ed5d93b6fbe919e`.
- Pre-reconciliation `docs/wayfinder/map.md` SHA-256:
  `a9c636ba0e6c8d58f7ab2f74e6d33c0c93a6ecca03dbb12e5f9815ef514032ce`.
- Pre-reconciliation `docs/wayfinder/frontier-portfolio.md` SHA-256:
  `430d86c8bc685ca39bc7d2221b4bed9cbba50cad83244c0fe8e6e7d9b2bccac1`.
- Closed Ticket 0096 SHA-256:
  `b59177dfe5c2ff9259a3d764d53e338a87910dafbe595cb227939ae3af1efe45`.
- Ticket 0096's formula, accepted addition-only LRAT, and admitted result
  SHA-256 values remain respectively
  `45fb4c67788558c920228e97625f17a6ca32e2cd52a44bbeb448213e5f9d35df`,
  `c1eb83fb01bbcc25bd9932d7298f6bbd963c50e5cbcb4e3daac31e42f223570d`,
  and
  `b44db6c40f6581bbf3028b21ef8a620bdeec1c07084fb404d262f8b43991ce7a`.

At selection start, `python3 scripts/wayfinder_status.py` reports no frontier
or blocked ticket, and `python3 scripts/check_frontier_portfolio.py` passes
with nineteen entries: two completed, six gated, two merged, one parked, two
retired, and six suspended.  No entry is `advancing`.

The continuous idea generator is live and idle at its six-call rolling-day
cap.  It has zero unreconciled batches and zero unreconciled seeds; its next
eligible call is `2026-08-29T01:22:32.731427+00:00`.  There is therefore no
campaign batch to reconcile or use as an automatic fourth slot.

### Required route review and independent semantic audit

The bounded route-review question, evidence memo, and packet have SHA-256
values
`a34819e58fd63f17ad12fc6ae7206c81167e66bcab197e24c3bc36da19a2e678`,
`86bc1cfa0c42dc72673014770a3d82b42a9b14cf44de23f33c3e451348067fa4`,
and
`e2b292c48d2c758e58dcbbe510d8ee6d47fc6797d57b65baa62f6c1d60fe7363`.
Sol completed its blind initial review at SHA-256
`01a80032b5cb35532e89f198cb267a2119fb63b0e0091d71d759dd0ade223a6f`
and returned `partially_supported` with high confidence.  Fable returned a
zero-token HTTP 429 usage-limit stop before reading the packet, so no
reciprocal round or joint verdict exists.  The identity was not retried or
substituted.  Sol's prose remains advisory; the result below rests on an
independent kernel check.

For an ordered quadruple `a<b<c<d`, the encoder orders its four face colors as
`abc, abd, acd, bcd` and declares the strong-quad atom true only when all four
are equal.  The project definition instead requires

```text
abc = abd  and  acd = bcd.
```

An exhaustive sixteen-word check leaves four Lean-strong words under
`OneChangeOn`: `0000`, `0011`, `1100`, and `1111`; the encoder accepts only
the first and last.  The independent run-local module
`runs/audits/20260828-fin15-semantic-gap-v1/Fin15SemanticGapAudit.lean`,
SHA-256
`68683fd4ba355b9c88c953bb8947f8cd7087478c4d622d9a35c82f7c9ebb4165`,
compiles an explicit `0011` coloring and proves all three facts:

- it satisfies `OneChangeOn` on `Fin 4`;
- its full four-set satisfies `IsStrongPolygonSet`; and
- it fails the encoder's all-four-equal predicate.

The source contains no `sorry`, `admit`, `unsafe`, `native_decide`, or new
axiom declaration.  Consequently the old formula's checked UNSAT remains
valid for its literal Boolean model, but neither the diagnostic dependency
core nor the full certificate can prove the proposed Lean endpoint.  This is
an `architecture-level` model gap with compiling-theorem evidence, not a
negative verdict on a corrected encoding or on the structural
single-exchange branch.  Its sole full failure genome is recorded in `FP-01`
as `FP-01-FIN15-MONOCHROMATIC-SEMANTICS-01`.

## Resolution

### Frontier reconciliation

`FP-01` remains `gated`.  Its old direct semantic-reflection successor is
expired at the exact formula/core/LRAT scope.  The replacement discriminating
gate is a new formula whose quadruple atom is literally the two Lean
pair-equalities.  Before a solver runs, two implementations must agree on all
sixteen quadruple words, representative strong-five expansions, and the
polarities of the no-strong-six and every-eight-has-strong-five clauses.

This reconciliation changes no load-bearing edge.  The first unresolved
fixed-six ambient cardinality remains fifteen.  The model gap prevents a false
promotion; it does not lower the remaining proof obligation.

### Temporary rolling slate

Cycle step 3 selects three activities.  There is one proof-producing support
contract and two information-gathering gates.  Only Slots 1--2 belong to
`FP-01`; Slot 3 is a pre-admission topology mutation.  Selection changes no
portfolio membership or state.

| Slot | Thread and mechanism | Class | Selected gate | Scope firewall |
| --- | --- | --- | --- | --- |
| 1 | `FP-01`, corrected-semantic Fin15 endpoint discriminator | information-gathering | Independently construct the exact Fin15 formula with strong quad defined by `(abc=abd) ∧ (acd=bcd)`.  First compare all atom truth tables and representative clause semantics; only on exact agreement, run one bounded SAT/UNSAT solve with an independent formula replay. | The old CNF, dependency core, LRAT, and their truth value are controls only and may not be reused as a certificate.  SAT rejects only this corrected abstract Fin15 endpoint.  Checked UNSAT licenses a separately planned Lean reflection; it is not proof movement. |
| 2 | `FP-01`, formal common-owner negative control | proof-producing | Under a new immutable implementation identity, replace the unavailable Boolean API step in the authenticated explicit-witness architecture and compile the unchanged theorem `not_fin15CommonOwnerDistinctCrossExteriorContract`. | No premise, coloring, witness table, checkpoint partition, address-space ceiling, or theorem statement changes.  Success upgrades an already checked candidate-local negative to a compiling control; it does not close `D-HALF` or revive a positive helper. |
| 3 | `CS027-VARCHENKO-POLARITY-SPLIT-v1`, polarity-separated bad-region nerves | information-gathering support | On the already authenticated recursive Fin8 dual-tope complex, separate the all-negative and all-positive bad sectors, reconstruct each split nerve twice, and test reduced zeroth homology before any higher factor or deletion stage. | This is the failure genome's smallest mathematical mutation, not a larger unchanged run.  Nonacyclicity kills only the split finite candidate.  Acyclicity is proposal-level search information until a non-enumerative producer and named consumer pass route admission. |

The slate has **one proof-producing** and **two information-gathering**
activities.  Two of three share the inclusive `FP-01` family, an explicit
concentration exception: Slot 1 repairs a formula-model mismatch, while Slot 2
formalizes a different already verified false helper as a regression control;
neither outcome supplies the other's missing premise.  No ready independent
portfolio theorem is displaced.  During execution, Slot 1 may use separate
workers for its two encoders and checker, but those are parallel
implementation lanes for one mathematical investigation, not extra routes.

The fourth mathematical slot remains honestly empty.  It may be backfilled
only after the generator produces a new batch and root authenticates and
reconciles a materially distinct seed, or after a current portfolio entry
acquires its missing producer.  Rolling execution need not wait for that
backfill.

### Predeclared outcome branches

- Slot 1 returns `SEMANTIC-PREFLIGHT-FAIL`, `CORRECTED-FIN15-SAT`,
  `CORRECTED-FIN15-UNSAT-CHECKED`, `SOLVER-UNKNOWN`, or one exact operational
  stop.  Only a separately planned compiling Lean theorem can move proof.
- Slot 2 returns `COMMON-OWNER-COUNTEREXAMPLE-COMPILES` or an exact
  compile/resource/input stop.  It may not silently change the theorem or use
  `native_decide`.
- Slot 3 returns `POLARITY-SPLIT-KILLED`, `POLARITY-SPLIT-LIVE`,
  `NO-SIGNAL`, or an exact input/checker stop at frozen Fin8 scope.

### Deliberate deferrals

- The diagnostic compact old LRAT core is not selected because its atom
  semantics are now formally incompatible with the intended endpoint.
- `FP-02`, `FP-03`, `FP-05`, and `FP-13` still lack an independently produced
  theorem card or completed route review.  `FP-16` remains source-suspended;
  no new complete licensed exact-six source exists.
- A greedoid-flattening v3 replay is not selected.  The two mismatched Fin8
  fixtures both already returned the same no-signal classification, so fixing
  only fixture identity would be operational authentication rather than a new
  mathematical discriminator.
- The old unpolarized Varchenko candidate is expired.  Slot 3 changes the
  cover object exactly as suggested by its candidate-local failure genome and
  starts again at the cheapest hostile test.
- No `advancing` portfolio entry is deliberately deferred because none exists.

## Proof-distance accounting

- **Net proof movement:** neutral.  The new compiling control invalidates an
  architecture; it closes no destination dependency.
- **Evidence:** a compiling run-local Lean model-gap theorem, checked finite
  UNSAT for the old literal formula, a partial advisory route review, and
  operational provider stop.
- **Damage scope:** `architecture-level` for only the old monochromatic-atom
  semantic-reflection architecture; `operational-only` for the Fable stop.
- **Difficulty displaced:** none.  The corrected Fin15 truth value, its
  possible semantic reflection, the Fano cross-extension branch, the
  exact-six ceiling, and the uniform producer remain open.
- **Counterfactual test:** knowing the mismatch before Ticket 0096 would have
  prevented investing in the old formula as a Lean endpoint, but it would not
  have reduced the proof work for the correctly stated theorem.  Therefore it
  is valuable search information, not proof progress.
- **Planning consequence:** proceed to cycle step 4 and freeze exactly these
  three identities, their staged dependencies, budgets, write sets, checks,
  terminal branches, and approval inventory before execution.
- **Load-bearing ledger edge changed:** none.  `D-HALF`, `D-DECOMP`,
  `D-NORMALIZE`, and `D-UPPER` remain open.

## User direction

The user's 2026-08-28 direction, "okay go on to the next step", authorizes the
read-only audit, required bounded route review, reconciliation, and temporary
selection recorded here.  It does not authorize cycle-step-4 execution.
