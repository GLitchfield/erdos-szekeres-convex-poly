---
title: Retry the exact affine-obstruction morphology microscope
type: research
mode: HITL
status: closed
claim: codex-affine-obstruction-morphology-retry-2026-08-19
blocked_by: none
---

# Ticket 0042: retry the exact affine-obstruction morphology microscope

## Question

After ticket 0041 stopped on an incomplete set-cover symmetry breaker, what
do exact deletion minors and realizable one-wall neighbors say about the
thirteen-point affine-tope counterexample?

This is one information-gathering slot and zero proof-producing slots.  It is
a harness-only continuation explicitly requested by the user.  It does not
revive `FP-07.A`, promote the affine producer, or alter `D-HALF`.

## Frozen inheritance

Preserve ticket 0041's exact witness, definitions, wall-crossing rule, four-
genealogy fallback search, structural-diversity requirements, source inputs,
resource ceilings, outcome labels, and no-post-outcome-repair rule.  The
failed artifacts remain immutable under

`runs/experiments/20260819-arithmetic-affine-microscope/affine/`.

The retry owns only

`runs/experiments/20260819-arithmetic-affine-microscope/affine-v2/`.

It may import the frozen producer/checker as read-only source, but every
override must be explicit and hash-bound.

## Mandatory preflight

Before freezing the outcome execution, the replacement exact-cover kernel
must pass both tests.

1. On the stored ticket-0037 incidence matrix it proves minimum blocker number
   five, enumerates all minimum covers, and includes the published cover.
2. On a synthetic cover instance, it handles the exact failure mode from
   ticket 0041: the first pivot is covered by a later selected edge while the
   same minimum cover contains an earlier unrelated edge.

The independent checker must use its own unordered exact-cover search.  A
wrapper may normalize JSON object keys but may not weaken or omit a semantic
comparison.

## Outcome execution

After source hashes, inherited hashes, commands, caps, and absent outputs are
frozen, run exactly one producer and then exactly one independent checker.
Root does not inspect producer output before checker termination.  No semantic
repair, threshold tuning, feature addition, or rerun follows an outcome.

Possible outcomes remain `AFFINE-BAD-COVERAGE-FAIL`,
`AFFINE-ISOLATED-OBSTRUCTION`, `AFFINE-MINOR-RIGID`,
`AFFINE-DEFECT-FAMILY`, `AFFINE-REPAIR-CIRCULAR`,
`AFFINE-REPAIR-SURVIVES`, `AFFINE-CHECKER-MISMATCH`,
`AFFINE-MODEL-GAP`, or `AFFINE-RESOURCE`.

Each process is capped at 1,200 seconds, eight CPU cores, 16 GiB address space,
and 2 GiB output.  Aggregate stored output remains below 5 GiB.  No Lean,
Lake, external provider, network, installation, destructive action, commit,
or push is authorized.

The user approved this retry on 2026-08-19.

## Proof-distance accounting

- **Net proof movement before execution:** neutral.
- **Evidence:** prospective exact checked computation.
- **Difficulty displaced:** none; this measures a refuted affine child.
- **Counterfactual:** morphology is useful search information only if it
  changes whether a non-affine repair family deserves study.
- **Planning consequence:** require structural coverage and a held-out
  genealogy before any repair card; otherwise keep `FP-07.A` suspended.
- **Load-bearing ledger:** no edge changes in this retry.

## Decision criteria

Admit morphology only if the repaired producer and independent checker agree
on the exact witness, all thirteen deletions, the complete frozen wall-neighbor
rule, blocker covers, distances, and every retained bad configuration.  Count
or structural diversity alone never admits a repair rule.  Such a rule also
requires a source-geometric selector frozen before outcomes and a genuinely
held-out genealogy.  Any missing held-out test keeps `FP-07.A` suspended even
when the defect-family computation passes.

## Resolution

The preflight passes: both exact-cover implementations agree that the stored
witness has blocker number five and exactly nine minimum covers, including the
published cover, and the repaired kernel handles the adversarial ordered-pivot
fixture.

The frozen producer and independent checker then terminate successfully and
agree on `AFFINE-DEFECT-FAMILY`.  The witness has defect one, six minimum-
defect topes, blocker number five, nine minimum covers, and Hamming distance
one to unrestricted valid bicolorings.  All thirteen one-point deletions have
valid affine topes.  Of twenty distinct exact one-wall neighbor chirotopes,
thirteen remain target-free; twelve are still affine failures, while the sole
target-free escape flips triple `{0,7,9}` and creates two valid topes.

The four-genealogy fallback retains 64 additional failures after 1,278
attempts.  Together with the witness and twelve bad wall neighbors, the atlas
has 77 distinct bad chirotopes and 73 recorded structural signatures.  All 77
are deletion-minimal and distance one from an unrestricted valid bicoloring;
76 have defect one and one has defect two; 72 have blocker number five and
five have blocker number six.

One output field is rejected by root contract review.  The producer reports
`repair_admission_passed=true`, but the mandatory held-out genealogy test was
not run.  The checker verifies the mathematical morphology but repeats the
same three-boolean admission reducer, so no repair rule or repair-survival
claim is admitted.

**Net proof movement:** neutral.  **Evidence:** independently checked exact
computation.  **Difficulty displaced:** none; a non-affine source-geometric
selector remains wholly open.  **Counterfactual:** the result establishes that
the affine obstruction is a robust thin-defect family rather than an isolated
coordinate accident, improving search allocation without shortening the
proof.  **Planning consequence:** retain one held-out source-selected repair
question for adversarial review, keep `FP-07.A` suspended, and schedule no Lean
work from this computation.  No load-bearing dependency changed.

## Evidence

- `docs/wayfinder/tickets/0041-test-arithmetic-walls-and-affine-obstructions.md`
- `runs/experiments/20260819-arithmetic-affine-microscope/affine/result.json`
- `runs/experiments/20260819-affine-tope-funnel/p3/incidence.json`
- `runs/experiments/20260819-arithmetic-affine-microscope/affine-v2/preflight.json`
- `runs/experiments/20260819-arithmetic-affine-microscope/affine-v2/manifest.json`
- `runs/experiments/20260819-arithmetic-affine-microscope/affine-v2/producer.json`
- `runs/experiments/20260819-arithmetic-affine-microscope/affine-v2/checker.json`
- `runs/experiments/20260819-arithmetic-affine-microscope/affine-v2/result.json`
- `runs/experiments/20260819-arithmetic-affine-microscope/affine-v2/summary.md`
