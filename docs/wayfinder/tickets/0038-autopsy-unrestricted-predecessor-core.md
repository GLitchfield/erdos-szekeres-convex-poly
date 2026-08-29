---
title: Autopsy the unrestricted predecessor core of the affine falsifier
type: research
mode: HITL
status: closed
claim: codex-unrestricted-predecessor-core-2026-08-19
blocked_by: none
---

# Ticket 0038: autopsy the unrestricted predecessor core

## Question

Does ticket 0037's exact 13-point affine-tope counterexample also refute the
unrestricted integral predecessor bicoloring or the weaker predecessor-free
half-subset contract?

This is the cheapest unresolved question exposed by the affine failure.  It is
not an affine repair and does not test a new representation language.

## Strategic admission

Ticket 0037 independently checked that the exact integer realization

`(0,2),(1,-486),(2,7),(3,9),(4,-51),(5,-24),(6,35),(7,36),`
`(8,126),(9,42),(10,44),(11,82),(12,422)`

is in general position, has no convex six-set, and admits no two-sided
predecessor-free affine cut or predecessor-free affine half support.  That
refutes `FP-07.A` only.  Neither all vertex bicolorings nor all arbitrary
half-sized subsets have been enumerated.

Because the predecessor-half family has a long negative streak, a fresh
Sol/Fable review was attempted before scheduling any descendant.  Codex Sol
returned `MODIFY`: authorize only the two unrestricted exhaustive tests and
stop if successful objects exist; do not preauthorize affine-distance,
minor-kernel, tope-algebra, Veronese, or robustness work.  Claude Fable failed
at its existing authentication boundary, so no joint consensus is claimed.
The review is stored under
`runs/reviews/20260819-affine-obstruction-autopsy/sol-fable/`.

## Frozen semantics

Let `P` be the 13 indexed witness points and let `E` be the exact family of
five-element subsets in convex position.

- `convexFiveFree(S)` means `e ⊄ S` for every `e ∈ E`.
- An unrestricted predecessor bicoloring is a mask `S ⊆ P` such that both
  `convexFiveFree(S)` and `convexFiveFree(P \ S)` hold.
- A predecessor-free half support is a mask `S ⊆ P` with
  `|S| ≥ ceil(13/2) = 7` and `convexFiveFree(S)`.

Convex-five-freeness is hereditary.  Therefore existence of a support of size
at least seven is equivalent to existence of one of size exactly seven.  The
producer will nevertheless enumerate all 4,096 masks of size at least seven
as a boundary check, in addition to all 1,716 exact seven-subsets.

## U-CORE execution

### Producer

Using exact integer determinant and hull arithmetic:

1. authenticate the witness against the ticket-0037 coordinate and chirotope
   commitments;
2. enumerate all `choose(13,5) = 1,287` five-subsets and freeze `E`;
3. enumerate all 8,192 color masks and record every unrestricted predecessor
   bicoloring;
4. enumerate every exact seven-subset and every mask of size at least seven,
   recording all predecessor-free supports; and
5. emit exact masks, counts, complement-pair counts, and the smallest witness
   for each nonempty class.

No optimization objective or early stop is allowed.

### Independent checker

The checker must not call the producer's convexity or mask routines.  It
reconstructs convex-five subsets from the coordinates using an independently
implemented orientation/containment or cyclic-hull criterion, replays all
8,192 masks, and checks every emitted and omitted mask.  It also verifies
complement symmetry, heredity, and relabeling invariance.

### Frozen corruptions

Before either outcome command, source self-tests must reject:

1. a convex pentagon labeled nonconvex;
2. a five-set with an interior point labeled convex;
3. one deleted predecessor edge in `E`;
4. a bicoloring accepted without checking its complement;
5. a six-point support incorrectly accepted as half-sized;
6. a missing exact-seven support from the emitted ledger; and
7. a relabeling that changes counts rather than only masks.

## Outcome branches

- `U-HALF-FALSIFIER`: zero predecessor-free support of size at least seven.
  This is checked finite evidence against `PredecessorHalfSubsetAt 6`; stop and
  separately reconcile every dependent route.  It is not a Lean theorem.
- `U-INTEGRAL-FALSIFIER`: at least one half support exists but no unrestricted
  predecessor bicoloring exists.  Retire `FP-07`; preserve `FP-01` and `FP-08`.
- `U-CORE-SURVIVES`: at least one unrestricted bicoloring exists.  Record all
  exact solutions and stop.  Do not compute affine distance or launch an
  algebraic representation search in this block.
- `U-CHECKER-MISMATCH`, `U-MODEL-GAP`, or `U-RESOURCE`: operational stop with no
  mathematical inference.

The bicoloring implication is one-way: failure of integral bicoloring does not
imply failure of a half support.  Branch accounting must preserve that
distinction.

## Exact commands and resources

Owned root:

`runs/experiments/20260819-unrestricted-predecessor-core/`

After producer/checker sources, manifest, schemas, and hashes are frozen, run
each command exactly once:

`/usr/bin/time -v timeout --signal=TERM 300s prlimit --as=2147483648 --fsize=67108864 taskset -c 0 python3 runs/experiments/20260819-unrestricted-predecessor-core/produce.py --manifest runs/experiments/20260819-unrestricted-predecessor-core/manifest.json --output runs/experiments/20260819-unrestricted-predecessor-core/primary.json`

`/usr/bin/time -v timeout --signal=TERM 300s prlimit --as=2147483648 --fsize=67108864 taskset -c 0 python3 runs/experiments/20260819-unrestricted-predecessor-core/check.py --manifest runs/experiments/20260819-unrestricted-predecessor-core/manifest.json --primary runs/experiments/20260819-unrestricted-predecessor-core/primary.json --output runs/experiments/20260819-unrestricted-predecessor-core/check.json`

The two outputs remain sealed until both commands terminate.  Aggregate cap:
one CPU core, 2 GiB RAM, 128 MiB output, and ten command-minutes.  The complete
block, including source freeze and integration, stops after 90 wall minutes.

No network/provider call, Lean/Lake, SAT/LRAT, installation, resource
escalation, destructive action, commit, push, or external mutation is in
scope.  There is no post-outcome source repair or rerun.

## Proof-distance accounting

- **Execution slate:** zero proof-producing slots and one information-gathering
  slot.
- **Net proof movement before execution:** neutral.
- **Evidence:** exact checked computation only.
- **Difficulty displaced:** none unless the witness falsifies a parent
  contract; positive finite solutions do not reduce the uniform producer.
- **Counterfactual:** a negative result materially retires `FP-07` or the
  stronger half-subset route.  A positive result only prevents misclassifying
  the affine witness and supplies input for a later discussion.
- **Planning consequence:** stop after U-CORE under every outcome.  Any tope
  algebra, fixed-degree lift, obstruction-minor, or source-theorem work needs a
  new review and user approval.

## Approval boundary

Approval authorizes source authoring under the owned run root, the two frozen
local commands above, packet-owned outcome files, one terminal ticket/portfolio
reconciliation, and timing updates.  It authorizes no later representation
ladder or formalization.

## Decision criteria

Approve only the isolated U-CORE enumeration with its exact predicates,
independent checker, one-shot commands, frozen corruptions, and unconditional
stop.  Reject approval if it is bundled with affine repair, tope algebra,
higher-dimensional lifting, post-outcome representation fitting, or Lean work.
Any semantic mismatch terminates operationally rather than changing the
predicate or rerunning the outcome.

## Resolution

Closed as `U-CORE-SURVIVES` on 2026-08-19.  Both independently implemented
exact enumerators passed their frozen source self-tests and one-shot capped
commands.  They agree on 114 convex-five edges, 762 color-labeled unrestricted
bicolorings (381 complement pairs), 506 exact seven-point supports, and 594
supports of size at least seven.  Complement symmetry, heredity, and all seven
frozen corruption checks pass.

The affine witness therefore refutes only the affine-tope child, not the
unrestricted integral or half-subset core.  This is checked finite search
information, not a uniform producer and not proof movement.  `FP-07`, `FP-01`,
and `FP-08` are retained without promotion; `FP-07.A` remains suspended.  The
frozen stop rule was honored: no affine-distance, algebra, lift, minor, or
robustness follow-up was run.  No load-bearing dependency changed.

## Evidence

- `docs/wayfinder/tickets/0037-test-affine-tope-predecessor-funnel.md`
- `runs/experiments/20260819-affine-tope-funnel/result.json`
- `runs/experiments/20260819-affine-tope-funnel/summary.md`
- `runs/experiments/20260819-affine-tope-funnel/p1/check.json`
- `runs/experiments/20260819-affine-tope-funnel/p2/check.json`
- `runs/experiments/20260819-affine-tope-funnel/p3/incidence-check.json`
- `ErdosSzekeres/StrongPredecessorBicoloring.lean`
- `runs/reviews/20260819-affine-obstruction-autopsy/question.md`
- `runs/reviews/20260819-affine-obstruction-autopsy/sol-fable/codex.initial.json`
- `runs/experiments/20260819-unrestricted-predecessor-core/primary.json`
- `runs/experiments/20260819-unrestricted-predecessor-core/check.json`
- `runs/experiments/20260819-unrestricted-predecessor-core/summary.md`
- `runs/experiments/20260819-unrestricted-predecessor-core/result.json`
