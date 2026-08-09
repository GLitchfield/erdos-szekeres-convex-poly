---
title: Force or refute a collective state-578 upper bracket
type: research
mode: AFK
status: closed
claim: codex-state-578-upper-bracket-2026-08-09
blocked_by: none
---

## Question

Does the exact 32-vertex state-578 package force two upper vertices which
strictly bracket at least seven vertices of one lower child, so the compiling
bracket theorem produces a forbidden seven-cap?

## Frozen inputs

- the six pairwise-disjoint four-caps occupying 24 reservoir vertices and the
  exact eight-vertex complement;
- four-cup density in every decomposable 23-vertex restriction;
- the cap-vertex-deletion residual ledger and its endpoint-shape alternatives;
- the full residual-cup/six-cap common-minimum matrix; and
- `HasDeepBelowSplit.bracketed_lower_card_le_six`.

## Decision criteria

- The first candidate must use at least two cap columns essentially.  A
  cap-by-cap classification or a restatement of the deletion ledger is not a
  consumer.
- State explicitly which two upper vertices form the proposed bracket and
  which seven lower vertices they bracket.  Address equality alone does not
  imply order bracketing.
- Test the smallest relaxed tree/color model before attempting a large Lean
  proof.  A negative model must retain every hypothesis it claims to refute.
- A numerical child-capacity consequence is required; pairwise endpoint
  classifications without a common bracket do not advance the route.
- Completed positive results must compile without `sorry`, `admit`, unsafe
  axioms, or an unverified oracle.  Computation and agent review remain
  advisory until promoted to such a theorem.
- Expire the bracket route if a target-free decomposable coloring realizes the
  proposed multi-column synchronization, or if the candidate does not use
  the six-cap/global-density package essentially.

## Candidate outcomes

1. A compiling cross-column theorem forces a seven-vertex upper bracket and
   closes the tight state-578 branch.
2. A compiling theorem forces a smaller bracket or synchronized endpoint
   carrier, reducing the state to one exact capacity obstruction.
3. A bounded exact countermodel refutes the collective bracket implication;
   retain the generic bracket theorem and select a different global invariant.

## Resolution

Outcome 2. Experiment 0076 proves the exact `24 → 18 → 9` replacement: at a
lower-localized common minimum, at least nine saturated cap sources lie on one
exterior side of the upper span, all their deletion rows have exactly one
upper endpoint, and those sources cannot lie in only two cap columns.

The seven-vertex common bracket is not forced by the current endpoint data.
A cardinality-minimal nine-vertex Lean counterexample refutes two-column
closure. A second exact 13-vertex decomposable, sweep-realizable Lean model
realizes the nine-source fan across three disjoint cap columns while avoiding
five-cups, seven-caps, and strong eight-sets. It does not retain the six-cap,
32-vertex, or `32/23` density package, so the full exact implication is not
refuted.

The bracket route is expired as a standalone local invariant. Ticket 0005
retains the compiling exterior fan but requires a consumer which uses the
full residual-density package essentially.

## Evidence

- `ErdosSzekeres/StructuralChargingNextState578DeletionLedger.lean`
- `ErdosSzekeres/StructuralChargingNextState578RestrictedMiddlePairs.lean`
- `ErdosSzekeres/StructuralChargingNextState578Bracket.lean`
- `docs/experiments/0075-state-578-deletion-middle-bracket.md`
- `ErdosSzekeres/StructuralChargingNextState578UpperBracket.lean`
- `ErdosSzekeres/StructuralChargingNextState578UpperBracketLedger.lean`
- `ErdosSzekeres/StructuralChargingNextState578UpperBracketCounterexample.lean`
- `ErdosSzekeres/StructuralChargingNextState578UpperBracketFanCounterexample.lean`
- `docs/experiments/0076-state-578-upper-bracket-fan.md`
