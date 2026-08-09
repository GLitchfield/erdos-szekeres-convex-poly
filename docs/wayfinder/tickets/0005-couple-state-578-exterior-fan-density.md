---
title: Couple the state-578 exterior fan to residual density
type: research
mode: AFK
status: open
claim: codex-state-578-exterior-density-2026-08-09
blocked_by: none
---

## Question

Does the exact six-cap, 32-vertex, `32/23` residual-density package turn the
compiled nine-source one-sided deletion fan into either a target outcome or a
four-cup transversal of cardinality at most nine?

## Frozen inputs

- `NineOneSidedDeletionFan578` and its exact existence theorem;
- six pairwise-disjoint four-cap columns on 24 vertices;
- the full residual four-cup family and its common-minimum address matrix;
- every residual four-cup transversal has cardinality at least ten; and
- the exact nine- and 13-vertex counterexamples from ticket 0004.

## Decision criteria

- The first candidate must use all six columns or the `32/23` density theorem
  essentially. A statement inherited by the 13-vertex three-column model is
  already false as a closing lemma.
- Merely classifying the nine rows, counting their upper endpoints, or finding
  a repeated address is insufficient. The conclusion must produce a named
  target or an explicit transversal/capacity contradiction.
- If proposing a transversal, state its finite set, prove it meets every
  residual four-cup, and prove its cardinality is at most nine.
- Run the cheapest relaxed incidence/tree falsifier before a large Lean proof.
  A negative model must list exactly which frozen hypotheses it retains.
- Completed positive or negative results must compile without `sorry`,
  `admit`, unsafe axioms, `native_decide`, or an unverified oracle.

## Candidate outcomes

1. A compiling density-coupled consumer closes the tight state-578 branch.
2. A compiling theorem yields a new global invariant with one exact remaining
   capacity obstruction.
3. An exact countermodel retaining the proposed density coupling refutes it;
   retain the exterior-fan infrastructure and change the main invariant.

## Resolution

Open. Experiment 0076 proves the exterior fan and refutes every consumer using
only three cap columns plus local endpoint/address data. The first candidate
must explain precisely where the full 32-vertex residual family enters.

## Evidence

- `ErdosSzekeres/StructuralChargingNextState578UpperBracketLedger.lean`
- `ErdosSzekeres/StructuralChargingNextState578UpperBracketFanCounterexample.lean`
- `docs/experiments/0076-state-578-upper-bracket-fan.md`
