---
title: Couple the state-578 exterior fan to residual density
type: research
mode: AFK
status: closed
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

Outcome 2. Experiment 0077 proves a genuinely six-column concentration
theorem: every one-upper fan row misses at least three of the six lower cap
columns, so nine rows create at least 27 deficits and one column is missed by
at least five source-indexed entries.

Exact density supplies two cups avoiding that blocker with disjoint
sweep-middle pairs. The total compiling reconnect exposes all previously
conditional fan premises: a deletion row either misses its source cap,
retreats wholly into the 24-vertex lower child, or yields the five-deficit
column together with the two density witnesses.

No target or nine-vertex transversal follows yet. A checked relaxed
32-vertex incidence/address model has residual transversal number four, so a
direct three-boundary argument needs genuinely color-sensitive information.
An exact 13-vertex decomposable Lean model further refutes the local repair
that five exterior source-private rows missing one blocker force a two-cover
of their sweep-middle pairs. The next theorem must continue to use the other
five columns or the full residual family after selecting the deficit column.
Ticket 0006 records that exact synchronization obligation.

## Evidence

- `ErdosSzekeres/StructuralChargingNextState578UpperBracketLedger.lean`
- `ErdosSzekeres/StructuralChargingNextState578UpperBracketFanCounterexample.lean`
- `docs/experiments/0076-state-578-upper-bracket-fan.md`
- `ErdosSzekeres/StructuralChargingNextState578ExteriorDensity.lean`
- `ErdosSzekeres/StructuralChargingNextState578ExteriorDensityCounterexample.lean`
- `data/derived/state578-exterior-density-relaxed-countermodel.json`
- `scripts/check_state578_exterior_density_relaxed_countermodel.py`
- `docs/experiments/0077-state-578-exterior-density-coupling.md`
