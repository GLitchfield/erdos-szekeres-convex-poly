---
title: Consume the state-578 blocker-family mixed rectangle
type: research
mode: AFK
status: closed
claim: codex-state-578-blocker-matrix-consumer-2026-08-09
blocked_by: none
---

## Question

Can the exact color and decomposition laws consume the complete
blocker-avoiding cup/six-cap matrix by producing a two-vertex cover for every
crossing middle pair, or turn its strict lower descent into a genuinely
smaller predecessor state?

## Frozen inputs

- `TightDeficitDensityReduction578` and its exact 32-vertex gate reconnect;
- the complete blocker-avoiding cup/six-cap address matrix and common minimum;
- the one-sided/minimum-column/mixed-rectangle classification;
- the two-blocker source escape and strict six-cell lower descent;
- the five deficit entries, their two distinct cups, and the independent
  blocker-avoiding density pair;
- the local upper three-boundary and restricted-transversal lower bounds; and
- the strengthened relaxed 32-vertex full-matrix certificate.

## Decision criteria

- The first consumer must use a `TripleColoring` color law or recursive
  decomposability essentially. Any conclusion inherited by the relaxed
  incidence/two-level-address certificate is false.
- A proposed two-cover must quantify over the complete crossing
  blocker-avoiding middle-pair family, not only the five selected rows or two
  density witnesses. It must state the two vertices and prove coverage.
- A recursive alternative must identify a strict subtree, prove the retained
  cup/cap avoidance hypotheses there, and name the smaller predecessor state
  or numerical capacity decrease. Strict address descent alone is not a
  completed induction step.
- A minimum-column or mixed-rectangle consumer must retain a nonblocker cap
  column. The blocker-family has no universal-intersection spine anchor.
- Run a bounded relaxed and exact-small-model falsifier before a large Lean
  proof. An exact target-free `TripleColoring` retaining the proposed
  color-sensitive contract expires that contract.

## Candidate outcomes

1. A compiling cover or recursive predecessor closes the tight state-578
   branch.
2. A compiling color-sensitive theorem eliminates one matrix alternative and
   leaves one named smaller-state or capacity obstruction.
3. An exact target-free coloring retains the proposed consumer; expire the
   blocker-matrix route and select a different invariant.

## Resolution

Outcome 2. `StructuralChargingNextState578BlockerConsumer.lean` proves that
opposite strict extensions from the common minimum are impossible under
strong-eight avoidance: the false extension localizes a four-cup in the lower
child, the true extension localizes a four-cap in the upper child, and the
deep-split gluing theorem gives a forbidden strong eight-set. The mixed
rectangle is therefore removed from the full blocker-family classification.

The remaining alternatives are one-sided localization of the complete
24-vertex cap support in one child, or a universal minimum column. Exact-small
decomposable target-free models show that neither projected alternative alone
forces a two-cover or a strict predecessor. They do not instantiate the full
32-vertex private-star/density package, so state `(5,7,8)` remains open rather
than refuted. Ticket 0008 owns the residual trichotomy.

## Evidence

- `docs/experiments/0078-state-578-deficit-density-synchronization.md`
- `ErdosSzekeres/StructuralChargingNextState578DeficitDensity.lean`
- `data/derived/state578-exterior-density-relaxed-countermodel.json`
- `scripts/check_state578_exterior_density_relaxed_countermodel.py`
- `docs/experiments/0079-state-578-blocker-consumer.md`
- `ErdosSzekeres/StructuralChargingNextState578BlockerConsumer.lean`
