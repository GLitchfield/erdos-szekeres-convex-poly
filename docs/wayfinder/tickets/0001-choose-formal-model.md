---
title: Choose the canonical formal model
type: research
mode: HITL
status: open
claim: unclaimed
blocked_by: none
---

## Question

Which formal representation should be canonical for attacking the exact
formula `ES(n) = 2^(n-2) + 1`: direct planar geometry, finite ordered
orientation configurations, or a two-layer architecture with a proved bridge?

## Decision criteria

- The target statement must quantify over actual finite point sets in
  `ℝ²`, express no-three-collinear general position, and include both forcing
  and sharpness.
- The representation must expose the cup--cap recurrence, convex-polygon
  predicates, and decompositions used in the 1935, 2025, and 2026 papers.
- Any abstract configuration theorem used for the upper bound must have a
  kernel-checked implication back to realizable planar point sets. The false
  ordered-hypergraph generalizations found by Balko--Valtr and Baek--Balko must
  not be silently assumed.
- Evaluate reuse versus reimplementation of Jineon Baek's Apache-2.0 Lean 4
  development. Record its exact revision and compatibility with the pinned
  toolchain before copying code.
- Demonstrate each candidate with the same bounded pilot: state general
  position, a cup/cap predicate, convex position, and one nontrivial bridge
  lemma. Limit the pilot to two hours per candidate and commit only small,
  maintained code.
- Advance the representation that gives the clearest trusted statement and
  shortest route to formalizing the all-`n` lower construction and one known
  upper-bound lemma. Redirect if a necessary mathlib geometry bridge is absent
  or if the abstract model cannot express realizability constraints locally.
- Closure requires compiling pilots, an API comparison, source/license
  provenance, and a bounded Sol/Fable review. Model review is planning evidence,
  not mathematical evidence.

## Resolution

Open. Do not choose a representation from the literature survey alone.

## Evidence

- [Initial literature review](../../literature_review.md)
- [Living bibliography](../../bibliography.md)
- [`ErdosSzekeres.Basic`](../../../ErdosSzekeres/Basic.lean), the provisional
  direct Euclidean statement layer
- Baek's formalization: <https://github.com/jcpaik/erdos-tuza-valtr>
