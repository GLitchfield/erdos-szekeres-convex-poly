---
title: Choose the canonical formal model
type: research
mode: HITL
status: open
claim: codex-sweep-orientation-2026-08-01
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

Open. The two-layer representation is the leading candidate, but it is not yet
canonical. Commit `2e34881d6f9f6adefe14d459def686fd90031964` establishes a
compiling sweep/orientation pilot. Commit
`37eb57cffbf277d152ab85952fcd343e6bb04e9c` discharges A7/A9: a finite forbidden
set supplies a generic determinant-one shear, and sorting constructs a
`SweptConfiguration` presentation of every finite general-position input while
preserving its orientation values exactly. The mathlib geometry/API redirect
condition therefore did not fire. C1/C3, the point-in-triangle and ordered
four-point convexity/sign criteria, were then discharged by commit
`33633efdbf52ef9625cfccccb03d2540f6634e6a`. The two-layer candidate now has
kernel-checked bridges in both directions: public points produce a realizable
sweep coloring, and the local convexity target is recoverable from its signs.
The ticket remains open only for the bounded alternative-API comparison
required by its original closure criteria. The next mathematical bridge is C4:
lift the four-point certificate to arbitrary finite convex-position subsets.

The 2026-08-01 Sol/Fable review was `partially_supported`. Both reviewers found
no false intermediary theorem in the packet, but correctly objected that one
candidate pilot is not the comparative evidence demanded above. We accept that
process objection, the need to encode realizability in theorem signatures, and
the priority of testing the public-to-sweep bridge. We independently verified
the committed pilot with `make test`; the reviewers did not receive
`ErdosSzekeres/Basic.lean` or that build output, so their inability to verify
those facts is a packet limitation rather than mathematical evidence.

## Evidence

- [Initial literature review](../../literature_review.md)
- [Living bibliography](../../bibliography.md)
- [`ErdosSzekeres.Basic`](../../../ErdosSzekeres/Basic.lean), the provisional
  direct Euclidean statement layer
- [`ErdosSzekeres.Sweep`](../../../ErdosSzekeres/Sweep.lean), the first
  compiling two-layer pilot
- [`ErdosSzekeres.Presentation`](../../../ErdosSzekeres/Presentation.lean), the
  generic public-point-set-to-sweep bridge
- [`ErdosSzekeres.Convexity`](../../../ErdosSzekeres/Convexity.lean), the
  triangle and four-point orientation-sign convexity bridge
- [Intermediary lemma ladder](../../formalization_plan.md)
- Baek's formalization: <https://github.com/jcpaik/erdos-tuza-valtr>
- Advisory review of revision `2e34881d6f9f6adefe14d459def686fd90031964`:
  evidence-packet SHA-256
  `fc25f7bd8fa6d6793e387bf269bf14640cb5430e6ee4a7c1712dfaf309679ea9`;
  Claude Fable 5 and Codex Sol, one reciprocal critique round. Raw run retained
  locally under ignored `runs/reviews/0001-model-review/`.
