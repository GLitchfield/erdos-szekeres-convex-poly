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
Commit `4aa66f09d4773f3e04ce5a471301dddda628cd8c` discharges C4: by
Carathéodory's theorem and general position, a finite planar set is in convex
position exactly when all of its four-point subsets are. Thus every local sign
certificate can now be lifted to arbitrary finite sets.
Commit `d701ef050c0c96ed9af688c65cb25ac74480efc0` discharges C5. It
defines `IsStrongPolygon` by the two color consistencies on every increasing
four-tuple and proves that this law is equivalent to convex position, first
for the swept configuration and then for the original public point set. The
latter transport uses a formal linear equivalence for the determinant-one
shear and proves convex position invariant under invertible linear maps.
Commit `a44624d0eb0f834100ac114591fa022cd11875de` discharges B1 by
defining increasing restrictions of ordered triples, colorings, and swept
configurations. Restriction preserves sweep realizability, and the exact
theorem `containsConvexSubset_iff_exists_isStrongPolygonOn` now translates the
public convex-subset predicate into existence of a restricted strong polygon.
Commit `6088939e351ec88a2e1dbb3635dc0adfe59a02a8` discharges B3. A
four-point orientation propagation identity and strong induction prove that
consecutive left or right turns force the same color on every triple of a
selected sequence. Named cup/cap equivalences are available for concrete
swept configurations and for colorings carrying an `IsSweepRealizable`
witness.
The ticket remains open only for the bounded alternative-API comparison
required by its original closure criteria. D1 and D3 now compile in
`ErdosSzekeres/CupCap.lean`: the adapted pincer recurrence constructs a cap or
cup at the binomial threshold, the realizability bridge upgrades consecutive
chains to all triples, and the strong-polygon bridge yields the classical
geometric upper bound. D2 now also compiles: `ErdosSzekeres/Extremal.lean`
constructs the matching planar Pascal family and proves `exact_cupCap`.

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
  compiling two-layer pilot and increasing-restriction API
- [`ErdosSzekeres.Chains`](../../../ErdosSzekeres/Chains.lean), the
  consecutive/all-triples cup-cap equivalence for realizable colorings
- [`ErdosSzekeres.CupCap`](../../../ErdosSzekeres/CupCap.lean), the compiling
  recurrence engine and classical binomial geometric upper bound
- [`ErdosSzekeres.Presentation`](../../../ErdosSzekeres/Presentation.lean), the
  generic public-point-set-to-sweep bridge
- [`ErdosSzekeres.Convexity`](../../../ErdosSzekeres/Convexity.lean), the
  triangle, four-point orientation-sign, and local-to-global convexity bridge
- [`ErdosSzekeres.StrongPolygon`](../../../ErdosSzekeres/StrongPolygon.lean),
  the exact combinatorial/geometric target-polygon and convex-subset bridge
- [Intermediary lemma ladder](../../formalization_plan.md)
- Baek's formalization: <https://github.com/jcpaik/erdos-tuza-valtr>
- Advisory review of revision `2e34881d6f9f6adefe14d459def686fd90031964`:
  evidence-packet SHA-256
  `fc25f7bd8fa6d6793e387bf269bf14640cb5430e6ee4a7c1712dfaf309679ea9`;
  Claude Fable 5 and Codex Sol, one reciprocal critique round. Raw run retained
  locally under ignored `runs/reviews/0001-model-review/`.
