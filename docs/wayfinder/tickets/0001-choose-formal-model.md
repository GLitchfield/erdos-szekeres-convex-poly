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

Layer E exposed and repaired a second representation boundary: the existing
`HasDeepSplit` described only contiguous sweep-order blocks, whereas the
Baek--Balko definition permits an arbitrary deep-below partition.  The new
`ErdosSzekeres.Decomposable` layer uses finite lower/upper index sets, proves
that every crossing triple is colored by membership of its middle sweep
vertex, derives this law from the coordinate definition, proves hereditary
closure, and proves that a lower cup union an upper cap is a strong polygon.
A required bounded route review was attempted on clean revision `24c22b4`
with packet SHA-256
`af30daa494d3959223ce356eb9d1e96110bc8acfd189725b622f94fc46707e92`.
Both provider calls failed at their execution boundary and an escalated retry
stalled until manually terminated; no advisory conclusion was produced or
used.  The failed run is retained locally under ignored
`runs/reviews/layer-e-route/`.

The 2026-08-10 Layer-F replacement audit now has a minimal compiling object
outside the decomposable class. `DecompositionPrime.lean` proves that every
nonempty indecomposable finite support contains a deletion-minimal
indecomposable subset and that this subset has no proper deep-below split.
This does not close the model ticket or the unrestricted upper bound: a bounded
prime core alone cannot invoke E3 at the exact threshold.

The proposed realizable one-or-two-deletion repair is now formally stopped.
`PrimeTwoDeletionCounterexample.lean` kernel-checks an integer-coordinate
seven-point swept configuration which is decomposition-prime and has no
strong six-set, while every restriction obtained by deleting one or two
vertices is non-prime. `DecompositionPrimeNormalization.lean` instead records
the exact load-bearing interface: a target-reflecting normalization to a
decomposable coloring on the same ground set promotes the decomposable exact
upper theorem to all sweep-realizable colorings. The surviving construction
proposal is target-free realizable single-triple mutation. Its path-to-
normalization consumer and one exact geometric edge from the prime
counterexample to a target-free decomposable coloring now compile; bounded
abstract connectivity remains computational proposal evidence.
Crossing deep splits supply a compiling strong-four fallback, but an exact
rational control shows they do not force a strong six without additional
capacity. See Experiments 0088 and 0089.

The next audit found and repaired an overstrong quantifier in the surviving
normalization interface. Both unthresholded contracts include `Fin 0` and are
therefore false for every positive target size: the empty coloring is
sweep-realizable and target-free, but cannot be recursively decomposable.
Lean now proves these refutations and supplies the exact-threshold replacement
`TargetFreeMutationNormalizesAboveAt`. A one-to-three-step decrease of any
natural-valued rank compiles to this normalization by strong induction, and
then to `SweepExactUpperAt`.

`DecompositionPrimeMutationRank.lean` provides the first noncircular rank
candidate. On nonempty ground sets, `PrimeCoreCount χ = 0` is kernel-proved
equivalent to `IsDecomposable χ`. Seven-point proposal diagnostics say that
one- and two-edge descent fail for natural prime/restriction-defect ranks and
that a three-edge macro is the smallest surviving contract; they are not a
general theorem. The ticket remains open at the exact hard target: prove
three-step target-free realizable descent above the threshold, or produce a
realizable target-free mutation component without a decomposable vertex.
Unrestricted representability-preserving mutation connectivity does not imply
connectivity after deleting all target-containing vertices. See Experiment
0093.

The highest-cardinality rank arithmetic is now complete.
`DecompositionPrimeMutationLocality.lean` proves that losing one prime core at
the highest changed positive cardinality stratum strictly decreases
`StratifiedPrimeCoreRank`; the base `2^n+1` dominates every possible lower
stratum. The file freezes `ThreeStepTopPrimeStratumDropsAboveAt` and proves
that contract supplies the previously compiled threshold-normalization
consumer. The remaining Layer-F obligation is therefore geometric, not
arithmetic: construct such a target-free realizable three-mutation endpoint
above the exact threshold, or find a realizable closed component.

Two independent predecessor directions were also screened. The prefix-free
middle-word frontier selector is stopped by a six-vertex abstract-signotope
counterexample in which all vertices have the same five available words; no
realizable counterexample is claimed. The stronger Property-B bicoloring
recurrence remains live: its exact base and doubling consumer compile, and the
balanced `k=5`, `Fin 8` counterexample formula has an independently checked
exhaustive certificate plus a bare Lean LRAT contradiction. The final
semantic Lean theorem is still open because its generated specialization
approaches the 16-GiB ceiling. Exact core minimization removed only 16 of
1,211 clauses while enlarging the certificate, so that repair is stopped. See
Experiments 0096, 0097, and 0099.

The fractional Property-B relaxation now has a compiling exact-doubling
consumer. `FractionalPredecessorCoverAt k` places nonnegative rational weights
on predecessor-free subsets, covers every vertex with weight at least one, and
uses total weight at most two. Lean bounds every positive-weight support by the
predecessor theorem and completes the finite rational double count. Checked
relaxed hypergraphs show this condition is genuinely weaker than integral
bicoloring, but the `k=5`, `Fin 8` signotope gate already has integral
bicolorings. The route is retained as a secondary contract and requires a
later exact-model fractional/integral separator before promotion. See
Experiment 0101.

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
- [`ErdosSzekeres.Decomposable`](../../../ErdosSzekeres/Decomposable.lean),
  arbitrary deep-below partitions, recursive subset closure, and the
  cup--cap-to-strong-polygon composition theorem
- [`ErdosSzekeres.DecompositionPrime`](../../../ErdosSzekeres/DecompositionPrime.lean),
  deletion-minimal indecomposable supports and their prime-split theorem
- [`ErdosSzekeres.PrimeTwoDeletionCounterexample`](../../../ErdosSzekeres/PrimeTwoDeletionCounterexample.lean),
  the realizable seven-point obstruction to one-or-two deletion descent
- [`ErdosSzekeres.DecompositionPrimeNormalization`](../../../ErdosSzekeres/DecompositionPrimeNormalization.lean),
  the corrected exact-threshold Layer-F consumer and three-step descent shell
- [`ErdosSzekeres.DecompositionPrimeMutationRank`](../../../ErdosSzekeres/DecompositionPrimeMutationRank.lean),
  the prime-core count and its zero/decomposable characterization
- [`ErdosSzekeres.DecompositionPrimeMutationLocality`](../../../ErdosSzekeres/DecompositionPrimeMutationLocality.lean),
  support locality and the compiling top-stratum arithmetic bridge
- [`ErdosSzekeres.StrongPredecessorBicoloring`](../../../ErdosSzekeres/StrongPredecessorBicoloring.lean),
  the integral and fractional exact-doubling recurrence interfaces
- [`ErdosSzekeres.PrimeMutationPositiveControl`](../../../ErdosSzekeres/PrimeMutationPositiveControl.lean),
  one exact realizable target-free mutation into the decomposable class
- [Intermediary lemma ladder](../../formalization_plan.md)
- Baek's formalization: <https://github.com/jcpaik/erdos-tuza-valtr>
- Advisory review of revision `2e34881d6f9f6adefe14d459def686fd90031964`:
  evidence-packet SHA-256
  `fc25f7bd8fa6d6793e387bf269bf14640cb5430e6ee4a7c1712dfaf309679ea9`;
  Claude Fable 5 and Codex Sol, one reciprocal critique round. Raw run retained
  locally under ignored `runs/reviews/0001-model-review/`.
