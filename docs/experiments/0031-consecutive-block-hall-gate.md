# Consecutive-block Hall gate

## Question

The child-ray bridge selects one endpoint profile incident to the actual
predecessor or successor ray of every retained exact-rank span.  The reflected
two-endpoint candidate family survived the earlier bounded Hall gate, but the
bridge did not show how to choose candidates injectively.

This experiment separates three increasingly weaker claims:

1. the single active profile is injective along each consecutive frontier
   block;
2. the entire lattice interval at the active endpoint expands every
   consecutive block; and
3. the original reflected union of both endpoint intervals expands every
   consecutive block.

Only the first two are tested negatively here.  The third remains the open
endpoint-candidate statement.

## Lean result

`StructuralChargingTransitionHallBlocks.lean` defines a frontier block by a
closed interval of left endpoints.  The compiling order theorem shows that
the same block is obtained from right endpoints.  Every endpoint block is
intrinsically consecutive, and every nonempty intrinsically consecutive
subfamily equals the block between its minimum and maximum left endpoints.
Consequently the endpoint-block and intrinsic-consecutive formulations of the
restricted Hall target are equivalent.

The file also proves the generic finite lemma that an injective selected
representative belonging to each candidate family gives the required union
cardinality.  This turns active-profile injectivity into an explicit strong
falsification target rather than an implicit assumption.

`StructuralChargingTransitionHallRayBridge.lean` now retains the full lattice
interval at the endpoint incident to the active ray.  It proves that the
distinguished profile belongs to that interval and that, before and after
orientation reflection, the active interval is contained in the original
two-endpoint candidate family.  The block file packages active-interval
expansion and proves that it implies the original reflected block target.
These are structural reductions only; no geometric expansion premise is
asserted.

`StructuralChargingTransitionHallReflectionCollision.lean` promotes the
decisive active-interval obstruction into the kernel.  It proves the new span
has exact cap rank three, is retained on the frontier, forms exactly a
two-span block with `(4,6)`, and that both reflected active candidate sets are
`{fullIdeal}`.  The compiling theorem

    activeBlockExpansion_fails

therefore refutes the all-parameter active block-expansion proposition without
an external oracle.

## Deterministic representative refutation

On the validated `n = 8`, `k = 6` decomposable coloring
`3218f2140c78bf`, support `ff`, lower child `aa`, the cap/rank-three frontier
is

    (0,3), (1,4), (2,5), (3,6), (4,7).

The reflected active profiles are

    0, f, 0, f, 0.

Thus the five-span block has two collision classes and active-profile
injectivity is false.  The reflected active intervals still have a union of
six ideals and admit distinct representatives, as does the original
two-endpoint family.  This witness refutes only the deterministic selection,
not block expansion.

The producer reconstructs cell-mask lower ideals from the validated parent
census.  The independent replay reconstructs row-height ideals and reproduces
the collision, membership in every candidate family, and both positive
matching checks.

## Active-interval block refutation

The stronger frozen root from the reflected-Hall gate is decisive.  It has
`n = 12`, `k = 7`, support `fff`, lower child `596`, and coloring

    c9f7fdfe93f000dfe107f9e80053009e8005300efeff083fd37ffff.

In its cap/rank-three frontier, the adjacent spans `(2,5)` and `(4,6)` both
receive the singleton reflected active interval `{3f}`.  They form a genuine
two-span consecutive block, but their candidate union has cardinality one.
Therefore active single-endpoint interval block expansion is false.

Lean kernel-checks this exact defect.  The bounded gate also checks every
consecutive interval directly, rather than inferring a block defect from
failure of a full matching.  The producer uses cell masks;
the independent checker uses nonincreasing row heights.  Both identify the
same first block, singleton family, and cardinality defect.  Because the
predeclared execution order stops at the frozen failure, no new `k = 6`
census was run for this already-refuted strengthening.

The representative-counterexample manifest has SHA-256
`2ca040b28d86b233016424da417fda0782ef756c2e8484c236cd91064b84a95d`.
The active-interval block manifest has SHA-256
`656b13043c2a13d2dfcceb7e7b9570b9600f4b22bd8c2473eda58a1ff0f20115`.

This does **not** refute the original reflected two-endpoint family.  That
family passes the complete frozen frontier and all 631,474 prior `k = 6`
groups.  The defect shows exactly that the unused endpoint interval can be
essential even when the actual child ray identifies one incident endpoint.

## Route consequence

The direct active-representative route is computationally refuted, and the
active single-endpoint-interval route is formally refuted.  The ordered-block
API remains reusable.  The Wayfinder's
predeclared fallback is now active: encode actual child-ray **events** as a
skew Bollobas-style set-pair system and seek the exact adjacent Pascal
coefficient without choosing only one endpoint interval or adding an
orientation tag.  A contrarian review must freeze the first noncircular
set-pair theorem and its bounded falsifier before Lean implementation.

That read-only review now supplies a proposal-level contract.  An actual ray
event key should contain a normalized past/future direction, a concrete child
chain, and a marked chain vertex, with proof terms kept out of the key.  For a
rank-`r` span, the proposed set pair has an incident `present` set of size
`r-1` and an actual but nonincident `absent` set of size `k-r-1`.  The missing
geometric assertion is the genuinely skew condition

    first.left < second.left ->
      ((pair first).present ∩ (pair second).absent).Nonempty.

Together with self-disjointness, the finite skew-Bollobas inequality would
give exactly `choose (k-2) (r-1)`; the event universe may depend on the ambient
child, but the bound depends only on the two fixed set sizes.  The construction
must be local to each span, since choosing absent events afterward to hit
earlier present sets would be circular.

The cheapest stop/go test uses only the newly formalized defective pair.  Its
first necessary condition is that the actual-ray incidence support of `(2,5)`
contains an event absent from the support of `(4,6)`.  If that support
difference is empty, every such skew selection is impossible and this redirect
must stop before a larger census or Lean engineering.

## Reproduction

    python3 scripts/check_active_reflected_representative.py \
      --output data/derived/e3-active-reflected-representative-counterexample-k6-n8.json
    python3 scripts/replay_active_reflected_representative.py \
      data/derived/e3-active-reflected-representative-counterexample-k6-n8.json
    python3 scripts/enumerate_active_reflected_transition_hall.py \
      --maximum-n 8 \
      --output data/derived/e3-active-reflected-transition-hall-k6-n8.json
    python3 scripts/check_active_reflected_transition_hall.py \
      data/derived/e3-active-reflected-transition-hall-k6-n8.json
