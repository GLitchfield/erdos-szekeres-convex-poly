---
title: Classify finite sweep realizability through six
type: research
mode: AFK
status: closed
claim: codex-finite-sweep-realizability-2026-08-14
blocked_by: none
---

## Question

For ordered triple colorings on four, five, and six vertices, does the complete
rank-three one-change law characterize exactly the colorings induced by planar
general-position point configurations?  Separately, which rightmost extensions
can be made from one fixed coordinate realization of a parent coloring?

The first question concerns full order types.  The second concerns realization
spaces and must never be promoted from one representative to a universal
order-type statement.  Complete orientation signs contain all affine-
combinatorial information used by the project's convex-position predicates;
this ticket makes no claim about distances or angle magnitudes.

## Decision criteria

The formal contracts, finite evidence contract, staged gates, outcome labels,
consumer audit, and resource stops below are binding.  Coordinate-search
failure is never nonrealizability evidence, and five/six Lean promotion
requires a named load-bearing consumer.

## Frozen formal contracts

The general bridge target is:

```lean
theorem IsSweepRealizable.oneChangeOn_univ
    {n : ℕ} {χ : TripleColoring n}
    (hχ : IsSweepRealizable χ) :
    OneChangeOn χ Finset.univ
```

The finite completeness predicate and initial public targets are:

```lean
def OneChangeRealizabilityCompleteAt (n : ℕ) : Prop :=
  ∀ χ : TripleColoring n,
    OneChangeOn χ Finset.univ ↔ IsSweepRealizable χ

theorem oneChangeRealizabilityCompleteAt_four :
    OneChangeRealizabilityCompleteAt 4

theorem oneChangeRealizabilityCompleteAt_five :
    OneChangeRealizabilityCompleteAt 5

theorem oneChangeRealizabilityCompleteAt_six :
    OneChangeRealizabilityCompleteAt 6
```

The names may be qualified by a new module namespace, but their mathematical
statements may not be weakened.  Existing
`SweptConfiguration.turnSequenceAllowed` supplies the pointwise easy direction.
Existing `IsDecomposable.isSweepRealizable` supplies the realization direction
for every catalog state whose exact decomposition predicate is proved.

## Frozen finite evidence contract

The admitted abstract catalogs have 8, 62, and 908 labeled `OneChangeOn`
colorings at four, five, and six vertices.  Their exact catalog SHA-256 is
`e80a7c8e955f3081be3e173b8a8511f35ffffcebaefe5ee7595c3381c4d8715c`.
The decomposable counts are 8, 62, and 718.  New explicit coordinate search at
six is therefore restricted initially to the 190 nondecomposable masks.

Every coordinate certificate must use exact rational numbers and record strict
sweep order, every nonzero triple determinant, and the complete induced mask.
An independent checker that imports no producer logic must establish exact
catalog coverage and reject at least: a coordinate change, a color change, an
omitted mask, a duplicated mask, and a broken sweep order.  Failure to find
coordinates is `REALIZABILITY-UNKNOWN`, never nonrealizability evidence.

## Work order and gates

1. Land the general realizable-to-one-change bridge and the complete four-point
   vertical slice, including exact coordinates, independent replay, and the
   compiling equivalence.
2. Reconstruct five/six coverage from the frozen catalog.  Reuse the compiling
   decomposable-realization theorem and seek exact coordinates only for the
   190-state six-point remainder.  The union must equal the frozen catalog
   exactly.
3. Freeze a one-page consumer audit for `FP-02.F` and `FP-16`.  Bulk five/six
   Lean promotion proceeds only if the recurrence-structured proof architecture
   remains under gate and a named consumer justifies it.  Computational
   coverage may finish without that promotion.
4. Only after global coverage, run exact arrangement-cell diagnostics on named
   coordinate parents.  A difference between two realizations with the same
   mask may establish realization-sensitive extension behavior.  Agreement of
   sampled representatives proves no universal invariance.
5. Do not begin seven or above in this ticket.  Reconcile the portfolio after
   six; seven/eight and the first nonstretchable nine-point boundary require a
   new frozen packet.

The classification proof should factor through
`oneChangeOn_univ_succ_iff`: 16 candidate extensions at the first step, 512 at
the second, and 63,488 at the third.  Generated proof modules must be bounded;
no million-case monolith, `native_decide`, unverified oracle, or silent theorem
change is allowed.

## Outcomes

- **`GEOM4-LAND`:** the exact four-point equivalence compiles.
- **`LOCAL-EQUALITY-456`:** independently checked finite evidence covers the
  full 8/62/908 catalogs.  This is computational evidence only.
- **`LOCAL-EQUALITY-456-LEAN`:** all three exact equivalences compile with
  standard axioms only.
- **`FIXED-EXTENSION-SENSITIVE`:** two exact realizations with the same parent
  mask have different independently checked rightmost cell-extension sets.
- **`REALIZABILITY-SEPARATES-n`:** an admitted mathematical certificate proves
  a one-change coloring nonrealizable.  Search failure cannot select this.
- **`REALIZABILITY-UNKNOWN`:** exact witness coverage is incomplete.
- **`RESOURCE-STOP`:** a bounded process or artifact gate fails; make no truth
  claim.

None of these outcomes changes `D-UPPER` without a separate named consumer.

## Resolution

### Results (2026-08-14 and 2026-08-15)

The bounded work reached four admitted outcomes:

1. **`GEOM4-LAND` (`file_compiles`).**
   `IsSweepRealizable.oneChangeOn_univ` and
   `oneChangeRealizabilityCompleteAt_four` compile in
   `TripleColoringRealizability.lean`.  The converse uses eight explicit
   integer-coordinate sweep configurations.  Direct Lean, targeted Lake, and
   declaration-axiom gates pass; the audited public theorems use only
   `propext`, `Classical.choice`, and `Quot.sound`.
2. **`LOCAL-EQUALITY-456` (`computational_evidence`).**
   Independent implementations reconstruct the complete 62/908 catalogs,
   validate 62 five-point and 718 six-point decomposition trees, and check
   exact integer coordinates for precisely the remaining 190 six-point
   states.  Thus the checked coverage is 62/62 and 908/908.  This is not
   `LOCAL-EQUALITY-456-LEAN`: the universal five/six declarations were not
   generated.
3. **`FIXED-EXTENSION-SENSITIVE` (`computational_evidence`).**
   An exact strict-half-plane cell enumeration compares two coordinate
   realizations of every five-point parent coloring.  The extension sets differ
   for 43 of 62 parents.  The independent checker validates all 1,550 claimed
   cells and their rational witnesses.  Therefore one representative's
   rightmost cells cannot be treated as universal for its order type.
4. **`EXTCELL-LAND` (`file_compiles`).**
   `isSweepRealizable_succ_iff_exists_rightExtensionData` gives the exact
   realization-sensitive recurrence.  It retains one existential parent swept
   configuration, a new point strictly to its right, every old-pair
   determinant nonvanishing condition, and all initial and incident colors.
   The converse reconstructs the full swept configuration.  No theorem claims
   that feasible extensions are determined by the parent's abstract coloring.

The corruption suites reject coordinate, color, omitted-mask, duplicate-mask,
broken-sweep, decomposition-tree, extension-cell, witness, and verdict changes.
Certificate/checker hashes are recorded in the run result; the deterministic
scripts are retained in `scripts/`.

## Consumer disposition

The required consumer audit rejects bulk five/six Lean promotion in this work
block.  `FP-02.F` needs a nine-vertex nonstretchability exclusion, so complete
realizability through six cannot discharge it.  `FP-16` needs a global
17-point forcing argument; allowing every six-point one-change type supplies no
new six-local forbidden pattern.  Generating hundreds of finite Lean modules
would therefore establish true but presently inert theorems.

The exact geometric extension interface is also strategically neutral.  It
formalizes rather than reduces the existential realization-space obligation:
no current `D-HALF`, `D-NORMALIZE`, or state-567 consumer extracts a smaller
cell/covector invariant from it.

No load-bearing destination edge moved.  The useful boundary information is
negative: realizability adds no independently checked local restriction through
six beyond `OneChangeOn`, and coordinate-representative extension sets are not
order-type invariants.  Seven and above remain outside this ticket.  Successor
ticket [0016](0016-classify-geometric-extension-fibers.md) has now formalized
the exact abstract/fixed/union fiber boundary and checked the fixed-coordinate
arrangements through six; it found no compressive consumer and left the
seven-point gate unopened.  Any later seven/eight packet must therefore name a
consumer and pass that successor's revival gate rather than merely extend the
census.

## Evidence

The bounded Sol/Fable review at revision `e45f230` used evidence packet SHA-256
`2d8d7baabd438388ce8352fbba739df2bc89bb0a3ec93a9ad8da67c5150fb737`.
Both reviewers returned `partially_supported` and recommended `MODIFY`.  The
binding dispositions are reflected above: start with an end-to-end four-point
pilot, reuse decomposable realization instead of producing 718 redundant
six-point witnesses, keep fixed-realization cells separate, and require a
consumer audit before bulk Lean promotion.  Review output is advisory, not
mathematical evidence.

Frozen source hashes at admission include:

- `ErdosSzekeres/Sweep.lean`: `6c3d002d...ba8a8`;
- `ErdosSzekeres/SmallCases.lean`: `68824f9a...2468`;
- `ErdosSzekeres/DecomposableRealization.lean`: `293eb6a2...451`;
- `ErdosSzekeres/TripleColoringExtension.lean`: `a03884e8...b568`;
- abstract producer/checker: `6e7ab867...5569` / `4d854373...d60`.

## Resources and approval boundary

- at most 30 minutes, 8 CPU cores, and 16 GiB RAM per process;
- at most 5 GiB under the ignored run tree;
- one serialized Lean builder lane;
- no network download, software installation, destructive action, or resource
  increase in the admitted block;
- any external order-type database, new solver installation, or larger bound
  requires a separate exact approval.
