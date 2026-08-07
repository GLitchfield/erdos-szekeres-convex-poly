# Conserved gap-token carrier and selected-branch pivot gate

## Question

Can the failed sum of local rank-two adjacencies be replaced by a genuinely
tree-global charge that owns an actual object, is transported rather than
duplicated, and survives both the three-point local/global-gap obstruction and
the ten-point cross-color obstruction?  If so, what is the first honest bridge
from that carrier to the uniquely saturated published child?

## Frozen design review

Three read-only persona packets were frozen at revision
`44b805506ec21656ba182e510dd45d1cc298e4c1`.  Their task-packet SHA-256 values
were:

- innovation: `7e7f155d2bb6ea1db6fed913768457038c18f7408ebef0f20484280f741a3db9`;
- contrarian: `9554ee69ec2fc997c6e107855bb17b02c3e20f84e17bb79e14b25728fa0c0bc4`;
- architecture: `276b7c3f8d3d9b7738ea12fb236e8d013a5f0061cd6a39bda611c039eeb7faec`.

All three independently proposed transporting adjacency threads by an actual
vertex owner.  This consensus was proposal-level evidence only.  It did not
establish a recurrence, retained-core membership, a Boolean history, or a
Pascal bound.

## Lean result: exact conservation

`StructuralChargingGapTokenConservation.lean` defines one token for every
sweep adjacency plus a sentinel.  The gap token is owned by its right endpoint
and the sentinel by the support minimum.  Lean proves:

- the owner map is bijective with the actual support vertices;
- disjoint nonempty child token families merge bijectively into the parent;
- the merge preserves the actual owner; and
- on hidden gaps it agrees exactly with the previously compiled canonical
  entering-parent-crossing transport.

`StructuralChargingTreeTokenConservation.lean` folds this equivalence over an
explicit decomposition tree.  Equal root owners come from the same
branch-indexed leaf charge and therefore the same Boolean leaf address.

`StructuralChargingGapTokenRegression.lean` checks the frozen gates.  On the
three-point tree, child gap `(0,2)` becomes root gap `(1,2)`; the two child
sentinels become the root sentinel and root gap `(0,1)`.  Both sides have
exactly three tokens.  On the alternating ten-point root, the two five-token
children merge to exactly ten parent tokens.  No cap/cup endpoint quotient or
single-coefficient payment is used.

## Unique branch and adversarial review

`StructuralChargingConservedBranch.lean` proves that feasible active published
arithmetic selects exactly one saturated branch, specializes the result to
actual lower and upper published slices, and exposes the corresponding
retained core.  This is selection only, not conservation or payment.

A bounded review at committed revision
`8053a6f0ceb34e7a1b57d3aae6c1d2e007a2aeb3` used packet SHA-256
`fbdd71e0ca938691364140abbf35412390107762248744033d25690758808b12`.
Sol returned `partially_supported` at high confidence and selected the
smallest proposed bridge: first prove that a live hidden-gap owner belongs to
the uniquely selected child, then choose a retained core containing it.  Its
raw structured result has SHA-256
`890cc017bd6e7c83e8b7ff87bc3d26f9b0cb3f6c77c95367bca420d87ffdb01c`.
Claude Fable returned HTTP 429 with zero tokens because its Fable 5 usage limit
was exhausted.  No Fable judgment, reciprocal round, or reviewer consensus is
claimed.

## Cheapest falsifier and corrected resource

The selected owner-membership premise is false.  At the first feasible
nonsingleton scalar boundary `(a,u,k,a',u') = (4,6,6,3,2)`, take a two-vertex
lower child `{0,11}` and its ten-vertex complement.  The actual published slice
indices are `2` and `3`, and the unique saturated branch is upper.  The lower
gap `(0,11)` is hidden by the upper child, but its conserved right-endpoint
owner `11` lies in the lower child.  Lean packages all of these facts and
refutes the universal owner-follows-branch statement in
`StructuralChargingSelectedBranchOwnerCounterexample.lean`.

The failure identifies a better actual object.  The canonical entering parent
crossing has a left endpoint strictly inside the hidden gap.  This pivot lies
in the opposite child, hence in the branch selected by the compatible promoted
color.  `StructuralChargingSelectedBranchPivot.lean` proves:

- the entering pivot lies strictly between the hidden gap endpoints;
- it lies in the selected opposite child;
- distinct hidden gaps have distinct entering pivots;
- branch-compatible hidden sources embed into actual selected-child vertices;
- a singleton pivot can be retained in an actual published slice; and
- if all pivot sources fit the retained-core cardinality, one simultaneously
  chosen published slice contains every canonical pivot.

Thus the corrected local state has two distinct roles: an immutable endpoint
owner for tree-global transport and an active pivot seed for the selected
published branch.

## Remaining obstruction and disposition

The elementary source-child bound is too weak for the retained core.  Lean
checks the feasible saturated scalar state `(4,8,8,3,4)` with child sizes
`10+13`: a ten-vertex source child permits nine hidden adjacencies, while the
selected upper core has cardinality only eight.  This does not prove that all
nine hidden gaps occur in an open geometric configuration.  It proves that
pure cardinal bookkeeping cannot establish the needed core capacity.

Conserved adjacency threads are promoted as the canonical conservation and
nonreuse carrier, not as a completed recurrence.  The next exact mathematical
target is a geometry-sensitive pivot-capacity theorem: in an open feasible
saturated split, bound the compatible hidden-gap pivots by the selected
published-core cardinality, or produce a forbidden cap, cup, or strong
polygon.  It must be falsified first at the `k=8`, `10+13` scalar gate and must
not merge the two disjoint color increments of the ten-point obstruction.

## Reproduction

```console
lake build
make test
```

All promoted statements above are kernel-checked Lean theorems.  The persona
and Sol/Fable outputs remain advisory evidence.
