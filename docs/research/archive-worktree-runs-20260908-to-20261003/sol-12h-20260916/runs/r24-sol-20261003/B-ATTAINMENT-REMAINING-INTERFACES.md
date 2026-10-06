# Exact remaining interfaces for the constructive B route

2026-10-04 01:16 UTC. Proof design, not a compiling B-attainment theorem.
Endpoint lifting is fully accepted `fa6dacd1`; the universal legal T lower
leaf is fully accepted `aebb6505`. Assigned-limit fixed-root v4 is fully
accepted at unchanged type `a89e497ebd1cfbea`, commit `e0e31525`.
All five stages of `op-e4fb2f1518694e80` passed, including full extraction
`20261003-203849-0c96ab`, audits and exact source review.
The upper N<=T and a closed sibling-loss invariant remain unknown.

For a WellFormed context sigma with sigma.k>=3, the desired witness has exactly B(sigma)
points, a weakly increasing map z into ORIGINAL child positions, all
nonempty cup/cap cardinalities bounded by sigma's limits at their actual
first/last assigned positions, and no strong sigma.k set. Require
decomposability and realization when the cardinality is positive. Permit
the empty configuration explicitly at value zero. Literal Ctx.Satisfies
is unsuitable: it fixes cardinality to the number of original child slots.

## Uniform-label base

The first original child position p suffices for a sigma.base witness,
even if other slots are unused. Give every constructed point label p.
If there is no original child position, base is zero and the witness is
the explicit optional empty configuration.
If either diagonal limit is zero, use the empty witness; if their minimum
is one, use a singleton. Otherwise instantiate the universal T constructor
with diagonal cap+1 and cup+1. WellFormed legal globals and the definitions
give both parameters at most sigma.k. Constant labels make monotonicity
trivial and every endpoint constraint the same diagonal bound. This needs
a general compiled constructor, not finite cases or a new upper argument.

## Stable ordered merging

Take two independently constructed point domains and their monotone labels
in disjoint child slot sets. Merge the two labeled sequences in increasing
label order, preserving each sequence's internal order. There can be ties
inside one sequence, but none across sequences. The merge gives increasing
order embeddings of both domains into the sum domain, an exhaustive
disjoint image partition, and a monotone combined label map.

One hand construction avoids a new execution algorithm: tag each point by
its side and old index, and order all tags lexicographically by
(assigned label, side tag, old index). Within each side, monotonicity of
labels and the index tie-break make this order strictly preserve old order.
The tags are distinct. Enumerating this finite ordered set gives a bijection
with Fin(nL+nU); its inverse restricted to each side gives the two increasing
embeddings. Exhaustiveness and disjointness follow from the tags, and the
combined label is monotone because it is the first lexicographic coordinate.
Cross-label separation follows from disjoint formal slot sets. This is a
general order argument, not a compiled theorem or a new workflow script.

A contiguous block among a context's formal child positions also becomes
an interval among its constructed occupied points: any label between two
block labels is a kept label in that block, and cross-child ties are
excluded. Unoccupied slots do not change this statement. Suppress steps
whose actual child is empty; every remaining positive-positive root retains
an interval child in actual sweep order. Thus zero-child terms cannot repair
the persistent maximal-root obstruction. This is part of the hand B-tree
interpretation; the complete construction is still uncompiled. Search:
`interval-root-assignment-final-search.json`.
Actual reusable APIs located and read: Finset.orderIsoOfFin and
orderEmbOfFin in Mathlib/Data/Finset/Sort.lean:189–224; List.Pairwise.merge
in Mathlib/Data/List/Sort.lean:349 supplies an alternative sorted-list route.

Use shared list merge/sorted APIs or a general finite ordered merge theorem;
search the source and harness before implementing any workflow code.
The mathematical contract is order preservation and exact label equality,
not arbitrary simultaneous geometric coordinates. Accepted generic coloring
pushforward retains each child's colors, decomposition, chain sets and
strong sets on its image. Preserve min/max endpoints through the order
embeddings and cardinalities through their injectivity.

At the image supports, the zero-gain path consumer already bounds lower
cups by alpha and upper caps by beta. Thus independent-color gluing may
first be used with trivial allowed predicates: it supplies the actual deep
root, decomposition, agreement and strong avoidance from this coupling.
Agreement transports the assigned child contracts. The assigned-limit
transfer then supplies every parent endpoint limit. This order avoids
assuming the parent constraints in order to build the parent.

## Exact recurrence induction

Induct on boundFuel, retaining WellFormedness and original-slot membership.
Prove the witness assertion for every fuel F. At the end instantiate
F=sigma.childPositions.length+1, exactly as Context.bound does; no separate
fuel stabilization theorem is required for this constructive direction.
Fuel zero has an empty witness. A one-run base uses the uniform-label
constructor. Otherwise choose an actual maximum term of the finite cuts
list. The source's blocks are nonempty proper intervals of child positions;
their complements are nonempty, and both have fewer slots. Both orientations
and every share in the actual recurrence must be covered.

Map the source parameters correctly: its first term has block lower with
reserved sibling maximum dp, and rest upper with reserved maximum
c=k−1−dp. Thus beta=dp bounds upper caps and alpha=c bounds lower cups.
The second orientation swaps supports, retaining these shares. The
registered transfer uses lower part reserved beta and upper part reserved
alpha, exactly this convention. All claims here use the actual source sum,
including one-zero terms, despite the older bound docstring's wording.

The proper formal partition supplies each part's new side and all opposite
converted-slot markers. Positive old levels prevent raw level zero from
merging into level one. New shares lie in1..k-2, retaining the declared
maximum invariant. Child slot membership supplies the label inequalities
and disjointness used in merging and transfer.

If an actual constructed child is empty, discard it and use inherited
ctx_part_limits_le with the other child's already established strong
avoidance. Do not create an empty deep decomposition root. If both are
empty, use the optional empty witness. The recursive witness size is the
selected exact sum, including these zero-child terms.

This would prove the hand optional inequality B<=N and make the general
two-cap interval obstruction a compiled B undercount argument. It would
not prove required-slot occupancy, literal upper bounds, interval normal
form sufficiency, the full profile optimization law, or the general upper
threshold. The remaining construction uses ordered merging and finite
induction; the missing upper bound instead needs a stable mathematical
capacity invariant. Neither narrowing is reported as a result by itself.
