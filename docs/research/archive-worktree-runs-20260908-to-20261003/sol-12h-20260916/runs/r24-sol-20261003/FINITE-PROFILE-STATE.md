# Exact endpoint state for the finite context recurrence

2026-10-03 17:07 UTC. General hand argument, not a compiled Lean theorem.

## Statement

Assume the context is WellFormed; in particular, every external level is positive and each level has one consistent side. List its existing S slots in order as0,...,n-1. Expand its run cup/cap matrices to these slots: Cp[i,j],Cu[i,j]. Record a barrier between consecutive slots exactly when the original word has an external marker between them. Keep all declared levels, including unused levels with default lower side, and natural-number subtraction. Fix s=k-1.

For a nonempty proper subset K of the slots, create the ordinary context child with those slots retained, side h and opposite maximum m. Its barriers are inherited between consecutive retained original slots; every gap containing a converted S slot becomes a barrier. Its non-growing matrix is inherited exactly. For a lower child the growing matrix is

    Cu_K[i,j] = max(0, min(
      Cu[i,j], s-m,
      {Cu[x,j]-1 : x outside K, x<i},
      {Cu[i,y]-1 : y outside K, y>j},
      {Cu[x,y]-2 : x outside K, x<i, y outside K, y>j})).

For an upper child use Cp in the same formula. All indices here are original slot indices; then restrict/reindex to K. Empty families add no minimum constraint.

Thus the finite bound B depends only on these matrices, the literal slot order/barriers and k. It does not require the remaining ancestor word or its list of maxima once their endpoint matrices have been computed. This does **not** say B depends only on a free zone profile: slot multiplicity and cut resolution remain essential.

## Why the transform is exact

The shared limits function computes extension paths separately on the left and right of a chain. It visits levels in increasing order and may add at most one endpoint on each side at a level with the growing side. A strong join at that level uses the already selected endpoint counts plus its sibling maximum. The final extension count is also a strong candidate.

For the new growing level1, each path chooses zero or one converted slot before i and zero or one after j. Once these choices are fixed, every subsequent transition is an old transition with its level shifted by1. The initial boundaries for those old transitions are i/j if no new endpoint was chosen, or x/y when one was. Increasing the external-position coordinates to insert the converted slots preserves every strict comparison between old external markers. Consequently the old admissible capacity is precisely Cu[i,j],Cu[x,j],Cu[i,y] or Cu[x,y], minus the number0,1 or2 of new endpoints.

At the new strong join no endpoints have yet been selected, so its additional constraint is s-m. Taking the strongest constraint over all path choices gives the displayed minimum. The zero-choice family contains all inherited constraints; the one- and two-choice families give every additional constraint. Conversely every displayed term comes from those choices and old paths, so this is equality rather than a sufficient inequality.

For the non-growing color, level1 is skipped. Converted slots are never selected, and shifting all old levels preserves the old transition and join calculations exactly. Unused old levels retain their side and maximum after shifting; none is deleted. Truncating at zero commutes with the displayed further subtractions: for e>=0, max(0,max(0,t)-e)=max(0,t-e).

## Why this evaluates the same finite B

Induct on the number of retained S slots. With no barrier there is one run; all endpoint entries equal its diagonal limit. Use the original arithmetic base:0 when either limit is0,1 when their minimum is1,otherwise T(cap+1,cup+1,k). This is the original finite-bound definition and assumes no upper theorem for T.

With a barrier, enumerate exactly the original nonempty proper contiguous S blocks, their complements, both orientations and every sibling split m in1,...,s-1. Every child has fewer slots. The exact transform above and the induced barriers supply its induction state. Both child values are included even when one is0. Taking the same maximum yields the same result. No occupancy requirement, slot deletion, alternative root shape or upper-bound oracle is introduced.

## Receipts and limitations

- `profile-transform-check.json`, guarded job20261003-130442-1dfe20: all39440 child transforms in400 depth3 sample contexts agree exactly with the original shared signature-limit implementation,1.551s algorithm.
- `profile-bound-check.json`, guarded job20261003-130544-868d59: all400 immutable C bounds plus unchanged4/6-slot cap-block B8/B9 receipts agree;0.944s total,2087 states. The6-slot query took0.624s versus original65.100s. These timings are matched algorithm observations, not a full-cost savings accounting.
- `profile_transform.py` is the small pure mathematical transform. `profile_bound.py` retains the original finite recurrence and uses bounded standard memoization. Existing context limits, child constructor and threshold arithmetic are reused.

The argument remains hand mathematics; cross-implementation tests do not prove general equivalence in Lean. The resulting evaluator is of B, **not** of N. Any literal counterexample computed with it must retain that semantic qualification until the transform/equivalence theorem or the specific finite bound is kernel-certified.

Qualification added23:23UTC: do not extend this converted-slot formula to arbitrary raw contexts containing external level0. Such a letter shifts into the new level1 and supplies another endpoint. For raw a=u=6,k=8,maxima[],word S S ext0L,keep[1],lower,m1, the parent cup entries are5 and this formula would give4, while the actual part ext1L S ext1L has chainExt2/joinExt2 and cupLimit3. This is a hand definition calculation, not a new compiler or probe receipt. It does not affect the positive-level numerical domains. The general raw endpoint-lifting theorem has an explicit side premise and includes every new level1 marker, so it does not assume this matrix equivalence.
