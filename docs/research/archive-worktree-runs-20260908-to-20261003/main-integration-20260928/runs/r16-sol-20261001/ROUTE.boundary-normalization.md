# Candidate exposed-end normal forms (unverified, 2026-10-01)

These are proposed diagnostics/proof routes, not accepted theorems or results.
Part1's weakening check is still pending; do not use these as established facts.

Let sigma be a legal one-level root on side s, with word starting with child,
old maximum m, and p=0. Let rest keep every child except p.

1. Opposite-side complement: sigma.part rest (opposite s) n may have exactly
   the bound of the root obtained by deleting p, keeping maximum m and side s,
   and changing the opposite global G to min(G-1,k-n), provided G>=2.
   Existing ctx_boundary_marker_erase_normalize gives the upper comparison
   while preserving older opposite-axis history, but gives no equality.
   The removed boundary letter becomes an unindexed inert endpoint; it must
   also be deleted without changing the recursive bound.

2. Same-side complement: sigma.part rest s n may have exactly the bound of
   a one-level root formed by changing p to an ext1s marker, retaining all
   old ext1s markers, and replacing the maximum by max(n,m+1).
   Globals and k stay fixed. The merged maximum need not remain <=k-2.

Reason for (2): in every further descendant all new external positions and
child positions are strictly right of p. For the chosen side, the boundary
level contributes exactly one left extension after every younger history;
it contributes no right extension. The older root markers can never extend
farther left after that boundary. Merging their support with p therefore
preserves full chain extensions. Joining the boundary sibling contributes
n plus the younger chain extensions; joining the older sibling contributes
m+1 plus those extensions. Their maximum is max(n,m+1). Opposite-side
extensions are unchanged. This needs a proof for all descendants/fuel,
not merely the initial point limits.

A possible reusable statement uses arbitrary younger prefix history and two
oldest same-axis levels N,N+1. Level N has only position0, level N+1 is actual
and wholly to its right, and all children/younger markers are right of0.
Merge N+1 into N with maximum max(M_N,M_(N+1)+1), then prove child-endpoint
limits and every-fuel bounds equal. Parts preserve the boundary geometry.
Empty child sets, absent chosen levels, unused levels, nat subtraction and
zero-valued parts need explicit treatment. An actual older marker is essential
to control sideAt's default lower value.

Even successful normal forms do not establish the exposed-end exchange:
every original proper interval cut must still be bounded by some legal
singleton-at-p cut, allowing both orientations and all couplings. Fixed
positions are proposed only when exactly one end is marked, following the
selector evidence. Neither-marked roots require the full four-candidate set.
No same-coupling/fixed-orientation lifting or R14 inner-block descent is proposed.
