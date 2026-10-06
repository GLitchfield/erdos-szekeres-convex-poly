# Critical unequal two-cap upper

2026-10-03 18:43 UTC. Hand proof shape, no Lean acceptance. This explains the
extra critical-strong loss in TWO-CAP-GATE-FORMULA.md; it does not replace
the multiple-zone allocation conjecture with a scalar fit.

For p>=4, two ordered caps of sizesp,p-1 cannot cover a decomposable set
with cap/strong limits p and cup limit3. Expose a nonempty deep root L/U.
First rule out root degeneracies and whole-block lower cases explicitly;
the mixed-cap intersection bound alone cannot establish U nonemptiness.
When L has at least two points, its vacuous two-cup forces every U cap to
have rank at mostp-2. Both blocks meet L; otherwise their full upper cap or
the classical two-cap induction contradicts strong coupling/cup avoidance.

The fullp block then has exactly two L endpoints, since U has at mostp-2
points in that cap and a mixed cap contributes at most two L points. The
other block has one or two. If both have their inner endpoint in L, select
upper0,lower0-last,lower1-first,upper1 to obtain a four-cup. This includes
two endpoints from each block. In the remaining case the other block has
only its outer L endpoint; U consists of two full(p-2)-caps. Its cap rank
is at mostp-2, so the classical two-full-cap lemma forces a four-cup in U.

Whole-lower cases use the same coupling carefully. If the fullp block is
wholly L, an inner L endpoint in the mixed block makes a lower three-cup
ending before an upper point and hence a four-cup. With only the outer
endpoint lower, the mixed upper cap has sizep-2, while the whole lower
p-cap plus that endpoint is not a(p+1)-cap and contains a three-cup; their
strong union has sizep+1. If the(p-1)-block is wholly L, mixed fullp has
at least two L endpoints by the two-cup coupling, hence exactly two and
upper sizep-2. The resulting lower cardinalp+1 cannot be a cap, so again
a lower three-cup plus the upper cap violates strongp.

After this and the already compiled equal-full critical root theorem, the
two-zone upper min(P+Q,2R-1,2s-2) has a direct cardinal argument. If R<s,
the bound2s-2 follows already from two zone sizes<=R. If R=s, violating it
requires only the full-full or full-nearly-full patterns handled above.
The classical two-cap induction supplies2R-1 independently of strong.
The explicit lower family covers all P,Q,R,s, including the nested nearly
full case. The remaining work is general formalization, not more case census.
