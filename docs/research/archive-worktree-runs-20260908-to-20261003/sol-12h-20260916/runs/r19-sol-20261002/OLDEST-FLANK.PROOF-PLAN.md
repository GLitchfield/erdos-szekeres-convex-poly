# Exact oldest singleton-flank normalization

2026-10-02. R19 verification of why the oldest unit flanks lift the raw PEEL
gap to global parameters4,4 without repairing its singleton-cut failure.
This is an invariant interpretation, not a new singleton-selection conjecture.

The selected level N is the last indexed maximum. Its external positions are
exactly[x], its maximum m>=1, and all children and all younger same-axis markers
lie strictly on one side of x. Other-axis markers are unrestricted. Positive
actual labels exclude old level0 markers from a new descendant level1. Raw
unindexed older positive letters remain allowed, so normalization can be
iterated after the selected marker becomes unindexed.

Normalize by taking the maxima prefix before N and replacing its axis global
parameter G by min(G-1,k-m), leaving the entire word unchanged. No WellFormed,
global lower bound or k-coupling premise is needed.

1. The full selected-side level list is the younger list followed by[N]; the
   other side has exactly the younger list. Below every younger top the lists
   and walk steps agree. All older indexed maxima agree.
2. Every sublist walk either omits N or is an old walk followed by N. A left
   walk only moves left, and a right walk only moves right. The boundary
   condition keeps the active walk endpoint on the children side of x, so
   appending N adds exactly one to its count. It adds zero in the other
   direction. Thus selected chain count=oldPure+1; other chain count is equal.
3. Every younger strong-join contribution is identical. The N contribution is
   oldPure+m. Since m>=1 this also dominates the full pure count oldPure+1.
   Therefore full selected join=max(oldJoin,oldPure+m); other join is equal.
4. The selected limit identity follows in natural arithmetic, including zero
   saturation:
   min(G-1-(E+1),k-1-max(J,E+m))
   =min(min(G-1,k-m)-1-E,k-1-J).
   The other axis is unchanged. Thus every child-endpoint limit agrees.
5. The word, children, run count, blocks and k agree. Normalization commutes
   with every part when the selected level shifts N->N+1. Its singleton and
   maximum are preserved. New same-axis markers come from former children and
   satisfy the boundary condition; older younger markers retain it. Positive
   labels and last-level identity are preserved. Base equality and fuel
   induction give equality of every recursive bound and hence bound.

Reuse existing boundary-normalization geometry/part transport, sorted-level
facts, sublist fold steps and max membership APIs. Search `boundary marker
exact equality normalization oldest singleton` found no duplicate; the existing
ctx_boundary_marker_upper_normalize gives only one-way comparison under weaker
hypotheses. No broader two-sided/multiple-marker claim is intended: markers on
both sides can add two extensions, and an indexed later level can alter joins.
