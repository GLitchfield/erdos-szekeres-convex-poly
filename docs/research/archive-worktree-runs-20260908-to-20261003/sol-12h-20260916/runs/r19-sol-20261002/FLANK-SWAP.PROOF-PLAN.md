# FLANK-SWAP: exact mechanism and transport plan

No theorem credit yet. The statement must require both designated levels to have
physical letters. The existing diagnostic tested that domain; absent levels are
not flanks. Clean diagnostic `20261002-083642-6bb0ca` gives `SS`, `(a,u,k)=(5,5,6)`,
maxima `(1,2) -> (3,2)`, values `10 -> 4`. It is not Lean-certified.

Register the full opposite-flank statement, with arbitrary older letters and
arbitrary multiplicities: level 1 is entirely left of every child and level 2
entirely right, or the mirror. Both levels are nonempty. Different sides keep
each physical level's maximum; same sides use `(M,M-1)`,
`M=max(m1,1+m2)`, with the brief's legality conditions.

## Why the descendant limits are identical

Carry the special pair as levels `L,L+1` through the fuel induction. All earlier
levels arise from discarded original children. They therefore lie between the
two flanks, as do the current children. This is the needed invariant: comparing
the flanks only to the current children would lose the earlier-level information.
There is no restriction on older levels.

For each direction, one flank's step is inactive. The left walk cannot use the
right flank, either before or after using the left flank. The right walk has the
mirror property. Thus the two adjacent steps commute on any endpoint reached
through earlier levels. Relabel a selected ordered level list, and restore the
order of the special pair if both were selected. All subsequent older steps see
exactly the same position and count. This gives full extension equality even
when older letters lie outside the special flanks.

For a join at the first special level, write the sum of earlier extension maxima
as `alpha`. At the second special level, the earlier flank contributes exactly
one if its side matches the chain type. Presence is essential at this point.
On the same side, the two old join candidates are `alpha+m1` and
`alpha+1+m2`; their maximum is `alpha+M`. The new candidates are `alpha+M`
and `alpha+1+(M-1)`, which have the same maximum. On different sides the other
flank is inactive for the given chain type, so exchanging the two individual
maxima preserves each candidate. Joins at all other levels use either neither
special level or the whole commuting pair and are unchanged.

The word map preserves children, run boundaries, and available cut blocks. It
commutes with taking a part, with `L` shifting to `L+1`. Maxima updates commute
with prepending the new coupling. Identical endpoint limits give equal bases;
equal recursive parts then give equality of the cut maxima by induction on fuel.

## Planned Lean implementation

Reuse the transport pattern and sorted-sublist helpers in
`ESBlueprint/B/CtxBoundLeMergeSameSideLevels.lean`; reuse `leftStep`, `rightStep`,
their count translation lemmas, and extension-as-sublist-maxima definitions from
`CtxSatisfiesOfDeepBelowSplit`. Use local `have` declarations inside the registered
node; do not alter any existing statement. A generic direction parameter should
avoid duplicating the walk argument.

No sibling-penalty narrowing is proposed. The obligation is equality of the full
bound, with the requested maxima rule. The remaining formal obstacle is the
ordered-sublist permutation and the exact one-unit contribution at the truncated
special level; the proof idea above explains why both hold.
