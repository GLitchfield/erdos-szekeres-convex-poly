# Mathematical analysis

## Actual companion

Write

`rest := σ.childPositions.filter (· ∉ keep)`,
`A := σ.part keep s m`, and `B := σ.part rest t n`.

At the legal `k=6` chosen-kept extreme, `m=4` and `n=1`.  A retained source
child `p` is an actual indexed marker in `B.extPositions 1`, with
`B.sideAt 1=t` and `B.maximumAt 1=1`.  The source chosen markers at levels
`N<M` survive in `B` at `N+1<M+1`; all actual chosen-axis positions remain
`x` or `y`.  No argument may replace `B.extPositions 1` by a singleton.

## Exterior marker saving

The sharp two-marker potential is

`P(v) = choose(v+1,2) + v`,

where `v` is the opposite width after uniform left/right extension losses.
If the actual level-one marker `p` lies strictly left of every child of `B`,
then every child has `leftExt t (N+1) >= 1`; if it lies strictly right, every
child has the analogous right extension.  Since the opposite global is at
most five, the remaining width is at most three and `P(v) <= P(3)=9`.

This uses the marker below the older chosen level, rather than only its
full-history endpoint exclusion.  It therefore gives a direct every-fuel
bound and preserves the original recursive semantics.

## Why the internal marker is different

When companion children occur on both sides of every synthetic level-one
marker, there is no uniform extension loss.  Splitting the children at the
marker gives separate triangular charges, and canonical chosen-capacity
splitting gives separate low/high pair charges.  Neither sum accounts for a
shared recursion reservation, so the known `6+6` and `6+9` diagnostic pair
sizes still overcount the actual maximum eleven.  A full proof needs a
coupled row/column or cut-reservation potential, not another application of
the endpoint lemma followed by independent summation.
