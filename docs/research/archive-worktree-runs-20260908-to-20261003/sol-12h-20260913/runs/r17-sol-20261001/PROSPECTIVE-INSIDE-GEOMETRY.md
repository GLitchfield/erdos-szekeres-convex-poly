# R17 prospective inside-pair geometry

Unregistered/uncompiled draft, not theorem credit. Search recovery16:19UTC:
es search "child outside adjacent pair two runs" and "num runs remove
singleton adjacent child pair" returned no results. Source search finds no
exported direct child-count contraction statement in the approved index.

Draft raw signature for later es node add, if useful to the inside residual:
(σ : Ctx.Context) (left right : List Ctx.Letter)
(hword : σ.word = left ++ [Ctx.Letter.child,Ctx.Letter.child] ++ right)
(hruns : 2 ≤ σ.numRuns) :
∃ r ∈ σ.childPositions, r ≠ left.length ∧ r ≠ left.length+1.

child-outside-pair.body.txt proves this by contradiction: if only the pair
positions were children, every child-run start would be left.length. The
second pair position cannot start a run because its preceding letter is a
child. Nodup-filter/cardinality then gives numRuns<=1. No global, side,
maximum, WF or threshold assumption is needed.

This supplies the explicit other-child premise in the already closed generic
inside leaf monotonicity helper. A root WF proof is already drafted/used in
outside-single-run-exchange.body.txt. It would justify applying that helper
to every actual inside cut of X at positive global axes, leaving exactly
the joint complement reallocation inequality.

A further raw source-complement fact is plausible: removing either member
of an adjacent pair cannot reduce child runs, since its twin retains that
run. For the first member, move any run start at p to p+1; other starts stay.
For the second member, p never was a run start, and all existing starts stay.
An injection between finite run-start sets would prove source numRuns<=part
numRuns. This is an unproved plan; no numeric or Lean result is claimed here.

Neither this draft nor the small chosen-three numeric formula is used in
the parent five-case composition. Current queued proof/falsifier source
and fixtures remain unchanged. Do not create extra nodes solely for counts
if a direct application within an actual inside-exchange proof suffices.
