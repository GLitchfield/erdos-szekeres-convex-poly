# R18 axis-two cut-path interpretation

Mathematical explanation under investigation, not a Lean theorem.
Existing Boolean diagnostic124627-f7b5d4 passed50400 legal one-level roots.
New raw proper-part-zero theorem298a3661 and existing common-singleton-rank
theorem give the structural reason: global<=2 has bound<=1, and a proper part
on that same axis has bound0. Every contributing cut path chooses the other
axis; its paired branch contributes0. This is a one-path optimization.

Let old chosen side have globalG, opposite globalO=2, legal globals<=k,
maxima=[m],1<=m<=k-2, and a uniform root word with r>=2 child runs. Let e be
the sum of the two endpoint-presence flags. The diagnostic condition is
bound=1 iff m<=k-3 and G>=e+3+[e=0 and r>=3].

Candidate direct positive witness: retain an entire outer child run in one
proper interval cut, choose the fresh maximum1 on the old chosen side, and
give the opposite branch maximumk-2. For one endpoint marker, retain the
outer run adjacent to the unmarked end; for both endpoint markers either
outer run; for no endpoint marker either outer run.

Predicted selected pure extension cost at the retained run is e+1, except
for e=0,r>=3 where it is2. The old join term is m+1: all fresh omitted children
lie on one flank, contributing one younger-level extension at old level2.
The opposite leaf capacity remains1. The chosen leaf capacity is positive
exactly under the diagnostic condition (using G<=k). This explains the
clamp3 exception: no-end roots with O=2,G=3 can be positive at two runs and
zero at three runs. For G=2 and r>=2 all these roots are already zero.

Ordered-path reasoning: with two no-end runs, old level2 lies nearer the kept
outer run than fresh level1, so they cannot form an outward 1,2 chain. With
three or more runs, a fresh removed child in the next run is followed by an
old separator before another removed run, giving an outward 1,2 chain.
One marked endpoint can be absorbed by choosing the unmarked outer end;
two marked endpoints cost an additional opposite-flank old marker.

OPEN: certify these ordered fold formulas for arbitrary run lengths and
marker multiplicities, and prove that EVERY recursive path reaching a leaf
pays at least this cost and old-join m+1. Merely exhibiting an outer cut proves
the positive lower direction, not the zero criterion. General paired
transport for larger axes and NF<=source remain independent. Do not infer
unbounded truth from the finite diagnostic or register more scalar-erasure
conjectures after the recorded failures.
