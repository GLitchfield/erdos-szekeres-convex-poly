# General actual-history extension for the two-cap obstruction

Current23:24UTC: target fully CLOSED/committed0930d3c7,
type1c941c8bec8aa44a. Isolated v4 182919-ec9e45, full183035-59cc84,
audits190157-0e4b14 and exact review passed; claim released closed.
TWO-CAP-CONTEXT-HISTORY-ACCEPTED.md pins complete receipts and failed bodies.
The proof design below is retained from22:00UTC; it is now implemented.

Target every p>=5 and ANY decomposable coloring on Fin(2*p) with its two
canonical p-cap blocks, cup<=4, cap<=p and noStrong(p+1). Extend it exactly
along the increasing map i -> i for i<p, otherwise i+3, to Fin(2*p+3).
Keep decomposition and existing sweep realization, the same global ranks,
and three actual nonempty lower-child/upper-singleton deep splits. The
core must satisfy the LITERAL context with globals(p+1,5,p+1), word
S^p,1L,3L,2L,S^p and maxima111. This exact target is the missing universal
actual-reach interface, not a bound computation or a finite-instance theorem.
The universal family can instantiate its input once fully accepted.

Write a=p, b=p+1, c=p+2 in the ambient index order. Build from the core by
adding a first, then c, then b. The actual root removes b first. Context
part shifts old levels by one and labels the new sibling level1, so the
three cuts label a as1L, b as3L, c as2L. An earlier informal b,c,a insertion
ordering was corrected before any proof trial; it was not a valid history
interpretation. The kept child's side is lower at all three ancestors.

Every core cup with at least3 points meets both cap blocks: a cup/cap
intersection has at most2 points. Consequently it spans every point in the
three-position gap. Adding a cannot create a four-cup involving a, because
that would extend a core three-cup at an endpoint in its interior. Thus
every four-cup after the first insertion is still a core four-cup.

Adding c can create a four-cup from a lower three-cup. If it misses a,
that three-cup is core and spans c, impossible. If it contains a, c must
be its right endpoint; a further core vertex must lie in the first cap
block, since second-block vertices lie beyond c. The resulting four-cup
contains a,c and a first-block point. It therefore spans b. Old four-cups
also span b. The last singleton b cannot extend any four-cup. Cup<=4 persists.

At each singleton step caps are inherited or gain at most2 points from
the lower side around the singleton; their new size is at most3<=p.
Strong coupling is lower cup<=4 plus upper cap1, hence<=5<=p. Reuse the
accepted independent-color gluing with true predicates, then the finite
endpoint iff to prove numeric ranks. This avoids new endpoint-set machinery.
Agreement transports prior splits and the exact original restriction.

Reuse public Ctx.Context.pos_part_eq for every nested rank map. At the
root, child positions are List.range(2*p+3), and Fin.card_Iio identifies a
vertex's rank with its value. Each part preserves this coordinate. Existing
mem_positionsOf and part_letterAt_of_child/of_ext then identify the final
word point by point: all core coordinates stay child, a becomes1L, b shifts
to3L and c to2L. Existing WellFormed.part and
ctx_satisfies_of_deepBelowSplit propagate actual satisfaction. Do not copy
the finite R19 computations. No closed B formula or matrix equivalence is
asserted; those remain separate after an actual-history receipt.

Search two-cap-ancestor-context-search.json and ancestor-position-map-search.json
have no exact bridge. Existing R19 history is a finite template; public
pos_part_eq, transfer and word-letter APIs were found by source search.
No new Python, solver, certificate, census or standalone small Lean target
is needed. Done requires the full unchanged general statement, isolated and
original-source/full checks, audits, receipt/source review and one-node commit.
