# General one/two endpoint path lifting through a context part

Accepted and committed fa6dacd1, unchanged type5f51f6e3b493f420, no sorry,
standard axioms. Normal op-58b7ff64fee64da9 completed all five stages.
PART-ENDPOINT-PATH-LIFTING-ACCEPTED.md supersedes the pending snapshot below.

2026-10-03 23:20UTC. Registered/claimed type5f51f6e3b493f420. V3 isolated
191451-b84563 passed15.8264s/2102MiB/std axioms, receiptc5192f26; normal
node-finish op-58b7ff64fee64da9 passed candidate191531-eff7d9 and source
191550-a7a040 (66.5806s/2361MiB). Full extraction191701-14ca1a is running;
audits/review/commit remain pending. Failed v2's two elaboration errors and
receipt6121d58a are preserved; type unchanged. Universal history is accepted
0930d3c7. Separate pre-admission reviewec5b0450cd1f4154 completed.
No new computation, finite target or duplicate weak lemma.
Search part-endpoint-path-lifting-search.json found no general bridge.

The exact candidate is part-endpoint-path-lifting-node-type.txt. Before
registration it was strengthened at22:49UTC to include the consumer limit
and coupling consequence; proof-v3 is now the isolated/source-accepted body and
the earlier approximately200-line v1 remains preserved. For ANY raw
context/keep/side/maximum, explicitly require the new level's side to be the
chosen side. At each endpoint select zero or one new level1 marker. A
selected left marker x lies strictly before the child's start p; a selected
right marker y lies strictly after its end q. An unselected endpoint keeps
its coordinate. The sum g of selections is0/1/2. Every old pure extension
and old sibling join at x,y lifts to at least g plus that count in the part
at p,q. The new maximum m is also a join candidate. No wellformedness,
occupancy, positive m, one-change, decomposition or actual coloring is
needed for these raw count inequalities. For every positive chain size r
obeying the part's cup limit on side lower or cap limit on side upper, the
conclusion also gives r+g within the old parent limit at x,y and r+m<=k-1.
Positivity rules out the misleading zero value of a truncated subtraction.

This is the general missing endpoint implication behind the hand virtual
bound construction: a nonempty lower cup gaining one/two upper endpoints
obeys the old parent endpoint bounds because the part has already reserved
those gains; the cap argument is dual. Empty slots may impose additional
constraints, and old unused levels remain. This does not by itself prove
attainment, a capacity maximum, reverse Ctx.Satisfies or a closed penalty.

Reuse CLOSED ctx_part_limits_le type760bee59c44abf5a for inherited limits
where appropriate, and CLOSED ctx_pure_extensions_position_monotone
type5152d30fbad865d6 for endpoint monotonicity. The former already proves
old-path dominance locally, so a standalone weak export is not worth a node.
Reuse public part level-list identities, mapped fold equality, count offset,
maximum-list membership and maximumAt shift from CtxSatisfiesOfDeepBelowSplit.

For every cutoff N, map an old attaining sublist by level+1. With no selected
marker, skip new level1 and obtain the same fold count. With a selected left
marker, the part's greedy first left step picks its rightmost level1 marker
z<p. Since x is eligible, x<=z. Old left extension at x is at most that at z
by public position monotonicity. Prepend level1 to a mapped old attaining
sublist at z; mapped fold equality and the count-offset theorem give exactly
1+old count at z. The right proof is the mirror, using its leftmost marker
and reversed monotonicity. The two sides add independently, producing g.

At cutoff0 this proves the pure-chain inequality. At each old join level
N>=1, use cutoffN+1 in the part and preserve maximumAt(N+1)=maximumAt(N).
The same g bounds every old join candidate. Compare finite maxima and the
pure-chain alternative to obtain join dominance. New level1 has maximum m,
giving the last conjunct independently. Raw level-zero letters are allowed
because the explicit side premise is used; declared old levels start at1.

Done requires the complete unchanged general statement, isolated source and
original/full checks, audits, exact receipt/source review and one-node commit.
Before admitting, finish current history validation and separate code review.
