# General attaining family for the persistent interval obstruction

2026-10-03 21:49UTC. Universal Q4 construction, registered/type locked;
no accepted proof yet. Type13c4148cbefaef7f, ready/lock true, claimed normally.
Registration174333-347391 passed; branch node/TwoFullCapBlocksFamilyExists,
base080a277ec5bc741f3582eb4790731b94cf079bfb. Existing proof imports were
added without changing the statement. Fixture
a38a0d61c4d6188d1289dd670286a4f9de98b8bca7a12adf5679e61f603deb71.
V1 isolated174658-1c23d5 failed13 tactic/API errors11.262s/943MiB;
v2 isolated174834-2d0b7b resolves those but retains two insertion-cardinality
goals10.149s/941MiB. All bodies/operations/diagnostics are preserved; the
registered type and general induction plan are unchanged.
The first body is drafted; static checks reused the exact source base and
corrected singleton bracketing/strong-image size. Search artifacts
two-cap-family-existence-search.json and
two-cap-family-root-obstruction-search.json found no exact theorem.
Reuse construct in two_cap_blocks.py and the hand obstruction; no new cases.
The final draft API includes all-root four-cup and both gap witnesses by
the accepted root-noninterval theorem, so existence and forced geometry
close in one general node. Existing IsDecomposable.isSweepRealizable also
appears explicitly in the final API; it realizes the coloring in planar
general position but does not assert geometric deepness of the same tree.
Earlier construction-only type/body are archived. No new realization proof.

The registered type quantifies over p>=2. The general
finite endpoint iff can avoid new endpoint-cardinality machinery: first
glue with trivially true predicates to get agreement, decomposition and
strong avoidance, then verify numeric predicates using pure and0/1/2
insertion cases. In the five-point base subtree the two cap/cup supports
are separated, so a two-opposite-endpoint bracketing of a nonempty growing
chain is impossible; the one-endpoint cases give rank3. Adjoining the
singleton gives rank3/4 and strong4. This proves base ingredients through
the same general constructor, without a standalone numerical Lean theorem
or a copied finite evaluator. Exact index/set arithmetic remains to draft.

Target for every p>=2: a decomposable, sweep-realizable coloring on Fin(2*p),
whose first and last p-point blocks are caps, with global cap<=p, cup<=4
and noStrong(max(4,p)+1). For p>=4 it additionally supplies a four-cup and
both interleaving gap witnesses for every nonempty deep root, using the
already accepted root-noninterval theorem. The broader family supplies the
induction inputs and the hand cup4 gate lower bound for every cap rank>=2;
it does not claim four-cups or forced interleaving at p=2 or p=3. It does
not certify B's cardinality upper, its
matrix backend or actual-history context interface.

Induct by two using a local universal auxiliary for p>=2 with strong bound
max(4,p). The two small base constructions are ingredients of this general
proof, not independent Lean-instance targets or claimed numerical progress.
X2 is the4cup split into two pairs. X3 keeps five points of the classical
cap3/cup3 tree (first three a cap, last two a pair), then adjoins an upper
singleton between the pair. The inner5point root has strong<=4 and the
outer singleton coupling is3+1, so X3 has strong4, cap3 and cup4. Its two
ordered blocks are3caps. This is the exact existing source construction;
an alternative whole-first-cap root could have strong5 and is not the base.

For p>=4, take a lower4cap and an upper embedded X(p-2). Put one lower point
before and after the old interior in each of two zones. Child order embedding
maps i to i+1 in the first old block and i+3 in the second. The planned
general coloring pushforward transports decomposition and all child ranks.
Accepted independent-color gluing supplies the parent. Cups of the lower
cap have at most2 points, opposite endpoints at most2, so parentcup<=4.
Caps in the upper have at mostp-2, hence parentcap<=p after two gains;
pure lower caps have at most4<=p. Strong coupling is2+(p-2)=p; child strong
bound max(4,p-2)<=p. Two endpoint insertion into each old cap gives its full
p-cap zone, and image cardinalities give total2p.

Reuse the PUBLIC FinsetPolygon.IsCupSet.isDecomposableOn_of_nonempty from
StructuralChargingNextState578SpanCounterexample and IsDecomposableOn.dual
for the constant cap. Local cardinal/avoidance conversion and order-index
arithmetic belong in the body, without new definitions or statements outside
ESBlueprint. Existing construction artifacts remain frozen. Kernel base
computations, if needed inside the universal induction, use ordinary decide
or explicit tree/finite tactics, never native_decide or generated certificates.

This is a real missing general construction, but its formalization is only
worth admitting after the finite endpoint and required embedding interfaces
are accepted and reviewed. Done requires full unchanged-statement receipts;
a drafted auxiliary or a p4/p5 check is not completion or new family credit.

Search two-cap-family-general-size-search.json also has no hits. The full
519-line first draft and narrow insertion adapter were independently read
in review window7a76c860293d46b8 before registration. The type was registered
with the minimal gluing import; only existing theorem imports were added
before capture. Failed attempts and corrected bodies remain separate.
The generic embedding's heavy import closure makes node-finish's targeted
source stage refuse the existing 4GiB limit. Use the supported non-targeted
full es check, then existing audits/layer checks, exact fixture/source
comparison and an independent receipt review. Preserve any failed operation
honestly; never report it as successful or change its cap to force a retry.
