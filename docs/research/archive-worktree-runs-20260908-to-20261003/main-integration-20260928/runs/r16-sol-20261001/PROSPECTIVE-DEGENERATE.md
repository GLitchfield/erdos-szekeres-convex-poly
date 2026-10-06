# R16 degenerate proof plans and accepted tools — final scope review17:01Z

The prospective routes below remain unproved; accepted29/30 tools are explicitly
identified. No additional registered statement or theorem credit is implied.
They belong to the same R16 trial and preserve its deadline. The
old queued registration20261001-105116-8f4f9d was cancelled before start and
replaced successfully; that admission event has no computation credit.
Accepted29 high-maximum zero is recorded below. Accepted30 is the separate
allchildren-bracketed indexed chosen-global<=3 raw everyfuel/fullzero theorem:
commitaab5395c45d32470b40458039b26b9a79fcbc0e0/typeca893a8c2e474cd0/
check20261001-123039-b16343, standardaxioms/noholes. HANDOFF.bracketed-three.md.
Its original8G registration115507-707995 was cancelledconfirmedunstarted;
sameargv5G120130-152844 finished140.7s2319MiB withoutguardoverride.
Accepted30 requires EVERYchild bracketed; it is not the protected-single-child
invariant below. Its raw-to-root selector consumer remains separately unproved.

## Protected bracketed child (priority after current selector)

Proposed claim: let sigma be any raw context with positive physical external
labels, chosen side s, chosen global<=3 and opposite global<=2. Suppose N is an
indexed level with sideAt N=s, actual markers x,y on that same level, and a child
r with x<r<y. Every fuel approximation and full bound should vanish. There is no
k/global lower/maximum legality/WellFormed/one-level/run-count hypothesis.

Proof invariant: retain r and the same old bracketing level through chosen-side
parts; its numeric index shifts by one at every part. Fuel induction is generic
over the context, old index, markers and protected child.

Base with numRuns<=1: reuse starts-uniqueness, predecessor closure and hfill from
ESBlueprint/B/CtxBoundAdditiveSingleRunBoundary.lean lines29-108. The first child
b is <=r. If b<=x<r, hfill would make old marker x a child, impossible. Hence
x<b<=r<y. One-left and one-right old-level witnesses give chosen chain>=2 at b,
so chosen global<=3 makes chosen point limit/base zero.

Recursive branch: every opposite-side proper part has an actual fresh opposite
marker and vanishes by accepted15 marker/global-two annihilation (closed source
Marker-two.closed.lean, commit56dfcefde8e66cf872a469889c0a34d7c5bae794).
For a chosen-side part keeping r, the invariant holds on shifted old N+1 and
fuel induction applies. For a part removing r, its fresh level1 marker r lies
between shifted old markers x,y. Apply closed
ctx_chain_one_children_exterior_of_two_levels twice, once to young r / old x
and once to young r / old y. Any child with chosen chain<=1 would have all
chosen markers both before and after it, contradiction. Thus every chosen point
limit vanishes; closed ctx_bound_le_sum_point_bases and fuel stabilization kill
the whole part. This avoids treating a noninterval complement as an interval.

Related search bracketed/zero returned ctx_bracketed_children_unit_bound
(global<=4 interior-part annihilation/unit upper), not this allfuel zero.
Actual core geometry is closed on approved5847 base. One-left/right witnesses
are the exact accepted15 local blocks, reused by accepted27. Generic part
positivity is available as the exported closed ctx_part_positive_letters in
CtxPartPositiveLetters.lean; reuse it instead of repeating the local body in
CtxBoundLeOneOfCommonSingletonRank.lean lines200-220.
No source has been edited or proof check launched for this candidate.

Consequence still to prove: a uniform one-level G3/A2 root with >=3 physical
child runs has an old-marker-bracketed child and is zero. The protected-child
claim would be reusable even for arbitrary histories, inert barriers and
run patterns. Extracting that child from run-count>=3 requires its own verified
physical run argument. Neither statement is credited.

## High old maximum / opposite two — ACCEPTED29

Closed claim: positive physical labels, indexed level N, opposite global<=2,
maximumAt N>=k-2, numRuns>=2 imply everyfuel/full zero, with no actual old marker
occurrence or legal chosen global/old maximum/WellFormed hypothesis.
Commitab116420cc781a232989c286f37c548008cdc364/check114629-186bbb/
type d29856495f62fe80,5.325975s662MiB4G standard axioms/no holes.
Exact proof/receipt/review in HANDOFF.large-max-two.md. No fullselector closure.

Every proper chosen part creates actual fresh level1. For each retained child p,
a fresh removed witness q!=p lies to its left or right and level1 lies below
shifted old N+1, so leftExt/rightExt at that old top total>=1. Core
le_joinExt_of_mem_levelsOn then gives join>=oldMaximum+1>=k-1, annihilating the
chosen point limit. Opposite parts vanish by fresh marker/global-two as above.
Proper block/complement witnesses and recurrence are already implemented in
Both-two.closed.lean (accepted24). Relevant exact core:
CtxSatisfiesOfDeepBelowSplit.lean part_maximumAt_succ line139 and
le_joinExt_of_mem_levelsOn line550. The accepted implementation reuses exact
closed large-sibling hKill rather than rebuilding its join witnesses.

## Two-run inner-end lower

The remaining A2/G3 neither-marked case includes the certified SSLSS example:
source1, all global-end cuts0, an inner extreme-run end cut1
(commit aad0cd4939df89e219189c4372b9e629a5f2950e, check094654-b4d99d).
For canonical child^L ++ oldMarker^M ++ child^R with L,M,R>0 and
old maximum<=k-3, remove p=L-1 (last child of first run) on the opposite axis.
Its opposite-global-two singleton leaf is zero. The chosen companion should be
at least one: retain the final run in a chosen cut of maximum1. The nested
context has chosen maxima [1,1,m], its new prefix markers before young p before
all old markers, and every marker before the retained final run. Pure chosen
chain should be1 and join at most m+1<=k-2, so its one-run base is1.
Cut domination then gives companion>=1; closed common opposite singleton rank
bounds source<=1. Requires checked prefix ordering, physical run and point/join
identities; a positive point/base of a multi-run context alone is insufficient.

No deadline extension, narrowed coverage presented as a result, target
refutation, integration, delegation or unguarded compiler execution.

## Higher chosen global / opposite two — unproved first-leaf route

For legaluniformonelevel roots G>=5,opposite2,1<=m<=k-3 and2runs,
source<=1 followsfrom closed common opposite singletonrank1. Firstchild chos-side
singletonmax1 shouldpay rawleafT1 by itself; companion merely nonnegative.
Freshremovedchildrenallright, oldchosmarkersshift2. Need checked left<=1,
right<=2 sochain<=3; oldleveljoin terms<=m+1, freshlevelmaximum1.
CORRECT fulljoin<=max(3,m+1), notjoin<=m+1: joinExtincludespurechain.
As k>=G>=5, m<=k-3 givesmax(3,m+1)<=k-2, selectedpoint>=1 andoppositepoint1.
Diagnostic reasoning witness disprovingtheoverstrongjoinbound: G5/A2/k5/m1,
word L S L S L, firstp1/chosleafmax1. Leftold2marker0 counts1, rightyoung1marker3
thenold2marker4 counts2 =>chain/join>=3>m+1=2. No compiledreceipt/proberesult.

G4 exposedendfirst/last useschain<=2 andjoin<=max(2,m+1)<=k-2.
G4bothmarked/oppo2 zeroaccepted26; highm>=k-2 zeroaccepted29. G3neither/oppo2
stillneedsprotectedchild andtwo-runinnercompanion. Need checkedfoldcounts,
levels/sideAt,join/threshold identities. Searchsingleton/opposite/two/five
receipt36460b3bb88bef76b7145839d4d5a874177e00913d560dc1c53dff1b50b3559a
hadrelatedpotentialsbutnodirectselector; fold/extension/length found onlyclosed
positionmonotonicity. No statement/claim/proof has beencreatedforthisroute.
