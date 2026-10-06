# R16 mathematical handoff: actual both-marked small-axis selector

2026-10-01 09:33Z. Same authorized trial,Sol/xhigh,no delegation/integration.
Independent branch node/CtxOneLevelRootFirstSingletonCutAttainsOfBothMarkedSmallEffectiveAxis,
approved parent5847e155fa613d4d2311eaee86b4b094f630e9a4. Commit10301b1910f55bbc159cbf069865a9da9d29e1d2 preserved5nodefiles,clean.

Accepted theorem:
ctx_one_level_root_first_singleton_cut_attains_of_both_marked_small_effective_axis.
Exact hypotheses and consumer:3<=k,3<=A<=k,4<=G<=k,1<=m<=k-2,
word letters are child or ext1side,head and last are ext1side,child present,
A<=3 or min(G-2,k-m)<=3,and at least two child runs.
The root's opposite global is A,selected global G,maxima[m].
Returns first child p with explicit legal c=k-A+1,leaf opposite to old side,
and root.bound<=raw T(leaf.cap+1,leaf.cup+1,k)+same-side complementary bound.
Arbitrary run lengths and marker multiplicities,both axes. This is an actual
first extreme-run-end attaining case; it does not prove full N_ends/N_root.

Receipt/job:20261001-053030-408dcf /
efeab9a4b1e916f9ebb557a316ee331d90188fa7012b5c2419b3b58cf36ad4e0.
Typec380b1b17be83d25 unchanged,locktrue,sorryfalse,standardaxioms only.
Build29.0568549633s,2257MiB/4G. Whole-source fixture
ab583128d9c54671fd67c2b491b12efd408877a691042fb561dcb1f8edcc6b79.
Frozen Both-marked-small-attainment.closed.lean SHA
47257564fb609add1ad49e43b753ffb644675a131c178e2542fb6ceb56c4a903;
CHECK.both-marked-small-attainment-v3.closed.detail.json SHA
1b8bd1e8628bc6261eb57b77da494c3f88b13a952b86d4d5f8af68d3a3581e9e.

Reusable argument:
V=min(G-2,k-m). Closed two-boundary normalization gives root<=bare(A,V).
Small-global bound gives bare<=T(A,V). First-child leaf exactlyT(A-1,V).
Same-axis complement absorbs the sole new marker,normalizing to globals
(A,G-1),maximummax(A-2,m+1),word still both-marked.
W=min(G-3,k-max(A-2,m+1))=min(V-1,k-A+2).
Complete selected-global induction gives complement>=T(A,W),with W=1
handled directly by zero. Capacity Pascal gives T(A,V)=T(A-1,V)+T(A,W).
The legal coupling complementary to c is A-2. Raw explicit leaf T is exact.

Preserved prior independent accepted commits:
weakeningcd1e05ce4528237b2cae5d120e310f044bcacdaf;
boundary-erasureaab76b86245a78f2f5648b83ebb90931b2e9c4dc;
Pascal1839fee7b02a6d9d405b9dabf445025ea1f7772c;
adjacent absorption4ad1c24f2cbc2b96d7263a9c20edcc1ff4ab6dec;
both-marked lower52237b4bc87c167ee79ddab868f72687a48778a4;
small-global upper42e07c0555940b8c75cd9a6d46453b8be5d7d2c8.
Open N_ends registration22d8137334ce31f2175aee57f29ff79d92fc1f36.
Detailed receipts/hypotheses are in their frozen HANDOFF/CODE-REVIEW files
and MATHEMATICAL-HANDOFF.md. No unclosed constant is used by this new theorem.

Failure records:
registration052130-c35664 finished107.5s/2605MiB.
Proofv1 job052748-604a9b introduced the local let context instead of the
run-count premise; explicit goal change repaired it.
Proofv2 job052908-eec238 completed25.977s/1932MiB but goal-only case
rewrites required reflexive head and simpa[hcp] at the final cut.
Proofv3 is fully closed. The patch-format rejection had no mutation.
All findings logged before next attempts. These are compiler repairs,
not two mathematical attempts at the full selector obstruction.

Open exact obligation:
For the general both-marked route one still needs
bare positive-label empty-indexed-history context bound<=T(A,V,k)
outside small axes. It retains physically inert uniform barriers,which preserve
multiple child runs. A=6,V=4,k=6 is the first saturated family:pointT11,
loose rank-pair potential15. Fixed four-isolated-child both-marked probes
041815-fe93b0 returned actual bound11 in both orientations;family042155-47b3cc
passed2538k5/k6roots. These are diagnostic,not a universal upper proof.
Pair/triple potentials can extend the nonsaturated small-axis range to4/5;
thin top/next-band potentials require an indexed large maximum absent in the
depth-zero root. One-marked and neither-marked selector obligations and
A<=2/G<=3 edges remain open. Do not apply single-run contraction bridges
to arbitrary multirun ancestors or repeat the refuted R13/R14 selectors.

Full one-marked five-child probe034251-3577ad finished9792/9792,0violations,
2992closed Leanunit-global rule rows plus6800C rows,52.5minutes;
source hashes/provenance verified. No long probe pending.
No counterexample to N_ends and no valid Stuck conclusion yet.
Native goal remains active; deadline17:04:46.416915Z,consolidation16:34:46.416915Z,
hard finalization17:34:46Z unchanged.

Researchwindow38635409475e4753 endedaccepted1; review8ed67b1effec4802 separate.
Sol self-review only because host forbids Astra/agents; see CODE-REVIEW.
Whole-thread sync09:32:43:594requests,input80393994,cached78030976,
output639404,reasoning331542,delta0. Cumulative thread snapshot,not window usage;
active/late recording and direct-job operation-link gaps remain explicit.


Exact commit-byte refresh and preservation:
Commit10301b1910f55bbc159cbf069865a9da9d29e1d2 via053831-8ce773,
5nodefiles,parent5847e155fa613d4d2311eaee86b4b094f630e9a4,clean verified.
Final checked receipt20261001-053631-a4510e /
b5a543dc72a63ad974f45746950dfad43116301977039e22bca857db7169d2e0;
same locked type,noholes,standardaxioms,28.8015882969s/2077MiB/4G.
Final fixture3693ddf69252813a9754b3bec65267ba81aad89d2a9d71c5116851607ed7b411.
Both-marked-small-attainment.commit.lean SHA
6ef0e743c2bddeae4d242f68c79488a2019ffdcef639616c6bc73340ccc3fd03;
CHECK.both-marked-small-attainment-v5.closed.detail.json SHA
9b974ec913a7ad416311ca11599ae58e88ebcbee6ff29e99495596592087db1b.
Commit053345-be1884 refused trailing whitespace before mutation.
Cleanup053434-41967c accidentally reduced final smallupper indentation; failed
25.817s/1989MiB,logged/repaired. Exact final versus acceptedv3 source differs
ONLY by removing spaces on blankline2155; all frozenv3 artifacts preserved.
These refreshes confer no extra theorem count. No new ad hoc/shared code changed.
