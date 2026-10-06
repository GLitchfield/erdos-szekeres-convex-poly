# Rank rows as a possible clear-block charge

Stored nonvacuous replay completed2026-10-03 20:44UTC,
job20261003-164403-d7bfe3,0.004238s algorithm. Existing10point model dual
has cap3/cup5/strong5,d3. Forward has Join(5,4), excluded explicitly;
reverse lacks Join and deletes0,1,2,3. Remaining six points have cup4,
strong4,d2, so all proposed reductions pass with the10=4+6 budget.
rank-row-stored-replay.json pins exact colors, ranks and source/input hashes.
This supports one nonvacuous example and proves no general trace or upper.
No extra census follows automatically; return to the endpoint/apex invariant.

20:26 scope audit: this tests actual cupR and strong<=R. A general profile
bounded by cupR,strongR may instead have actual cupR-1 and strongR.
Under no4cap, strong is at most cup+1, so strong<=R is automatic in that
near-cup branch. Its desired upper is classicalF(R-1,3,d)=G(R,d)-1,
with the same truncated d. That classical upper is still open in the
intermediate range. The tested deletion conjecture alone cannot close G;
this is a structural reduction, not a result or a hidden scope extension.

20:20 mechanism checkpoint: BAEK-BLOCK-INVARIANT-OBSTRUCTION.md explains
why d does not bound Baek alpha. A four-point decomposable coloring has
d2 but alpha>=2. This does not refute the beta-row deletion conjecture;
it excludes a direct truncated-label explanation and exposes the need to
control apex relations when extending a surviving cup.

2026-10-03 20:00 UTC. General mechanism hypothesis, not a theorem.
Read accepted Baek C proof: beta(p) is longest cup ending atp minus1.
Its delta removes the first vertex of each beta row belowR-1, at cost<=R-1.
Under absent Join(R,R-1), the accepted induction proves the remaining cup
limit decreases fromR toR-1. It does not assert strong or block-cover reduction.

Let d be the minimum partition into consecutive nonempty cup blocks, equivalent
to one plus the packing number of three-cap open endpoint intervals. In a
DS coloring with no4cap, noStrong(R+1), actual longestcupR>=3 andd>=2,
propose: the same deletion, when Join(R,R-1) is absent, also leaves noStrongR
and reduces the minimum cup-block count to at mostd-1.

If both hold, delta would explain a general rank charge rather than fit data:
G(R,d)-G(R-1,d-1)=R-1, with the whole-cup baseG(R,1)=R. Mirroring treats the
other absent join. Both joins present are already handled by the accepted
interweaved-laced argument. One must prove the strengthened deletion claims
and their precise scope, not assume them from that existing induction.

Pilot allDSn<=4 then a measured n<=6 pass tests this precise invariant. A
saved counterexample to either new deletion conclusion rejects this proof
route while leaving G itself open. A negative finite search only supports it;
the next step would be a general explanation, not more census. Prior
classical packing n<=6 generation/check cost0.0758s. Libraries reused:
coloring-enumeration/chain_profiles/strong_sizes, endpoint chain_table and
frozen classical_packing minimum_clear_blocks. No rectangular-cover substitute.

rank_row_deletion.py contains the small mathematical candidate separately
from ordinary argument/output handling. Every execution is a guarded job,
with item counts/rate and durable source hashes. No timeout or Lean instance.

Pilot155930-92bde0 completed10colorings/2admissible in0.000445s. Fulln6
160039-b9583b completed790colorings/166admissible in0.042568s with no
failures; rank-row-n6.json. This supports the first nontrivial cover cases,
but it cannot prove either general conclusion. In particular R>=4 leaves
at most3points atn6, so the strong reduction is not meaningfully tested.

The general obstruction is now explicit. Under no4cap, a strong support's
middle-determined turn sequence has at most one interior cap-colored vertex:
it is a cup or a cup plus an interior apex. Accepted cup reduction excludes
surviving R-cups. The missing implication would promote any surviving
(R-1)-cup plus apex to an original forbidden Strong(R+1). Baek's laced
extension does not immediately do this, since an arbitrary balanced apex
polygon need not contain two interwoven long cups. A future first nontrivial
apex test must name this exact question; no larger census follows automatically
from nonfailure. Source/code review precedes another trial.
