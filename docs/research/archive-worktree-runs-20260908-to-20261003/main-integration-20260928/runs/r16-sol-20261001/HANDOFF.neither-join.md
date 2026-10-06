# R16 join-limited neither-marked first-cut handoff

Accepted commit c5a274622d52c69bcf692d8b492d7baedcfad047 on
node/CtxOneLevelRootNeitherMarkedJoinLimitedFirstCutThresholdLowerAndSmallAxisAttainment.
Approved independent parent5847e155fa613d4d2311eaee86b4b094f630e9a4 verified;
five node files, clean checkout, left_uncommitted[]. Commit job
20261001-091403-c99c32 DONE. No integration, push or primary source edit.

The closed theorem is
ctx_one_level_root_neither_marked_join_limited_first_cut_threshold_lower_and_small_axis_attainment,
unchanged locked type e31666b7a0b32f8f.
Exact hypotheses: k>=3,3<=A,G<=k,1<=m<=k-2,k-m<G;
uniform child/ext1 marker word, actual old marker, head and last child,
actual child and at least two runs. Either marker side, arbitrary run lengths
and marker multiplicities.
The first global child p has legal opposite-side maximum c=k-A+1 and selected
companion maximum k-1-c=A-2. For its actual raw singleton threshold plus
actual complementary context bound:
T(A,k-m,k)<=cutValue p holds for ALL legal axes;
source bound<=cutValue p holds under
R=(A<=4 OR k-m<=4) OR ((A<=5 OR k-m<=5) AND A+(k-m)<=k+3).
No open upper or selector premise. The all-axis floor is independent of R.

Proof: generic geometric/absorption/Pascal/lower prefix accepted14;
legal-root WF and reflection, actual-marker leaf and prefix complement accepted17.
Set H=k-m. Strict join limitation gives min(G-1,k-m)=H, hence leaf T(A-1,H,k).
Complement keeps G unchanged and merges maximum M=max(A-2,m+1);
its word starts at a marker and ends at a child.
W=min(G-1,k-M)=min(H-1,k-A+2). If W>=2, M is legal and reflected unrestricted
exposed lower gives T(A,W)<=complement. If W=1, threshold zero and nonnegativity
suffice; no reflection of an illegal root. Capacity Pascal pays T(A,H).
Actual marker witness identifies the source side before sibling-maximum
normalization to globals A,H and maxima[]. Physical markers remain positive,
inert barriers. Axis-four or axis-five-below-saturation upper pays source under R.
Raw singleton threshold, filter identity and .k=k restored explicitly.

Closed targeted v2 check20261001-091003-b5b6e3:
79.19654488563538s /3947MiB /5G; status closed, locktrue, sorryfalse;
standard axioms propext/Classical.choice/Quot.sound;
nonstandard, blocked, uncovered[]; no open N_ends/N_root/X proof dependencies.
Immutable receipt ba516ffb446506e13c9b281985da71e73faa95520bcc9c0612130bdb58f5728a.
Fixture6f80e06ea64250210a15f9a9d7de9578ff6f7814bf1fa70db604fc786cb669b6.
Frozen Neither-join.closed.lean:213889chars4589lines, SHA
bff5a18579d568bc4eaf2b4e5c2a645bcc3ab38c864fb1d3b1dcc5a9f7f2d236.
CHECK.neither-join-v2.closed.detail.json SHA
116264d0e355bcbbca8dbb1c89fa99f6b95ff41453e831cd7488c4a26f45a914.
Registration090345-38ffd2 and branch090307-27b687 DONE.

Failed v1 check090725-60f843:73.99153s3736MiB5G/noOOM/no guard;
receiptf86af4e34a46072e3b87e19a6cc73c612ce87edaa00ba302037a1c843abb5517.
Only redundant rfl after last-child transport in copied pre-final helper.
Exact comparison confirmed helper equals frozen accepted17v3 after removal.
Initial journal diagnosis mislocated it as WF; corrected before repair.
Neither-join-v1.failed.lean SHA
8e6323eb46cccabedc7be50abd839219876500f9f82dc3ec785d26d7e8aebf89.
CHECK.neither-join-v1.failed.detail.json SHA
58d58e127abd9734a4dbc1cbe5450140616e9f85fac6653f98da4554b0f35e4f.
No mathematical counterexample. Header assembly/static issue, unknown-node
registration submission and two run-end CLI refusals logged and recovered.
Supported run-end syntax is positional window ID.

Search before proof: neither marked join limited first singleton cut threshold
lower small axis attainment; no matching hits.
Researchf9e35d5031b5459a ended accepted1;
separate Sol selfreview f26bb8d451294797 ended accepted0.
CODE-REVIEW.neither-join.md records statement/receipt/code/inline-command audit.
No independent Astra under host no-delegation rule. No new Python/C/workflow
algorithm. Existing accepted proofs and node/proof automation reused;
promotion unnecessary for proof-only work, integration/factoring deferred.

Full N_ends/N_root remain OPEN. G-limited H>=G is outside this theorem.
Unsupported saturated normalized axis-five and both-larger-axis source upper
remain open; HANDOFF.larger-axis-upper-stuck.md has the two failed routes.
Broad six-child finite coverage and opposite-global-two selector edge open.
No pending jobs for this proof. Same R16 native goal ACTIVE;
consolidation16:34:46.416915Z/research17:04:46.416915Z unchanged.
Next useful candidate: both orientations of exactly-one-marked-end selector
under certified range R with V=min(G-1,k-m), adding nonsaturated axis-five cases.
Not yet registered or proved; do not credit prospective statements.

Whole-thread usage13:14:14Z:1107requests,input152696685,cached148730240,
output1147698,reasoning538152,delta0. This is not per-window cost; active/late/
direct-job attribution gaps remain explicit. No cost double counting.
