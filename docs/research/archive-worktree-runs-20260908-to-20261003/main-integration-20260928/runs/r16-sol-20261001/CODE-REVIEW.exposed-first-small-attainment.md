# R16 review: exposed-first, marked-last small-axis selector

2026-10-01 10:04Z; separate review window window-33a970fb09414626.
Configured Sol/xhigh self-review only; host forbids model changes and delegation.
No independent Astra review was possible.

Reviewed the new 3919-line Lean proof, locked statement, complete parent receipt,
reused local bodies and new exposed-end instantiations, guarded branch/register/check
commands, and frozen exact source. No new Python, C evaluator, workflow wrapper,
or library algorithm was introduced. The accepted lower induction, Pascal,
prefix exact merge, and small-global upper bodies were reused locally because
this branch independently starts at approved base 5847e155.

The result requires legal opposite/selected globals A,G>=3, m in 1..k-2,
uniform child/ext1 letters, word head child and last old marker, at least two
runs, and A<=3 or V=min(G-1,k-m)<=3. It proves the actual first child cut
with opposite leaf maximum c=k-A+1 and selected complement maximum A-2.
No open selector, contraction, or upper-bound assumption is used.

First child is position zero; all old markers and retained children follow it.
Leaf limits yield T(A-1,V,k). The sole newly externalized prefix marker and old
level satisfy the exact prefix merge hypotheses. The selected global G stays
unchanged, the merged maximum is max(A-2,m+1), and the complement is both-marked.
Its point parameter W=min(G-2,k-max(A-2,m+1)) equals min(V-1,k-A+2).
For W>=2 the accepted both-marked selected-global induction applies; W=1 has
zero threshold. Capacity Pascal pays T(A,V,k). Last-marker upper normalization
and the small-global upper pay the source root. The raw explicit singleton
threshold is retained in the conclusion. Mirror/neither-marked patterns and
larger effective axes remain open; this is not full N_ends/N_root.

Accepted targeted check 20261001-060132-eada08, complete receipt artifact
3c731ee7698cf243c925b1ffb28e9c8a5e931888439fb2554e46f311e96ce7e9:
56.0297715664s, peak2997MiB,4G guard. Locked type c8e0da0d4fb01920;
sorry=false; only propext, Classical.choice, Quot.sound.
Fixture 9322ce5c2433a8f1d90fb5e3966b1432fdcb1a0ca22429754add160020256a7c.
Source Exposed-first-small-attainment.closed.lean SHA
1b2eabc08eced8faaf4e10b082747871318783a1f50b61a9fbb5395c768adeda.
Receipt CHECK.exposed-first-small-attainment-v3.closed.detail.json SHA
df554940c06bdcd3736e380e266c4ab2cbe6df5b32cae36d3175f2feaa89c878.
Failed checks055511-5be6e9 and060003-1a8b68 were solely a record-update layout
error; logged before each repair. No mathematical failure or extra theorem credit.

Search/reuse: es search found no equivalent actual exposed-end selector;
CtxSingletonPartBoundEqThreshold, CtxBoundaryMarkerUpperNormalize,
CtxBoundLeMergeSameSideLevels, CtxBoundLeOneOfCommonSingletonRank,
CtxBoundZeroOfUnitGlobalAxis, and prior accepted R16 local transports.
No recurring ad hoc algorithm needs promotion. Duplicated local proof transport
factoring is deferred to separately authorized library integration. Original
probe artifacts/runners/shared recurrence are unchanged. Whole-thread usage
snapshot10:04:04 has677 recorded requests; this is not window-local usage.
Active/late usage and direct-job resource attribution gaps remain explicit.
