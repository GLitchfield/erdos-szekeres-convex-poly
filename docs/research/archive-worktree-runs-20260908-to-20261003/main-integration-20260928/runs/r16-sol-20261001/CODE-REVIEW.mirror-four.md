# R16 separate Sol self-review: reflected exposed-end selector through axis four

Reviewed 2026-10-01 11:14Z in window-d165da2e6ee74cca after research
window-5ffcd738d48640da endedaccepted1.
Host restriction permits only Sol/xhigh and forbids delegation; this is Sol
self-review, with no independent Astra review.

Locked statement ec1cbd24ca384549:
3<=A,G<=k,1<=m<=k-2; uniform child/ext1-side word; actual head old marker,
actual last child, a child and at least two runs; A<=4 or min(G-1,k-m)<=4.
The conclusion names childPositions.getLast? and the actual opposite-side
singleton cut c=k-A+1, with selected complement maximum A-2, using raw leaf T.
Both axes and arbitrary marker multiplicities/run lengths.
This removes the mirror application gap in that scope, not larger-axis,
neither-marked or degenerate selector obligations.

Exact accepted source matches v2. The accepted d2680bd first-selector proof
is unchanged under indentation inside local hFirst. It receives the reversed
word with head-child/last-marker hypotheses. Canonical root and axis definitions
avoid proof-dependent match elaboration; final side cases restore the locked type.
The geometric child/part/rest/run helper prefix is copied from existing closed
CtxBoundReverse. The root-WellFormed construction is copied from the closed
conditional one-level contraction proof and generalized over the two legal globals.
Legal maxima establish WellFormed for both original actual cut parts.
ctx_bound_reverse is applied only to those parts and the original root.
No reversal is assumed for the empty-history normalized raw contexts.
The first selector's raw leaf threshold is converted to the actual singleton
bound, transported with the complement, and restored at the original last child.
The returned position is proved to be the getLast? child, not merely a word endpoint.

Accepted check20261001-071014-c02565:
receipt08b51b7b9485b40079166f81303ef7cd9a0ed7348fc40e09951abf219bc2bdf7,
lockedtypeec1cbd24ca384549,statusclosed,sorry=false,
axioms propext/Classical.choice/Quot.sound only.
Build78.04580283164978s,peak3674MiB/4G.
Fixture51c6551a640ca8313d7299cea3964271b15c654bd8f1562ed3567877dc9e496c.
Frozen Mirror-four-attainment.closed.lean SHA
e9c4dec42e373ba5733d216644ca42a6001fe096c57c991c734d12ffd874fddd.
Receipt CHECK.mirror-four-v2.closed.detail.json SHA
3c25d023852c815eea4f816c2684e50f794466b85a00a4694718c6e20cd9d807.
git diff --check passes; source220576characters/4526lines.

Failed check20261001-070712-d63424:74.8201589584s/3088MiB/4G.
Only two errors at final side cases: copied hchild geometry helper shadowed
outer child-membership hypothesis. Rename hChildReverse at seven occurrences
was the entire v2 repair; accepted first proof and locked statement unchanged.
The failed parent earns no theorem credit. Exact failed source, log and check:
Mirror-four-v1.failed.lean (SHAc83bd58ff94b18b9b33741a83e407f66acc0335ad942c375b0808059dac5a6b4),
BUILD.mirror-four-v1.failed.log, CHECK.mirror-four-v1.failed.json.
Registration20261001-070213-89af3c:82.1s/2288MiB/20G.
Branch20261001-070116-2ae281 approved5847.

Search before writing: marked first exposed last singleton returned only the
opposite exposed-first theorem, no duplicate mirrored statement.
Exact ctx_bound_reverse search returned the existing closed theorem,
type4125616738b08f1d. Additional root-WF and part/reverse searches were inspected.
No new reflection algorithm, Python/C/workflow glue or shared script was introduced.
Reusable geometry already lives in checked Lean source; no harness-library
promotion is appropriate. Public cut-value reflection and proof factoring could be
future Lean maintenance, deferred until authorized integration. No integration here.
Unused copied local transport helpers were retained; no cleanup/retest is needed
for the accepted proof.

No pending check; commit and frozen mathematical handoff remain to be preserved.
Native goal stays ACTIVE under its no-completion-before17:04 contract.

