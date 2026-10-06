# R16 handoff: reflected exposed-end selector through axis four

Frozen 2026-10-01 11:17Z. Closed independent commit
67eea57d1668fbf4a3ca70a1a5c6935547f64fab, branch
node/CtxOneLevelRootLastSingletonCutAttainsOfMarkedFirstExposedLastEffectiveAxisAtMostFour.
Approved parent5847e155fa613d4d2311eaee86b4b094f630e9a4; five node files, clean.
Commitjob20261001-071427-2339ae completed; parent/status verified.

Accepted exact theorem: 3<=A,G<=k,1<=m<=k-2; uniform child/ext1-side word,
actual head old marker, actual last child, a child, at least two runs;
A<=4 or min(G-1,k-m)<=4. The last child p attains the opposite-side singleton
cut with maximum c=k-A+1, selected complementary maximum A-2, and explicit raw T.
Both axes, arbitrary marker multiplicities/run lengths. This completes the
mirrored exposed-end application in that scope; larger axes/neither-marked/edges
remain open. Together with d2680bd, both exposed-end orientations are checked.

Accepted check20261001-071014-c02565:
receipt08b51b7b9485b40079166f81303ef7cd9a0ed7348fc40e09951abf219bc2bdf7,
build78.04580283164978s/3674MiB/4G, lockedtypeec1cbd24ca384549,
sorry=false, axioms propext/Classical.choice/Quot.sound only.
Fixture51c6551a640ca8313d7299cea3964271b15c654bd8f1562ed3567877dc9e496c.
Mirror-four-attainment.closed.lean SHA
e9c4dec42e373ba5733d216644ca42a6001fe096c57c991c734d12ffd874fddd.
CHECK.mirror-four-v2.closed.detail.json SHA
3c25d023852c815eea4f816c2684e50f794466b85a00a4694718c6e20cd9d807.

Exact accepted first-selector proof is nested unchanged. The existing approved-base
ctx_bound_reverse (closedtype4125616738b08f1d) supplies reflection.
Local child/part/rest/run correspondences are reused from that checked source.
The root-WellFormed construction is reused from the closed conditional contraction
proof. Both actual original cut parts have legal maxima and are WellFormed.
No reflection is assumed for normalized raw/inert contexts. Convert raw first-leaf
threshold to actual bound, reflect it and the complement, then restore original
last-leaf threshold. Canonical root/axis definitions and final side cases handle
proof-dependent raw matches. Returned position is proved to be childPositions.getLast?.

Failedv1 check20261001-070712-d63424:
74.8201589584s/3088MiB/4G, two errors only at final side cases.
Copied hchild geometry helper shadowed child-membership input; renaming it to
hChildReverse at seven uses was the entire repair. Failed parent grants no credit.
Mirror-four-v1.failed.lean SHA
c83bd58ff94b18b9b33741a83e407f66acc0335ad942c375b0808059dac5a6b4;
BUILD.mirror-four-v1.failed.log and CHECK.mirror-four-v1.failed.json retained.
Registration20261001-070213-89af3c:82.1s/2288MiB/20G.
Branch20261001-070116-2ae281 completed.

Researchwindow-5ffcd738d48640da endedaccepted1.
SeparateSolselfreviewwindow-d165da2e6ee74cca and CODE-REVIEW.mirror-four.md verify
source identity, exact scope, WF applications, commands and maintenance decision.
No independentAstra underhostrule. No new Python/C/workflow algorithm.
Geometric proof factoring/public cut-value transport is deferred to authorized
integration; no extra test or source cleanup after acceptance. No pending node job.

Thirteen helpers accepted. N_ends/N_root open. Two larger-axis bridge routes
failed at the same exact upper obligation; frozen
HANDOFF.larger-axis-upper-stuck.md supplies36-root/1240-cut evidence.
Actual tested bounds/cuts still held, so no target counterexample.
Next same-trial reusable lemma: exposed-first/marked-last threshold lower with no
small-axis restriction, extracted from the accepted lower/Pascal/cut-domination
argument. Actual-indexed-marker/global-axis-two zero bound is another unproved route.
Neither-marked exchange remains essential: no fixed global child works in all cases.

Whole-thread usage snapshot11:16:23Z:838requests,input116264448,
cached113058176,output867930,reasoning426990,delta0. Not per-window totals.
Research/review usage sync was sequential and successful. Active/late and direct-job
attribution gaps remain explicit. Native goal ACTIVE until stated deadline;
consolidation16:34:46Z,research17:04:46Z,hardfinalization17:34:46Z.
Same trial; no integration, delegation, deadline extension or early completion.

