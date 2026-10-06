# R16 unrestricted exposed-first lower handoff

Accepted independent commit 30388a5b794e81b6e0af3ca2155aae539cabb7bb,
branch node/CtxOneLevelRootExposedFirstMarkedLastPointThresholdLower, parent
5847e155fa613d4d2311eaee86b4b094f630e9a4. Exactly five node files committed;
left_uncommitted=[] and git status clean. No merge, push or primary source change.

Accepted theorem:
ctx_one_level_root_exposed_first_marked_last_point_threshold_lower.
Locked type fdb8683f45235ae. Assumptions: 3<=k, 3<=A,G<=k, 1<=m<=k-2,
uniform word containing only child or ext 1 side, head child, last old marker,
and a child. For the one-level root with old-marker global G and opposite
global A, T(A,min(G-1,k-m),k) <= root.bound.
Both sides, all run counts, arbitrary marker multiplicities and child lengths.
No small-axis restriction. This is a lower bound; it does not supply the
general matching upper or a full selector.

Receipt: targeted check 20261001-073044-ff609e,
f82abcd72d868a4fe6c3845eb99401dccfbf109611dff84e0d806790aedfe54a.
53.206103801727295s /2615MiB /4G guard; closed, lock_ok=true, sorry=false,
standard axioms only; no blocked, nonstandard or uncovered axioms.
Whole-parent proof fixture:
379ee68af41b96c788efa15d5b16d055c49482cade33e70effa78da7b8778ba8.
Commit job 20261001-073338-428d3d completed successfully.

Frozen artifacts in this directory:
- Exposed-first-lower.closed.lean, SHA256
  0488c1db7144f92615e6b99678b8cb40e1fb61097734f093ae14e8f41ad91d4f.
- CHECK.exposed-first-lower-v2.closed.detail.json, SHA256
  d5b91299a3c4b6f79fa55161fe57aad518c4159c043019dd6946e2fb415ccae3.
- Exposed-first-lower-v1.failed.lean, SHA256
  fa7299a4777309057562271d12faba1aa87e9f6090a0d308b55884c36694890d,
  CHECK.exposed-first-lower-v1.failed.json and BUILD.exposed-first-lower-v1.failed.log.
- CODE-REVIEW.exposed-first-lower.md; COMMIT.exposed-first-lower.txt.

The single-run case uses exact exposed first-point base. The multi-run case
uses first-child singleton opposite maximum k-A+1, complement selected maximum
A-2, and exposed-prefix merge retaining G. Its merged maximum is max(A-2,m+1).
Set V=min(G-1,k-m), W=min(G-2,k-max(A-2,m+1))
=min(V-1,k-A+2). The unrestricted both-marked lower bounds the complement,
the exposed leaf equals T(A-1,V,k), and capacity Pascal plus cut domination
proves the result. W=1 is handled as threshold zero.
The checked small-axis upper and attainment wrapper were removed from this node.

Failed first check 20261001-072726-492880: final two cut transports left rho.k
as a projection while arithmetic equalities mentioned k; 133.708565s /2611MiB.
The repair rewrites rho.k=k explicitly on each side. Earlier subproofs reported
no errors. This was an elaboration failure, not a failed mathematical inequality.

Research window window-f54b868a196a4fe9 ended with accepted=1. Separate configured
Sol self-review window window-f30c5cb89a254095 ended with accepted=0.
No independent Astra review: host forbids delegation. No new Python/workflow code
or shared algorithm was introduced; existing automation reused, promotion deferred.

Exact open obligations remain: larger-axis positive-label empty-history bound
<=T, neither-marked four-candidate exchange, degenerate full-selector edges,
and N_ends/N_root. The larger-axis two failed charge routes are documented in
HANDOFF.larger-axis-upper-stuck.md and are diagnostic, not a target refutation.
Useful next helper: actual indexed marker on chosen global <=2 forces every
point base and recursive bound zero, via existing left/right-extension witnesses
and unconditional sum-point-base upper. Search returned no exported match.
Same native trial and deadline remain active.
