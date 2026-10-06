# R18 usage and final inventory — 2026-10-02 02:42 UTC

Deadlinefinalsnapshot02:45:42.643Z:1383recordedrequests, input190481336,
cachedinput184497536, output1699147, reasoningoutput871795; reconciliation
deltasall0. USAGE.DEADLINE.FINAL.SYNC.json supersedes the cumulative snapshot
below; historical per-window counts remain bounded by their ended intervals.
The current finalresponse/later reporting can still lag. Nativegoal externally
PAUSED at02:45:22.637741Z, observed02:45:33Z, tokensUsed6837776/time43199s;
these native counters differ from provider aggregate semantics. FINAL-STATUS.json.

Provider session01a0f7ed-59fc-7af0-94d8-48d685c62129,1369 recorded requests;
snapshot through02:41:35.880Z: input189612500, cachedinput183648000,
output1693539, reasoningoutput870312. All four reconciliation deltas are0.
These are full-session cumulative counts, not a per-window claim. Current and
later reporting requests can lag the imported snapshot. No price or savings
is inferred. USAGE.RESEARCH.LATE.SYNC.json, USAGE.MAINTENANCE.LATE.SYNC.json,
and USAGE.FINAL-MATH.SYNC.json preserve the exact reconciled import.

Explicit ended windows and recorded per-window output:

| Window | Accepted public nodes | Input | Cached input | Output | Reasoning output |
|---|---:|---:|---:|---:|---:|
| research window-bff1ef2d0f4547b3 | 12 | 182149549 | 176548224 | 1625581 | 837791 |
| self-review/publication window-a4873af9906b446d | 1 | 4938550 | 4845824 | 32407 | 18646 |
| final mathematical review window-c85462127fc74aca | 0 | 2289828 | 2039936 | 34231 | 13772 |

Window reports cover only recorded requests assigned to each explicit window.
Their sum is not the full-session snapshot; setup, other associations and late
reporting remain separate. Resource links on those window reports cover only
explicitly linked jobs. Failed attempts, setup, recovery and review are retained
in the full job inventory and session accounting; no matched savings comparison
exists. FACTUAL.RESEARCH/MAINTENANCE/FINAL-MATH.HANDOFF.json are automation
resume bundles; MATHEMATICAL-HANDOFF.md is the separate mathematical account.

Final host review artifacta39380e6971e2110e3046ad93bbeed60fdc6678ce093a5c3357120429788dad7
is235848bytes, preserved as HOST.REVIEW.FINAL.JSON plus four bounded pages.
It lists171 researcher jobs,0pending,0unknown,0activeclaims; resources17964.3
worker-seconds/max8687MiB. The host carrier20261001-104505-2e0e57 is explicitly
excluded from researcher jobs and remains running pending native-goal deadline.
No wait, review, cancellation or mutation was issued against that carrier.

Inventory26 explicitproofreceipts/25artifactcodefiles/39baselinechangedcodefiles/
2inlinecommands is not theorem credit. Exactly13 original-source CLOSED public
receipts are accepted, with matrix FINAL-ACCEPTED-RECEIPT-MATRIX.json. General
ROOT-NF partial receipt is OPEN/threeholes and creates no theorem credit.
The host review reports usage unavailable because its separate explicit window
cannot reassign responses already held by the actual research/setup windows;
its zero fields do not mean zero consumption. The exact UsageError is preserved.

Final versus pre-final code inventory: only the already-reviewed portable
endpoint regression changes hash9db4db2a... to75d036fc...; only the audited
same-side bridge module is newly visible among changed tracked sources,
SHAdf5b48d34c3e3b1ddca4d77a8a305deed594b5f8a403e498d88a1e40685d0e3b.
No other artifact/inline/source changes. All were reviewed in
CODE-REVIEW-AND-MAINTENANCE.md and FINAL-MATHEMATICAL-REVIEW.md.

Final git HEAD0edc7d9d49a59651765b973d571408edc7b30af0 on
node/CtxSameSideRootPartLeOneLevelRoot; tracked status empty, diff--check0,
config cmp0 against SAME-SIDE-PART-ROOT.registration-config-original.toml.txt.
General partial commit09395dfc6e2f254881b29899625b250fb2ef2062 remains on
its independent node branch. No merge/push or primary tracked-source edits.
