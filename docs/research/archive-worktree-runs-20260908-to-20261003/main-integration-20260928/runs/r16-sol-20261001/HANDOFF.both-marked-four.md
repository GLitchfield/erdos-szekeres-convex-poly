# R16 handoff: both-marked first-child selector through axis four

Frozen 2026-10-01 10:33Z. Closed independent commit
969fbbaa55474f6aa839058758f75c90a499ac8b, branch
node/CtxOneLevelRootFirstSingletonCutAttainsOfBothMarkedEffectiveAxisAtMostFour.
Approved parent5847e155fa613d4d2311eaee86b4b094f630e9a4; five node files, clean.
Commit job063230-c73537 completed; parent and worktree status verified.

Exact accepted theorem: 3<=A<=k,4<=G<=k,1<=m<=k-2; uniform child/ext1-side
word with both actual ends marked and a child; at least two runs;
A<=4 or min(G-2,k-m)<=4. The first child p attains with opposite singleton
maximum c=k-A+1 and selected complementary maximum A-2. The conclusion uses
the raw explicit leaf threshold. Arbitrary marker multiplicities and run
lengths, both axes. For k<=6 the effective-axis condition is automatic.
The stated global hypotheses remain; this is not the full selector.

Check20261001-062838-278d13 firstcandidate,34.1950259209s/2468MiB/4G.
Receiptbd186247942c56b66dbf431361f75e5547c3a684ccad9e04ea7ac4cabef368bc.
Lockedtype3e9549000369df01,sorryfalse,onlypropext/Classical.choice/Quot.sound.
Fixture62ca6bbd9f751e91958cf2a704668ef31690e1046d0465c41f7e336d7af050eb.
Frozen Both-marked-four-attainment.closed.lean SHA
187460aab244554226ea6a694e50c64db872503e27f1d757857139e02ea44ba3.
Receipt CHECK.both-marked-four-v1.closed.detail.json SHA
36eb14f2a013a2f3fd5d38fe2e90c2bf25e9081af86faeb8c8e57ef1f28bda9a.

The 95,410-character lower/Pascal/complement proof is unchanged from10301b1.
Only the normalized small-axis hypothesis and upper helper broaden to four.
The upper helper is the full accepted9c1bbea3 body, reused locally on this
independent branch. Two-boundary normalization leaves legal globals and
positive inert markers, so the arbitrary-history global-four upper applies.
This verifies that composition beyond the earlier three-axis cases.
No new ad hoc Python, C or workflow code, and no compiler failures.

Research7360549f07e34788 endedaccepted1; separateSolselfreviewe3354bca00d142f0.
CODE-REVIEW.both-marked-four.md records signature, source, exact-byte reuse,
receipt, commands and maintenance review. No independentAstra underhostrule;
factoring duplicated proof transport is deferred to authorized integration.
No pending job for this node. Existing <=3 statement is unchanged.

Eleven accepted helpers are preserved. N_ends/N_root remain open. Two
larger-axis upper routes failed at the same exact obligation; see frozen
HANDOFF.larger-axis-upper-stuck.md and its 36-root/1240-cut diagnostic receipts.
Neither-marked, mirrored exposed end, larger effective axes and degenerate
edges remain open. Next verify the exposed-first/marked-last selector through
axis four using the same accepted upper. A global-axis-two edge may instead
require the selected-side leaf because the opposite-side leaf is inactive.
This is a proposed follow-up, not accepted mathematics.

Native goal remains active under its no-completion-before17:04 contract;
same trial, no integration or deadline reset. Whole-thread usage10:31:41:
749requests,input103235756,cached100345216,output783741,reasoning390106,delta0.
Active/late and unlinked-job attribution gaps remain explicit.
