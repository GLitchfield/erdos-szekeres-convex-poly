# Accepted ordered root endpoint geometry

2026-10-03 18:45 UTC. General theorem accepted through the full repository
workflow; commit `0422f8c765737dd921bf04f54781dee3acab819a` on its separate
`node/TwoFullCapBlocksRootNoninterval` branch contains exactly five node files.
No finite instance
is formalized and the statement was not edited during proof repair.

`ErdosSzekeres.two_full_cap_blocks_root_noninterval` in
`ESBlueprint/B/TwoFullCapBlocksRootNoninterval.lean`, locked type
`50cecd70f72957e5`, has no sorry or nonstandard axiom. Its assumptions are
p>=4, a nonempty deep-below root, two disjoint ordered fullp-cap blocks
covering that root, and absence of(p+1)-cap and(p+1)-strong sets. It proves
a four-cup and explicit lower-upper-lower and upper-lower-upper ordered
subsequences. Each subsequence witnesses a gap in one root child.

Use the accepted incidence theorem to obtain exactly two lower points per
block. Mixed-cap endpoint geometry makes them the block's first and last
points; choose an upper point strictly between. Across the blocks, upper0,
lower0-last,lower1-first,upper1 form a cup because every mixed triple has
its middle point lower. The same selected points provide the gap witnesses.
No sweep-realizability or one-change hypothesis is used.

Fixture `c3a43aee84c59d80f3674c2535200862498c0d156174627547bb1c478b249113`;
body `91210be034e9bd274e4dd13b41993a860dcb17bca0cf64f7d31309e3d0422af3`;
source `326bc17416d31afeb6193e93eb1b903962c04dedd06602386c4fc76415c79633`.
Archived v1 failed only at four local elaboration names; v2 supplied the
consumed nonemptiness witness explicitly and used omega for strict-order
contradictions. Failure diagnostics and every repair were logged.

Final operation `op-bc27079636eb4091` is SUCCEEDED. Isolated check
`20261003-141948-474392` accepted receipt
`4276de0f864f64d0296972590585d2e1dfeae4b8cc319e9e60d36cd3c8e64e8e`.
Original-source check `20261003-142153-7631e6` accepted receipt
`b7ffaee18516393348ba723e18c5b5ee3e91d1b07f385f067aa4cb0a8c1f568e`.
Full extraction `20261003-142251-748654` took1069.728s/5656MiB, was fresh
and problem-free, receipt
`cbfda24fa8ecb1ff90912468f2306dad02caece74455fc2583dfda3dea863709`.
Audits `20261003-144238-a9434b` found no failures or layer violations.
Review `20261003-144249-eaad57` accepted receipt
`266b3e4e41c7453e6f04890c4f8025dcee8eb638f68c8b010356fd0a96587fdd`.
All axioms are propext, Classical.choice and Quot.sound. Complete receipts:
`root-noninterval-final-operation.json`.

This certifies the general geometry behind the interval-root obstruction.
It does not certify the extremal construction, literal B9 or the exact
matrix-state reduction. The universal two-cap construction and literal history
are now separately accepted in TWO-CAP-FAMILY-ACCEPTED.md and
TWO-CAP-CONTEXT-HISTORY-ACCEPTED.md; the generic strong iff is accepted in
STRONG-COMPOSITION-ACCEPTED.md. Those later receipts do not certify literal
B9 or matrix equivalence. The classical peeling law without critical strong
avoidance remains a distinct structural obligation under the same deadline.
