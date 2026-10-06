# ROOT-NF partial induction checkpoint, 2026-10-01 18:18 UTC

Branch `node/CtxOneLevelRootBoundNormalForm`, commit
`fc037f7fc2eac7f283dc8dfe27b3daa73c46172f`, exact type
`e0cedb9ee88cc591`. Targeted check `20261001-140511-cb43c3` compiled
in 7.98s/640MiB; receipt `ROOT-NF.induction-v8.DONE.RECEIPT.json`, immutable
`2395afde00833b1593e4532e4b27f24dcc7ed5d4a7d1860ddfbb3f2ad1db4911`.
Source snapshot `ROOT-NF.induction-v8.txt`. The theorem remains OPEN and uses
three explicit ESBlueprint sorries; it receives no theorem credit.

The proof uses strong induction on the number of children with the complete
smaller-root equality as its IH. Empty and unit-global cases compile. The
raw single-run equality is proved locally and resolves both inequalities;
its independent closed theorem is committed at
`8cd359e6c71ec20d80ab1254f7a97999d4f5a5f1` (see
`SINGLE-RUN-NF.HANDOFF.md`). Existing common-singleton-rank gives the raw
positive-label global-at-most-two bound <=1. Thus a positive normal form
settles the axis-two upper direction. Proper block and complement child
counts are strictly smaller, but their two-level histories prevent directly
applying the one-level root IH.

Exact remaining obligations: both coupled lower/upper interval-cut sums are
at most the normal-form bound, and the normal form is at most the source for
multirun roots. Independent component domination and several erasure routes
were diagnostically refuted; paired sums were not. Retaining ordered marker
threads and their cut capacities is necessary. The next same-trial step is
the generic two-level unilateral youngest-marker profile prepared in
`TWO-LEVEL-UNILATERAL.signature.txt` and `.body-v1.txt`; it supports a direct
outer-run witness for axis two, but does not establish every recursive path's
minimum cost. See `AXIS-TWO-THREAD-INTERPRETATION.md` for that open criterion.

Frozen ROOT-NF diagnostics passed the official 29,520 k=3/4 cases and the
157,680 k=5/6 cases (at most four children). Larger-child pilot
`20261001-141337-6802f1` compares four/five-child no-end alternating roots at
a=u=k=7,m=1,lower: both values are 31; five children took 1.0324s.
All evaluator comparisons are diagnostic, not Lean-certified equivalence.
No own job is pending at this checkpoint. Research remains active under
R18; this branch claim is released partial while an independent helper is
checked from main. No merge, push, full extract, or existing statement edit.
