# K4 singleton-only exchange obstruction

The registered statement is kernel-closed, type `7b96730d60e9b6fd`.
Its well-formed witness has globals4/4/4, word1U,S,S,S,S,1U,S,S,
maxima[1], children[1,2,3,4,6,7], keep[1,2,6] and complement[3,4,7].
Both keeps are noninterval. Membership is TTFFTF, so the only singleton
maximal homogeneous segments are6 and7. The old lower1/upper2 sum is3.
Removing6 or adding7 gives sum<=2 at every legal d=1,2 and both
orientations. This refutes the singleton-only exchange candidate already
at the first positive k boundary. It does not refute any-length FLIP;
diagnostic whole-segment free maxima are[3,3,2,2].

Accepted check: `20261001-070404-e30a90`, rc0,182.2s,3372MiB,OOM0,
budgetfalse, innerbuild125.193188429s. Full99776B receipt:
`CHECK.k4-singleton-counter-v2.json`, file SHA
`7f6ddfb35f70c72c838dbb83b8419f8a23e4970e4da7a266c35911e66ed555b4`.
It records closed/locktrue/noSorry/standard axioms only/blocks[]/errors[],
targeted=true,incremental=true. Candidate1688127B SHA
`6a11d8b7ab532518e3fef3e07825e516c14f59561d0ba47cf74562cb13444613`
is `K4-SINGLETON-COUNTER.candidate-v2.txt` and byte-identical to checked source.

Proof reuses retained cut-DAG construction, directional projection and
scoped emitter: jobs065943-7d4f0a (one4child timing,275nodes/.0198s),
070029-dc2d90 (all18roots,3570nodes/.9658s),070105-d57870
(996facts/914contexts/.0228s),070232-81738a (clean candidate,maxlive96).
All64 IO progress pairs were removed before the accepted check. C values
only selected untrusted certificates: Lean checked all finite base arithmetic,
part equalities and interval-cut upper/lower arguments independently.

Reusable closed dependency: CutUpper commit
`05165669189e2bbbbe4994579e0d4ff28d171236`, exact archived source
`CUT-UPPER.proved-source.txt` SHA0a05fbfa4f83dc8d17bd3da78bde0e87cce5930c3ed10352c0c808bf8c03e7e8.
Its untracked module overlay is excluded from this node's commit and must
be removed after commit. Baseline point-sum and large-sibling-maximum
lemmas supply finite upper shortcuts. Integration needs the separate
CutUpper commit; no merge or primary source edit was made.

Failed approaches preserved: candidate-v1 monolithic ordinary decide
check063529-35124b hit24GiB guard after967.1s/twoOOMkills (no proof credit),
complete failure receiptCHECK.k4-singleton-counter-v1.json. The30GiB
admission062805-f975f0 never started and was cancelled before execution;
no coverage stopped. Registration062229-0cab66 failed preexecution because
the ES_AGENT shell assignment was treated as argv; identical env-prefixed
062335-547415 registered the unchanged type. Capturesa6404693... and
9c8014fc... preserve pre-repair sources. Exact C replay062149-dd27fc is
diagnostic, not a substitute for the accepted Lean receipt.

Open mathematical obligation: positive-k>=4 paired uncrossing for an
entire maximal membership segment of arbitrary length. Changing coupling
or orientation while keeping a singleton move is insufficient. Neither
positive point capacity nor unchanged surviving point capacities alone
give a full recursive lower bound; see fresh-unit-clear-timing.json and
inactive-insertion-timing.json. Those latest routes are diagnostic only.

One-node commit completed: job `20261001-070823-a88881`, commit
`0eba300863870b28df2b74f67d5e765cfa5c92b6` on
`node/CtxKFourSingletonMaximalSegmentFlipCounterexample`. It includes exactly
the own module/root import/lock/index/status records, excludes CutUpper overlay.
