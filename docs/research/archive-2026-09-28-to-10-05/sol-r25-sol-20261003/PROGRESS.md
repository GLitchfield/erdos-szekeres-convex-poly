# R25 progress

Finalized: 2026-10-04 02:49 UTC (host clock). Research deadline passed;
native goal was paused at the deadline; obstruction-analysis alternative delivered.
**No BDL proof or refutation, and no new Lean theorem/receipt.**

Full-core BRL+ is now diagnostically REFUTED, paper82. Independent exact
replay223307-714ff0 gives n24,c4/d5/sigma6,core(6,15),bands1..3:
both bottom<=6 and bottom>=15 impossible. The singleton parent at gap7
still has a verified ordinary map with z inband2. Ordinary BDL/MIXED ROOT
remain open; no sibling-specific all-A-bottom impossibility is inferred.

The exact remaining lemma for the accepted size induction is MIXED ROOT:
s=p+beta, beta>=4, p>=1, alpha=p+m, 3<=m<=beta; nonempty
A<<B with c(A)=p,c(B)=alpha,d(B)=d(A union B)=beta,
sigma(A union B)<=s, a valid supplied B map on p,...,alpha-1, and
a maximum beta-cap meeting BOTH children. Construct a parent map on
those same bands; all points may recolor and A need not all enter bottom.
BDL-CORE-REDUCTION.md proves its conditional equivalence to BDL.

The proof idea is fixed-s size induction plus DS, endpoint splitting and
duality. Ordinary separated/non-tight roots and the beta3 boundary close.
Paper81 now closes every no-mixed-maximum root: lower cap-first endpoints
enter bottom, remainder enters second. This works for every supplied valid
child map, even pure-only strict core contraction. The endpoint split
supplies bottom's missing cup unit and the no-mixed hypothesis prevents
second-band cap overflow. There is no general constructor for MIXED ROOT.

The obstacle is compatible regional nearmaximum chains: conserved inner
points can change an outer maximum-cap response without changing either
maximum-chain family. The retained n14 mixed root blocks every frozen
insertion but has an explicit globally recolored partition. Core movement,
cardinality slack and fixed natural child witnesses do not provide repair.

The cardinal deficit CD is sharp and its two-band boundary classical,
but demand>=3 remains unproved. Diagonal padding preserves exact excess;
saturated partitions need not normalize old points into their natural
bands. Neither interpretation proves BDL. Generic matroid exchange fails.
Shared Q25 attained threshold contexts also fail universal self-inductivity
in its diagnostic scope; none is independently replayed or credited here.

Key inspected guarded evidence:
- 20261003-223307-714ff0: BRL+ witness, passed10.6s/1613MiB; resource-only
  pilot223237-f65078 passed0.1s/13MiB and pinned the source labels.
- 20261003-215341-49dcb5: pure-only repair, checker0.207469503s;
  guarded job0.7s/7MiB, rc0.
- 20261003-205050-aa468a: exact regional identities, all72344cells agree,
  passed0.772579555s/8MiB.
- 20261003-212610-152877: uniform sharpness construction at two declared
  cases, passed0.688677356s/12MiB.
- 20261003-214014-b7e0ed:26library tests passed, XML0.639s,
  guarded job1.0s/37MiB, zero XML
  failures/errors/skips; 214014-ee7fcb shared example passed.
Earlier decisive failures and all job/receipt paths are in the current
MATHEMATICAL-HANDOFF.md; chronology preserved as .history-0209.md.

All154owned jobs terminal/inspected, none pending. Latest review
0e1dc2a43d7d58604bc67c0becb0f36f6e2d9c5939c0453ddca19d1b53a2f734:
102artifact sources/nine tracked/eleven inline, old hashes unchanged,0new
proof/validation receipts. Reviews/promotions are in CODE-REVIEW.md and
CODE-INVENTORY-RECONCILIATION.md. Only configured Sol xhigh self-review,
no delegation or independent Astra review. Research36 ended accepted0;
review36 window67bcc8fba66a46d0 ended accepted0. Final consolidation/report
window27df83d6901d4161 ended02:48:29UTC, accepted0. Deadline usage sync
has1150recordedrequests/deltas0; active final response is excluded.
Final statusf9184444... has stale[]/problems[] and tracked tree clean.
Separately owned
coordinator audit221231-81fdd3 reports conditional BRL=>BDL replay FAILS[]
through n7; source/output read, no general theorem or owned-job credit.

Branch research/r25-bdl-20261003; local library commits0ecad62e,d0715adf,
5cd45a7f, HEAD233168fa6cfec18e0eed46238f6fa4cabaf23306. No merge/push,
Lean edits or generated certificate changes; R21/R22/R23/R24 preserved.
Node decomposableStateUpper_all remains OPEN/sorryAx, same hash/blocker.
Claim released PARTIAL at02:48:28UTC, before expiry;0activeownedclaims.

Consolidation02:18:19UTC; research deadline02:48:19UTC; report by03:18:19UTC.
No new research admitted after the deadline; host and other jobs unchanged.
Safest next mathematical action: prove a compatible
regional-context family for MIXED ROOT, including its closure quantifiers
and ambient base truth, before registering or formalizing BDL.
