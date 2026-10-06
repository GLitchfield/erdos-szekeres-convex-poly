# R25 mathematical handoff — final, 2026-10-04 02:49 UTC

**This run has not proved or refuted BDL. No new Lean statement, theorem or
proof receipt.** The obstruction-analysis alternative has an exact paper
reduction and independently checked diagnostic evidence. The formal node
decomposableStateUpper_all remains OPEN (hash a5d6767d0f8a1d2e, sorryAx),
blocked by ctx_card_le_bound. The formal claim was released PARTIAL at
02:48:28UTC, before expiry. The native goal was paused at the research
deadline; this finalization delivers its obstruction-analysis alternative.

## Proof idea and exact missing lemma

Fix s=k-1. Write c,d,sigma for actual cup, cap and strong-set maxima,
with zero on the empty set. BDL asks for a partition on[s-beta,alpha-1]
with cup in bandj<=j+1 and cap<=s-j, when sigma<=s and alpha+beta>=s+1.

The intended proof is size induction at a decomposable root, using DS,
endpoint splitting and duality. Its precise remaining obligation is:

- beta>=4, p=s-beta>=1, 3<=m<=beta, alpha=p+m;
- nonempty decomposable A,B form X=A<<B;
- c(A)=p, c(B)=alpha, d(B)=d(X)=beta, sigma(X)<=s;
- a valid B partition on p,...,alpha-1 is supplied;
- a maximum beta-cap of X meets BOTH A and B.

**Construct a valid partition of X on those same bands. Every point may
change bands; all A need not enter bottom.** This is MIXED ROOT, not the
false frozen-child extension statement. BDL implies it; the full conditional
size induction in BDL-CORE-REDUCTION.md proves the converse using the closed
cases below. It is minimal for this accepted reduction, not a globally
unique minimal conjecture or a compiling theorem. No general constructor
or preserved induction invariant is known for it.

For a maximum-cap core, L*=max first(D) and R*=min last(D) over all
maximum caps D; open means L*<R*. The retention geometry is exact.
Every maximum beta-cap of B strictly
encloses ALL A, d(A)<=beta, and d(B intersect open span(A))<=beta-2.
A is classic and sigma(A)<=s-2; the join p+beta=s forces sigma(X)=s.
Mixed maximum-cap existence is equivalent to at least one threshold:
d(B_<maxA)=beta-1, d(B_>minA)=beta-1, or, for |A|>=2,
d(B intersect span(A))=beta-2. These are one/two-A-endpoint extensions.
An arbitrary bottom may create a p+2 cup, exceeding its p+1 limit.

Putting ALL A in bottom is equivalent to a child map whose bottom C has
c(A intersect span(C))<=p-1. Full-core BRL+ positioning implies this,
but is stronger than ordinary ROOT and diagnostically REFUTED by paper82.
The pinned n24 child c4/d5/sigma6,core(6,15),bands1..3 admits neither
bottom<=6 nor bottom>=15. Ordinary singleton parent at gap7 still has a
verified valid map with z inband2. This does not prove that all-A-bottom
fails at that gap, and refutes neither ordinary ROOT nor BDL. No all-A-bottom
normalization, parent-core openness or d(A)<=beta-1 reduction is assumed.

## Closed paper cases and what they teach

One band is immediate; two bands use maximum-cap first points and their
complement. Both strict maxima give separated child ranges; non-tight
retention absorbs the lower child in bottom; retained cup is dual.
At beta3 the open B core splits into two spatial cups, R20 bounds their
total by2s-2, and endpoint splitting yields a positioned bottom. All
small/singleton hypotheses are checked in BDL-CORE-REDUCTION.md.

Paper81 closes EVERY hard root with no mixed maximum beta-cap, even if
pure A caps strictly contract the core. Let F be first points of A's
maximum beta-caps, or empty if d(A)<beta. Then c(F)<=p-1 and
d(A minus F)<=beta-1. Put F into supplied bottom and A minus F into
second, leaving other cells unchanged. DS gives both cup limits; bottom
cap follows from containment in X, and second cap cannot overflow without
a mixed maximum cap. This works for EVERY supplied valid B map. The
endpoint theorem needs p>=2 only when A has a beta-cap; p1 is a singleton.
Paper68 core conservation is the F-empty subcase.

Paper74 explains the remaining difficulty: a conserved inner insertion
can preserve both exact maximum-chain families but create a regional
(beta-1)-cap that an outer point extends. Maximum-core events are bounded
(paper73), yet deleting conserved stretches loses this extension state.
Exact regional merge identities (paper76) need prefix, suffix AND
two-endpoint interval ranks. There is no established compatible family.

The cardinal alternative CD is |B|<=F-choose(s-2,p-1) for open-core B,
where F=sum(j=p,...,alpha-1)choose(s-1,j). It is conditionally equivalent
to the general cardinal upper bound, not known sufficient for BDL.
Paper80 attains it uniformly and proves its m2 boundary classically;
m>=3 remains unproved, and a demand1 quad refutes unqualified propagation.
Restoring the sharp family's missing classical face gives full bands but
closes its core to(maxA,minA). This is not a universal representation.

Diagonal padding (paper78) preserves old triples and exact numerical
excess while reaching c=d=sigma=s. The diagonal upper bound remains open.
A saturated diagonal map can leave old points outside their natural
range (paper79), so capacity equality does not prove normalization.
Generic matroid exchange/rank submodularity also fail (paper75).

## Accepted inputs and receipts, separate from R25 credit

DS: sigma(A<<B)=max(sigma(A),sigma(B),c(A)+d(B)); cups meeting A use
an A cup and at most one B endpoint at each end, caps dual. Audited
paper source in the primary checkout:
runs/claude-audit-667-20261003/AUDITED-PROOF-667.md section6.1.
The crossing strong-set construction is already in Decomposable.lean.

R23 common-endpoint extension, retained commit7806d5c4 on
node/ContainsCupSetSuccOrContainsCapSetSuccOfOneChangeCommonEndpoint:
hash e6dfd0cd7e387aa5, sorry=false, only standard axioms, uncovered/
nonstandard empty. Requires both chains>=2, OneChangeOn their union,
cup MAX=cap MIN. It is absent from this branch index and not imported.

R23 classical per-band bound, retained commitbad5a94e:
card_le_choose_of_oneChange_no_cap_no_cup, hash6e4f3d0cdd9013a5,
sorry=false, standard axioms. Exclusions a=s-j+1,u=j+2 yield
choose(s-1,j), including endpoint bands. Not imported or changed here.

R20 diagonalCupBlocksForce4kk_of_five_le and
diagonal_cup_block_card_add_le require k>=5 and two disjoint spatial
cups, OneChangeOn, no four-cap, no k-cup and no strong k-set.
Receipt hash7b9515ee94a1f04b, sorry=false; proof artifact
bdb377a1fb55ede6b5b84c038b1b62a63e7121a934d1cc9271b93b29b460d0bf.
Reuse only. Review36 also checked threshold/classical/window interfaces
and monotonicity against the current source; no Lean reduction is added.

## Evidence and failed routes to preserve

All computations below are diagnostic, not Lean certification.

| Question answered | Artifact / exact guarded job | Outcome |
|---|---|---|
| Full-core one-sided BRL+ positioning | brl24-backtracking-recheck.txt / 20261003-223307-714ff0 | n24 c4/d5/sigma6, both inclusive sides impossible; singleton ordinary map valid; passed10.6s/1613MiB |
| Pure-only contraction and endpoint repair | pure-maximum-closure-certificate.json / 20261003-215341-49dcb5 | n15, exact two pure caps, no mixed cap; checker0.207469503s, guarded job0.7s/7MiB, rc0 |
| Frozen supplied map can block all bands | exact-frozen-child-root.json / 20261003-163902-f49cdf | n14 mixed ROOT, every insertion blocked, explicit recolored parent valid; passed0.016231s/13MiB |
| Upward-only higher-band repair insufficient | top-middle-required-certificate.json / 171455-14b1ba,171640-4579d2 | every sided repair needs old top into new middle; ordinary BRL survives |
| Natural child witnesses need not glue | natural-pascal-trap.json / 182312-e38782 | all256 red maps,66valid, blocked; ambient/parent maps valid |
| Endpoint-only removal of spare budget fails | unit-budget-failure-certificate.json / 191726-370f1c | both canonical peels fail; noncritical-cell repair exists |
| Exact regional profile formula | regional-merges-n6.json / 20261003-205050-aa468a | all792colorings/1214roots/72344cells agree; passed0.772579555s/8MiB |
| Max-family conservation loses outer response | core-conservation-regrowth-certificate.json / 201604-fa2c8b | regional cap4->5, changed outer core; passed0.042144339s/12MiB |
| Tower base needs ambient third band | tower-ambient-base-certificate.json / 195147-9e13a6 | natural2/3 impossible by capacity6/7<10; ambient3/3/4 valid |
| Uniform cored sharpness | cored-pascal-sharpness.json / 20261003-212610-152877 | both entire cap families/cells validate; passed0.688677356s/12MiB |
| Padding and failure of automatic normalization | diagonal-padding-fixed.json / 211338-422631; saturated-padding-map-certificate.json / 211955-bd7fb4 | constructions pass; saturated old point outside natural range |

Single-point/monotone repair already fails on the retained isolated n13
map; a repair must include a band-transfer cycle. Whole-core cap drop,
merged-context DS siblings, root choice, raw-rank/Hall windows and frozen
higher bands also have retained failures. Exact scopes and proofs are in
BDL-OBSTRUCTION.md sections1-82; do not retry fitted variants.
Canceled n29 probes123638-8b81d1/125750-914085 had no verdict:
ALL dropped n29 coverage stays OPEN. Budget-lowering corpus191430-632b5c
stopped2/5; remaining3inputs are UNCLASSIFIED for that operation.
Wrong-path184908-b200d4 was canceled before execution, zero coverage.

Shared Q17/Q25/Q23 reports are not independently replayed R25 evidence.
Q25's attained threshold contexts are not universally self-inductive;
its named n7 output was empty at02:02. A later shared journal reports
n7 failures too; none is independently replayed here. A special closed
family still needs proof.
SOURCE-PROVENANCE.md records source hashes, scope and public-source limits.
The later published journal-paper full text remains unread; no proof
contents are inferred from that inaccessible source.

Late shared journal3968c872... inspected02:44 reports no full BDL proof.
Its ZLOCK hard scan is now reported complete; our earlier partial-at02:26
statement is historical. The proposed point-by-point multi-A reduction
fails because a second A point is not a lower singleton of B plus the
first A point: the mixed-middle coloring rule changes. Its joint keep/lift
criterion needs cup intervals plus prefix/suffix AND two-endpoint cap
ranks, agreeing with paper76. Finite reported keep-all successes are not
a normalization theorem. These late sources/outputs were not independently
replayed here. A separately owned guarded conditional BDL=>Theorem8
scratch is reported; it proves neither BDL nor the mixed root, and is
not an R25 statement/import/receipt. SOURCE-PROVENANCE.md keeps the scopes.

Separately owned coordinator audit20261003-221231-81fdd3 finished rc0/
24MiB; its source/output were read. Conditional BRL+=>BDL constructions
have FAILS[] through n7,1262406 candidate parent checks. This does not
prove the BRL premise, test paper81 n15, or add an owned job/theorem.
Exact source/output hashes and DP scope are in SOURCE-PROVENANCE.md.

## Code, jobs, branch and accounting

All154 owned jobs are terminal and inspected, NONE pending. No other
agent's jobs or caps were changed. Claim decomposableStateUpper_all was
released PARTIAL at02:48:28UTC, with this handoff and the exact unresolved
mixed-root obligation recorded in the release note.

Branch research/r25-bdl-20261003, baseline d63b3fb8. Local library commits:
0ecad62e3a9b3364e7371f611aa60869fde2f77a (root cuts),
d0715adf9b776c976853d9db430b24e4ff5a97d2 (exact triple metrics),
5cd45a7fccf170716341edc1edb8925fec6a5d85 (root quotient),
HEAD233168fa6cfec18e0eed46238f6fa4cabaf23306 (classical labels/decoder).
No merge/push; R21/R22/R23/R24 preserved. Baseline diff14files741insertions,
all library/docs/tests/fixtures, no Lean or generated-certificate edits.

Guarded library checks:23tests150348-e7be8e;40tests181658-d45568
(1.76s/35MiB);40tests184930-602e54 (2.20s/36MiB);
26tests20261003-214014-b7e0ed (XML0.639s, guarded1.0s/37MiB), zero XML failures/errors/skips,
and example214014-ee7fcb. Commit214048-a8f601 and clean tree inspected.
No source edits after passed checks, so no repeats are warranted.

Final inventory0e1dc2a43d7d58604bc67c0becb0f36f6e2d9c5939c0453ddca19d1b53a2f734:
102artifact sources, nine tracked Python, eleven inline. Exactly two
byte-identical copied independent checkers and resource/replay commands
were added since64da2681...; all prior100/9/9 hashes unchanged, no removals.
There are0pending/unknown/proof/validation receipts. Source/inventory
reconciliation is complete through that checkpoint, including comparison
to295c038a...: all102/9/11 hashes unchanged. It records0activeclaims.
CODE-REVIEW.md and CODE-INVENTORY-RECONCILIATION.md record full reviews,
recurring promotions and deliberate one-off deferrals. Only configured
gpt-6.1-sol xhigh self-review; no delegation or independent Astra review.

Research36 d1c73f6ae0ca4f74 and review36 67bcc8fba66a46d0 ended accepted0.
Final consolidation/report window27df83d6901d4161 ended02:48:29UTC,
accepted0; earlier windows ended accepted0. Final statusf9184444... has
stale[]/problems[] and the tracked tree is clean; no extract required.
Claim release, final status and recorded-usage reconciliation are done.
Snapshots exclude the active final response and later reporting until
recorded; this is not an exact final-token total. Initial ~20sec research/maintenance
overlap prevents exact phase attribution; no savings/cost claim.
Review36's explicit phase sync has24recorded responses/33551output
tokens, exceeding its observational10000target; no quota/deadline was
reset. CODE-INVENTORY-RECONCILIATION.md records source reconciliation.

Explicit deadline sync has1150recorded requests, input156710296,
cached150921728,output1842958,reasoning1076854, reconciliation deltas0.
The closed final window's factual handoff has80responses/output74676,
reasoning41047, also exceeding its observational10000target.
Its resource report has0explicitly-linked jobs; the two late BRL jobs
are nevertheless captured in the agent-owned154-job inventory. No
complete causal phase/resource attribution or savings is claimed, and
no usage records were reassigned. Final reporting is included only as
it becomes recorded; CODE-INVENTORY-RECONCILIATION.md has later snapshots.

Chronological handoffs are preserved as .history-0209.md,
.history-2300.md and .history-1906.md. Current proof account:
BDL-CORE-REDUCTION.md; full record: BDL-OBSTRUCTION.md; living synthesis:
GENERAL-PICTURE.md. The safest next mathematical action is to prove a
compatible regional-context family for MIXED ROOT, with its quantifiers
and ambient terminal truth explicit, before registering/formalizing BDL.

## Finalization and resumption

Consolidate2026-10-04T02:18:19Z; research deadline02:48:19Z; final report
by03:18:19Z. Research admission stopped at the deadline; no new research
was started in the authorized finalization turn. The claim is partial,
all owned jobs terminal, accounting window closed accepted0. Coordinator
host20261003-104816-63f404 and other agents' jobs were not managed.
On resumption read es status, relevant node journal and this handoff first.
