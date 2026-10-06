# R16 final mathematical handoff — 2026-10-01 17:06Z

**Full N_ends/N_root: Stuck, still open. Part 1: done. Thirty independent helper
theorems: accepted.** All exact commits/checks/type locks/evidence links are in
[ACCEPTED-INVENTORY.md](ACCEPTED-INVENTORY.md); their scope is summarized in
[CERTIFIED-SCOPE-MAP.md](CERTIFIED-SCOPE-MAP.md). This account supersedes the
historical checkpoint headers, preserved in MATHEMATICAL-HANDOFF.history-preconsolidation.md.

The target is a uniform one-level root
`σ={a,u,k,word,maxima:=[m]}`, with k≥3, 1≤a,u≤k, 1≤m≤k−2 and physical
letters child or ext 1 side. For 2≤numRuns, N_ends asks for an attaining
singleton at one of first child, last child of first run, first child of last
run, last child. Its raw cut is T of the singleton part's cap/cup limits plus
the complementary part's bound, for some side and 1≤c≤k−2, complementary
maximum k−1−c. Exact Lean signature: [N-ends.signature.txt](N-ends.signature.txt).
The target itself has no separate actual-marker hypothesis; helper theorems
that use one require that bridge explicitly. The end filter is
`p+1=word.length ∨ letterAt(p+1)≠child`.

N_ends is registered and open at
`22d8137334ce31f2175aee57f29ff79d92fc1f36`.
The weakening theorem `cd1e05ce4528237b2cae5d120e310f044bcacdaf`
has an explicit selector premise and no dependency on an open conjecture.
Neither registration, falsifier success nor this implication closes either target.

Accepted selector scopes, writing G for chosen global, A for opposite global,
Vb=min(G−2,k−m), Ve=min(G−1,k−m), H=k−m:

- Both ends marked: first child attains for G≥4,A≥3 when A≤5 or Vb≤4.
- Exactly one end marked: global child at the exposed end attains when G,A≥3
  and either A≤4 or Ve≤4, or an axis≤5 with A+Ve≤k+3.
- Neither end marked: first child attains for A=3,G≥3 and for G=3,A≥3.
  An all-axis first-cut floor T(A,H,k) is accepted when H<G; attainment is
  accepted in the axis-four/axis-five-below-saturation range for (A,H).
- Indexed actual chosen marker with G≤2: arbitrary raw every-fuel/full bound
  zero; a separate first-child selector follows under k≥3 and two runs.
- Raw positive context with indexed maximum at least k−2, opposite global≤2
  and two runs: every-fuel/full zero, plus optional legal first max-one cut.
  This needs no actual occurrence at that indexed level.
- Positive boundary geometry: chosen G≤3/opposite≤2 with one suitable marked
  boundary, or G≤4/opposite≤2 with both suitable boundaries, gives zero and
  the first-child selector under each exact handoff's hypotheses.

These statements do not combine into full N_ends. In particular, no claim here
closes all neither-marked A=2 edges, all larger-axis cases or the general
neither-marked exchange.

Reusable compiled tools include exact sole boundary erasure, adjacent boundary
merge, exposed-prefix merge, capacity Pascal identity, both-marked unrestricted
axis threshold lower and exposed-first unrestricted axis threshold lower.
The prefix merge preserves globals because the young marker is before all
older markers and children. Adjacent boundary merge can decrease chosen global
by one; its geometry is different. Do not interchange those transformations.

The raw positive-history global-T upper is compiled for either axis≤4, and for
either axis≤5 with a+u≤k+3. A one-level absorbed-marker upper is also compiled
for opposite global≤3. Raw positive labels and an indexed actual chosen marker
with G≤3 imply every-fuel/full bound≤2; two distinct actual chosen levels improve
this to≤1. This is an upper bound, not selector attainment or zero by itself.

Latest accepted raw geometric annihilation:
indexed N of side s, actual x,y∈extPositions N, every child p satisfies x<p<y,
and global s≤3 imply every fuel and full bound are zero. No positivity, WF,
opposite bound, k, history legality, run count or maximality premise.
Its proof forces every child chain≥2, annihilates point contributions, bounds
full context by their sum, and transports through closed fuel stability.
Commit aab5395c45d32470b40458039b26b9a79fcbc0e0; check
20261001-123039-b16343; type ca893a8c2e474cd0.
[HANDOFF.bracketed-three.md](HANDOFF.bracketed-three.md) contains exact receipt,
proof hashes and the failed first import attempt. No raw-to-root consumer
composition has been separately certified.

The exact Stuck obligation is:
positive physical labels, legal 1≤a,u≤k, empty indexed history, arbitrary runs
and positive inert barriers ⇒ bound≤T(a,u,k).
Remaining range: min(a,u)=5 with a+u≥k+4, or min(a,u)≥6.
Both same-obligation failures are diagnostic and preserved:
[HANDOFF.larger-axis-upper-stuck.md](HANDOFF.larger-axis-upper-stuck.md).

1. Rank-triple support charging at chosen5/opposite7/k7 counts 56 triples
   while T=26. Job20261001-061913-2ecdcc tests 36 both-marked A=U=7,m1/2
   roots, 2–4 runs, run lengths1/2 and≤4 children, both sides. Normalized
   Python/compact-inert-C evaluations give actual26, no actual upper violation.
2. Scalar split charging asserts
   T(A,min(G−1,k−m),k)+T(min(A,k−n),G,k)≤T(A,G,k),
   with legal m+n=k−1. At A5/G7/k7,m4/n2 it gives30>26;
   m5/n1 gives27>26. Job20261001-062036-f1475c tests the same36roots and
   1240propercuts:496 scalar failures, no individual estimate or actual cut
   violation. The lost correlation is geometric, not a tested target violation.

Semantic warning: a normalized context with maxima=[] but an ext1 marker is
not in the C evaluator's ordinary depth-zero accepted domain. Use the explicitly
matched Python reference or compact inert C semantics described in that handoff.

A kernel-certified narrower failure is SSLSS,A2/G3/k4/m1: source1, every legal
global-end cut0, inner first-run end p1 cut1. Closed commit
aad0cd4939df89e219189c4372b9e629a5f2950e/check20261001-094654-b4d99d.
[HANDOFF.global-end-counterexample.md](HANDOFF.global-end-counterexample.md).
It refutes global-end-only selection, not N_ends, N_root or universal selector
minimality. Ordinary decide first OOMed; successful proof uses trusted-kernel
decide+kernel, no native_decide or new axiom.

Other diagnostics: owned N_ends falsifier5976roots/98688cuts/zero violations;
neither-marked k5 probe20261001-074826-1998b8 covers1242roots/32076cuts,
zero FIRST/LAST/paired failures but46 fixed-coupling failures; k6
20261001-074826-da70dd covers2944roots/101376cuts, zero selector failures but184
fixed-coupling failures. These are finite families, not Lean theorems. The
readonly coordinator k8 result20261001-100119-2c9c39 covers25872contexts/
20366nonzero,≤4children,2–4runs of lengths1–3,both sides,A/U2..8,m1..6;
zero N_root and extreme-run-end failures,10global-end failures. Its family
differs from earlier≤5children probes. No dropped≤6children scope was closed.
Evidence references and semantics remain in the preserved historical handoff.

Unproved prospective routes:
[PROSPECTIVE-DEGENERATE.md](PROSPECTIVE-DEGENERATE.md).
Crossed actual chosen levels with G≤3 could force chain≥2 using the closed
chain-one exterior dichotomy twice. A protected child between old markers
may allow recursive G3/A2 zero via that lemma. Two-run inner-end comparison
needs a nested cut keeping the entire last run; keeping only its last child
can create an annihilating fresh marker. For higher chosen G≥5/opposite2,
the first chosen singleton join estimate is max(3,m+1), not m+1:
L S L S L/G5/A2/k5/m1 has chain/join≥3. This correction is diagnostic inference
and was logged before any attempted proof; none of these routes is credited.

Operational handoff: no owned job is pending at16:58Z. All thirty helper claims
are released closed; N_root/N_ends research claims were released partial16:56Z
after immutable HANDOFF.full-target-STUCK-1655.md was linked in es, SHA
adb73b4101e9eec7cf82c05485ee921b7de07687e1525e251a1160b1bf888ec4.
Administrative checkout/restore jobs125548-1dd609/125647-78fb16 bothdone; accepted30
branch is restored, clean/stale0/problems0. ADMIN.final-claim-releases-1657.json.
No integration or primary source edit occurred. Shared DB recovered16:18Z after lock
errors; [OFFLINE-LOG.pending-1608.md](OFFLINE-LOG.pending-1608.md) was reconciled
in es before the next proof. Admission cause remains unconfirmed.
Only standard guarded es jobs were used for Lean/compiler/long work.

Sol self-reviews, receipts and source-parent checks are recorded per result.
The final thirty-result receipt/parent/path inventory is
[ACCEPTED-RECEIPTS.final-audit-1646.json](ACCEPTED-RECEIPTS.final-audit-1646.json).
Every commit changes its own module and four import/node metadata files.
Guarded diagnostic job20261001-124906-638eb3 completed17.5s/20MiB/1GiB,
all30 proof bodies match frozen candidates;28 full modules byte-match and
the other2 differ only by one final empty line. Exact comparison output:
[AUDIT.committed-proof-spans-1649.json](AUDIT.committed-proof-spans-1649.json)
and [nonbody diffs](AUDIT.committed-proof-nonbody-diffs-1649.json).
These read-only checks add no mathematical theorem credit.
Independent Astra review was forbidden by the host; shared-library diagnostics
were reused, and generic resource-readonly CLI promotion was deferred outside
the allowed one-node research scope. Whole-thread usage is reconciled without
reassigning historical explicit windows; offline/overlapping/direct-job
attribution gaps remain. No savings or matched-comparison claim is made.

Resume by reading es status, node-filtered journal spanning this entire run,
this handoff and the exact failed inequalities. Safest main advance is a
cut-aware larger-axis charge retaining correlation, with neither-marked
exchange and degenerate edges kept explicitly open. Do not repeat rank-triple,
uncorrelated scalar-split, global-end-only or fixed-coupling routes unchanged.

Finalization17:06Z: research deadline passed and host paused native goal;
explicit user permits only this report turn, no new research. Existing receipts
and clean restored checkout were inspected; every owned job already terminal,
both full-target claims partial, all30 helper claims closed. Trial/report complete
under the brief's supported Stuck criterion; mathematical targets still open.
Final whole-thread usage snapshot USAGE.final-snapshot-1705.json has1569records
through17:05:09Z/delta0; active/later reporting and window attribution gaps explicit.
