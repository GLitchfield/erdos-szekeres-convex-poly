# R16 mathematical handoff — 2026-10-01 08:16Z

The single authorized Sol/xhigh trial is active. N_ends and N_root are still open.
No counterexample to N_ends and no mathematical Stuck conclusion has been found.
The exact target is a proof of the four extreme-run-end singleton selector,
or a real counterexample. The certified helpers below do not complete that target.

## Accepted independent commits

All branches have approved parent
5847e155fa613d4d2311eaee86b4b094f630e9a4. No merge, push or cherry-pick occurred.

- N_ends registration: 22d8137334ce31f2175aee57f29ff79d92fc1f36,
  node/CtxOneLevelRootBoundAttainedByExtremeRunEndSingletonCut.
  Locked type32c6d22aba01da18, still sorry/open. Check013617-679625 receipt
  99837175bd83963572ec457b7b8276546fe74708f3b3104c56805f54bb6df62f.
- Pointwise N_ends-to-N_root weakening:
  cd1e05ce4528237b2cae5d120e310f044bcacdaf,
  node/CtxOneLevelRootBoundAttainedBySingletonCutOfExtremeRunEnds.
  Locked type6ecc666112a7ba4e, no sorry, standard axioms.
  Check020205-1f077b receipt
  991be85828438d7ff956f52180772f70f96d8be9f55630edc52fde8964383315.
  Closed fixture2424d496c068f5b790e6b772d06981e15bd82a51ce465dfbe4c6b5a8bed2a450.
  This takes the exact selector conclusion pointwise and discards its candidate
  restriction; it does not depend on the open selector theorem constant.
- Exact boundary singleton marker erasure:
  aab76b86245a78f2f5648b83ebb90931b2e9c4dc,
  node/CtxBoundarySingletonMarkerEraseNormalizeExact.
  Locked type81fb6b0b14b6f62a, no sorry, standard axioms.
  Check030155-fd7bff; receipt-file SHA
  56ede496302f1bcd63a4bbe643af9853cb1af7fe98167b4bcce114e6616c20a3;
  fixture64f6fe0aa17c4aa95b8129cccc7ab0f0441781f526712d82283841d6d1ef3397.
  Positive labels, sole selected marker, all children/younger selected markers
  strictly on one side, oldest selected indexed level, positive marker maximum.
  Erase/reindex that level, cap selected global by min(G-1,k-M), retain opposite
  history; exact all child-endpoint limits, all fuel/full bounds.
  Physical erased marker remains inert. Frozen Boundary-exact.closed.lean,
  source SHA f0cb79aef9c6bc2377e047325d3613545bdc5e6f30b03688e9e8d53967eb2.
- Capacity-aware Pascal:
  1839fee7b02a6d9d405b9dabf445025ea1f7772c,
  node/DecomposableThresholdCapacityPascalLeft.
  For 3<=a<=k and 2<=u<=k,
  T(a,u,k)=T(a-1,u,k)+T(a,min(u-1,k-a+2),k).
  Locked type909643c533edfebe, no sorry, standard axioms.
  Check032731-9e217b; receipt-file SHA
  c2991a671fd53891d303c8bf2796ab1c3c57d6c05605667d92881874ffb73e68;
  fixturea6f75b1f619b42dd918a5d78e21164751440b806e1ac555fa642921abbe9c442.
  Capacity-pascal.closed.lean SHA
  474a0488b2e5bef06fffc14646abb8153e5d38f03388d65e7b41aae4a8e68ae4.
- Exact adjacent same-axis boundary marker absorption:
  4ad1c24f2cbc2b96d7263a9c20edcc1ff4ab6dec,
  node/CtxBoundaryAdjacentSameSideMarkerMergeNormalizeExact.
  Locked type98bb67be7dd8f195, no sorry, standard axioms.
  Check041119-280ff1 receipt
  58c9ef0ef8e21c116e7e98592a6d190ad4c520d9d2256ca2e7f7604c230aea26;
  fixture5a470668cc9300f9eb0bca040b8b1344b9cf5d823f2bebdc3f2ef4739873c3ee.
  Positive labels, MergeLevels.Inv at N,N+1, sole younger marker x,
  older selected witness before x, children and younger selected markers after x,
  no selected indexed level older than N+1, selected global<=k.
  Merge/relabel with maximum=max(Myoung,Mold+1), selected global decreased1.
  Exact all child-endpoint cup/cap limits, all fuel/full bounds.
  Source selected chain=normalized chain+1; source selected join=
  max(normalized chain+1,normalized join); opposite chain/join unchanged.
  Part commutation and all hypotheses inherited, including newly removed children.
  Frozen Adjacent-marker-exact.closed.lean SHA
  766e592a2fe05a4c80c8e9958cc594385f8c86396c060f567f809c5edb5e983f.
  Commit041437-eb828a verified exactly5nodefiles, clean tree.

Current branch is the adjacent helper. Its claim release is next after this handoff.
N_root and N_ends claims remain held; N_root expiry around17:05Z,
N_ends around17:41Z. Every later helper branch must start independently from
approved5847e155. Do not import absent modules from another independent branch;
reuse complete proofs as local haves if needed in the eventual N_ends proof.

## Open mathematical route

For an unmarked exposed first child with old lower markers, let opposite
global A, old selected global U, V=min(U-1,k-m). Choose singleton upper maximum
c=k-A+1 (legal A>=3). Proposed leaf T(A-1,V,k). Same-axis complement has
M=max(A-2,m+1), selected global U-1, point parameter
W=min(U-2,k-M)=min(V-1,k-A+2). The certified Pascal identity pays T(A,V,k).

Exactly-one-marked root upper remains open. Closed
ctx_boundary_marker_upper_normalize allows multiple occurrences of the old level;
a marked word end lies beyond every child, so it bounds the root by a depth-zero
context with selected global V, leaving physical markers inert.
Missing inequality: for legal globals and positive unindexed inert barriers,
maxima=[] and arbitrary child runs imply bound<=T(a,u,k).
No exact theorem found by es search / source search. Context.root_bound_le in
DecomposableStateUpperAll only covers a replicate-child single run.
Inert-end deletion covers literal ends; isolated-child external deletion has
additional WF/isolation/retained-level assumptions. Neither closes this gap.
A possible conditional route through smaller-global C1r/C1p must be examined
without using the open bridge for arbitrary multirun histories.

Both-marked root lower by its initial point threshold remains open. The new
adjacent absorption theorem now supplies the first-child same-axis complement
normal form for a Pascal induction. Opposite globals1/2 and selected/global
dead cases need explicit handling. M>=k-1 can make the point parameter<=1.
Next diagnostic: determine whether both-marked roots equal their point threshold
or merely dominate it; current finite evidence only tests the lower inequality.
Neither-marked roots require the actual four-end selector: there is no fixed
global word-end selector. Do not claim the exposed word-end construction covers
all four end-marking cases or proves the full theorem.

## Diagnostic evidence and pending job

- Registered N_ends falsifier013208-804918 passed5976roots,
  127472explicit-T leaf audits,98688selectedcuts,0violations.
  Frozen N-ends.falsifier.py SHA
  feb2d66a986fa80a59df02d47bde870ea415ac77c83039bb466eea245e3c96b0.
- Unmarked-first normal forms022949-45f3ec passed2700k5roots:
  14580bound/matrix equalities,8100same/6480opposite.
  1620opposite-global1 cases were explicitly outside that normalization;
  coverage there remains open.
- Marked-first same-axis normal form033705-93c1e7 passed1350k5roots,
  4050full-bound and4050all-limit-matrix equalities.
  810normalized global0 bounds used closed ctx_bound_zero_of_unit_global_axis;
  they are explicit theorem-rule values, not C measurements. Full family
 033602-36ec69 had previously failed before any audited root because C rejects0.
- Point-potential four-child families: k5 one031548-bc8545 passed2700,
  both032101-42f1c5 passed810; k6 one033126-a2b061 passed5184,
  both033127-828e73 passed1728. All zero violations; both requires opposite>=3.
- Six-child selector sizing022301-b442da: one k7 shape60leaf/30selected,
  0violations,391.15s/367MiB. 8M memo023250-2d3f25 same result367.84s/1402MiB;
  insufficient gain, original tracked source restored. Same k5 shape030249-bbe853
  passed36leaf/18selected in20.32s. Broad six-child coverage is open.
- RUNNING034251-3577ad: full9792roots, k6 exactly-one-marked,2..5runs,
  lengths1..2,<=5children,all legal globals/maxima,both sides/mirrors.
  Output point-base-one-five-k6-unit-rule.json. Latest6800done at1889.41s,
  zero violations. Explicit unit-global rule for2992expected roots,
  nonunit shared C for6800expected roots; final counts await complete JSON.
  Next review~08:19Z. Latest checkpoint5800 at1545.92s estimated30..55min left,
  left running unchanged. The original033628-3c3c4a was canceled at a performance
  checkpoint after700roots; rc-15 acknowledged, no completed JSON/result.
  SAME full coverage is rerunning; no narrowed coverage/result credit.
  Candidate/runner and all dependency files must stay frozen during this job
  because source hashes are recorded at end. Current hashes:
  point_base_candidate.py bcfcf8ef2ff8ca5b500985d5b238c8bbe24a5a4180a32cbb693b8c0216861aed;
  probe_one_marked_point_base.py 23c2b2b4cba253aadd0e3770b0ebd18768ffc2ceee54233e65948c8c9ba7598c.

Finite passes do not certify a universal theorem. Before any resumed proof work,
inspect pending job status/progress and the node-filtered journal; do not end
the reporting turn while an authorized job remains queued/running without a
verified client callback. No callback is verified.

## Failures, limitations and non-routes

Adjacent-helper compiler failures are logged before each repair: v0 generated
match branch order; v2 nil membership/decide/untyped forall; v4 redundant omega;
v7 Boolean conjunction order/wrong top=0/shadowed binder; v10 unreduced global
match in omega. All repaired; final v13 is closed. Earlier v3 20G wrapper was
canceled while queued, with no compiler result; reusable auto-sized warm
targeted checks admitted4G and passed. All partial receipts are diagnostic.
Boundary helper development failures and weakening local-let repair are in
their check artifacts and shared journal; final closed receipts supersede them.
Initial default registration/import build010756-d2fff1 hit harness1200s guard
with0modules; thin registrations were rerun through guarded background jobs.
Cold4G nested20G readiness refusals are not proof failures. Queue stalls/shared
reservations were inspected, no active reservation was force-cleaned or bypassed.
A job-review invocation using unsupported --review was rejected before recording;
the supported --next10 invocation recorded the08:09 review.

Do not retry refuted R13 minimum-active-capacity/fixed-position lifting or
R14 optimal-block/internal shrink: a3u4k5m1 SLSLSLSS,B=[2,4] attains only at
outside child7. Unit+unit base1 terms do not imply a proper cut value2.
Closed C1p bridge assumes a SINGLE-RUN ancestor; arbitrary multirun parts are
outside its contract. At most3children unrestricted attainment is not a selector
base: SLSLS gives candidates0,0,4,4 and omits internal attainer2.
Neither-marked SSLSS,a2u3k5m1 has bound1 with attainers1,3; word ends0,4 fail.

## Review, usage and operation boundaries

Configured ES_AGENT=codex:agent-run-58eb8a64138d4dfc,
thread01a0f5d9-cae4-75d0-99d9-1b543f6b3445.
Sol/xhigh only; no delegation. Separate Astra review forbidden by host constraint.
CODE-REVIEW.adjacent-marker-exact.md records Sol self-review, source/receipt
hashes, proof reasoning and current ad hoc code review. Existing boundary,
Pascal, point-base and marked-first review records remain durable. No shared
C/workflow code changed. Generic unit-global evaluator shortcut deferred while
the running family pins shared sources; any promotion needs fixtures/catalog/example.
One-off mathematical candidates remain small, separate from shared execution.
Ignored run artifacts are preserved, never included in node commits.

Research windows: ba706cd5c60c4a0e accepted2; boundary review3f3a2be329af4056;
research561503711f884f12 accepted1; Pascal reviewd3db95196e9841c3;
researche2f61983e16d47ea ended08:12Z accepted1;
current separate review72353247b15a4945. Host window9a54784a439c4b76 untouched.
Latest whole-thread usage snapshot405requests,input54270583,cached52763264,
output451988,reasoning253390,zero reconciliation delta at08:14:43Z.
This is not current-window usage. Active and late responses lag; resync each
explicit window and all-in totals. Direct jobs lack operation resource links;
zero resource totals are a coverage gap, not zero work. No savings claim.
Own initial usage-boundary correction030618-05dcd8 is preserved and reviewed.

Consolidation16:34:46.416915Z; research admission ends17:04:46.416915Z;
hard finalization17:34:46Z. Keep native goal active until full target or its
specified stopping condition, never mark it complete for Part1/helpers alone.
No new trial, full extract, primary source modification, merge/push or other model.
