# R19 progress

Finalized 2026-10-03 00:28 UTC, after the fixed deadline. Agent
`codex:01a0fc94-0467-7b90-823c-bce1e6fe6128`. Research deadline
2026-10-03T00:25:54.693298Z; consolidation starts 2026-10-02T23:55:54.693298Z.
Only configured Sol/xhigh; no delegation, merge or push. Every independent
node branch starts at `e3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8`; R18 branches preserved.

## Mathematical outcome

The requested splitting maximum and FLANK-SWAP with present flanks are proved.
The brief's positional predicates alone allow absent levels and are insufficient,
as a separate Lean counterexample certifies. Full PEEL is
refuted with its stated raw-context hypotheses. There is no proof idea for
that false statement. The refutation witness is also certified infeasible
for Satisfies, so it does not settle singleton attainment on actual histories
or the happy-ending conjecture.

The k=6 middle-child example now has exact bound eight, unique attaining
child, a certified failure of pointwise remaining-budget-loss selection,
and an actual decomposition history. Its explanation is residual run
separation: the middle cut leaves two unit runs and the old final run of
capacity four, giving remainder six. End cuts leave a contiguous pair or
remove the last run. Equal leaf gains do not eliminate this difference.
A general feasible-selection invariant remains unknown. No sibling-penalty
narrowing was commissioned.

Feasibility also fails to pass through every legal formal cut: the same k6
parent satisfies its constraints, but its p0 upper3 cut has a lower2 remainder
whose first pair has cup limit one. Both parts are WellFormed; no coloring or
ambient set satisfies that remainder. The chosen cut is nonoptimal. This rules
out arbitrary-part feasibility as an inductive invariant, without refuting
singleton attainment for a suitably chosen cut on actual histories.

## Accepted statements and evidence

All sixteen accepted claims are released CLOSED, with original-source
receipts, unchanged locked types, standard axioms only, no sorry or uncovered
dependencies, and passing changed-node audit/layers. Each independent branch
preserves all 378 inherited lock objects and adds exactly one statement.
The per-node handoffs contain exact hypotheses, searches, failures and receipts.
ACCEPTED-EVIDENCE-16.json indexes each pin, compiler receipt, captured fixture
and recorded final body. ACCEPTED-EVIDENCE-16.verified.json combines the original
fifteen-record static audit20261002-171010-38e8c4 (0.7s/27MiB) with the new
arbitrary-part verification. All sixteen proof spans match; fifteen full fixture
assemblies match exactly, and the raw PEEL refutation additionally has its
documented module-level heartbeat option. Types and proof text are unchanged.
The earlier fifteen-record operation snapshot and PART-FEASIBILITY.release.json
record the closed releases; all original proof jobs are terminal. This is
independent provenance verification, not an integrated build or extra theorem credit.
Scheduled FINAL-REVIEW.operation-state.json confirms all sixteen terminal
original jobs/CLOSED releases and the clean current pin, with no owned live
claim/nonterminal job. FINAL-REVIEW.documentation-provenance.json preserves the
last handoff's original acceptance snapshot alongside its post-release update;
the proof source and all other handoff digests are unchanged.

| Result | Pinned commit | Original check | Detailed account |
| --- | --- | --- | --- |
| Split attained at d=a-2 | 991b783989fd7515b23409ec3202bd9b860210e3 | 20261002-083132-7de94e | SPLIT-ATTAINED.HANDOFF.md |
| Every split sum <= threshold | e29026398ad8cafe3ce1c93dd80a85dda8978c4b | 20261002-084819-794720 | SPLIT-LE.HANDOFF.md |
| Opposite FLANK-SWAP | e05ed9a3a90443aff49d04047dda17f97ba4627b | 20261002-092340-20d151 | FLANK-SWAP.HANDOFF.md |
| Full PEEL negation | 119a082b4ee8a668e565027b226f5bc4cacddb66 | 20261002-101239-d357fa | PEEL-REFUTATION.HANDOFF.md |
| Satisfies implies pair limits >=2 | c37f3751de15f776209110fdf31048fa3d8b2319 | 20261002-105442-376a39 | PAIR-LIMITS.HANDOFF.md |
| Exact PEEL witness not Satisfies | 1e8e5c90b897d653c1e875ee39bee22f172ce64e | 20261002-110525-546700 | PEEL-INFEASIBLE.HANDOFF.md |
| Oldest singleton-flank normalization | e51c80334b2da5be84b6630d5f1491129462b742 | 20261002-112036-dd5454 | OLDEST-FLANK.HANDOFF.md |
| Satisfies under larger same-position limits | a2f5f1388b4109415e8b8a703dd2a8ea30d43dc7 | 20261002-113919-10c1db | SATISFIES-TRANSPORT.HANDOFF.md |
| Satisfied k6 end-cut failure | 8e2f72ce9b0ae129609f051661313b7bee767dcf | 20261002-122611-18dca1 | K6-SATISFIED-END-GAP.HANDOFF.md |
| Unindexed exterior padding | 940641e30236f2dbf0b0f229cacbfe05872f8f5a | 20261002-130548-84659e | UNINDEXED-PADDING.HANDOFF.md |
| Satisfies under ordinal limit transport | 3ef1651152fa03db37ef45215344ea5c986f256d | 20261002-133225-571382 | RANK-TRANSPORT.HANDOFF.md |
| Remaining-budget-loss cost failure | c0094d67eaf0247835dcb62b4720328896c815ba | 20261002-135814-128f53 | BUDGET-LOSS.HANDOFF.md |
| Exact k6 bound and unique middle child | 1cd0281b18dddb1177d47d876c1e6b87f15fc741 | 20261002-145508-8b2f02 | K6-EXACT.HANDOFF.md |
| Actual k6 history | d3b81e384ff288237fbef7fa380c985dd0ded1ca | 20261002-160456-155bf5 | K6-HISTORY.HANDOFF.md |
| Vacuous flank predicates insufficient | c6cbb39d5f845059595734204ca0d1c9a561a497 | 20261002-164625-6c030a | ABSENT-FLANK.HANDOFF.md |
| Arbitrary legal parts can lose feasibility | 6b5dce7e7d26dc99172f89b72e9b4bebcefd51fc | 20261002-172857-7ed08e | PART-FEASIBILITY.HANDOFF.md |

The positive PEEL statement was registered unchanged with its falsifier on
node/CtxBoundAttainedBySingletonCut, commit
528caa7e560a86e8e77661d4a21e54d29f3454e4. Its Blueprint sorry is a placeholder,
not an accepted theorem. Official exact-dataset falsifier
20261002-100340-9841d8 returned COUNTEREXAMPLE/inner rc2. The accepted negation
uses the same literal context.

## Actual-history result

ctx_k6_actual_history_witness, type 80c84048681897f7, certifies the coloring
with levels [0,0,0,1,3,2,0]. Six actual deep-below splits construct a decomposable
tree; the existing realization theorem supplies IsSweepRealizable. Root
profile upper bounds are cap/cup <=4 and strong <=5. Actual singleton sibling
cap maxima equal one. Three applications of the closed context-transfer theorem
give the literal context SSS1L3L2LS/maxima111 at (5,5,6), with an actual
four-vertex child satisfying it.

Original check 20261002-160456-155bf5 CLOSED: compiler 6.601233s, guarded outer
55.5s/2353MiB under 4G. Receipt
d882dc65055b3a1af3920b833c3e518df688494e481c51e80b25075ff88f965d.
Pinned d3b81e384ff288237fbef7fa380c985dd0ded1ca. Research window
window-919a78fd58a7486a ended accepted1; separate Sol self-review
window-93d73fe61830469a ended accepted0. Claim release confirms evidence copied
to the primary checkout. All owned jobs are terminal.

This does not establish sharp child cardinality eight or the stronger
IsGeometricallyDeepBelow coordinate predicate for the same tree. The exact
bound/attainment and history have independent receipts; no compiled combined
corollary is claimed.

## Open obligations and failure boundaries

The raw PEEL witness is (4,4,5), 3U4LSS1L2USS/maxima1111. Its bound >=2 is
certified, all 24 legal singleton sums equal one, and exact bound two is
diagnostic only. Its first ordered pair has cup limit one, contradicting the
vacuous two-point cup requirement. No happy-ending counterexample is implied.

Oldest-flank normalization changes the selected axis G to min(G-1,k-m);
unindexed exterior erasure and ordinal Satisfies transport explain the lift.
The normalized raw context need not be WellFormed. Logical compositions of
independent branches have no separate proof receipt.

PEEL.MECHANISM.md gives the k6 structural explanation. Side/coupling uniqueness
and the zero-valued optimal-leaf example remain diagnostic. The accepted exact
k6 theorem proves uniqueness of the child, not uniqueness of its side/coupling.
Pointwise limit-loss minimization is refuted; a capacity trade incorporating
residual runs and strong joins has no proved general invariant.
The zero-leaf example also records first-pair caplimit1; it therefore supplies
no feasible-history evidence against positive-leaf selection. Its literal
infeasibility has not been compiled as another theorem. ZERO-LEAF.scope-diagnostic.json
preserves the exact diagnostic profile and the certified pair-limit condition
explains the scope boundary.

The superseded generated PEEL scan 20261002-093527-a2bca0 ended ERROR/-15,
not PASS. Exact-identity recovery 20261002-100139-bd1337 stopped it after the
depth-four witness settled the full target. Partial coverage and unvisited
rows remain explicit in PEEL.HANDOFF.md. No missing output earns credit.

Failed compiler, parser, guard and launcher attempts are documented in the
shared journal and per-node handoffs. The lost sandbox runner was reconciled
only after exact observations; no foreign process or lease was changed.
Worker-backed guarded checks are the reliable path used for final receipts.

## Accounting, review and continuation

Scope verification, inherited-end-cut reconciliation and absent-flank research
and review windows are complete. Evidence consolidation window-1feefd39ee0f40c6
and source-adapter self-review window-f57238c373c44fad are complete.
Feasibility-obstruction research window-dd9b0cbfa73f418c ended accepted1;
separate self-review window-b1703224a25d450e ended accepted0. Final mathematical
synthesis window-412e1171c13e4480 and separate code/documentation self-review
window-b28ad7f3aa8e44a3 ended accepted0. The scheduled consolidation checkpoint
is complete: hold window-b306cab98c484543, mathematical review
window-51ef1b9b7c494ddd and separate code/library self-review
window-320b2a5076bd4ddc ended accepted0. Completion reporting/deadline
observation window-ceadbb22e48046f9 also ended accepted0 after the fixed deadline.
No research resumed after the host pause. FINAL-REPORT.md is the completion account.
Current branch
node/CtxSatisfiesArbitraryPartCounterexample is pinned at
6b5dce7e7d26dc99172f89b72e9b4bebcefd51fc, with the exact baseline parent and clean tree.
The fixed deadline passed and the host paused research admission. Finalization
inspected existing receipts and operational state only; no new research or
compiler check was launched. The R19 research/reporting objective is complete
to its qualified outcomes. Feasible PEEL and the main conjecture remain open.

All accepted-node research and separate self-review windows are complete. Reviews are
Sol self-review under the fixed no-delegation contract; independent coordinator
review remains pending. Only the inherited-end falsifier and its recorded
result changed among tracked execution files, on their separate correction branch. Shared
evaluators, parts, split classifiers, guarded jobs and proof assembly were reused;
fixed candidates were not generalized solely to grow the library.

LATE-USAGE.completed-windows-38.json records 1058125 outputs in thirty-eight completed,
nonoverlapping windows, with zero reconciliation deltas. Latest guarded usage job
20261002-200041-c9d1c3 is verified; final mathematical review7422/code-review4981 outputs.
Bounded finalization sync/report commands reconciled completion window6557
outputs after its close, importing available session usage through00:27:39UTC.
The code-review stayed below its observational10000 target. The hold window's
10772 outputs exceeded observational10000 by772; earlier excesses remain recorded.
LATE-USAGE.final-report.verified.json preserves the exact scope.
Active/unassigned work and incomplete
resource associations prevent an all-in matched-work claim; no savings claimed.
The host/session identity gap remains documented and is not repaired by rewriting
identities or double-counting. Available late usage is reconciled; subsequent
finalization/reply remains outside the recorded window total.

Preserve runs/r19-sol-20261002/ alongside pinned branches: it is ignored by Git.
MATHEMATICAL-HANDOFF.md and per-node handoffs are the research account.
The previous long progress snapshot is PROGRESS.20261002-2005.md.

Inherited end-cut-of-four-le is refuted/notready on its correction branch. Its old
falsifier covered only two external levels and missed both accepted witnesses.
Pin4bd6580007983864837acf6bf65930f709d04c21 adds fixed regressions using the shared
evaluators, changing only falsifier and result on an independent baseline branch.
Official replay20261002-163119-f885b2 records counterexample/innerrc2; claim released
refuted after separate self-review. END-CUT-RECONCILIATION.HANDOFF.md is exact.
No inherited statement or R18 branch changed; this grants no new theorem credit.
The falsifier result is tracked per checkout: independent e3baseline branches
still carry the old pass until the coordinator integrates this pin. The shared
journal records the refutation but does not replace their tracked records.

Latest scope certificate: absent-flank example SS at(5,5,6), maxima1,2. Positional
flank predicates hold vacuously, but the exact FLANK-SWAP normalization to3,2
changes bound10 to4. ctx_absent_flank_swap_counterexample is CLOSED and pinned
c6cbb39d5f845059595734204ca0d1c9a561a497 on independent e3base. Original check
20261002-164625-6c030a: compiler3.984048s, outer52.1s/2345MiB under4G, receipt
b6b07830e79402c133ded8f19180ce85d5a8135d5b24280d4866dbc435346e84.
Both contexts are WellFormed and satisfy the exact swap formula's M legality.
Declared absent maxima still contribute to strong joins despite zero external
walks; one-run thresholds give10 and4. This certifies insufficiency of vacuous
positional predicates, not independent necessity of each presence premise.
The accepted presence-restricted FLANK-SWAP remains unchanged. Separate self-review
and claim release are complete; four evidence files copied to primary. General
feasible PEEL remains open without a proof invariant.

Latest accepted obstruction: a legal formal part need not preserve feasibility.
The same satisfied k6 parent has a p0/upper3 cut whose lower2 remainder gives
its first pair cupLimit1,2=1; both parts remain WellFormed. The theorem certifies
that no coloring/set satisfies that remainder, using finite parent limits and
the two-point cup/rank argument without bound recursion. It refutes an
inductive invariant, not feasible PEEL or all optimal cuts.
Search found no exact duplicate; preceding code/library self-review is complete.
Independent node/CtxSatisfiesArbitraryPartCounterexample starts exactly at e3base;
branch job20261002-172031-876925 DONE. Registration20261002-172112-317d5d DONE
89.9s/2304MiB4G; type9bd7f9a32a302abf and post-lock claim succeeded. Fresh
fixture captured before body. First check failed only at unfolded-alias endpoint
simplification; same-type repair passed original check20261002-172857-7ed08e:
compiler3.833904s, guarded outer41.1s/2354MiB under4G, receipt
739ee383947782d1c2d2ebb2bb7f19e20f6f804fd1d5834ccf1a2ac4e252ce81.
Pin6b5dce7e7d26dc99172f89b72e9b4bebcefd51fc, exact five-file change;
claim released CLOSED after separate self-review, eleven evidence files copied
to primary. PART-FEASIBILITY.HANDOFF.md is exact. No new selector trial is active.
