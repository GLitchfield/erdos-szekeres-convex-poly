# R14 mathematical handoff (research stopped, verified 2026-10-01 00:49Z)

One authorized Sol xhigh trial; no delegation. Agent
codex:01a0f4c8-720d-7fe2-afe2-0052a6bdd4b4, window window-7e3932fdc6b84ad4.
Original research deadline12:06:12.335613Z was superseded by coordinator early
finish at00:57:33.947017Z; finalization hard stop01:27:33.947017Z.
Part1 narrowing is **Done**. Full Done is unmet. Part2 is **Stuck** after two
consecutive failed lifting attempts at the same obligation; new research stopped
at00:45Z under RESEARCH-BRIEF.md. Independent witness verification then passed.
No third attempt or new trial is authorized by this brief. The native goal is not
marked complete: its proof objective remains incomplete and its current status is
paused. This account does not claim N_root is false. Coordinator result review
confirmed Part1 Done/Part2 Stuck and ended the trial; COORDINATOR-REVIEW.json
preserves that authoritative receipt.

## Exact remaining obligation

Prove `ctx_one_level_root_bound_attained_by_singleton_cut` (N_root), type
81be57bce6e33074. Its complete signature and current registered module are in
`N-root.signature.txt` and `N-root.registered.lean`.
For globals 1<=a,u<=k, k>=3, maxima[m] with 1<=m<=k-2, a word over
child/ext1side and at least two runs, there must exist child p, side s and
1<=c<=k-2 with

    sigma.bound <= T(capLimit(sigma.part[p]s c,p,p)+1,
                     cupLimit(sigma.part[p]s c,p,p)+1,k)
                   + (sigma.part(P minus p) opposite(s) (k-1-c)).bound.

No arbitrary raw-context singleton theorem is asserted. N_root remains sorry.
X (`ctx_one_level_root_singleton_base_exchange`) is open on main and is a
stretch goal only after N_root. Closing N_root would leave composed C1r dependent
only on X; the global happy-ending proof remains open.

## Accepted Part1 receipts and independent-main commits

All branches start at main4d0be1b72911 (no merge or push).

| Result | Commit | Targeted check | Type hash / status |
| --- | --- | --- | --- |
| N_root registration | 763b4b67730ef5e3c8215ec5c441bb7b84979a41 | 20260930-201226-c5e3cf | 81be57bce6e33074, compiling conjecture |
| Explicit N+X conditional | f575ec7269a34e65846110120a6d3e68a3fdce6f | 20260930-201714-9a8260 | fdf891b82544f272, closed |
| C1r composition | 9262f92e48bad197df1c1462064ff2f067bdfb40 | 20260930-202121-ffa3b9 | 94e83f4b24e9975d, transitive sorry |

N_root branch: node/CtxOneLevelRootBoundAttainedBySingletonCut. Registration
job20260930-200854-e937c8, commit job201349-17fac2.
Conditional branch: node/CtxBoundChildRunContractionOneLevelRootOfSingletonExchange.
Registration201439-59e3cd, commit201903-b6756f. Closed claim released.
C1r branch: node/CtxBoundChildRunContractionOneLevelRootR14. Commit202519-534b19.
Its existing declaration statement and docstring were preserved.

`CHECK.conditional.json` (artifact
d8eb137d025c8948d4153f304fdcf6de19ec731ecb3a7f4384e5735c67431833)
reports sorry=false, lock_ok=true and only propext/Classical.choice/Quot.sound.
`CONDITIONAL-HANDOFF.md` explains its reused R13 proof and exact hypotheses.
`CHECK.C1r.json` (artifact
96563eef872ef2ff67beea8e0f377a711eeb352de52ac71fe7139d873fa8c0bd)
reports unchanged locked type, sorry=true, and exactly the three direct theorem
dependencies: closed conditional, N_root and X. C1r has no local sorry.
That check used byte-identical untracked source overlays from the two independent
commits; they were removed after checking. Integration must bring those two commits
before C1r. C1r used closure-only extraction (incremental=false), so its full branch
index was not refreshed; the targeted receipt proves the composition.
Source snapshots, proof fixtures and all commit/check receipts are alongside this file.

## Diagnostic N_root evidence

Falsifier20260930-201130-95f7bd passed 5976 roots, 127472 singleton cuts and
127472 independent explicit-T leaf audits. `FALSIFIER.n-root.json` has complete=true,
zero violations and exact parameters. Family: 2..4 runs, run lengths1..2, <=4 children,
one old marker per gap, optional single end markers, both old sides; k5 all25 globals,
k6 only(5,5),(6,6), every legal m. Finite compiled arithmetic only, no theorem credit.
Cold longest four-child/four-run k6 timing201006-634c3f:0.07987s,32cuts/audits.
Earlier timing200854-cd2368 covered <=3runs; an initial word-count error was corrected
in the journal before the sweep. Shared singleton-cuts/context-part/evaluator APIs reused.

## Two failed Part2 attempts

Both attempts sought to replace an attaining original-root interval cut B,R by a
strictly smaller attaining original-root block. Neither fixed a selected leaf or
used R13's minimum-active-capacity selector. All root sides/couplings were free.

1. **Shrink inside B, with every internal block free.** Job203426-6088a8:
   root(a,u,k,m)=(3,4,5,1), word S L SS L SS, zero-based children[0,2,3,5,6].
   B=[2,3], R=[0,5,6], lower c=2 (also c=3) gives1+2=3=rootbound.
   Every proper original-root block strictly inside B, every side and legal c,
   has cut value at most2. Root singleton6 upper c3 attains3 outside B.
   Both outer parts have at least two children. Evidence rotation-fixtures.result.json.
   This refutes internal shrink after full internal reoptimization, not N_root.

   The same fixture job independently exposes the single-run boundary needed for
   the brief's Pascal step. Root(3,3,4,1), word SS L SS, has bound2 and singleton
   maximum2. Its prefix[0,1] upper c1 part has point limits cup=cap=1 and base1;
   every legal further proper cut of that part sums to0. An unrestricted claim
   that a single-run part's base is attained by its proper cuts is therefore false.
   The closed ctx_base_pascal_combine and ctx_bound_three_way_base_allocation are
   upper bounds; they do not assert attainment in this unit/unit case. A separate
   treatment of this boundary could still be part of a valid global proof.

2. **Rotate among three whole pieces, all attaining inner cuts free.** If B is
   multi-run, optimize over ALL cuts A/(B minus A) attaining its actual part bound.
   Allow the root's isolated block to be A, B minus A, or R whenever that set is
   an original child-order interval; reoptimize all root sides/couplings. Test both
   unrestricted piece size and the version requiring size strictly less than B.
   Cold timing203852-88f833: k=a=u=6,m1, five isolated child runs with upper old
   markers at gaps and both ends; bound11, all25 eligible cuts pass,0.704429s,249MiB.
   Sweep203944-6341ad then finished728/728 roots,11228 eligible optimal multi-run
   outer cuts,50 failures in BOTH versions across25 root rows,307.193866s,257MiB.
   Five-minute review at715/728 estimated6-20s left and left the job unchanged.

   Exact positive-component witness: (3,4,5,1), word S L S L S L SS,
   children[0,2,4,6,7], B=[2,4], R=[0,6,7], lower c2 (also c3),1+2=3.
   B is multi-run. All12 attaining inner cuts choose A=[2] or[4], either side,
   c=1,2,3, with values0+1 or1+0. The maximum root cut isolating either of these
   singletons, all root orientations/couplings free, is2. R is not an original
   interval, so isolating that whole piece is not an admissible root cut.
   Singleton7 upper c3 attains3, outside the available whole interval pieces.
   Exact nested rows and all singleton values: FAILED-ROTATION-WITNESS.json.

   Sweep scope: exactly five children in2..5 runs, run lengths1..3, one old
   marker per gap, optional single end markers, both old sides (104 words);
   globals(3,4,5) and(6,6,6), all legal m,728 roots. All25 failed root rows are
   retained (record cap40 was not reached):15 at(3,4,5,m1,lower),10 at m2,lower.
   Ten of50 failed outer cuts have positive B value. Every retained failure root
   still has an attaining singleton. No claim is made about N_root over the
   unretained nonfailure rows; this sweep tested the rotation predicate.

The two failed attempts are the internal lifting law and its three-piece repair,
at the same attaining-cut replacement obligation. They do not refute an argument
that uses additional minimality assumptions or a more global exchange.

## Exact remaining inequality and reusable observations

Write P=sigma.childPositions and

    V_sigma(K,s,c) = (sigma.part K s c).bound
                  + (sigma.part (P minus K) opposite(s) (k-1-c)).bound.

For a legal one-level root with at least two runs, an original interval B with
|B|,|P minus B|>=2 and V_sigma(B,s,c)=sigma.bound, the missing unrestricted
replacement law is

    exists K in sigma.blocks, |K| < |B|,
      exists t,d, 1<=d<=k-2 and sigma.bound <= V_sigma(K,t,d).

Together with recurrence attainment, swapping complementary singleton sides and the
closed <=3-child base, this would give a block-size descent to a singleton.
No proof of this law is supplied. Its restrictions K strictly inside B and
K among the three whole nested pieces are refuted above. The witness family
satisfies the unrestricted inequality by an outside singleton, illustrating
precisely the extra movement/refinement a valid exchange must permit. The
counterexamples do not imply the missing unrestricted inequality is false.

MERGE can compare the first nested part when the two new sides agree, using the
larger maximum. Regrouping the other part with R creates different external
history and may add an active same-side extension in the new R part. Cut lower
bounds do not by themselves compare that sum with its old value. Erasing a level
keeps its letters external but inactive; it does not directly yield the desired
root-part history. A value-dependent sum exchange remains necessary.

Do not repeat R13's refuted minimum-active-capacity selector, fixed-position
lifting, general end-cut normal form or unrestricted adjacent contraction.
R13's handoff at the path in RESEARCH-BRIEF.md was read. M2's parent HANDOFF.md
update reports a diagnostic singleton-segment flip for interleaved partitions;
it supplies no certified nested-history exchange here.

## Verification and code review

Independent Python zero-child recurrence replay passed with no mismatches:
204700-42ee55: unit/unit fixture,0.108813s,22MiB (AUDIT.first-python.json);
204828-4db107: internal shrink,7.933801s,34MiB (AUDIT.internal-python.json);
204828-2be80b: three-piece rotation,9.256834s,33MiB (AUDIT.rotation-python.json).
Checks include root and every singleton-cut value, both relevant outer parts,
all12 attaining inner cuts, and the exact failed maxima. These are independent
arithmetic checks, not Lean certification of any counterexample.

REVIEW.receipt-source.json checks committed module bytes against snapshots and
captured source/type hashes, direct parent4d0be1b729110f969f78ee88e77fd970f82173e8,
whitespace, and unchanged C1r statement/docstring. All pass. Mutable main has since
advanced to0d161d4d84ad38f6fb560fde2cc735fb1e52cd7a; the initial review's inappropriate
current-main comparison is retained as REVIEW.receipt-source.mutable-main.json.
The corrected review uses the immutable base specified by the brief.

The audit adapter had one misplaced branch caught before execution; its unexecuted
version is audit_rotation_witness.prelaunch-bad.py. The corrected adapter's jobs
all pass. There were no new Lean compiler failures or statement changes in R14.
No new theorem body for N_root was accepted or committed after its registration.
Shared singleton-cut, context-part, compiled and Python evaluator APIs were reused.
Sol self-review is recorded separately from the coordinator's received result
review. No delegated review was run by this session; the coordinator confirmed
the reported Done/Stuck outcome and initiated early finish at00:57:33.947017Z.

## Infrastructure and resume state

Worktree Git metadata is read-only in the sandbox; direct branch creation failed before
mutation, then guarded branch jobs succeeded. All compiler work used guarded es jobs.
No full extract, merge, push, model change or delegation. Three missing helper oleans
warmed in201131-230441; X warmed202043-5d9f98.
N_root claim could be taken only after targeted check incrementally refreshed its
falsifier status. The 4096-byte default artifact page caused one receipt JSON parse
failure; the complete receipt was then fetched with explicit byte limit, without
recompiling. Failed fragment retained as FAILED-RECEIPT-FETCH.conditional.fragment.txt.
Harness `es release` unexpectedly copied CONDITIONAL-HANDOFF.md to primary runs/;
the side effect is logged. No primary source was edited; future releases cite immutable
receipts and put worktree handoff paths in the report separately.

Current branch is N_root's branch (return job20260930-202658-4ede16 terminal).
All R14-authorized compiler/research/verification jobs are terminal. Other agents'
jobs, including the external host, are not ours to alter. N_root and C1r claims
have been released partial with immutable receipt IDs; the conditional claim was
released closed. REPORT.sol.md and PROGRESS.md record final release state.
No callback has been verified and no notification is promised.
Research window7e3932fdc6b84ad4 ended with1 accepted theorem (closed conditional).
Mathematical/code self-review window9d7251efd05a4851 and separate maintenance
accounting are recorded in the final report; late usage may still reconcile.
The compact host review inventories these files but misses explicit job/proof
linkage because its registered researcher id differs from this session's consistent
ES_AGENT, and its baseline includes older main changes. The explicit targeted
receipts and immutable-base source review above supply the mathematical evidence.
On explicit resumption read es status, this handoff, node-filtered journal and job
state first. This brief's two-attempt stop remains in force; do not start another
trial without a new research instruction. Coordinator result review is received.
Safest next proof step is a separately scoped exchange route that permits an
outside block, refines the complement and handles the single-run unit boundary.
