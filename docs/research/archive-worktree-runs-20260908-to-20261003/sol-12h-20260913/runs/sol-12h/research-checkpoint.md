# Sol 12-hour research checkpoint

- Window: `window-e407d7cd27124261`, active from `2026-09-13T20:55:05Z`; deadline
  `2026-09-14T08:55:05Z`; consolidation begins `2026-09-14T08:25:05Z`.
- Agent: `codex:agent-run-530ee02777134960` (the first startup reads and one log used the
  provisional identity `codex:sol-12h-20260913` before the active window record was inspected).
- Starting recorded frontier: 217 closed, 12 open, one refuted; `es context` initially reported a
  stale tree. A completed full extraction later refreshed the frontier at commit `97a1459` with
  the same counts and no extraction problems.
- First obstruction: the explicit next-band `k = 6, m = 4, n = 1` gap left by
  `ctx_nonmonotone_new_marker_cut_bound_except_six_extreme`. The parent and the new focused node
  `ctx_extreme_next_cut_of_large_chosen_history_maximum` are claimed. The branch is
  `node/CtxExtremeNextCutOfLargeChosenHistoryMaximum`.
- Initial refresh receipts:
  - Direct `es extract` refused because this sandbox cannot access the systemd user bus.
  - Job `20260913-165620-1137e9` failed: the worker's inherited `ES_PROJECT_ROOT` selected the
    primary checkout; its declared output exists and records the missing-source failure.
  - Job `20260913-165723-eebd66` reproduced that failure after replacing this worktree's ignored
    `.lake` symlink with a local build directory. The original symlink is recoverable at
    `/tmp/sol-12h-lake-link-before-repair`; only dependency packages remain shared.
  - Diagnostic job `20260913-165757-6ddd19` succeeded and proved cwd is this worktree while nested
    `es` used the primary frontier (13 closed). Source inspection identified the inherited
    `ES_PROJECT_ROOT` path.
  - Job `20260913-165830-16bca7` fixed the project root and then failed because its non-login shell
    lacked Lake; output exists and records that distinct error.
  - Job `20260913-165857-9f5e8b` used the login toolchain and correct root. It compiled 164 real
    modules, then the cold full-parallel blueprint pre-build was stopped at the unchanged 28G cap
    (`rc=-15`, terminal and acknowledged; output exists). The local cache now contains 165 oleans.
- Decision: use the registered `es build blueprint --serial` path to warm missing dependency chains
  under the existing guards. Do not treat any failed extraction as a refreshed index and do not
  claim proof credit from build artifacts.
- Subsequent refresh receipts:
  - Serial warm-up job `20260913-170531-7617f7` was deliberately stopped after demonstrating that
    a cold rebuild would be too slow; it produced 28 additional oleans and was not counted as a
    result.
  - A checked hard-link cache snapshot rebased only trace path metadata; job
    `20260913-170955-1f4ec0` reported 10,511 oleans and zero old-root references. Validation job
    `20260913-171028-ba2964` found zero stale blueprint modules.
  - Full extraction job `20260913-171105-1d3aa1` succeeded in 486.7 seconds with 230 nodes,
    17 destinations, 12,910 indexed declarations, and no problems.
- Focused node receipts:
  - Exact searches found no duplicate; node-add job `20260913-172148-478f98` registered the
    statement and dependencies. Fixture `846757db6fbf903884e2a36af1739c05a40d8476ec10fa06200350a251833d17`
    captures the final import context.
  - The proof gives the extreme part bound 1, normalizes the companion using a chosen-axis history
    maximum at least `k-4`, applies the saturated triangle estimate, and closes the quadratic
    arithmetic for `k >= 6`.
  - Isolated check operation `op-adff1dcee4aa43b6` accepted the proof. Finish operation
    `op-58792b0bfbb04582` passed its candidate and original-source stages; guarded full extraction
    job `20260913-173503-24af21` is currently running.
- Operational note: `harness/config.toml` temporarily names `/home/gavin/.elan/bin/lake` because
  the background service PATH omits Elan. It must be restored to `lake` before committing.
- Commits: none yet.

## One-hour milestone — 2026-09-13T21:55Z

- Closed, fully extracted and audited
  `ctx_extreme_next_cut_of_large_chosen_history_maximum`; local commit `ff3b799`.
  Node-finish operation `op-58792b0bfbb04582` accepted the original source, extracted 231 nodes
  with no problems (peak 7,989 MiB), and audited 248 declarations with no failures or layer
  violations. The commit job returned rc=0 but is journaled as `unknown_execution` solely because
  its declared output receipt was initially omitted; the commit and clean tracked tree were
  verified afterward and the receipt was reconstructed under `runs/sol-12h/`.
- Registered and claimed
  `ctx_extreme_next_cut_of_small_chosen_maxima_capacity_two`. Exact searches found no duplicate.
  The theorem transports source small maxima into the companion, applies the checked
  `3*w-2` small-maxima potential, and proves the exact next quadratic cut budget. Consequently,
  after combining it with the first node, an unresolved extreme case must contain an active
  companion child of chosen-axis capacity at least three.
- Fixture `3dff25d18f397a7c6ac722bdd4861a877d4e4d9f5b02e6cc981ea650e706e96e` and
  isolated check operation `op-c41b49463b834c52` accepted the second proof on its first attempt.
  Full node finishing is next.
- The parent remains claimed and unchanged. No push, publication, external delegation, cloud
  proving, download, purchase, or model change has occurred.

## Tight-layout transition — 2026-09-13T22:31Z

- The second node finished through review, extraction, and audit under operation
  `op-3477e91ea1de4162`: 232 nodes, 12,910 indexed declarations, no extraction problems, and 249
  audited declarations with no failures or layer violations. It is committed locally as
  `34b6bd6` on `node/CtxExtremeNextCutOfSmallChosenMaximaCapacityTwo`; the tracked tree is clean.
- The first registered tightness probe `op-4839733bb1334a9b` / job
  `20260913-181317-cf4ac4` reached its 900-second limit after 205 completed cases and 362 per-case
  timeouts. It found no sum above 12 and eleven sum-12 cases; this is bounded retained-evaluator
  evidence only.
- A focused budget-11 probe `op-3c68012fc0084ecf` / job `20260913-183052-be099f` found a replayable
  sum-12 layout (result artifact
  `b9b0c62985a6ab11f88737813894d1f37e58bb243cfc0ea146b979bc6be19f9e`): `A=1`, `B=11`, source
  chosen maxima `[1,1]`, and four new opposite-side unit markers in `B`. This does not have Lean
  equivalence or refutation credit. It rules out using an across-the-board `A+B <= 11`
  strengthening and redirects the next formal step to the residual active-capacity-three
  structure.

## Capacity-three bridge — 2026-09-13T22:54Z

- Closed `ctx_bound_le_sum_run_group_prunings_of_actual_marker_global_five`. One actual marker on
  an axis with global at most five forces one pure extension at every physical child and hence
  minimum point capacity at most three. The theorem exports that observation through the existing
  arbitrary finite run-constant coloring decomposition, which is the interface needed for
  groupwise residual accounting.
- Isolated accepted proof: fixture
  `38125ed29ad8e5ec5ca8e1be75d40f59b07c73784a3ceedd088f41007a68a14d`, operation
  `op-04465fd858504e71`. Review/finalization operation `op-b83675a0bbf14e9a` rebuilt the original
  source, extracted 233 nodes and 12,910 indexed declarations with no problems (peak 5,407 MiB),
  and audited 250 declarations with no failures or layer violations. Local commit: `34310609`.
- Two preliminary proof checks failed before acceptance: `op-1e3b86094b4d4bb1` exposed an
  under-specified `min` arithmetic step, and `op-72a70dbaf4824d84` correctly rejected reuse of a
  fixture after the source changed. Both diagnostics were inspected; no unknown execution was
  retried.
- The bridge reused the checked capacity-three decomposition and existing marker-extension
  argument. No new Python, workflow helper, or ad hoc evaluator code was introduced; only
  declarative registered-probe JSON was added under the ignored run artifacts, so the user-forbidden
  Astra review was neither needed nor invoked.

## Three-hour milestone — 2026-09-13T23:55Z

- Frontier: 223 closed, 11 open, one claimed parent, one refuted; 236 nodes and 12,910
  declarations were indexed at the latest full extraction. The parent
  `ctx_bound_additive_sandwich_one_singleton_end` remains claimed and unchanged.
- The focused smaller-child budget-12 probe `op-d57cb74ea066484c` / job
  `20260913-185521-e49707` ended at its 300-second limit. It completed 263 count-seven cases,
  incurred 188 per-case timeouts, found no target sum above 12, and reached 12 in ten cases.
  Artifact `f0975a4becc895e05e0af0ff93209137c621dd9e21b9b1beee741cba5f9266b6` explicitly has
  `finite_negative_has_proof_credit=false`; no Lean claim was inferred.
- Closed `ctx_capacity_three_children_exterior_of_two_levels_global_five`: with two actual
  chosen-axis levels and chosen global at most five, every chosen-capacity-at-least-three child
  lies in one common exterior marker region. Isolated check `op-4f0678881e5f44c4`; finish
  `op-337d88db5a0f475e`; extraction 234 nodes/no problems at 5,394 MiB; audit 251/no failures.
  Local commit `b4cdc3f2`.
- Closed `ctx_point_limits_eq_of_child_interval`: cup and cap point limits agree across an
  uninterrupted interval of child positions, by reducing the no-intervening-marker condition to
  the checked axis-region equality theorem. The first isolated proof `op-20fa20e807684bce` failed
  because it referenced a helper not exported by its initial import; repaired check
  `op-a02876c872454e60` passed. Finish `op-dc73e0a19f3d4b9c` extracted 235 nodes/no problems at
  5,398 MiB and audited 252 declarations/no failures. Local commit `4789001b`.
- Closed `ctx_bound_le_sum_chosen_capacity_prunings_of_actual_marker_global_five`: the actual
  marker caps chosen capacities below four, and the interval theorem proves capacity is constant
  on physical child runs, yielding an explicit sum of the four original-history prunings selected
  by capacities 0, 1, 2 and 3. Two isolated checks (`op-21a9e0452ca74bc4`,
  `op-10bd618203984982`) exposed dependent-match elaboration problems; the side-parameterized
  helper repair passed as `op-3b1f682d274a4669`. Finish `op-e82c1d22ce9046bf` extracted 236
  nodes/no problems at 5,537 MiB and audited 253 declarations/no failures. Local commit
  `757593df`; tracked tree clean.
- Quantitative obstruction: in the exact `k=6,m=4,n=1` branch the chosen part costs one, the
  general two-actual-marker companion potential costs 13, and the target is 13, so the companion
  still needs a one-unit improvement to 12. The capacity-two potential costs at most 10 at width
  four; the explicit capacity-three pruning and its common-exterior restriction are now the named
  locus for the remaining saving. Next step: transport the common-exterior conclusion into that
  pruning's own preserved history, then test which checked boundary/rank potential yields the
  strict overlap.
- No new ad hoc Python or workflow code was introduced, so no library promotion was appropriate.
  No delegation, alternate model, Astra invocation, cloud proof, download, purchase, push, or
  publication occurred. All commits are local reviewed commits on one-node branches.
