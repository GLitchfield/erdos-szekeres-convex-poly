# R12: compose three special-case nodes from the single-run chain (one Sol trial, gpt-6.1-sol)

Approved by Gavin on 30 Sept 2026 (evening round, item 3: "make the open list honest"). Coordinator:
`claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude). Callbacks are not verified: never wait
for replies; keep `PROGRESS.md` here current. One trial, three nodes in order; never reset the host
deadline. When all three are closed-modulo-their-dependency and committed, say so in PROGRESS.md: the
coordinator reviews and ends the run early with `es run finish`.

## Why

Three open B conjectures are special cases of results that now depend only on the root form of run
contraction (`ctx_bound_child_run_contraction_one_level_root`, C1r):
1. `ctx_bound_additive_sandwich_one_singleton_end` and 2. `ctx_bound_additive_three_blocks` are
   single-run additivity for particular keep sets, i.e. instances of `ctx_bound_additive_single_run`;
3. `ctx_bound_uniform_separator_contraction` is run contraction on a part of a single-run context:
   turning its level-1 separator letters into children (and lowering the older levels by one) gives a
   single-run context of which it is a part, so it follows from
   `ctx_bound_part_run_contraction_of_one_level_root` (the bridge, closed) applied to C1r.
Each gets a real proof term in place of `sorry` (statement unchanged), so `es status` shows it as
blocked by its true dependency instead of as an independent open conjecture.

## Checkout and scope

- **Worktree:** `runs/worktrees/main-integration-20260928` (Lake build cache; base main f55e3b92).
  One branch per node, each created from main by you:
  `node/CtxBoundAdditiveSandwichOneSingletonEnd`, `node/CtxBoundAdditiveThreeBlocks`,
  `node/CtxBoundUniformSeparatorContraction` (`git -c gc.auto=0 -c maintenance.auto=false checkout -b <branch> main`;
  if a branch name already exists and is merged into main, fast-forward it instead).
- **Edit only the proof** of each node module (never the statement line; add imports as needed).
  The three modules are imported by nothing, so a targeted check updates the index incrementally.
- **Harness:** `/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/main-integration-20260928`.
  Before a targeted check, build any imported module without an olean in this worktree with a
  small guarded job (`es job run --mem 4G ... -- lake build <Module>`), otherwise the sized cap falls
  back to 20G. Only one Lean build runs at a time project-wide: a refusal saying "concurrency
  reservation is occupied" means wait, not fail.
- **Commit** each with `es node commit <node> --message-file <file>` on its branch.
- **Never kill a job at a self-chosen time**; at `review_due` record `es job review` (AGENTS.md).
- **Forbidden:** merging, pushing, touching the primary checkout, editing statements, a full
  `es extract`, delegating.

## Outlines

1. **Sandwich, one singleton end.** Apply `ctx_bound_additive_single_run` with
   keep = `List.range' b l ++ List.range' (b + l + m) r`: `hkeep` from `hpos`; `hne` from `0 < l`;
   `hall` since `l + r < l + m + r`; `σ.numRuns ≤ 1` from `σ.childPositions = List.range' b n`
   (R6's `hInterval` has the converse direction; a contiguous child interval has one run). The
   complement `σ.childPositions.filter (· ∉ keep)` equals `List.range' (b + l) m` (list lemma), and
   `part` depends on `keep` only through membership, so the parts agree. Both orientations.
2. **Three blocks.** The same with arbitrary l, m, r > 0.
3. **Uniform separator.** Let σ̂ be σ with its level-1 letters (the separator block) turned into
   children and every older level lowered by one, with maxima `σ.maxima.tail`; σ̂ is WellFormed and
   single-run (houter: every outer letter has level >= 2), and σ = `σ̂.part keep side m` with keep = the
   children of σ and m = `σ.maximumAt 1` (check `1 <= m <= k-2` from WellFormed). Contract the two
   runs one letter at a time, each step by the bridge applied to C1r (the theorem
   `ctx_bound_child_run_contraction_one_level_root`), re-expressing the contracted context as a part
   of σ̂ minus the removed child each time (the representation R11 used). Induct on r - 1 + t - 1.

## Procedure and stop criteria

- For each node: scratch development in `runs/r12-sol-20260930/`, `es check <node> --targeted`
  (expect sorry only through the dependency: `sorry=True` with `sorryAx` from single_run or C1r, and
  no other axiom), `es node commit`, note it in PROGRESS.md.
- **Done:** all three committed. **Stuck:** two consecutive attempts fail at the same obligation: write
  the exact missing lemma in the handoff and stop (say which nodes are committed).
- **Rules:** AGENTS.md; `es log` findings with job IDs; at the end `MATHEMATICAL-HANDOFF.md` and
  `REPORT.sol.md` here. These nodes are blocked in the index, so `es claim` may refuse: log instead.
