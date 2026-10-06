# Harness and evidence fixes: one fixed 6-hour Sol trial (R5)

Approved by Gavin on 29 Sept 2026 as round R5 of
`/home/gavin/git/erdos-szekeres-convex-poly/runs/next-round-proposal-20260929/PROPOSAL.md`
(§3.2 lists the defects with evidence). Coordinator:
`claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude). Callbacks to the coordinator are not
verified: do not wait for replies; keep `PROGRESS.md` current.

## Checkout and scope

- Work only in this worktree: `runs/worktrees/harness-fixes-20260929`, branch
  `harness/fixes-20260929`, base `5d58845b` (main).
- Commit to this branch as you go (one commit per fix, message says what and why). **Do not**
  merge into main, push, rebase main, touch the primary checkout, restart or signal the
  running `es worker` (pid 586987), run a full `es extract`, or build Lean. The coordinator
  reviews and lands the branch after the trial.
- Two research runs share the machine (a Sol run on Workstream C and a Claude run on
  Workstream B). Keep your jobs at ≤ 2 GiB each; never more than 4 GiB at once.
- Run harness commands (`claim`, `log`, `job run`, `release`) with the **primary** launcher,
  `/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/harness-fixes-20260929`,
  never with this worktree's `tools/es/bin/es`: the worktree has no venv, so its launcher would run the
  code you are editing against the shared state database. Exercise your edited code only through tests.
- No node claim is needed (no ESBlueprint node); `es log` without `--node`.
- Tests: `es job run --mem 2G --why "..." --out runs/harness-fixes-20260929/tests -- env PYTHONPATH=tools/es /home/gavin/git/erdos-szekeres-convex-poly/tools/es/.venv/bin/python -m pytest -q tools/es/tests`
  from this worktree. The suite must pass (272 passed, 1 skipped on 29 Sept) after each fix,
  with new tests for each behaviour change. Tests that need Lake keep their skip guards.

## Fixes, in priority order

1. **One worker only.** `es worker` must refuse to start when another live worker holds the
   project's lock (flock or pidfile under the `.es` state dir; stale lock after process death
   must not block). On 29 Sept two workers ran (a suspended pre-cutover one and a new one).
2. **Opened dates** (`tools/es/es/nodes.py:403-425`, used by `commands/extract.py:142`).
   - Replace per-module `git log --diff-filter=A --follow` (0.81 s mean per module, ~66–83 s per
     extract) by one history pass over the blueprint and core directories with rename detection.
     `git log -M --name-status --diff-filter=AR` over `ESBlueprint` takes 0.045 s.
   - It must see files introduced by merge commits: `ESBlueprint/B/CtxBoundAdditiveThreeBlocksOfUniformContraction.lean`
     arrived in merge `08424522` and currently shows `opened: uncommitted` forever
     (use `-m`/`--first-parent` or equivalent; test it with a fixture repo containing a merge).
   - Cache committed dates in the index; at every extract, including `--incremental`, recompute
     only entries that are missing or `uncommitted`. `CtxSandwichMiddleBlockContraction.lean`
     (added in `9fa75e98`) is a second stale example.
3. **`es ready` and `es status` metrics.**
   - `ready` must treat a node as blocked when any node in its `deps_actual` (not only
     `deps_declared`) is open or sorry-bearing. Today `decomposableStateUpper_all` is listed
     ready although its actual dependency `ctx_card_le_bound` is blocked.
   - `status` gains a root-cone section: for each destination and each open node with no
     consumer, the number of closed and open nodes in its Lean dependency cone
     (`deps_actual ∪ deps_declared` restricted to indexed nodes). On 29 Sept only 2 of 309 closed
     B nodes were in `decomposableStateUpper_all`'s cone; this number must be visible.
   - `burn_down` (`commands/status.py:77`) counts only `closed` events from `es close`; it shows 0
     closures for W37–W40 while 273 claims were released `closed`. Count node closures from
     releases with outcome `closed` and from index status transitions, without double counting.
4. **OOM accounting.** Jobs 20260928-164854-ee2880 and 20260928-165115-2e5eff were OOM-killed
   (systemd logged `oom-kill`) but recorded rc −15, peak 0, oom_kills 0: the in-scope stats writer
   dies with the scope. Take the kill and peak from the scope unit after it stops (e.g.
   `systemctl --user show` Result/MemoryPeak, or the journal for the unit), with a test that
   simulates the missing stats file.
5. **Evidence durability.**
   - `es log --attach FILE` (repeatable): copy the file into the shared artifact store and record
     its artifact ID in the log entry, so findings survive when a caller cannot write report
     files (Claude subagents were blocked from writing FINDINGS.md on 28 Sept).
   - `es release` with a note that cites `runs/...` paths: when the caller's checkout is a
     worktree, copy each cited file that exists there into the primary checkout's same `runs/`
     path (never overwrite a different file; report conflicts). The 28 Sept Sol handoff exists
     only under `runs/worktrees/sol-12h-20260916/runs/...`.
6. **Compiled context-bound evaluator (if time remains).** A C implementation of
   `Ctx.Context.bound` with the `context-bound-zero-children-v1` semantics of
   `harness/research/recursive.py`, memoized, exposed through the existing evaluator interface
   behind an explicit semantics name. Regression fixture: agreement with the Python evaluator on
   a few thousand random contexts at (4,4,5), (4,5,6), (5,5,6), and on the end-cut
   counterexample `[1L,S,S,2U,S,S]` maxima (3,1) at (3,4,5) (bound 1). Register it in
   `harness/research/catalog.json` with a runnable example. `tools/decomp_enum/enum_avoid.c` shows
   the build conventions. Stop at a working, tested prototype; do not change existing callers.

## Rules

- `AGENTS.md` applies. `es lib search` before writing new workflow code.
- `es log` each fix, each meaningful failure and each plan change, with commit and job IDs.
- At the deadline: finish the current fix or revert it, make sure the branch is committed and the
  suite passes, then write `REPORT.sol.md` here: commits in order, tests run (job IDs), what was
  left undone and why, and anything the reviewer must check before merging (behaviour changes,
  migration of existing `nodes.json` fields, worker restart needed).

## Coordinator addendum (Claude, ~20:05Z): review findings to fix before your deadline if time allows

The full review is at `/home/gavin/git/erdos-szekeres-convex-poly/runs/harness-fixes-20260929/COORDINATOR-REVIEW.md`.
In priority order, each with a test:
1. `es release` must not stay blocked on an evidence-copy conflict (`claims.py:129-133`).
   Publish under a content-suffixed name and report it.
2. Normalise absolute and `runs/worktrees/<wt>/runs/...` citations before copying
   (`claims.py:47,93`).
3. OOM detection must match only systemd's OOM result lines, not any `oom-kill` substring
   (`build.py:315-318,365`).
4. `es log --attach`: add a size cap, and resolve relative paths against the current directory
   (`log.py:83-86`).
5. Remove the `runs/` files from the branch history. Rewrite only your own commit 360f063f, e.g.
   with an interactive-free `git rebase --onto`, or add a commit that `git rm --cached`s them.
   Keep the files on disk.
Do not merge, push or touch the primary checkout.
