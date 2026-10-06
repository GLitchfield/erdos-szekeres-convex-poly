# Main integration, 2026-09-28

The user authorized integrating and pushing the accumulated committed work.
The primary checkout's `ESBlueprint.lean` edit and untracked
`harness/dataset/ctx_end_cut_normal_form/` were not touched. The active Sol
worktree's uncommitted partial proof was not committed or copied.

Starting `main` and `origin/main`: `ebe39571` (2026-09-08).
Integrated target branch `node/CtxTwoActualMarkerSmallHistoryInternalChosenKeptCutSixBound`
at `322f1c38` (458 commits ahead of old main) and the remaining unique
committed tips: older-exterior small-opposite bound `39322566`, approved
uniform separator statement `f48696c3`, approved three-block statement
`b11406cf`, insertion regression example `c07fbf92`, and harness automation
`dca5dfb4`. Merge conflicts only affected the aggregate imports in
`ESBlueprint.lean` and adjacent approved lock entries in
`harness/statements.lock`; both entries and their original type hashes were
retained. Full extraction refreshed `harness/nodes.json` and
`harness/status.md` in commit `a0ff614f`.

Verification:

- `es layers`: passed, 325 Blueprint modules, 9,857 certificate modules,
  336 core modules, 33 encodings.
- Full harness tests: job `20260928-133504-d2d542`, 254 passed, 1 skipped.
  Earlier job `20260928-133417-375f37` had four setup failures because the
  research extra (`numpy`) was omitted; the corrected job passed.
- Isolated cache copy: job `20260928-133741-2f6d38`, complete; `es doctor`
  then found 9,857/9,857 certificate and 319/319 core root-closure oleans.
- Guarded Blueprint build: job `20260928-134428-3a9b7e` compiled 84 module
  groups but its final root reservation was refused because the root requested
  30 GiB above the enclosing 20 GiB cap. With a temporary integration-only
  28 GiB final cap, job `20260928-135514-48a120` passed; build log
  `build-20260928-135516-blueprint.log` says 9,960 jobs completed
  successfully. The tracked cap was restored before commit.
- Full extraction: job `20260928-135602-80ce58`, complete, 15,667 modules,
  324 nodes, 17 destinations, 12,910 indexed declarations, peak 27,554 MiB.
  `es status` reports the new frontier without a stale-index warning.
- `es audit --changed`: 299 declarations audited, zero failures; immutable
  artifact `b9a9c7a44cc00e1290c79bf4279a9ecf4be8b1ad28851418727cb198a295e70e`.
- Focused generated-metadata tests: 13 passed. `git diff --check` passed.

Trust limit: `ctx_bound_additive_three_blocks` and
`ctx_bound_uniform_separator_contraction` are registered open conjectures and
retain `sorryAx`. The active chosen-kept target also retains `sorryAx` in this
commit. The checked small-opposite theorem
`ctx_two_marker_older_exterior_internal_interval_cut_eight_bound_of_opposite_global_le_four`
has type hash `9c669577d23b4b44`, `sorry: False`, and only standard axioms.

At the time of the first push, all committed local and remote branch tips were
reachable from `a0ff614f`. The push to `origin/main` was a regular, non-force
update from `ebe39571` to `a0ff614f`. Hosted CI run
https://github.com/GLitchfield/erdos-szekeres-convex-poly/actions/runs/36462868296
failed in three Lake-dependent fixture tests because that runner has no `lake`
binary: 251 passed, 1 skipped, 3 failed. The failure was recorded in the
shared journal before repair. Commit `5cc60537` adds a `shutil.which("lake")`
skip condition to those three tests. Local verification with Lake present gave
3 passed; with Lake absent, 3 skipped, and the complete hosted-style suite gave
251 passed, 4 skipped. A second regular push advanced `origin/main`, local
`main`, and this clean integration worktree to `5cc60537`. Hosted CI run
https://github.com/GLitchfield/erdos-szekeres-convex-poly/actions/runs/36463468909
completed successfully: both `harness-tests` and `layers` passed.

The twelve-hour Sol trial is separate, active in
`runs/worktrees/sol-12h-20260916` under job `20260928-132926-6df35b`.
Its fixed research deadline is `2026-09-29T05:31:24.146129Z` and finalization
deadline is `2026-09-29T06:01:24.146129Z`. Any accepted result from that
trial requires its own Lean receipts and a later main update.
