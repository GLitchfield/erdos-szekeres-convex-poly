# Cutover runbook: incremental index, then the three node branches (prepared 28 Sept, updated 29 Sept)

**Done 29 Sept, and pushed (origin/main `21cdd7ad..5d58845b`).** Deviations from the plan below:
- The node branches were rebuilt in the primary checkout (`checkout -B node/<X> main`, files
  copied from the worktrees), not by stash and rebase, so every `es check --targeted` reused the
  primary checkout's full build.
- One extra harness commit (`13a54afb`) makes a full extraction fingerprint the sources before
  it runs the extractor.
- After verification, the five Claude worktrees were removed. Codex's review artifacts moved
  to `runs/reviews/incremental-index-20260929/`.
- Commits: bootstrap `b76736c3`; refutation `0679da68`; four_le `afd0a1d7`; merge `03d7d4ac`;
  allowlist `5d58845b`.
- Still to do by hand: restart the `es worker` (pid 15389) from a terminal.

Codex's Sol run `older-exterior-sol-12h-20260928` has ended; its result is main `21cdd7ad`.
Do this once the harness branch's review fixes (commit `5c0a9a51`, 29 Sept) are accepted.
Every git command uses the repo form
`G="git -c gc.auto=0 -c maintenance.auto=false --git-dir=.git-data --work-tree=."`.

## 0. Preconditions

- `tools/es/bin/es job list --status running` shows no running jobs, and nothing is queued.
- Codex has no claim or worktree mid-commit that would race main:
  `tools/es/bin/es status --brief`, `es journal --since 2h`.
- main is still `21cdd7ad`, the base of `harness/incremental-index`. If it moved, rebase the
  branch onto it and rerun the harness tests first.

## 1. Land the harness branch

    $G checkout main            # in the primary checkout; see step 2 first
    $G merge --ff-only harness/incremental-index   # daba3fd0, 2ff506c1, 5c0a9a51

## 2. Put the primary checkout on main

The primary checkout is on `harness/automation-20260912` (already merged into main) and carries:
- an uncommitted one-line edit to `ESBlueprint.lean`, adding
  `import ESBlueprint.B.CtxActualMarkerQuadraticPenultimateCutBound`. main already has that line,
  so discarding the edit loses nothing;
- an untracked `harness/dataset/ctx_end_cut_normal_form/` from 7 Sept (falsifier outputs; leave it).

Commands:

    $G checkout -- ESBlueprint.lean
    $G checkout main && $G merge --ff-only harness/incremental-index

Then restart the job worker so it runs the new code (reservations, OOM accounting).
- The running worker (pid 15389 on 28 Sept) was started by hand from a terminal. Stop it with
  `kill <pid>` once `es job list --status running` is empty.
- Start `tools/es/bin/es worker` again from a terminal (or install a user service for it).
- Re-install the nightly unit so it runs the real backstop (`--check --no-cache`):
  `tools/es/systemd/install.sh`.

## 3. Bootstrap the fingerprinted index (one full extraction)

    tools/es/bin/es build blueprint --budget 180   # restores main's ~320 blueprint modules from the cache
    tools/es/bin/es extract                        # full, <= 28 GiB; writes fingerprints
    tools/es/bin/es extract --check                # must pass without Lean ("mode": fingerprint)
    $G add harness/nodes.json harness/status.md harness/index.json
    $G commit -m "Bootstrap fingerprinted index"   # hook: layers, extract --check --changed, audit

The final build step asks for the 30 GiB final cap, so no other job may be running. Check that
`nodes.json` now has `"extract_mode": "full"`, a `blueprint_axioms` block and a `fingerprints`
block.
- The full extraction also records an attestation in the shared database
  (`.es/erdos-szekeres/es.db`, used by every worktree). The no-Lean check and
  `es check --targeted` trust only attested index content.
- So if `es extract --check` in step 3 does not report `"mode": "fingerprint"`, look for a
  hand-edited or textually merged `nodes.json`: rerun `es extract`, do not edit the file.

## 4. The three node branches, one at a time

For each worktree, in this order:
1. `runs/worktrees/claude-endcut-refutation` (`node/CtxBoundAttainedByEndCutCounterexample`)
2. `runs/worktrees/claude-endcut-four` (`node/CtxBoundAttainedByEndCutOfFourLe`)
3. `runs/worktrees/claude-merge-levels` (`node/CtxBoundLeMergeSameSideLevels`)

Commands:

    cd runs/worktrees/<wt>
    $G stash push -u -m "<wt>-wip"      # or commit WIP; see the stash caution in CLAUDE.md
    $G rebase main
    $G stash apply <sha>                # conflicts: ESBlueprint.lean and statements.lock only.
                                        # Keep BOTH sides' import lines and lock entries
                                        # (the lock is sorted JSON)
    tools/es/bin/es check <node> --targeted     # re-extracts this node and updates nodes.json/status.md
    $G add -A ESBlueprint.lean ESBlueprint/B/<Module>.lean harness/statements.lock \
        harness/nodes.json harness/status.md harness/index.json <falsifier and falsify files>
    $G commit -m "<node>: ..."          # hook passes by fingerprints (no Lean)
    cd ../../.. && $G merge --ff-only node/<Branch>

Files per branch:
- **refutation:** the module; `harness/falsifiers/ctx_end_cut_normal_form.py` (runs a=3 first);
  `harness/falsify/ErdosSzekeres.ctx_bound_attained_by_end_cut.json` (result `counterexample`).
  The conjecture then shows `refuted`.
- **four:** the module; `harness/falsifiers/ctx_end_cut_normal_form_four.py`;
  `harness/falsify/ErdosSzekeres.ctx_bound_attained_by_end_cut_of_four_le.json` (`pass`).
- **merge:** the module only (expect `closed`, type hash `3db6cc13c593f0b0`).

Do not commit `harness/dataset/ctx_end_cut_normal_form/` (regenerable falsifier output, never
tracked).

Last, the allowlist branch `harness/allowlist-fin4-native-decide` (worktree
`runs/worktrees/claude-allowlist`, Gavin approved option 1 on 28 Sept). It changes only
`harness/allowlist.json`: one exact entry for the `native_decide` auxiliary axiom of
`CommonAnchorFin4State.fin4_permutation_reorder_table`, reaching that theorem and its wrapper
`reorderedOneChange`. `es audit` passes with it (341 declarations, 0 failures). Rebase onto
main, commit (the hook re-renders the index with the new allowlist, without Lean), then
fast-forward main. No Lean rebuild is needed.

## 5. Verify and publish

    tools/es/bin/es extract --check        # fingerprint mode, no problems
    tools/es/bin/es status                 # refutation closed; end_cut refuted; four_le open+ready; merge closed
    tools/es/bin/es audit

Pushing main (and the node branches) to origin is outward-facing: ask Gavin first. Codex's Sol
branch(es) from the 28 Sept run are integrated separately, by Codex or in the same way.

## Rollback

- The harness change is three commits: `$G revert 5c0a9a51 2ff506c1 daba3fd0` restores the old
  behaviour.
- The old `es extract --check` compares whole files, so it reports the fingerprinted index as
  stale (extra `fingerprints` and `blueprint_axioms` blocks). After a revert, run one full
  `es extract` and commit the result.
