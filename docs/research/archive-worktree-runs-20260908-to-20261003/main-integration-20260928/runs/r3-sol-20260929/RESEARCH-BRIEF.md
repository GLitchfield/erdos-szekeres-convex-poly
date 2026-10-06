# R3: k=6 inheritance gate, then reflection invariance — one Sol trial (gpt-6.1-sol)

Approved by Gavin on 29 Sept 2026 as round R3 of
`/home/gavin/git/erdos-szekeres-convex-poly/runs/next-round-proposal-20260929/PROPOSAL.md` §4.
- Coordinator: `claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude).
- Callbacks to the coordinator are not verified. Never wait for a reply; keep `PROGRESS.md` here
  current.
- This is one trial. Never start a second. The host fixes the deadline; never reset it.

## Checkout and scope

- **Worktree:** `runs/worktrees/main-integration-20260928` on branch `node/CtxBoundReverse`, base
  `5d58845b` (main). It has a full Lake build cache.
- **Harness commands:** use the primary launcher with `--root` for this worktree:
  `/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/main-integration-20260928`.
- **Where to write:** only under `runs/r3-sol-20260929/` here, plus the reflection node module and
  its falsifier once registered. Commit to this branch only.
- **Forbidden:**
  - merging, pushing, rebasing main, or touching the primary checkout;
  - editing any other statement, or running a full `es extract`;
  - delegating.
- **Shared machine:**
  - A Claude run (R1) and a Sol harness run (R5, ends about 01:40Z) share it.
  - The N27 solver job `20260929-154930-35aca9` holds 8 GiB until 07:00Z. Leave it alone.
  - Probe jobs ≤ 4 GiB. Scratch Lean compiles as guarded jobs ≤ 4 GiB.

## Part A — the stop/go gate for the k=6 chain (at most 3 hours, diagnostic only)

**Target.** `ErdosSzekeres.ctx_two_actual_marker_small_history_internal_chosen_kept_cut_six_bound`.
- 12-hour trials on this node are paused (journal, 29 Sept). This gate decides whether the chain
  continues.
- Claim it: `es claim … --why "R3 gate: is the missing one-unit saving inheritable under cuts?"`.
- Release it at the end of Part A with the gate verdict.

**Background.**
- `runs/worktrees/sol-12h-20260916/runs/older-exterior-sol-12h-20260928/MATHEMATICAL-HANDOFF.md`,
  with `ASTRA-REVIEW.md` beside it.
- The source, with its two admissions at lines 3605 and 4024:
  `ESBlueprint/B/CtxTwoActualMarkerSmallHistoryInternalChosenKeptCutSixBound.lean` (main, 21cdd7ad).
- The evaluator driver `diagnose_middle_cuts.py` in the same run directory.

**Question.** Is the missing one-unit saving inheritable? Find a predicate π on contexts, built from
marker geometry and capacities, and a checked independent-charge potential Ψ such that:
- (i) π(σ) ⇒ bound σ ≤ Ψ(σ) − 1; and
- (ii) for every interval cut of a π-context, either the parts' independent charges already total
  at most Ψ − 1, or one part satisfies π with its own Ψ and the other part's charge makes up the
  rest.

Test it exhaustively on the finite families behind the two admissions at k = 6, and on the
analogous family at k = 7.

**Evaluator.** The compiled one is about 50× faster. It is on unmerged branch
`harness/fixes-20260929`, at `runs/worktrees/harness-fixes-20260929/harness/research/context_bound.py`,
`compiled_evaluator(a,u,k)`, semantics `context-bound-zero-children-c-v1`. Load it by file path, as
`runs/claude-comb-reduction-20260929/p1_multirun_usc.py` in the primary checkout does. Cross-check
a sample against the Python evaluator.

**Verdict.**
- **Fail** (no small-feature π satisfies (ii) at k = 6, or it fails at k = 7):
  - write the parking handoff `runs/r3-sol-20260929/K6-GATE.md`;
  - release the claim `blocked`, with the reason.
- **Pass:**
  - write the general statement of the inherited-saving lemma in `K6-GATE.md`;
  - do not register it: the coordinator reviews it first.
  - Then continue to Part B.

## Part B — reflection invariance (the rest of the trial)

**Statement.** Proposed name `ctx_bound_reverse`. Reversing a well-formed context's word, with
parameters, levels, sides and maxima unchanged, preserves the bound:
```lean
theorem ctx_bound_reverse (σ : Ctx.Context) (hwf : σ.WellFormed) :
    ({ σ with word := σ.word.reverse } : Ctx.Context).bound = σ.bound
```

**Why.**
- The sandwich parent needs it; no node exists. The plan in
  `runs/2026-09-08-lemma-pilot/reflection-recursion-plan.md` (primary checkout) was never carried
  out.
- It halves case analysis in every route.
- Evidence: 90/90 random contexts agree
  (`runs/next-round-proposal-20260929/spotcheck_reversal.py` in the primary checkout).

**Things to check in the definitions (`ErdosSzekeres/DecomposableContext.lean`).**
- `base` reads only the first child's limits. For a single run, all children share limits because
  no external letter lies inside the run, so the reversal is fine there. Prove that as a lemma.
- `sideAt` uses the first letter of a level. It is reversal-invariant only under `WellFormed`'s
  one-side-per-level clause.
- `leftExt` and `rightExt` swap under reversal.
- `blocks` map to reversed blocks, and `part` commutes with reversal.
- Induct on fuel, as `ctx_bound_le_merge_same_side_levels` does
  (`ESBlueprint/B/CtxBoundLeMergeSameSideLevels.lean`). That file is a template for fold and
  extension transport.

**Procedure.**
1. Run `es search` first and record the result.
2. Develop the proof in a scratch file under `runs/r3-sol-20260929/`, compiled by guarded jobs of
   ≤ 4 GiB with `lake env lean` against this worktree's build.
3. Register with `es node add --targeted --ws B --kind formalization --import
   ErdosSzekeres.DecomposableContext --consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end`.
   - `es node add` reserves 20 GiB. That cannot fit until R5's host ends (about 01:40Z).
   - The coordinator also needs one 20 GiB slot for its own node after that. If refused, retry
     every 20 minutes rather than waiting idle.
4. Then prove it in the module, and run `es check <node> --targeted`.
5. When it closes with standard axioms only, commit on this branch. Do not merge.

**Stop criteria.**
- **Closed:** stop, commit, write the report.
- **Stuck:** after two consecutive attempts that fail at the same obligation, write the exact
  missing lemma in the handoff and stop.

## Rules

- `AGENTS.md` applies.
- `es log` every finding, failure and plan change, with job IDs, before the next attempt.
- `es lib search` before writing Python.
- At the deadline, or on a stop criterion:
  - write `MATHEMATICAL-HANDOFF.md` and `REPORT.sol.md` here;
  - release every claim you hold with the right outcome and the handoff path.
