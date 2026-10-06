# R8: prove external-letter deletion monotonicity for isolated children (one Sol trial, gpt-6.1-sol)

Approved by Gavin on 30 Sept 2026 (the round of research targets after R1/R6). Coordinator:
`claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude). Callbacks are not verified: never wait
for replies; keep `PROGRESS.md` here current. One trial only; never reset the host deadline.

## Why this node matters

R7 (`/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-comb-closedform-20260930/`, see the
journal: `es journal --node ErdosSzekeres.ctx_bound_additive_single_run_alternating --since 2026-09-30`)
found that C3 (`ctx_bound_additive_single_run_alternating`) follows from C1 plus THIS lemma plus closed
nodes. A parallel Sol trial (R9) proves that reduction with this lemma as an explicit hypothesis. Once
this node closes, single-run additivity depends on C1 alone.

## Checkout and scope

- **Worktree:** `runs/worktrees/sol-12h-20260916`, branch `node/CtxBoundExtLetterDeletionMonoOfIsolatedChildren`
  (base: main c53fb41d; full Lake build cache). The node is already registered there (module
  `ESBlueprint/B/CtxBoundExtLetterDeletionMonoOfIsolatedChildren.lean`, statement fixed; do not restate).
- **Harness:** the primary launcher with `--root`:
  `/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916`.
- **Write** only under `runs/r8-sol-20260930/` and in the node module. **Commit** with
  `es node commit ErdosSzekeres.ctx_bound_ext_letter_deletion_mono_of_isolated_children --message-file <file>`:
  in your sandbox it queues a small job that `es worker` runs outside (then `es job wait <id>`).
- **Forbidden:** merging, pushing, touching the primary checkout, editing other statements, a full
  `es extract`, delegating.
- **Compute:** scratch compiles are guarded jobs (`es job run --mem 4G ... -- lake env lean <file>`);
  `es check <node> --targeted` now reserves only ~4-5 GiB for this module. Other jobs share the box.
- **Long computations (new rule, AGENTS.md):** never kill a compile or probe at a time limit you chose
  (no `timeout N`); run it as a job, and when `es job wait` reports `review_due`, read its progress and
  record `es job review <id> --note ...` with your estimate and decision.

## The statement (registered)

```lean
theorem ctx_bound_ext_letter_deletion_mono_of_isolated_children (σ : Ctx.Context) (hwf : σ.WellFormed)
    (hiso : ∀ p ∈ σ.childPositions, p + 1 ∉ σ.childPositions)
    (left right : List Ctx.Letter) (lev : ℕ) (side : Ctx.Side)
    (hword : σ.word = left ++ [Ctx.Letter.ext lev side] ++ right)
    (hother : Ctx.Letter.ext lev side ∈ left ++ right) :
    σ.bound ≤ ({ σ with word := left ++ right } : Ctx.Context).bound
```

## Proof outline (checked on paper by the coordinator; the work is bookkeeping)

Let x = left.length be the deleted position and δ = the context with x deleted.

1. **Replace x by an inert letter.** Let ι be σ with the letter at x replaced by
   `ext (σ.maxima.length + 1) side` (a level outside `levels`, used by no extension or join).
   `ctx_single_level_occurrence_prune_bound_mono` (closed) is exactly this operation for level `lev`
   with `keep` = the other positions of `lev` and witness `w` from `hother` (sideAt unchanged). It gives
   `σ.bound ≤ ι.bound` (and every fuel approximation). `ctx_bound_mono_of_marker_inclusion` (closed) is
   the general form if the packaging does not fit.
2. **Delete the inert letter.** Prove, by induction on fuel, for every context ι with an inert letter
   at x (level > maxima.length), pairwise non-adjacent children, and δ := ι with x deleted WellFormed:
   `boundFuel f ι ≤ boundFuel f δ`.
   - Limits are identical at corresponding child positions (positions > x shift by one): the inert
     letter is never selected by `leftExt`/`rightExt`/`joinExt` (only levels in `levels` are used), and
     relative order of all other letters is unchanged.
   - `childPositions` correspond by the shift; `blocks` correspond; `part` commutes with deleting x
     (the inert letter stays inert in a part: its level and `maxima.length` both grow by one).
   - numRuns ι ≤ 1: then numRuns δ ≤ 1 and the bases are equal.
   - numRuns δ ≥ 2: same cut list; each part value is ≤ by the induction hypothesis (parts keep
     isolated children and stay WellFormed after deletion: `WellFormed.part`).
   - numRuns ι ≥ 2 but numRuns δ ≤ 1 (a merge): only the two children adjacent to x merge, so ι has
     exactly two children and they sit at x−1 and x+1. Its cuts are the singletons; each cut value is
     ≤ the corresponding cut of δ (induction), which is ≤ δ.bound = δ.base by
     `ctx_bound_additive_prefix_suffix` (closed; l = r = 1, both orientations).
3. Combine: σ.bound ≤ ι.bound ≤ δ.bound.

Useful: `ESBlueprint/B/CtxBoundCutLe.lean` (`boundFuel_mono`, `bound_le_boundFuel`, cut lemmas),
`ErdosSzekeres/DecomposableContextLemmas.lean` (`part_letterAt_*`, `WellFormed.part`, `getD_max?` lemmas),
the positional machinery in `ESBlueprint/B/CtxBoundAdditiveSingleRunOfRunContractionAndAlternating.lean`
(R6), `ESBlueprint/B/CtxBoundExternalLetterContraction.lean` (deleting a letter from a word: shifted
positions), `ctx_erase_level_bound_mono`, `ctx_part_limits_le`. Search with `es search` by name.

## Procedure and stop criteria

1. Develop in `runs/r8-sol-20260930/` scratch files compiled by guarded jobs; split step 2 into lemmas.
2. When the module compiles with standard axioms only, `es check <node> --targeted`, then `es node commit`.
- **Closed:** stop and report.
- **Stuck:** two consecutive attempts fail at the same obligation: write the exact missing lemma in
  the handoff and stop. If step 2's merge case needs something false, record the counterexample.
- **Rules:** AGENTS.md applies; `es log` every finding, failure and plan change with job IDs. At the
  end write `MATHEMATICAL-HANDOFF.md` and `REPORT.sol.md` here and release any claim you hold (claim
  the node first).
