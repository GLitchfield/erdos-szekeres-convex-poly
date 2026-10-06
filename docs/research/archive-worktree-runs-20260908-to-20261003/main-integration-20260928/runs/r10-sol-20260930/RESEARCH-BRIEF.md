# R10: prove the bridge from root-form run contraction to parts of single runs (one Sol trial, gpt-6.1-sol)

Approved by Gavin on 30 Sept 2026 (evening round). Coordinator:
`claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude). Callbacks are not verified: never wait
for replies; keep `PROGRESS.md` here current. One trial only; never reset the host deadline. When
the node is closed and committed, say so in PROGRESS.md: the coordinator will review the receipts
and end the run early with `es run finish` (you then get the single finalization turn).

## Why this node matters

Single-run additivity now depends only on C1 (run contraction), and the chain uses C1 only on parts
of single-run contexts. By the closed `ctx_single_run_descendant_bound_normalize` those parts have
the bounds of one-level contexts over a bare root. The coordinator registered the root form as the
conjecture `ctx_bound_child_run_contraction_one_level_root` (C1r, on its own branch). This node is
the bridge: C1 for every part of a well-formed single-run context (C1p) follows from C1r. A parallel
trial (R11) re-proves the two reductions with C1p in place of general C1. Journal:
`es journal --node ErdosSzekeres.ctx_bound_child_run_contraction_of_level_one_span --since 2026-09-30`.

## Checkout and scope

- **Worktree:** `runs/worktrees/main-integration-20260928`, branch
  `node/CtxBoundPartRunContractionOfOneLevelRoot` (base main 15f36571; Lake build cache). The node is
  registered there (module `ESBlueprint/B/CtxBoundPartRunContractionOfOneLevelRoot.lean`; statement
  fixed; C1r is taken as the explicit hypothesis `hroot`).
- **Harness:** `/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/main-integration-20260928`.
- **Write** only under `runs/r10-sol-20260930/` and in the node module. **Commit** with
  `es node commit ErdosSzekeres.ctx_bound_part_run_contraction_of_one_level_root --message-file <file>`
  (from your sandbox it queues a small job for `es worker`; then `es job wait <id>`).
- **Checks:** `es check <node> --targeted` reserves ~4-5 GiB (sized). `es check --async --targeted`
  is also sized now. Scratch compiles: `es job run --mem 4G ... -- lake env lean <file>`.
- **Long computations:** never kill a compile at a time you chose (no `timeout N`); at `review_due`
  read progress and record `es job review <id> --note ...` (AGENTS.md).
- **Forbidden:** merging, pushing, touching the primary checkout, editing other statements, a full
  `es extract`, delegating.

## Statement (registered)

`(hroot : C1r in ∀ form) (σ) (hwf : σ.WellFormed) (hruns : σ.numRuns ≤ 1) (keep) (s) (m) (1 ≤ m)
(m ≤ σ.k - 2) (left right) (hword : (σ.part keep s m).word = left ++ [child, child] ++ right) :
(σ.part keep s m).bound = ({ σ.part keep s m with word := left ++ [child] ++ right }).bound`.

## Proof outline (checked on paper by the coordinator)

Let π = σ.part keep s m, π' = π with one child of the doubled pair removed.
1. π' is itself `σ'.part keep' s m` for σ' = σ without that child (a kept child): σ' is WellFormed
   and single-run (deleting one child from a contiguous run). Word equality by positions (R6/R9 have
   this bookkeeping: `ESBlueprint/B/CtxBoundAdditiveSingleRunAlternatingOfRunContractionAndDeletion.lean`).
2. Apply `ctx_single_run_descendant_bound_normalize` (closed) to (σ, π) and to (σ', π') with D = 1:
   bound π = bound τ, bound π' = bound τ', where τ = {a := σ.capLimit b b + 1, u := σ.cupLimit b b + 1,
   k, word := π.word, maxima := [m]} and similarly τ' with σ'. The capacities agree: all children of
   a single run have equal point limits (`ctx_point_limits_eq_of_child_interval`; R3 reused it), and
   σ' has the same outside letters.
3. In τ the older letters (levels >= 2) are inert (level > maxima.length = 1) and lie outside σ's run,
   hence outside the span of π's children and never between two children. Delete them: the bound is
   unchanged (limits ignore inert letters; runs, blocks and parts are unchanged up to a uniform
   shift). R8 proved an inert-deletion transport by fuel induction in
   `ESBlueprint/B/CtxBoundExtLetterDeletionMonoOfIsolatedChildren.lean`; here no merge can occur.
   The remaining word consists of children and `ext 1 s` letters only (the removed children of σ).
4. Apply `hroot` with a = capLimit+1, u = cupLimit+1 (both in [1, k]: the limits are at most k-1),
   3 <= k (from 1 <= m <= k-2), and the side s.

Useful closed nodes: `ctx_single_run_descendant_bound_normalize`, `ctx_single_run_descendant_limits_normalize`,
`ctx_point_limits_eq_of_child_interval`, `ctx_base_child_letter_contraction`, R8's module (inert
transport), R6/R9 modules (deletion/part word bookkeeping). Search with `es search`.

## Procedure and stop criteria

1. Develop in `runs/r10-sol-20260930/` scratch files compiled by guarded jobs.
2. `es check <node> --targeted`, then `es node commit`; note it in PROGRESS.md.
- **Closed:** stop and report. **Stuck:** two consecutive attempts fail at the same obligation: write
  the exact missing lemma in the handoff and stop. If a step is false, record the counterexample.
- **Rules:** AGENTS.md; `es log` every finding with job IDs; at the end `MATHEMATICAL-HANDOFF.md` and
  `REPORT.sol.md` here; claim the node first and release it at the end.
