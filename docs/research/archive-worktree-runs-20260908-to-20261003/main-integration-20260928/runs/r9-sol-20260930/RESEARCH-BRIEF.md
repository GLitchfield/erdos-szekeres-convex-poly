# R9: prove C3 from C1 and deletion monotonicity (one Sol trial, gpt-6.1-sol)

Approved by Gavin on 30 Sept 2026 (research targets after R1/R6). Coordinator:
`claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude). Callbacks are not verified: never wait
for replies; keep `PROGRESS.md` here current. One trial only; never reset the host deadline.

## Why this node matters

`ctx_bound_additive_single_run` already follows in Lean from C1 and C3 (R6's glue, closed). R7
(`/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-comb-closedform-20260930/`; journal:
`es journal --node ErdosSzekeres.ctx_bound_additive_single_run_alternating --since 2026-09-30`)
reduced C3 to C1 plus external-letter deletion monotonicity for isolated children (DelMono, node
`ctx_bound_ext_letter_deletion_mono_of_isolated_children`, being proved in parallel by R8). This trial
proves the reduction with both as explicit hypotheses, exactly like R6's glue.

## Checkout and scope

- **Worktree:** `runs/worktrees/main-integration-20260928`, branch
  `node/CtxBoundAdditiveSingleRunAlternatingOfRunContractionAndDeletion` (base main c53fb41d; full Lake
  build cache). The node is registered there (module
  `ESBlueprint/B/CtxBoundAdditiveSingleRunAlternatingOfRunContractionAndDeletion.lean`; statement fixed).
- **Harness:** `/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/main-integration-20260928`.
- **Write** only under `runs/r9-sol-20260930/` and in the node module. **Commit** with
  `es node commit ErdosSzekeres.ctx_bound_additive_single_run_alternating_of_run_contraction_and_deletion --message-file <file>`
  (queued for `es worker` from your sandbox; then `es job wait <id>`).
- **Forbidden:** merging, pushing, touching the primary checkout, editing other statements, a full
  `es extract`, delegating.
- **Compute:** scratch compiles as guarded jobs (`es job run --mem 4G ... -- lake env lean <file>`);
  `es check <node> --targeted` reserves ~4-5 GiB. Never kill a job at a self-chosen time (no `timeout N`);
  at `review_due` read its progress and record `es job review <id> --note ...` (AGENTS.md).

## The statement (registered)

Hypotheses `hcontract` (C1, verbatim the glue's) and `hdel` (the DelMono node's statement, quantified
over τ); conclusion exactly `ctx_bound_additive_single_run_alternating`'s: for σ WellFormed, numRuns ≤ 1,
2 ≤ n = childPositions.length, r < 2, 1 ≤ d ≤ k−2, with
`keep := ((List.range n).filter (· % 2 = r)).map (σ.childPositions.getD · 0)`, both orientations.

## Proof outline (checked on paper by the coordinator)

Strong induction on n. σ is one contiguous run: `childPositions = List.range' b n` (R6's `hInterval`).
Write c_i = b + i.

1. **n = 2.** keep is `[c0]` (r = 0) or `[c1]` (r = 1): `ctx_bound_additive_prefix_suffix` with l = r = 1
   (for r = 1 swap the conjuncts).
2. **n = 3.** keep is `[c0, c2]` (r = 0) or `[c1]` (r = 1):
   `ctx_bound_additive_sandwich_singleton_ends` with m = 1 (for r = 1 swap the conjuncts).
3. **n ≥ 4: delete c1 and c2.** Let σ'' be σ with the letters at c1 and c2 removed (a single run of n−2
   children, same outside letters); its alternating keep with the same r is exactly the old keep minus
   {c1, c2}, positions shifted by two above c2.
   - **K part** (the part keeping keep): for r = 0, c1 is a separator (`ext 1 s`) between teeth c0 and
     c2; for r = 1, c2 is a separator between teeth c1 and c3.
     1. Delete that separator with `hdel`. The part is WellFormed (`WellFormed.part`); its children are
        pairwise non-adjacent (alternating keep in a run); the level keeps a letter (another separator
        exists since n ≥ 4).
     2. The two teeth are now adjacent: contract one with `hcontract`. Every letter strictly inside the
        child span of the part is a child or `ext 1 s`, because σ's run is contiguous.
     3. The result is `σ''.part keep'' s m` (word equality; the same maxima).
   - **Complement part:** symmetric. The deleted K letter is the separator between two complement
     teeth; delete it, then contract the doubled tooth. The two deleted positions are again {c1, c2}.
   - Hence each orientation's pair value for σ is ≤ that for σ''. By induction that is ≤ σ''.bound
     = σ''.base = σ.base = σ.bound: numRuns ≤ 1 gives bound = base, and
     `ctx_base_child_letter_contraction` applied twice gives the base equality.
4. Both orientations and both r are symmetric instances; factor one lemma over (side, coupling) pairs.

Reuse R6's machinery: `ESBlueprint/B/CtxBoundAdditiveSingleRunOfRunContractionAndAlternating.lean`
(`hCtxEq`, `hInterval`, part/word equalities after deletions, getD/filter bookkeeping). Also useful:
`ctx_bound_external_letter_contraction` (for how deletions shift positions), `ErdosSzekeres/DecomposableContextLemmas.lean`.

## Procedure and stop criteria

1. Develop in `runs/r9-sol-20260930/`, compiled by guarded jobs. Then `es check <node> --targeted`
   and `es node commit`.
- **Closed:** stop and report.
- **Stuck:** two consecutive attempts fail at the same bookkeeping obligation. Write the exact missing
  lemma in the handoff and stop.
- **Rules:** AGENTS.md applies. `es log` every finding with job IDs. At the end write
  `MATHEMATICAL-HANDOFF.md` and `REPORT.sol.md` here, and release any claim you hold (claim the node first).
