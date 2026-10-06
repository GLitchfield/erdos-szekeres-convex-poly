# R6: prove the glue theorem single_run ⟸ C1 + C3 (one Sol trial, gpt-6.1-sol)

Approved by Gavin on 29 Sept 2026, after R1. Background: the R1 handoff
`/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-comb-reduction-20260929/HANDOFF.md`,
section "Open obligation".
- Coordinator: `claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude).
- Callbacks are not verified. Never wait for replies; keep `PROGRESS.md` here current.
- One trial only. Never reset the host deadline.

## Checkout and scope

- **Worktree:** `runs/worktrees/sol-12h-20260916`, now on branch
  `node/CtxBoundAdditiveSingleRunOfRunContractionAndAlternating`, base `5d58845b` (main). It has a
  full Lake build cache.
- **Harness commands:** use the primary launcher with `--root` for this worktree:
  `/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916`.
- **Where to write:** only under `runs/r6-sol-20260929/` here, plus the node module once
  registered. Commit on this branch only.
- **Forbidden:** merging, pushing, touching the primary checkout, editing other statements, running a
  full `es extract`, delegating.
- **Shared machine:**
  - Two other Sol runs share it: R3 until 09:31Z, R5 until about 01:40Z.
  - The N27 solver job holds 8 GiB until 07:00Z.
  - Scratch compiles are guarded jobs of ≤ 4 GiB with `lake env lean`.

## The theorem

Statement: exactly the second theorem in `runs/r6-sol-20260929/GlueStatements.lean`,
`ctx_bound_additive_single_run_of_run_contraction_and_alternating`. It type-checked against main's
oleans in job 20260929-210922-2536a4.
- **Hypotheses:**
  - `hcontract` (C1): delete one of two adjacent child letters when every letter strictly inside
    the child span is a child or `ext 1 side`.
  - `halternating` (C3): the alternating singleton partitions of a single run.
- **Conclusion:** exactly the statement of `ErdosSzekeres.ctx_bound_additive_single_run`.
- Both hypotheses are explicit, never axioms. The template is
  `ESBlueprint/B/CtxBoundAdditiveThreeBlocksOfUniformContraction.lean`, which proves three-block
  additivity from an explicit contraction hypothesis.

## Proof outline

The argument has been checked on paper by the coordinator; the list and position bookkeeping is the
work. Take σ single-run, any keep K, and d.
1. **Every part is in the C1 class.** σ's children occupy one contiguous interval, so in
   `σ.part K s m` every letter strictly inside the span of K's positions is a K letter or a
   K-complement letter, now `ext 1 s`. σ's own external letters, shifted to level ≥ 2, lie outside
   σ's run and hence outside that span. The same holds for the complement part.
2. **Deleting a doubled K letter.** Suppose some maximal block of consecutive positions of K has
   length ≥ 2, and let x be a letter in it.
   - In `σ.part K lower d`, deleting x preserves the bound by `hcontract`.
   - In `σ.part Kᶜ upper c`, x is `ext 1 upper` next to an identical letter, so
     `ctx_bound_external_letter_contraction` (closed) preserves the bound.
   - The same works in the other orientation.
   - Deleting position x from σ commutes with taking parts, once the positions after x are shifted.
3. **Deleting a doubled Kᶜ letter** is symmetric.
4. **The base is unchanged.** `σ.bound = σ.base` for a single run, and deleting one letter of a run
   of length ≥ 2 keeps the base. All children of a single run have equal point limits: search for
   `ctx_point_limits_eq_of_child_interval`, which R3 found and reused (standard axioms). Also look at
   `ctx_base_child_letter_contraction`.
5. **Induct** on Σ over blocks of (length − 1). At zero, K and Kᶜ alternate in singletons along a
   run of length m ≥ 2. Then K is the alternating keep with r = 0 if the first child is in K,
   otherwise r = 1, exactly as `halternating` states it (filter-map over indices). Apply
   `halternating`.
6. Duplicates in `keep` are harmless, because `part` uses only membership. `hall` guarantees the
   complement is nonempty.

Useful closed nodes to read first:
- `ctx_bound_external_letter_contraction`
- `ctx_base_child_letter_contraction`
- `ctx_bound_child_letter_expansion`
- `ctx_sandwich_middle_block_contraction` (similar list surgery on parts)
- `ctx_bound_additive_three_blocks_of_uniform_contraction`
- `ctx_point_limits_eq_of_child_interval`

Also search with `es search` by name and statement. Prose search missed some of these.

## Procedure

1. Develop the proof in a scratch file under `runs/r6-sol-20260929/`, compiled by guarded jobs.
2. When it compiles with standard axioms only (audit as R3 did), register the node:
   `es node add --targeted --ws B --kind formalization --import <narrowest module that works> --consumer ErdosSzekeres.ctx_bound_additive_single_run --depends <closed lemmas used>`.
   - `es node add` reserves 20 GiB. Several registrations are queued behind the R5 host and the
     N27 job: R3's `ctx_bound_reverse` and the coordinator's C1/C3 nodes.
   - If refused, retry every 20 minutes. Don't `--queue` a 20 GiB job: it blocks the worker queue.
3. Put the proof in the module, run `es check <node> --targeted`, and commit on this branch when it
   closes.

**Stop criteria:**
- **Closed:** stop and report.
- **Stuck:** two consecutive attempts fail at the same bookkeeping obligation. Write the exact
  missing lemma in the handoff and stop.

## Rules

- `AGENTS.md` applies. `es log` every finding, failure and plan change, with job IDs.
- At the end, write `MATHEMATICAL-HANDOFF.md` and `REPORT.sol.md` here, and release any claim you
  hold. You may claim the new node after registration.
