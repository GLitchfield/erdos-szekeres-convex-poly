# R15: narrow multi_run to a singleton-flip exchange, then attack it (one Sol trial, gpt-6.1-sol)

> **CORRECTION (coordinator, 2026-10-01 01:15Z):** FLIP must quantify over maximal segments of ANY
> length, not singletons. The singleton form is structurally false (00110011). See COORDINATOR-NOTE.md
> and the es journal on ctx_bound_additive_multi_run. Restate FLIP with `es node restate` on your
> branch; the conditional proof is unchanged.


Approved by Gavin. Item 2 of the 30 Sept evening round ("multi_run after M1"), plus his 30 Sept night
direction to focus compute on Workstream B induction steps. Coordinator:
`claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude). Callbacks are not verified: never wait
for replies; keep `PROGRESS.md` here current. One trial; never reset the host deadline. When a Done
criterion is met and committed, say so in PROGRESS.md and the coordinator ends the run early.

A parallel trial, R14 (`runs/worktrees/main-integration-20260928/runs/r14-sol-20261001/`), works on
C1r through singleton attainment N_root and the exchange X. Do not touch those nodes. Read its journal
entries (`es journal --node ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root`) for
reusable lemmas.

## Target

`ErdosSzekeres.ctx_bound_additive_multi_run` (conjecture, sorry, falsifier pass).

The statement: σ is WellFormed with `2 <= σ.numRuns`, keep is an arbitrary nonempty proper set of child
positions (any interleaving), and `1 <= d <= k-2`. Then both orientation sums of part keep and part
complement are `<= σ.bound`.

The interval case is the closed `ctx_bound_cut_le` (every block in `σ.blocks`, both orientations).
The content is interleaved keep sets.

## Evidence: M2

Diagnostic, compiled evaluator `context-bound-zero-children-c-v1`. See
`/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-comb-closedform-20260930/m2/`, script `m2_multirun_domination.py`, and
`HANDOFF.md` section "M2".

- **Scope:** 2-3 runs, separators from levels 1-2, <= 5 children, maxima all-1 or all-(k-2), six
  (a, u, k) cases, 32,688 interleaved partitions. Interleaved means neither K nor its complement is
  contiguous in child order.
- **Result:** 0 multi_run violations. Let V(K) be the max over d and both orientations. For every
  interleaved K, some maximal same-side segment S of K's child sequence has V(K xor S) >= V(K), and
  a SINGLETON segment always works.
- **End segments alone are not enough:** up to 88 exceptions per case.
- **Rejected route:** deleting one of a doubled same-side pair (route D) is unsound on interval
  partitions. Example: [S,1L,2U,S,1L,2U,S,S], (1,1), where the bound drops 9 -> 8.
- **n = 6 is untested.** The evaluator is exponential in depth: a 6-child context with 5-6-child runs
  took >50 min. Time heavy contexts before sizing anything.

## Part 1 (do first): register the narrowing

1. **Register FLIP** with `es node add`, as a conjecture. State it per coupling, matching multi_run's
   shape.
   - Hypotheses: σ WellFormed, `2 <= numRuns`, K a keep set such that neither K nor its complement
     is a block, `1 <= d <= k-2`.
   - Conclusion: there is a child p whose child-order neighbours (one at an end) are all on the other
     side of K, and there are d', o' with `value(K, d, o) <= value(K xor {p}, d', o')`.
   - Formulate it exactly in Lean terms. Keep it as weak as the induction allows: any orientation and
     coupling on the right.
   - **Falsifier:** broader than M2. Use WellFormed contexts from
     `scripts/decomposable_additivity_test.contexts` (levels <= 3, mixed maxima, both sides) with <= 5
     children, and a timed n = 6 slice. Reuse `harness.research.context_bound` (persistent=True) and
     `es lib search` first. Run a targeted `es falsify`.
2. **Register and close** the conditional "multi_run from FLIP" (FLIP as an explicit hypothesis), by
   strong induction on the number of maximal segments of K in child order.
   - A singleton flip lowers the count by 2 (interior) or 1 (end).
   - Partitions with <= 3 segments are intervals or complements of intervals, so `ctx_bound_cut_le`
     applies. `part` depends on keep only through membership (R12 used this).
3. **Compose** multi_run's module from the conditional and FLIP, so multi_run shows sorry only through
   FLIP.

**Done (narrowing)** = all three committed, each on its own branch.

## Part 2: prove FLIP

FLIP is a local exchange.
- Moving child p from K to its complement turns p into a level-1 letter in part K and adds a child to
  the complement part. One side loses value and the other gains it, and the coupling may need
  re-optimizing (compare R13's X: side change or a coupling shift of -1/-2 at k = 7).
- Useful closed tools: `ctx_singleton_part_bound_eq_threshold`,
  `ctx_bound_attained_by_singleton_cut_of_le_three_children`, `ctx_single_level_limits_exact`, DelMono
  `ctx_bound_ext_letter_deletion_mono_of_isolated_children`, `ctx_bound_le_merge_same_side_levels`,
  `ctx_erase_level_bound_mono`, `ctx_bound_mono_of_marker_inclusion`.
- First record WHICH singleton works: an end, an interior neighbour of a separator, the first or last
  of a run. A deterministic choice rule makes the Lean proof far easier.

**Done (full)** = FLIP closed (then multi_run closes). **Stuck** = two consecutive attempts fail at the
same obligation: write the exact missing inequality with a falsifier-tested family and stop.

## Checkout and rules

- **Worktree:** `runs/worktrees/sol-12h-20260916` (Lake cache). Create every branch from main
  (4d0be1b7) with `git -c gc.auto=0 -c maintenance.auto=false checkout -b <branch> main`. If direct
  branch creation is refused by read-only metadata, use the guarded branch job as R14 did.
- **Harness:** `/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916`.
  - Build imported modules without oleans in a small guarded job first.
  - One Lean build at a time project-wide, shared with R14. A concurrency refusal means wait.
  - If a job queues on memory for more than 15 min, say so in PROGRESS.md.
- **Probes** over a minute: `es job run --why ... --out runs/r15-sol-20261001/... --review MIN`. Time
  one heavy context before sizing. Never kill at a self-chosen time; `es job review` at checkpoints.
- **Commits:** `es node commit <node> --message-file <file>` on its branch.
- **Statements:** new ones only via `es node add`; never edit an existing statement.
- **Forbidden:** merging, pushing, touching the primary checkout, a full `es extract`, delegating,
  axioms or native_decide.
- **Rules:** AGENTS.md. `es log` every finding, including failed routes, with job IDs, before the next
  attempt. At the end write `MATHEMATICAL-HANDOFF.md` and `REPORT.sol.md` here.
