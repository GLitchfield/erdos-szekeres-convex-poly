# R14: register C1r's two-lemma narrowing, then prove singleton attainment N_root (one Sol trial, gpt-6.1-sol)

Approved by Gavin on 30 Sept 2026 (evening round, item 1: "C1 narrowing plus proving it"; the R13
follow-up was proposed in the progress report). Coordinator: `claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f`
(Claude). Callbacks are not verified: never wait for replies; keep `PROGRESS.md` here current. One
trial; never reset the host deadline. When a Done criterion is met and committed, say so in PROGRESS.md
and the coordinator ends the run early with `es run finish`.

## State on main (4d0be1b7)

Single-run additivity and every composition under it are blocked only by the conjecture **C1r**
`ctx_bound_child_run_contraction_one_level_root`.

R13 (`/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916/runs/r13-sol-20260930/`, read `MATHEMATICAL-HANDOFF.md` first) narrowed it:
- **X** `ctx_one_level_root_singleton_base_exchange`: registered conjecture on main, falsifier pass.
  Each singleton cut of the doubled root σ maps to a singleton cut of the contracted root ρ at a
  re-optimized orientation and coupling.
- **N** (singleton attainment): when σ.numRuns >= 2, σ.bound <= some singleton cut value (explicit
  threshold of part [p], plus the complement part). Closed for <= 3 children in raw contexts:
  `ctx_bound_attained_by_singleton_cut_of_le_three_children`, on main.
- **Scratch (compiles, not registered):**
  - `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916/runs/r13-sol-20260930/RootConditionalInterface.lean`: C1r from N (as hypothesis hN, for σ) and X.
  - `RootReverse.lean`: the reverse inequality ρ.bound <= σ.bound.
  - `RootBranches.lean`: single-run contraction for raw contexts.
- **Stopped** under R13's two-failed-attempt rule. Failed selectors for N:
  - minimum active capacity: witness (3,4,5,1), [S,1L,S,S,1L,S];
  - fixed-position lifting through a cut.
- **Also refuted:** the general end-cut normal form. Do not use it.

This is a new trial. R13's two-attempt count does not carry over, but do not repeat those two
selectors.

## Part 1 (certain, do first): register the narrowing

My R13 brief required "C1r from X alone"; that was too strict. A two-hypothesis narrowing is valid,
because both lemmas are strictly narrower than C1r and are tested.

1. Register **N_root** with `es node add`, as a conjecture.
   - Statement: the hN hypothesis of RootConditionalInterface.lean, generalized over the root word.
     One-level root σ (maxima [m], letters child or `ext 1 side`, 1 <= a, u <= k, k >= 3,
     1 <= m <= k-2), and `2 <= σ.numRuns`. Then there are p, s and c in [1, k-2] with
     σ.bound <= T(part [p] s c limits) + (part (children minus p) (opposite s) (k-1-c)).bound.
   - Only the ONE-LEVEL ROOT case is needed; do not state it for raw contexts.
   - Falsifier: reuse R13's singleton-attainment probes (`probe_singleton_normal*.py`) and the
     merged library primitive `harness/research/singleton_cuts.py` (`es lib show research.singleton-cuts`). Give it a
     targeted `es falsify`.
2. Register and close the conditional **C1r-from-(N_root, X)**, with both as explicit hypotheses, as
   R9′, R6′ and the bridge do. Its proof is RootConditionalInterface.lean plus RootReverse.
3. Compose C1r's module from the conditional, applied to the two conjecture theorems. C1r's check
   then shows sorry only through N_root and X.

Each gets its own branch from main, a targeted check and `es node commit`. **Done (narrowing)** = all
three committed.

## Part 2: prove N_root (after Part 1)

Induction on the size of the optimal cut's block, with the closed <= 3-children theorem as base. Take
an optimal interval cut (B, R) with |B|, |R| >= 2.

**(a) B spans several runs.** Then `σ.part B` is multi-run, and its bound is a cut (B1, B2) of the
part, which is an interval inside B. Lift it.
- `σ.part B |>.part B1` has B2 at level 1, R at level 2 and the old letters at level 3.
- Compare it with `σ.part B1` (B2 ∪ R at level 1). Use `ctx_bound_le_merge_same_side_levels` (MERGE)
  when the sides agree and `ctx_erase_level_bound_mono` otherwise.
- The rest, `part B |>.part B2` + `σ.part R`, is bounded by `σ.part (B2 ∪ R)` through its interval
  cut (B2 is contiguous inside the complement of B1), with `ctx_bound_cut_le` when that part is
  multi-run.
- The result is a cut of σ with a strictly smaller block. Coupling choices are value-dependent:
  choose them from the limits, not from positions.

**(b) B lies in one run.** Then `part B` is single-run with explicit base T(A, U, k)
(`ctx_single_run_descendant_bound_normalize`, `ctx_singleton_part_bound_eq_threshold`).
- Split it with the window identity T(A,U,k) = T(A,k-e,k) + T(e+1,U,k) (`ctx_base_pascal_combine`,
  `ctx_bound_three_way_base_allocation`) into an end child b of B plus B-b.
- Regroup (B-b) with R as in (a).

**Evidence.** M2 (`/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-comb-closedform-20260930/m2/`, HANDOFF update "M2"): in 32,688
interleaved partitions of multi-run contexts, flipping some singleton segment never lowers the value.
This is the same principle for multi_run, so an exchange lemma general enough to serve both is a bonus,
not a requirement.

**Done (full)** = N_root closed (C1r then depends only on X). X itself is a stretch goal after N_root.
**Stuck** = two consecutive attempts fail at the same obligation. Then write the exact missing
inequality, with a falsifier-tested witness family, in the handoff.

## Checkout and rules

- **Worktree:** `runs/worktrees/main-integration-20260928` (Lake cache). Create every branch from
  main (4d0be1b7) with `git -c gc.auto=0 -c maintenance.auto=false checkout -b <branch> main`.
- **Harness:** `/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/main-integration-20260928`.
  - Build imported modules without oleans in a small guarded job first.
  - One Lean build at a time project-wide. A concurrency refusal (even worded "cannot fit") means
    wait.
  - The coordinator keeps memory headroom for you. If a job queues on memory for more than 15 min,
    say so in PROGRESS.md.
- **Probes** over a minute: `es job run --why ... --out runs/r14-sol-20261001/... --review MIN`.
  - The compiled evaluator is exponential in recursion depth: time one heavy context before sizing
    a sweep.
  - Never kill at a self-chosen time; record `es job review` at checkpoints.
- **Commits:** `es node commit <node> --message-file <file>` on its branch.
- **Statements:** new ones only via `es node add`; never edit an existing statement.
- **Forbidden:** merging, pushing, touching the primary checkout, a full `es extract`, delegating,
  axioms or native_decide.
- **Rules:** AGENTS.md. `es log` every finding, including failed routes, with job IDs, before the next
  attempt. At the end write `MATHEMATICAL-HANDOFF.md` and `REPORT.sol.md` here.
- **Claims:** R13 may still hold the C1r claim. If a claim is refused, log instead and continue.
