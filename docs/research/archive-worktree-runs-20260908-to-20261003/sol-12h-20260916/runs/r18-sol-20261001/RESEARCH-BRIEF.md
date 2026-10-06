# R18: C1r through a root normal form (one Sol trial, gpt-6.1-sol)

Approved by Gavin on 01 Oct: focus all trials on C1r and park multi_run's FLIP core. Coordinator:
`claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude). Callbacks are not verified: never wait
for replies; keep `PROGRESS.md` here current. One trial; never reset the host deadline. When a Done
criterion is met and committed, say so in PROGRESS.md and the coordinator ends the run early.

Parallel C1r trials (do not touch their nodes; reuse their closed helpers, see their journals):
- **R16:** N_root / N_ends, in `runs/worktrees/main-integration-20260928`. It has 16+ closed
  one-level-root helpers: exposed-end threshold lower bounds, small-axis threshold upper bounds, and
  absorbed-marker upper bounds. It is stuck on the LARGER-AXIS UPPER bound.
- **R17:** X, in `runs/worktrees/sol-12h-20260913`.

## Target and the new route

C1r `ctx_bound_child_run_contraction_one_level_root` (open; on main it is composed from the closed
R14 conditional, N_root and X). This trial attacks C1r WITHOUT N_root or X, through a normal form.

**Coordinator data** (diagnostic, compiled evaluator; `/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-n-selector-20261001/`: closed_form.py, closed-form-table.txt,
shift-fit.txt, saturation_quick.py; journal on C1r):
1. **Run-count saturation.** For a, u >= 3, a one-level root's bound is the same for 2, 3 and 4 runs
   (contracted words, k=4..6: 792 contexts, 0 variation). In the axis-2 class, 12 contexts give 1 for
   2 runs and 0 for 3 or more. A wider test (up to 6 runs, k up to 7) is running:
   `saturation.txt`.
2. **Single-run closed form.** With no end markers the bound is exactly T(a, min(u, k-m), k), at
   k=5,6,7, all m. With one end marker it is T(a, min(u, k-m+1) - 1, k). Fits are per side; see
   shift-fit.txt.
3. **Multi-run bounds are not a single capped and shifted T**, and no simple two-term sum fits across
   all k and m. Get their values from the recursion on the normal-form words, which have at most 2
   children.

## Part 1 (register, falsify)

Register **ROOT-NF** with `es node add`, as a conjecture.
- Statement: for a one-level root σ (letters child or `ext 1 side`, maxima [m], 1 <= a, u <= k,
  k >= 3), σ.bound equals the bound of its normal-form word, which has the same end markers and
  min(numRuns, 2) runs of length 1.
- Adjust the run-count clamp for the axis-2 class as the data require (3 there instead of 2), or
  restrict to a, u >= 3 and treat axis 2 with the closed zero/unit-axis lemmas.
- Give it a falsifier and a targeted `es falsify`.

Register and close **C1r from ROOT-NF**. Contracting a doubled child preserves the end markers and the
run count (`ctx_num_runs_child_letter_contraction`, closed), so both words share a normal form.

**Done (narrowing)** = both committed, each on its own branch from main.

## Part 2: prove ROOT-NF

Strong induction on the number of children, with ROOT-NF for all smaller one-level roots as the
hypothesis. This contains C1r and saturation for smaller roots, which is stronger than either alone.
- **(>=)** σ's bound is at least its normal form's: exhibit the cuts. The extreme-run-end selector
  from R16 says which singleton attains.
- **(<=)** Every interval cut of σ is at most the normal form's bound. Each cut has 2-level parts.
  For parts of a single run, `ctx_single_run_descendant_bound_normalize` turns them into one-level
  roots with (a', u') = (capLimit+1, cupLimit+1), where the IH applies. Multi-run parts are the hard
  case. Find what weaker statement suffices there, and reuse R16's explicit threshold upper bounds
  for small axes.
- The base cases are the closed theorem for <= 3 children, `ctx_bound_zero_of_unit_global_axis` and
  `ctx_singleton_part_bound_eq_threshold`.

**Done (full)** = ROOT-NF closed (then C1r closes). **Stuck** = two consecutive attempts fail at the
same obligation: write the exact missing inequality with a tested witness family. A counterexample to
ROOT-NF or saturation is also a valid result.

## Checkout and rules

- **Worktree:** `runs/worktrees/sol-12h-20260916`. Create branches from main (local main has R15's
  integration; use `git -c gc.auto=0 -c maintenance.auto=false rev-parse main`, or the guarded branch
  job).
- **Harness:** `/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916`.
  - The job memory budget is 40G, two Lean builds at once, shared with R16, R17 and a coordinator full
    extract (30G) queued right now: expect waits.
  - Time heavy contexts before probes. Never kill at a self-chosen time; `es job review` at
    checkpoints.
- **Commits:** `es node commit`. Statements only via `es node add`.
- **Forbidden:** merging, pushing, touching the primary checkout, a full `es extract`, delegating,
  axioms or native_decide.
- **Rules:** AGENTS.md. `es log` every finding (including failed routes) with job IDs. At the end write
  `MATHEMATICAL-HANDOFF.md` and `REPORT.sol.md` here.
