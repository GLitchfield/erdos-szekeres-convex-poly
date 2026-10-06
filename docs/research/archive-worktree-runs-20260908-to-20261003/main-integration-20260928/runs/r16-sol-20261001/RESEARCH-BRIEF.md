# R16: prove N_root through the extreme-run-end selector (one Sol trial, gpt-6.1-sol)

Approved by Gavin. This is item 1 of the 30 Sept evening round ("C1 narrowing plus proving it"), plus
his 30 Sept night direction to focus on Workstream B induction steps. Coordinator:
`claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude). Callbacks are not verified: never wait
for replies, and keep `PROGRESS.md` here current. One trial; never reset the host deadline. When a Done
criterion is met and committed, say so in PROGRESS.md and the coordinator ends the run early.

A parallel trial, R15 (`runs/worktrees/sol-12h-20260916/runs/r15-sol-20261001/`), works on
multi_run / FLIP. Do not touch its nodes.

## State on main (5847e155)

- **C1r** `ctx_bound_child_run_contraction_one_level_root` is composed from the closed conditional
  `ctx_bound_child_run_contraction_one_level_root_of_singleton_exchange` (R14), applied to two open
  conjectures:
  - **N_root** `ctx_one_level_root_bound_attained_by_singleton_cut`: for a one-level root σ with
    `2 <= numRuns`, σ.bound is at most some singleton-cut value.
  - **X** `ctx_one_level_root_singleton_base_exchange`.
- Every single-run composition (C3, single_run, sandwich, three_blocks, uniform_separator) is blocked
  only by C1r.
- Closed tools:
  - `ctx_bound_attained_by_singleton_cut_of_le_three_children` (N for <= 3 children, raw contexts);
  - `ctx_singleton_part_bound_eq_threshold`;
  - `ctx_single_level_limits_exact`;
  - `ctx_num_runs_child_letter_contraction`;
  - `ctx_bound_zero_of_unit_global_axis`;
  - `ctx_bound_cut_le`;
  - DelMono;
  - MERGE, `ctx_erase_level_bound_mono`;
  - the normalization `ctx_single_run_descendant_bound_normalize`;
  - the bridge `ctx_bound_part_run_contraction_of_one_level_root`.
  Use `es search`.

## What failed (do not repeat)

- **R13:** minimum-active-capacity selector (witness (3,4,5,1) [S,1L,S,S,1L,S]); fixed-position
  lifting.
- **R14:** block-size descent restricted to blocks inside B, or to the three nested pieces. In R14's
  witness (3,4,5,1) S L S L S L SS with B=[2,4], only the OUTSIDE singleton 7 attains. The Pascal
  split also fails at a unit/unit component ((3,3,4,1) SS L SS).
- General end-cut normal form is refuted. Global ends alone are not enough (see below).

Read `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/main-integration-20260928/runs/r14-sol-20261001/MATHEMATICAL-HANDOFF.md`.

## New evidence: WHICH singleton attains

Coordinator probes, diagnostic, compiled evaluator. Sources:
`/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-n-selector-20261001/` (`n_selector.py`, `which_end.py`, shard-*.json) and the
journal on N_root.

- **Family:** one-level root contexts with 2-4 runs of length 1-3, single separators, optional end
  markers, both sides, <= 5 children, all a,u >= 2, all m.
- **Results so far:** k=5: 5,230 nonzero contexts; k=6: 12,606; k=7 partial: 14,968 (shards finishing).
  0 N_root failures.
- **Selector:** an attaining singleton ALWAYS exists among the <= 4 children at the two ends of the
  FIRST and the LAST run (0 failures at every k).
  - Global end alone fails (12/18/24); inner extreme end alone fails (4/6/8).
- **Finer structure** (k=5,6, <= 4 children), the same for both sides and mirror-symmetric:
  - both word ends carry a marker: all four candidates attain;
  - exactly one end unmarked: both ends of the run at the UNMARKED end always attain, including the
    global end child there;
  - neither end marked: some candidate attains, but no fixed one does.

## Part 1 (certain, do first)

1. Register **N_ends** with `es node add`, as a conjecture.
   - Statement: N_root with p restricted to the ends of the first and last run. Pick the cleanest Lean
     form: for example p in {first child, last child of the first run, first child of the last run,
     last child}, via `σ.childPositions` and the run decomposition already used in the closed
     nodes.
   - Falsifier: adapt `n_selector.py`.
2. Register and close **N_root from N_ends**. This should be a direct weakening.

Each gets its own branch from main 5847e155, a targeted check and `es node commit`.

## Part 2: prove N_ends

Suggested routes; log your choice and why.

**(a) Exposed-end case first.** If one word end is unmarked, show the global end child there attains,
by an exchange between an optimal interval cut and the end cut (the singleton at the unmarked end).
The unmarked end means the end child's singleton part sees no external letter on that side; compute
its threshold with `ctx_singleton_part_bound_eq_threshold` and `ctx_single_level_limits_exact`.
Then handle both-marked and neither-marked separately.

**(b) Joint induction on the number of children.** Assume N_root AND C1r for all one-level roots with
fewer children; C1r follows from N_root + X for those, so assume X, or prove X along the way. With
C1r for smaller roots and the bridge, parts of single runs contract, and run lengths inside the parts
an optimal cut produces can be shortened. That may turn the descent R14 could not do into a statement
about contracted words, where every child is a run end.

**Done (full)** = N_ends (hence N_root) closed. **Stuck** = two consecutive attempts fail at the same
obligation; write the exact missing inequality with a tested witness family. A falsifier
counterexample to N_ends is also a valid result: report it.

## Checkout and rules

- **Worktree:** `runs/worktrees/main-integration-20260928`. Create branches from main 5847e155 (use the
  guarded branch job if direct creation is refused).
- **Harness:** `/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/main-integration-20260928`.
  - The job memory budget is now 40G and two Lean builds may run at once.
  - Time heavy contexts before sizing probes. Never kill at a self-chosen time; `es job review` at
    checkpoints.
- **Commits:** `es node commit`. Statements only via `es node add`.
- **Forbidden:** merging, pushing, touching the primary checkout, a full `es extract`, delegating,
  axioms or native_decide.
- **Rules:** AGENTS.md. `es log` every finding (including failed routes) with job IDs. At the end write
  `MATHEMATICAL-HANDOFF.md` and `REPORT.sol.md` here.
