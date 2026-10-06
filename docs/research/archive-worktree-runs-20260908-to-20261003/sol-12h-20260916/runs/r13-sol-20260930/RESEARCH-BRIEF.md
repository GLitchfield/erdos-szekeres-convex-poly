# R13: prove C1r, or narrow it to a sharper registered lemma (one Sol trial, gpt-6.1-sol)

Approved by Gavin on 30 Sept 2026 (evening round, item 1: "C1 narrowing plus proving it").
Coordinator: `claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude). Callbacks are not verified:
never wait for replies, and keep `PROGRESS.md` here current. This is one trial; never reset the host
deadline. When a Done criterion below is met and committed, say so in PROGRESS.md. The coordinator
then reviews it and ends the run early with `es run finish`.

## Target

`ErdosSzekeres.ctx_bound_child_run_contraction_one_level_root` (C1r,
`ESBlueprint/B/CtxBoundChildRunContractionOneLevelRoot.lean`, conjecture, `sorry`).

The statement: a context with 1 <= a, u <= k, k >= 3, a single level of maximum m in [1, k-2], and a
word `left ++ [child, child] ++ right`, where every letter of left/right is a child or `ext 1 side`
(one fixed side). Deleting one of the two adjacent child letters leaves `Context.bound` unchanged.

It is the single open conjecture under single-run additivity on main (41cc0e4b):
- single_run = R6'(bridge(C1r), C3);
- C3 = R9'(bridge(C1r), DelMono);
- the three special cases (sandwich_one_singleton_end, three_blocks, uniform_separator) compose from these.

Closing C1r closes all of them.

## What is known (read before choosing a route)

**Closed lemmas you can use.** Search with `es search`.
- DelMono `ctx_bound_ext_letter_deletion_mono_of_isolated_children` (R8): deleting an external
  letter never lowers the bound, when the child letters are pairwise isolated as stated.
- The normalization `ctx_single_run_descendant_bound_normalize`: parts of a single run equal
  one-level root contexts with (a', u') = (capLimit+1, cupLimit+1).
- The bridge `ctx_bound_part_run_contraction_of_one_level_root`: C1 on parts of single-run
  contexts, from C1r as hypothesis hroot.
- `ctx_bound_mono_of_marker_inclusion`, `ctx_bound_mono_of_zero_capacity_marker_inclusion`,
  `ctx_single_level_occurrence_prune_bound_mono`, `ctx_erase_level_bound_mono`.
- The base/threshold lemmas `ctx_base_child_letter_contraction`, `ctx_base_pascal_combine`,
  `ctx_bound_three_way_base_allocation`.

**Negative facts (diagnostic, compiled evaluator; do not retry these as stated).**
- *Unrestricted adjacent-letter contraction is false.* See the closed refutation
  `ctx_bound_adjacent_letter_contraction_counterexample`: (5,5,6), [S,1L,2U,S,S], maxima [1,1],
  bound 12 -> 9. The level-two letter inside the span is essential.
- *Contraction is not closed under cuts* (P7, `/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-comb-reduction-20260929/HANDOFF.md`).
  Parts of C1 contexts can fail contraction. Example: at (5,5,6) the C1 context [2L,S,1U,S,1U,S,S],
  maxima (1,1). Its part [3L,S,2U,1U,2U,S,S], maxima (1,1,1), has bound 6 -> 5 when its last run is
  shortened.
- So **an induction that transports each cut of rho to the "same" cut of rho' cannot work.** A
  proof must compare *different* cuts by value.
- *Multi-run partition-value contraction fails* (M1, `/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-comb-closedform-20260930/m1p/`).
  This is off target here, but it confirms the same point.

**Positive evidence (diagnostic).**
- *C1R* (`/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-comb-closedform-20260930/c1r/`, k = 5, 6, 7, all a, u, m, sides and
  ends, <= 5 children). rho has the doubled pair y y'; rho' = rho - y'.
  - Every cut of rho is dominated in rho' by one of the two moved partitions (B, R-y') or
    (B-y, R-y'+y), where B is the block holding y.
  - Usually this holds at the same orientation and coupling. There were 0 exceptions and 0 C1
    violations.
- *P11* (`/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-comb-closedform-20260930/p11/`, script `p11_exchange_patterns.py`).
  Cuts that are not dominated at their own coupling (k=5: 2,382 separating and 2 non-separating;
  k=6: 9,294 and 38) are all rescued by a moved partition at another orientation or coupling.
  - The needed coupling shift grows with k: side change only, or a shift of -1 or -2 at k = 7.
  - The failures concentrate where the block is the singleton {y}. Then one side is a single-child
    context with an explicit base value T(p+1, c+1, k), and the other side loses the isolated child
    y' next to the new level-1 letter y.
  - The k7-*.json `separating_rules` tables list every rule with counts.
- *External-letter contraction* (EE -> E) is closed. For a singleton cut {y} whose y' is followed by
  another child, the case is trivial: the base side contracts a doubled external letter, and the
  rest side contracts a doubled child inside a part of a single run (bridge). The hard case is y'
  followed by an external letter or the word end.

## Routes (your choice; log the choice and why)

1. **Direct proof by strong induction on the word (or the Lean fuel).**
   - (>=) Lift each cut of rho' to rho.
   - (<=) Dominate each cut of rho by a moved partition of rho' with a re-optimized coupling. That
     needs an exchange inequality: the gain of deleting the level-1 letter y' from the block's part
     (DelMono side) against the loss of deleting child y' from the rest part, at a shifted coupling.
   - Find the invariant class first. It must be closed under the parts the argument actually uses;
     the negative facts above say which classes are not closed.
2. **Narrowing (the fallback, and a valid Done).** State the exact exchange inequality the
   domination needs, e.g. for singleton blocks {y}. Test it with a small falsifier over the P11
   ranges using the compiled evaluator (`harness/research/context_bound.py`,
   `compiled_evaluator(..., persistent=True)`; see `es lib show research.compiled-context-bound`).
   Register it with `es node add` as a conjecture. Register and prove a conditional node
   "C1r from X": X enters as an explicit hypothesis, the pattern of R9', R6' and the bridge. Then
   compose C1r's module from it, so that C1r's sorry is only through X. The new X must be strictly
   narrower than C1r: a single-child base versus a part, with explicit T values.

## Checkout and scope

- **Worktree:** `runs/worktrees/sol-12h-20260916` (Lake build cache).
  - Create every branch from main (41cc0e4b) with
    `git -c gc.auto=0 -c maintenance.auto=false checkout -b <branch> main`.
  - Target branch: `node/CtxBoundChildRunContractionOneLevelRoot`. Any new node gets its own
    branch, named after the node.
- **Harness:** `/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916`.
  - Before a targeted check, build any imported module that has no olean in this worktree with a
    small guarded job (`es job run --mem 4G ... -- lake build <Module>`).
  - Only one Lean build runs at a time project-wide. A refusal saying the concurrency reservation is
    occupied (even if it says "cannot fit") means wait, not fail.
  - Probes over a minute go through `es job run --why ... --out runs/r13-sol-20260930/... --review MIN`.
    Report progress, never kill at a self-chosen time, and record `es job review` at review_due.
- **Commit:** use `es node commit <node> --message-file <file>` on its branch.
- **Edit statements only through the harness** (`es node add` for new ones). Never edit an existing
  statement.
- **Forbidden:** merging, pushing, touching the primary checkout, a full `es extract`, delegating,
  and axioms/native_decide.

## Done / stuck

- **Done (full):** C1r proved with standard axioms, targeted-check receipt, committed.
- **Done (narrowing):** a registered and falsifier-tested lemma X, strictly narrower than C1r, plus a
  closed conditional node C1r-from-X. C1r's module is composed from it, and its check shows sorry
  only through X. Everything is committed.
- **Stuck:** two consecutive attempts fail at the same obligation. Write the exact missing lemma and
  its evidence in the handoff, and stop.
- **Rules:** AGENTS.md. `es log` every finding (including failed routes and probes) with job IDs
  before the next attempt. At the end write `MATHEMATICAL-HANDOFF.md` and `REPORT.sol.md` here.
  C1r may be claimable. If `es claim` refuses, log instead.
