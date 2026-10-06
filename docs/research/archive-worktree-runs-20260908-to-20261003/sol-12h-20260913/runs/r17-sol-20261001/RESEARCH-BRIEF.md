# R17: attack X, the singleton-base exchange under C1r (one Sol trial, gpt-6.1-sol)

Approved by Gavin. This is item 1 of the 30 Sept evening round ("C1 narrowing plus proving it"); on
01 Oct he asked that the whole machine be used on the B induction steps. Coordinator:
`claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude). Callbacks are not verified: never wait
for replies; keep `PROGRESS.md` here current. One trial; never reset the host deadline. When a Done
criterion is met and committed, say so in PROGRESS.md and the coordinator ends the run early.

Parallel trials:
- **R16** works on N_root / N_ends, in `runs/worktrees/main-integration-20260928`;
- **R15** has finished multi_run / FLIP.

Do not touch their nodes. Read their journals for reusable lemmas: R16 has 16+ closed one-level-root
helpers, including exposed-end lower bounds and threshold upper bounds for small axes.

## Target

`ErdosSzekeres.ctx_one_level_root_singleton_base_exchange` (X; registered conjecture, falsifier pass:
106,912 cuts; full k=6 diagnostic: 516,096 cuts, 0 failures). On main 5847e155:
`C1r = closed conditional (R14) applied to N_root and X`. C1r blocks single_run additivity and every
composition under it.

**X, informally.** σ = one-level root `left ++ [S,S] ++ right` with `2 <= numRuns`; ρ deletes the
second copy; q is the image of p. For every singleton cut (p, s, c) of σ there is (t, d) with
`T(σ.part [p] s c limits) + bound(σ.part (others) (opp s) (k-1-c)) <=`
`T(ρ.part [q] t d limits) + bound(ρ.part (others) (opp t) (k-1-d))`.

**Equivalent form (coordinator).** For every child p, the best singleton value at p (max over side
and coupling) does not drop under contraction.

## Case split and evidence

**(i) p outside the pair.**
- Leaf side: σ's leaf sees the pair as two adjacent level-1 letters and ρ's leaf sees one. Doubled
  external letters contract (closed), so with `ctx_single_level_limits_exact` the leaf thresholds
  should agree at the same (s, c). Prove this first.
- The content is the complement part. It still contains the adjacent pair S S, with the old
  separators at level 2. Same-coupling contraction can FAIL there: level-2 letters inside the span,
  as in the closed refutation `ctx_bound_adjacent_letter_contraction_counterexample` and the P7
  failures. This is why X re-optimizes (t, d).

**(ii) p in the pair.** Both copies map to the same q. Then the leaf and the complement both change.

**Evidence and rescue tables:**
- R13's localized-exchange probes, `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916/runs/r13-sol-20260930/probe_singleton_exchange.py`,
  `exchange-k5-all5.json`, `exchange-k6-all5.json`: 10,084 rescues at k=6, of which 5,568 change
  side only, 3,816 shift -1, 284 shift +1, 416 shift -2.
- P11: `/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-comb-closedform-20260930/p11/`.
- First step: classify the rescues by case (i) / (ii) and by the leaf limits. Look for a DETERMINISTIC
  (t, d) rule, the way the N_root selector search (`/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-n-selector-20261001/`) found
  "an end of the first or last run attains".

## Routes (your choice; log it)

1. **Joint induction on the number of children with C1r and N_root.** Assume both for smaller roots.
   The complement part has fewer children; check whether the closed bridge plus the normalization
   lemma reach it (they need parts of SINGLE-run contexts), or what weaker contraction suffices.
2. **Direct value comparison** using the explicit leaf thresholds and Pascal/three-way allocation:
   `ctx_base_pascal_combine`, `ctx_bound_three_way_base_allocation`, `ctx_bound_cut_le`.
3. **Narrowing:** split X into case (i) and case (ii) nodes, prove the easier one, and leave a sharper
   statement for the other.

- **Done (full):** X closed.
- **Done (narrowing):** X composed from strictly narrower, falsifier-tested registered nodes, at
  least one of them closed.
- **Stuck:** two consecutive attempts fail at the same obligation; write the exact missing inequality
  with a tested witness family. A counterexample to X is also a valid result.

## Checkout and rules

- **Worktree:** `runs/worktrees/sol-12h-20260913`. Create branches from main 5847e155 (use the guarded
  branch job if direct creation is refused). Build missing imported oleans in small guarded jobs
  first.
- **Harness:** `/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260913`.
  - The job memory budget is 40G and two Lean builds may run at once (shared with R16).
  - Time heavy contexts before sizing probes. Never kill at a self-chosen time; `es job review` at
    checkpoints.
- **Commits:** `es node commit`. Statements only via `es node add`.
- **Forbidden:** merging, pushing, touching the primary checkout, a full `es extract`, delegating,
  axioms or native_decide.
- **Rules:** AGENTS.md. `es log` every finding (including failed routes) with job IDs. At the end write
  `MATHEMATICAL-HANDOFF.md` and `REPORT.sol.md` here.
