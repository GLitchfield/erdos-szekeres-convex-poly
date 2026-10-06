# Track C: an equivariant rewriting from partition trees to interval trees

Run `claude-uniform-mechanism-20260928`, Track C. Coordinator: `claude-code:17de3bb4-…`.
Ground rules: exactly those of `RESEARCH-BRIEF.md` (harness jobs with caps of 4 GiB at most,
`es log` for every finding, writes only under `runs/claude-uniform-mechanism-20260928/rewrite/`,
no git and no Lean). Budget: about two hours of wall time. Stop earlier on a clear refutation.

## Background you must read first

- `descent/FINDINGS.md` (Track B). Its Theorem 4 is a paper proof of a per-tree Pascal identity:
  `val_k(t) = val_{k−1}(t↓cap) + val_{k−1}(t↓cup) + N11(t)` for every cut tree `t`
  (a, u ≤ k−1). The couplings shift d ↦ d−1 in the cap world and stay unchanged in the cup world.
  `N11` counts leaves whose cap and cup limits are both 1 (single-vertex leaves).
  `descent/pascal_lib.py` implements the reductions, the tree values and N11.
- `exchange/FINDINGS.md` (Track A), in particular §4.4. For every partition tested, some
  prefix/suffix-rooted interval tree dominated every k-optimal partition tree in three worlds at
  once: k, cap and cup. Domination leaf by leaf and domination in (vc, vu, N11) both failed.
  The scripts are `exchange/leaf_domination.py` and `exchange/leaf_domination_n11.py`.

## The idea

Suppose a rewriting `R` maps every partition tree (any partition at every node) to an interval
tree and satisfies:
1. **Equivariance.** `R(t↓cap) = R(t)↓cap` and `R(t↓cup) = R(t)↓cup`. This holds automatically
   when `R` reads only the tree's combinatorial structure (partitions, orientations, and couplings
   only up to a common translation), never part values or limits.
2. **N11 monotonicity.** `N11(R(t)) ≥ N11(t)` in every world.

Then Theorem 4 gives `val_k(R(t)) ≥ val_k(t)` by induction on k (plus base cases). Hence every
partition tree's value is at most `bound σ`, which is additivity (`ctx_bound_additive`) for all k
at once. Coupling-0 cuts appear in reduced worlds; Track B's open lemma E0 ("coupling-0 cuts
never help", 0 counterexamples) covers them.

## Questions, in order (stop at the first clear refutation and characterize it)

1. **All-worlds domination (a necessary condition).** For every partition tree `t` of small
   contexts, not only k-optimal ones (reductions of optimal trees are arbitrary trees), is there
   one interval tree `τ` with `val(τ↓w) ≥ val(t↓w)` for every Pascal word `w` over {cap, cup}, to
   the depth where contexts become trivial? Test the stronger form too:
   `N11(τ↓w) ≥ N11(t↓w)` for all `w`.
   - Ranges: k = 5 with s ≤ 4; k = 6 with s ≤ 3 or 4; e ≤ 2; two levels; a few (a,u).
   - Report failure counts and minimal failing examples.
2. **The rewriting.** If question 1 holds, search for a value-independent `R` that realizes it.
   Start from natural candidates: recursively replace each node's partition by an interval cut
   chosen from the membership pattern (first alternation, end strip, hull), keeping or
   translating the coupling, and rebuild the subtrees. Measure `N11(R(t)) ≥ N11(t)` and
   equivariance directly.
3. **What the obstruction is**, if question 1 fails: the smallest failing trees, and whether the
   failures sit only at coupling 0, at a = 3 / u = k, or in the bulk.

## Deliverable

Return the full text of `rewrite/FINDINGS.md` in your final report. The harness may block
subagents from writing report `.md` files; if it doesn't, write the file too. Include:
- exact statements;
- evidence tables with job ids;
- failures;
- whether the induction route is alive or refuted;
- the recommended next step.

All results are diagnostic, not Lean-certified.
