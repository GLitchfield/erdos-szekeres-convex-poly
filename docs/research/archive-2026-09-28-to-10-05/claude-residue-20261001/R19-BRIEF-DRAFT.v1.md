# R19 brief (DRAFT, not launched; needs Gavin's approval)

> **CORRECTION 2026-10-01 20:05 local:** EXTREME-PEEL2 (and END-PEEL) are REFUTED at k=6 on three-level contexts (non-degenerate, e.g. SSS1L3L2LS mx (1,1,1): bound 8, only the middle child of the run attains it; job 20261001-191322-86bf03). PEEL (singleton attainment, any child) survives and should replace EXTREME-PEEL as the organizing conjecture. See NOTE.md "CORRECTION".


## Goal

Replace the scattered one-level conjectures (N_root, N_ends, X, end-cut) with one organizing
statement, the **deque normal form EXTREME-PEEL2**, and prove its exact ingredients.

Judge progress by whether the induction step is understood and closed, not by helper counts
(AGENTS.md rules).

## Background

Read `runs/claude-residue-20261001/NOTE.md` and `HANDOFF.md`.

**Statement.** For a,u >= 4, at least 2 runs and bound(sigma) >= 2, some first-or-last-child
singleton cut attains bound(sigma).
- Evidence: 102k two-level contexts and 40k three-level contexts at k=5 (all failures have
  bound 1); k=6 and 5-6-child checks are in progress.
- At one-level roots the depth-one closed form is exactly a two-step deque peel.

## Work items, in order

1. **FLANK-SWAP (formalization, MERGE-sized).**
   - Setting: level-1 letters all left of every child, level-2 letters all right of every child
     (or the mirror). Relabel ext 1 <-> ext 2. Maxima: different sides keep each letter's
     maximum; same side use (M, M-1), M = max(m1, 1+m2).
   - Claim: the bound is unchanged.
   - Proof idea: a flank letter is always usable on its side, so extension counts are
     order-independent. For chains using both flanks the strong term is alpha + max(m_first,
     1+m_second) in either order. Hence every descendant's limits agree; finish by induction on
     fuel, as in `ctx_bound_le_merge_same_side_levels`.
   - Falsifier: `runs/claude-labels-20261001/flank_swap.py`.
2. **Splitting identity (arithmetic).** For 3 <= a, 3 <= u:
   max_{1<=d<=k-2} T(a, min(u-1,k-d), k) + T(min(a-1,d+1), u, k) = T(a,u,k).
   - Classic regime: Pascal with d in [a-2, k+1-u].
   - Window regime: window split with d in [k-u+1, a-2], extending
     `decomposableBinomialWindow_pair_le` to an equality.
3. **MIDDLE-DOMINATION (base case, three children).** Peeling the middle child first is never
   better than peeling an end child first. Treat it as an explicit inequality between T-sums with
   nested strong terms, and classify by which constraint binds.
4. **Rotation step (A).** For consecutive blocks A=[p] < B < C, compare ((A,B),C) with
   (A,(B,C)):
   - B is invariant by FLANK-SWAP; A gains a merged level, C loses one.
   - Prove the coupling-limited case: choose nu' in [max(nu, y+1), k-1-x].
   - Classify the threading-limited case against data: 12,532 rescues at k=5, by the other side
     for A or by the mirror rotation at the other end. Produce a rule and prove it.
   - Script: `reroute_rescue.py`.
5. **Interface case (C).** Moving the interface child keeps the optimum in 96% of cases. Find
   what handles the other 4%: moving the other side's interface child, or a direct extreme
   peel.

## Constraints

- Usual rules: es job run for anything over a minute, no self-chosen timeouts, es log every
  finding, and a handoff at the end.
- Register new statements only with es node add on node/ branches. Do not touch other trials'
  worktrees.
- The local main statements.lock repair must happen first (user action); otherwise base the
  worktree on origin/main.

## Proof of the splitting identity (item 2), checked by hand

Let a,u >= 3 and k >= 3.

- **Classic regime (a+u <= k+3).** Any d in [a-2, k+1-u] works; the interval is nonempty in
  this regime and lies in [1,k-2]. Then min(u-1,k-d) = u-1 and min(a-1,d+1) = a-1, and both
  terms are classic:
  C(a+u-5,a-2) + C(a+u-5,a-3) = C(a+u-4,a-2)   (Pascal).
- **Window regime (a+u >= k+4).** Any d in [k-u+1, a-2] works. Then the terms are
  T(a,k-d,k) + T(d+1,u,k).
  - The window formula is valid for both even at the classic boundary: at a+(k-d) = k+2 and
    k+3, and at (d+1)+u = k+2, the classic and window values coincide.
  - So the terms are the sums over sizes [k-a, k-d-2] and [k-d-1, u-2] of C(k-2,j). These tile
    [k-a, u-2], giving T(a,u,k).

In Lean: case split, `decomposableThreshold_eq_choose` / `_eq_window`, `Nat.choose_succ_succ`,
and `Finset.sum_Icc` consecutive splitting. About 100 lines.
