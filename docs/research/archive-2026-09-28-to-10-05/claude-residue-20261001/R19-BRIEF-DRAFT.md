# R19 brief (DRAFT v2, 2026-10-01 20:15 local; not launched; needs Gavin's approval)

v1 (`R19-BRIEF-DRAFT.v1.md`) proposed the deque normal form EXTREME-PEEL. It is refuted at k=6
on three-level contexts (job 20261001-191322-86bf03). This version organizes around the
surviving statement.

## Target: PEEL (singleton attainment for all contexts)

For a,u >= 4, at least 2 runs and bound(sigma) >= 2, some child p (any position), side s and
coupling c satisfy

  bound(sigma) = (sigma.part [p] s c).bound + (sigma.part rest s' (k-1-c)).bound.

- **Generalizes:** N_root (one-level roots, registered) and the closed three-child case.
- **Evidence** (diagnostic):
  - two-level contexts at k=5: 102k, failures only at a=3/u=3;
  - two-level contexts at k=6: PEEL-all 11/16 (a,u) pairs, and EXTREME 121k clean, which implies
    PEEL;
  - three-level four-child contexts at k=5, and at k=6 on the 56 EXTREME failures so far: PEEL
    holds in every case.
- **Why it should be true.** The bound is a sum of leaf thresholds, and splitting a run into
  singletons loses nothing (the splitting identity), so an optimal hierarchy can always be
  refined to singleton leaves. PEEL says the refinement can be organized top-down, one child
  first.
- **The obstacle.** Rotating an optimal hierarchy so that a single child comes first makes some
  sibling block see two nested levels instead of one merged level (MERGE direction). Whether
  the loss is absorbed depends on coupling slack; no fixed selector works.
  - At three levels the only optimal first peel can be the middle child of a run, as in
    SSS1L3L2LS mx (1,1,1) at (5,5,6).
  - First/last-child and run-end selectors fail there.

## Work items

1. **FLANK-SWAP (formalization, MERGE-sized).** Swapping two adjacent levels whose letters lie
   on opposite outer flanks preserves the bound under a maxima rule. Verified exactly
   (job -171623-44dbc9). It is useful wherever the peeled child or block is outermost.
2. **Splitting identity (arithmetic, ~100 lines).**
   max_d T(a, min(u-1,k-d), k) + T(min(a-1,d+1), u, k) = T(a,u,k) for a,u >= 3.
   Proved on paper (appendix).
3. **Explain the k=6 middle-of-run cases.** Why is peeling the middle child of SSS optimal in
   SSS1L3L2LS? Compute the leaf and rest limits by hand and relate them to the depth-one
   'inside' structure (a run split by an inner letter). This is the first test of any selector
   rule.
4. **Rotation step with a non-extreme first child.** Generalize FLANK-SWAP to the case where
   the peeled child sits inside the sibling's span, and identify which part still sees opposite
   flanks. Prove the coupling-limited case; classify the threading-limited case with explicit
   inequalities, not lookup tables.
5. **Done criterion:** PEEL closed, or refuted by a counterexample. Narrowings count only with a
   stated reason the pieces are easier.

## Constraints

- Usual rules: es job run, no self-chosen timeouts, es log every finding, handoff at the end.
- Install the local main statements.lock repair first (user action, see
  runs/claude-coordinator-20261001/PENDING.md), or base the worktree on origin/main.

## Appendix: splitting identity proof (unchanged from v1)

- **Classic regime (a+u <= k+3).** Take d in [a-2, k+1-u]. Then the sum is
  T(a,u-1)+T(a-1,u) = C(a+u-5,a-2)+C(a+u-5,a-3) = C(a+u-4,a-2).
- **Window regime (a+u >= k+4).** Take d in [k-u+1, a-2]. Then the two windows
  [k-a, k-d-2] and [k-d-1, u-2] tile [k-a, u-2]; the window formula stays valid at the
  classic boundary.
