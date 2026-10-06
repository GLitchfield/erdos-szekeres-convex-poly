# Proposal: a context-free top-level route for Theorem 8 (draft, needs Gavin's approval)

Claude, 2026-10-02. This builds on `HANDOFF.md` in this directory. All evidence is diagnostic, except where a Lean
receipt is cited.

## The reduction (paper proof)

Let s be decomposable with no a-cap, no u-cup and no strong k-set, and take 3 <= a, u <= k. Induct on |s|. Write
s = L << U for the root deep-below split.

1. **Classic regime** (a+u <= k+3). Then T(a,u,k) = C(a+u-4, a-2). Done by the classical cup–cap theorem
   (`containsCapSet_or_containsCupSet_of_choose_lt`) and `IsDecomposable.isSweepRealizable`.

2. **Window regime, non-nested root.** Suppose the leftmost and rightmost points of s lie in different parts.
   - Every L-cup gets an extension from U and every U-cap one from L, so cup L <= u-2 and cap U <= a-2.
   - Structure (P) (lower cup plus upper cap is strong; already in `ErdosSzekeres.Decomposable`) gives
     cup L + cap U <= k-1.
   - Induction with d = cap U gives |L| <= T(a, min(u-1, k-d), k) and |U| <= T(min(a-1, d+1), u, k).
   - The sum is at most T by **`decomposableThreshold_split_le`** (R19, closed, e2902639).

3. **Window regime, nested root, L inside span U.**
   - If cap U <= a-2: same as step 2 (here L's cups even get two extensions).
   - If cap U = a-1:
     - Then cup L <= k-a, so |L| <= T(a, k-a+1, k) = C(k-3, a-2).
     - Every (a-1)-cap of U crosses L's span. **GAP BOUND** then gives |U| <= T(a-1,u,k) + C(k-3,a-3).
     - The sum is C(k-2,a-2) + T(a-1,u,k) = T(a,u,k). This uses `decomposableThreshold_split_attained`
       (R19, closed, 991b7839) with d = a-2, together with the classic-regime value C(k-2, a-2).

4. **U inside span L.** Mirror of step 3, by colour duality (`decomposableStateUpper_comm`).

## The single open statement

**GAP BOUND** (window regime). Let 3 <= a <= k-1, u <= k and a+u >= k+4. Let U be decomposable with no a-cap, no
u-cup and no strong k-set. Suppose there is a cut index g with points of U on both sides, such that every
(a-1)-cap of U has points on both sides of g. Then

    |U| <= T(a-1,u,k) + C(k-3,a-3).

## Why this frontier is better than the current one

- **It is true.** GAP BOUND follows from Baek–Balko Theorem 8: put an extremal (a, k-a+1, k)-set into the gap.
  The current additivity conjectures are statements about the recursive context bound, and their general forms
  keep failing:
  - end-cut refuted;
  - PEEL refuted by R19 (kernel-certified);
  - my plain shortcuts SP' and Lemma G refuted today.
- **It is exactly the published gap.** The `(4,5,5,1,3)` regression is this case: u' <= k-a forces U to have an
  (a-1)-cap across the inner part.
- **It is minimal.** One set, one virtual interior point, no context words.
- **It has a candidate proof shape.**
  - G(a,u,k) = T(a-1,u,k) + C(k-3,a-3) obeys the Pascal recurrence G = G(a,u-1,k-1) + G(a-1,u,k-1), and the
    gap class is closed under Pascal splits.
  - So GAP BOUND follows from the existence of a *gap-compatible Pascal split*.
  - SAT tests found such a split in every hard nested case generated: about 2.5k random maximal ones, including
    about 640 with |U| = G exactly, plus all decomposable n <= 7.
  - Job 20261002-104722-230b99.

## Proposed work (one Sol trial, R20)

1. **Formalize steps 1–4 as a closed theorem:**

       decomposableStateUpper_all_of_gap_bound : GapBound ∧ GapBound' -> ∀ a u k, ... DecomposableStateUpper a u k

   Register `gap_bound` (and its dual, or derive the dual by duality) as conjecture nodes with a falsifier.
   Ingredients:
   - the deep-below root split and hereditary decomposability (existing);
   - structure (P) (existing);
   - the one-point cup and cap extension lemmas (new, small);
   - R19's split_le and split_attained;
   - the classical theorem;
   - duality.

   This is a real Lean theorem. It replaces `ctx_card_le_bound`/`ctx_bound_additive` as the only gate to
   `decomposableStateUpper_all`.
2. **Then attack `gap_bound`**, starting from the gap-compatible Pascal split. One possible tool: the existing
   one-level context machinery, applied to a single interior lower letter.

## Risks

- GAP BOUND's own proof will probably need positional induction on U's tree, i.e. contexts again. The gain is a
  true, minimal statement and a closed reduction. It is not yet a proof idea for the core.
- Step 1 must handle |L| = 1 and the a = 3 / u = 3 boundaries. The classical theorem covers a+u <= k+3, so the
  window regime needs a,u >= 4.

## CORRECTION (same day, after reading the August history)

This reduction largely duplicates existing work.

- **Experiment 0081** (2026-08-10, `StructuralChargingPascalTails.lean`) already reduced E3 in Lean to two
  parameterized singleton-tail gate families. A child in the binomial tail lowerCard <= C(k-3,a-2), or the dual,
  is exactly my nested case.
- **The structural-charging line** (experiments 0024–0104, `StructuralCharging*.lean`) attacked those gates:
  - closed at (4,5,5): `HasDeepBelowSplit.singleton_root_card_le_seven`;
  - stalled at k=6, where it reached a coarse bound of 23 against the 15 needed.

What is new today, all diagnostic:
- the tail gates are needed only for NESTED roots with a spanning maximal cap; non-nested roots close by R19's
  `split_le`;
- the gate bound G obeys the Pascal recurrence, and gap-compatible / double-cap Pascal splits exist in every hard
  case tested. This is a candidate proof shape for the gates.

I withdraw the "formalize the reduction" recommendation, since it would mostly duplicate 0081. Any trial should
target the tail gates directly, through the gap-compatible Pascal split.
