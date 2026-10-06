# Audit: BDL and invariant P (claude-audit-bdl-20261003)

Everything below is **diagnostic**: own Python/C/pysat code, no DRAT, no Lean.

## Verdicts

**BDL: no counterexample. Verified exhaustively to n = 9.**
- This covers every decomposable colouring on at most 9 points: 9,716,124 multi-band (X, k) pairs.
- The n ≤ 8 part is 442,930 pairs, the same number the uniform run reports.
- It also covers 6,600 sets at k = 7 (n ≤ 30) and 2,800 at k = 8 (n ≤ 60). These are random, near-extremal, and tight-nested case-R sets of depth 1–3.

**P, as stated (both sides), and P′: no counterexample. Verified to n = 9.**
- There are 8,872,097 interior-core cases.
- The core is (L*, R*), where L* is the largest first point and R* the smallest last point over the maximum caps, with L* < R*.
- The stronger form PF always holds as well: the bottom band can be placed inside the first points of the max caps, and another partition places it inside the last points.

**Validation.**
- My colouring counts are 2, 8, 62, 718, 10,596, 186,888 and 3,816,380 for n = 3..9. For n ≤ 8 they match the catalog enumerator.
- T(a,u,k) equals the exact maximum in all 152 cases with value below 9.

## Paper claims

1. **BDL ⇒ Theorem 8: correct**, but the case cup + cap ≤ k−1 should be added.
   - In that case classical ES gives C(α+β−2, α−1) ≤ C(k−2, j) for some window index j.
   - The arithmetic holds for all k ≤ 20.
2. **DS-induction cases: correct.**
   - Free band, absorption, case R with B classic or one-band (the F-trick), and case R with a one-sided bottom band all check out.
   - Every recipe was verified on every root split for n ≤ 8, with 0 failures.
   - The notes leave the colour-dual case R′ implicit; it needs P′.
   - An arbitrary BDL partition of B is one-sided only 50% of the time, so P is genuinely needed.
3. **BDL + P ⇒ gap bound: repaired.**
   - P only covers cup + cap ≥ k+1.
   - For cup + cap ≤ k, peel F, the first points of the (a−1)-caps. F lies in L and has cup ≤ α−1, so |F| ≤ C(k−4, a−3), and |U∖F| ≤ T(a−1,u,k).
   - Only one side of P is used.
   - **Interface:** Lean's `PascalTailTwoSideBound` quantifies over `OneChangeOn` sets, not decomposable ones. BDL + P therefore needs a decomposable variant of `singletonLowerPascalTailGate_of_twoSideBound`. This is easy, because `upper` is decomposable.
4. **"Missing" is understated** (`ds_prop2.py`, n ≤ 8).
   - Rebuilding X's partition in recipe shape is compatible with P(X) whenever only multi-band children reach band j0.
   - It fails in some instances whenever a classic or **one-band** child, or an absorbed A, sits whole in j0. This happens in more than the three listed cases: both children classic, B whole in j0 in case R, and one-band A (recipe shape fails in 116,182 of 123,488 WC-free instances).

## Convention issues

- The uniform run's main P evidence (about 1,600 samples, `bdl_core.py`) tested "left OR right". Only about 240 samples tested both sides.
- P is trivially false for one-band sets that have a core. "Window" means cup + cap ≥ k for BDL but ≥ k+1 for P.
- The convention that sets of at most 2 points are both cups and caps limits bands 0 and k−2 to one point each, which is consistent with ES. Both codes agree on it.

## Decomposability

BDL, P and P′ hold for **all** 1,232,944 signotopes on 8 points, including 1,046,056 non-decomposable ones. So small cases never show where decomposability is needed. PF, however, fails on 27 non-decomposable 7-point signotopes.

## Literature

- I do not recognise BDL as a published lemma.
- Its bands mirror the Erdős–Szekeres 1960/61 construction, which has blocks of size C(k−2, j) (Morris–Soifer survey).
- For general point sets BDL would imply the ES conjecture.
- I know of no such partition in Szekeres–Peters or in Suk's proof.
- I cannot speak to "Morris–Craft" or to Baek–Balko, so the identification of case R with their gap is unchecked.

## Status

- **Proof idea:** prove BDL ∧ P jointly by DS induction.
- **What works:** the children's band ranges are disjoint.
- **Obstacle:** a classic or one-band child in band j0 must be split by the F-rule, which needs band j0+1 to be free in context.

Evidence: `exh8.txt`, `bdl9_s{0,1}.txt`, `tval.py`, `arith.py`, `ds8.txt`, `ds_prop2_8.txt`, `data/sig8/`, `rand_out/` (`summarize.py`); jobs are listed in `es journal` for this node.
