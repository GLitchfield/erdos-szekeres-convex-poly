# a=6, u=k−1 cores: H1-6, N2d, N2f (claude-a6u1-20261002)

Detailed hand proofs are in `PROOFS.md`; the SAT log is `sat_results.txt`. Everything computational is diagnostic,
not Lean.

## Status

**H1-6 at k = 7 is not an independent core.** It follows by hand from the other two u = k−1 cores, N2d(7) and
R2-6(6,7), plus these inputs:
- G(6,5,7) (audited);
- T(5,6,7);
- the a=5 two-side bound H(7) = 21;
- Marker6, Z6 and ES.

**N2d(k) reduces by hand, for every k, to its marker case N2d-M.** N2d-M(7) is SAT-verified (decomposable): 24 UNSAT
and 23 SAT, with all cut and marker positions in one solve.

So for (6,6,7), only R2-6(6,7) lacks even a SAT check, and the hand proofs of N2d-M(7) and R2-6(6,7) remain open.

## What the marker case means, and why it is true

**Meaning.** In U = A << {b}, the set A carries two gates at once:
- q (deep below) gives a cap gate: sides 5cf, 6cf;
- b gives a cup gate: no (k−1)-cup, and every (k−2)-cup straddles b.

The bound is DG(6,k−1,k) = T(5,k−2,k) + C(k−3,3) + C(k−3,k−4) = T(6,k−1,k) − C(k−3,4) − 1.
- In the word picture, q kills the bottom words that start with U and b kills the one top word D U^{k−3}.
- At k = 7, DG is self-dual: 28 = 32 words minus UUUUU, DDDDD, UDDDD and DUUUU.

**Why it holds: absorption.**
- b lies only in 3-caps (Lemma A1). So B1 ∪ {b} satisfies every block-cap-freeness hypothesis of order ≥ 4 that B1
  does, and every row of the G(6,k−1,k) table whose B-bound is such a lemma loses one point.
- Dually, q lies only in 3-cups, so it can be absorbed into the A-part.
- The primal view fails only when B1 is a cup around b or a singleton. The dual view fails only when A1 is a cap around
  q or a singleton. Both fail at once only when |A| ≤ 10.
- At k = 7 the dual is again DG(6,6,7), so the marker costs exactly one point in one of the two views.

## Results proved by hand

1. **Lemmas A1 and A2 (absorption).**
   - A cap through b has 3 points.
   - If a cup B1 does not contain b in its span, then B1 ∪ {b} is a cup.
2. **Lemma A3 (NN1-R).** In configuration NN with B1 a cup and y1 < b, every (k−3)-cup of A1 straddles y1. Then
   Marker6 gives |A| ≤ G(6,k−2,k) + 1.
3. **Theorem P (all k).** Every row of the G(6,k−1,k) table closes for DG, except two:
   - (R1) N1b-R: B1 is a (k−2)-cup around b;
   - (R2) B1 = {y} with α1 = k−2.
4. **Theorem D (k = 7).**
   - In the dual (flip every label bit), (R2) is row N2f with q* absorbed: R2-6(6,7) ≤ 28.
   - (R1) is row N2d with q* absorbed: N2d(7) ≤ 24, so |A1| ≤ 23 and |A| ≤ 28.
   - For general k the dual is DG(k−1,6,k), whose table is unavailable.
5. **Theorem N (N2d ⟸ N2d-M, all k ≥ 7).** A full root-split table:
   - the N1 and NN cup rows are tight (Θ(k−2) + k−2);
   - N2 with β = 3 uses Lemma 2 plus C(k−1,2), or three cups;
   - N2 with β = 4 uses two-sidedness at a⁺ (giving H(k)), or Lemma 6;
   - NN with β = 3 uses Lemma 2, or two cups.

   The only leftover is the N1 marker row. (N2d is KS profile "111" at a = 5; no union deficiency is needed.)
6. **N2d-M by absorption.** Rerunning the table, every row closes except three leaves:
   - L1 (NN, B1 a (k−2)-cup around b): proved for k ≤ 8 by the crude bound E 4cf;
   - L2 (N1b-R);
   - L3 (double marker).

   L3 is the dominant leaf (239 of 990 replays).

## SAT evidence (decomposable unless noted)

| check | result |
|---|---|
| DG(6,5,6) / DG(6,6,7) | 14 tight; 28 tight; 29 undetermined (106 s) |
| X-route "τ((k−2)-cups) ≤ k−3" | fails in 17/52 tight k=7 models; "X or Y" fails at k=6 |
| N1b-R tight | k=6 n=14, k=7 n=28 SAT; no single point of Y∪{b} absorbable |
| replay7: Theorem P + D, k=7 | 377 instances, 0 failures; dual closes 101 R2 and 74 R1 |
| N2d (variable cuts) | k=6: 14/15; k=7: 24 SAT, 25 undetermined (140 s) |
| N2d table replay | 660 instances (k=6,7,8), 0 failures |
| **N2d-M(7)** | **24 UNSAT (11 s), 23 SAT**; k=6: 14 UNSAT, 13 SAT |
| N2d-M absorption replay | 990 instances, 0 failures |
| WE for 3 blocks; classic 3-block marker m=4 | WE false (SAT at m=4); 14 SAT without strong sets, UNSAT with them |
| R2-6(6,7) | 29 undetermined (97 s); marker case: 27 SAT, 28 undetermined (84 s) |

## Remaining obstacles

- **R2-6(6,7)** (N2f) is now the binding core for (6,6,7).
  - Its marker case is not self-dual: its dual is "G(6,6,7) with a cup-R2 profile".
  - The duality trick does not apply, and the R2-6 table at u = k−1 is still missing.
- **N2d-M by hand.** WE ("E or F is a cup") fails for three blocks, and the classic bound is too weak. The leaves are
  self-similar:
  - L2 means "Θ(k−2) with three cup super-blocks loses 1";
  - L3 is a chain of nested upper singletons.

  Both are instances of one missing general statement: **a gate set with a cup-block profile Π loses exactly the
  dual-KS count C(k−1−q, u−2)**. KS predicts every loss seen here, but KS itself is unproved in the window.
- **General k for H1-6.** Theorem P leaves R1 and R2; R1 is the three-super-block statement at u = k−2. Without
  duality they need the same cup-profile lemma, or the (k−1,6,k) gate tables.
