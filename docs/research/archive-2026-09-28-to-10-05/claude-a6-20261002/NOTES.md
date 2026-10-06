# Decomposable two-side bound at a = 6 (claude-a6-20261002)

**Status.**
- **u = k−2:** proved for every k ≥ 7, except for one lemma, R2-6. R2-6 is SAT-checked at k = 6 and 7 for every |P|. So **decomposable (6,5,7) holds** (paper proof plus SAT).
- **u = k−1 and u = k:** the case tables are done; open cores remain, listed below.
- **Identity:** G = T(5,u,k) + C(k−3,3) = T(6,u,k) − C(k−3,4) = lowerPascalTailReservoir − 1 (`arith.py`).

Notation: "cf" means cap-free. A set is *classic6* if both sides are 5cf and the whole set is 6cf.

## New lemmas (hand proofs)
- **(D) Decoupling, U = A << B.** A cup meeting A has B-points only at its ends (dually for caps); a strong set lies in A, lies in B, or has ≤ α+β points.
  - *Proof:* an interior B-point next to an A-point is the middle of a mixed triple, hence a cap.
  - So U's hypotheses are exactly per-part conditions + endpoint gains + (P). 94,827 random sets: 0 failures.
- **Z6.** A classic6 set with no v-cup has ≤ C(v+1,3) + C(v,3) points.
  - Z = first points of 5-caps ⊆ L; a Z-cup extends by a 5-cap's second point.
- **Marker6.** Assume sides 5cf, no (m+1)-cup, and every m-cup straddles h. Then E or F has no 4-cap, so |A| ≤ C(m,2) + Z6(m) = 2C(m+1,3).
  - *Proof:* template Lemma 5 with every cap one longer; Lemma X yields a 5-cap (o,p,q,e,c″) inside L, X′ one inside R.
  - Exact at m = 3, 4 (SAT). "E or F is a cup" is SAT-refuted at a = 6, even with no strong set.
- **Θ (iterated Z).** Three 4cf blocks with a 5cf union and no v-cup have ≤ C(v,2) + C(v−1,2) + C(v−2,2) points.
- **Gains,** with B = P₁|P₂|P₃ around span A: cap(P₂) ≤ 3; cap(P₁∪P₂), cap(P₂∪P₃) ≤ 4; P₁ ⊆ L ⇒ 4cf; a 5-cap in A forces a⁻ ∈ L, a⁺ ∈ R.

## u = k−2 (G = C(k−1,3) + C(k−3,3))

| case | A | B | slack | status |
|---|---|---|---|---|
| NN1 β≤2 | Z6(k−3) | ≤ k−3 | <0 | hand |
| NN2 β=3 | Z6(k−3) | C(k−2,2) | 0 | hand |
| NN3 β=4, A⊆L | C(k−3,3) | C(k−1,3) | 0 | hand |
| NN4 β=4, A meets R | Z6(k−4) | (k−3)², B classic5 at a⁺ | <0 | hand |
| N1a β=3 | Z6(k−3) | C(k−2,2) | 0 | hand |
| N1b β≤2 | Marker6, m = k−3 | ≤ k−3 | 0 | hand |
| N2a, N2b β≤3 | Z6(k−4) | k−3 or C(k−2,2) | <0 | hand |
| N2c β=4, A 5cf | C(k−3,3) | C(k−1,3) | 0 | hand |
| N2d β=4, A has a 5-cap | Z6(k−4) | Θ(k−2) | 0 | hand |
| N2e β=5, A has a 5-cap | Z6(k−5) | min(Θ+C(k−3,2), C(k−2,2)+(k−3)²) | ≤0 | hand; empty at k=7 |
| N2f β=5, A 5cf | C(k−4,3) | **R2-6** | 0 | SAT at k = 6, 7 |

BN follows by reflection. The arithmetic is checked for k = 7..60 (`cases.py`).

**R2-6.** If B = P|Q with P 4cf and Q 5cf, B is 6cf, has no u-cup and has no strong k-set, then |B| ≤ T(5,u,k) + C(k−4,2).

## u = k−1 (G = C(k−1,3) + k − 2 + C(k−3,3))
- **Close:**
  - NN1 and N1b, via the u = k−2 result.
  - NN2, N1a and N2b, by hand.
  - NN3 and N2c, given the one-sided threshold T(5,k−1,k) as an input.
  - NN4, via the template theorem.
- **Open** (bound needed at k = 7 in brackets):
  - **N1c** (H1-6, A << {b}) [28]: SAT-checked at k = 6.
  - **N2d**: three 4cf blocks with no strong k-set should have ≤ C(k−1,2) + C(k−3,2) + C(k−4,2) points [24]. Θ is 2k−7 too weak. SAT: exact at k = 6; at k = 7, 36 of 97 cut pairs UNSAT, the rest not run.
  - **N2f** = R2-6 at u = k−1 [28]: SAT-checked at k = 6. At k = 7 it is infeasible within one minute.
  - N2e: open only at k = 8, 9.

## u = k
- **Close:** NN1, N1b, N1c and N2a from the u = k−1 and u = k−2 results; the rest given inputs T(4,k,k), T(5,k,k) and G(5,k,k) (the last open except decomposable k = 7).
- **Open:** N2d [25], N2f [29], N2e at k = 8–10.

## R2-6 is a core
- Insert an extremal 5cf set (cups ≤ k−6) into the P|Q gap of any R2-6 instance. The result is a valid N2f instance, so the theorem implies R2-6. H1-6 is likewise the theorem for A << {b}.
- Root-splitting R2-6 (sketch, not audited): an asymmetric marker case closes ("E has no 3-cap or F has no 4-cap", SAT-checked; the mirror fails). Two cores remain:
  - **cup|5cf ≤ T(5,u,k) + (k−5)**, the exact a=6 analogue of template Lemma 6 (SAT at k = 6, 7);
  - a three-block 6cf core, the analogue of R1.

## Sharpest obstacle
- **No fixed structure carries the reservoir C(k−3,3).**
- In R2-6, Z ⊆ P has cups of length ≤ m−2, but the bound needs ≤ m−3. The excess is paid for elsewhere, in variable amounts.
- Samples support **Lemma C6**, which implies R2-6 via |Z| ≤ C(m−2,2) + τ(Z):
  - |F_{m−1}(B∖Z)| + |F_{m−2}(B∖Z)| ≤ C(m,2) + C(m−1,2) − τ(Z);
  - F_j are the start-rows, and τ(Z) is the minimum hitting set of the (m−2)-cups of Z;
  - 0 failures in 84 samples with τ > 0; the end-layer version fails.
- Template Lemma C does not lift: its rows are cups, and its free-edge step uses 4-cap-free propagation, which fails when W is only 5cf.
- H1-6 meets the same obstacle: E and F are only 4cf, and the minimum hitting set of (k−2)-cups can be k−2.
- **Refuted:**
  - a 5-cap transversal of size ≤ C(k−4,2);
  - the one-layer Pascal peel;
  - a per-layer trade-off.

## Evidence (diagnostic only)
- `sat_results.txt` lists every run with sizes and times; scripts are `a6sat.py`, `we_*.py`, `r2*.py`, `cupside_rows.py`, `decouple_test.py`, `cases.py`.
- On general signotopes, (6,5,7) at n = 25 is UNSAT for gaps 0..7 (8..12 not run).
