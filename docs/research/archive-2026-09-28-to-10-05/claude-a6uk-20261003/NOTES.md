# (6,7,7) at u = k (claude-a6uk-20261003)

**Bottom line.** For decomposable sets, G(6,7,7) = T(5,7,7) + C(4,3) = 26 + 4 = **30**. This matches a6 NOTES
(N2d 25 + Z6(3); N2f 29 + C(3,3)). It is **SAT-certified and attained**, both directly and row by row. No
counterexample was found. SAT is diagnostic (CaDiCaL, no DRAT; r26u1 Lemma DS recursion and
cache). Hand proofs (`PROOFS.md`) are not audited.

## Verdicts at k = 7

| row (u = k) | bound | verdict | evidence |
|---|---|---|---|
| whole G(6,7,7) | 30 | **SAT: ≤30, attained** (223 pairs, 81 tight) | 20261003-002910-527c66 |
| NN1, N1b, N2a (β=2) | 24+6 | hand, from audited G(6,5,7) | tight in 527c66 |
| NN1′, N1c (\|B\|=1, the u=k marker case) | 29+1 | hand, from G(6,6,7) by (P) | G(6,6,7) ≤ 29 SAT: 20261003-004527-8a814e |
| NN2, N1a, N2b | 14+16 | hand + T(4,7,7) = 16 | direct SAT: 17 UNSAT (1.4 s) |
| NN3, N2c | 4+26 | hand + T(5,7,7) ≤ 26 | 20261003-004105-14df57 |
| NN4 | 5+22 (slack 3) | hand + G(5,7,7) ≤ 22 | audit 5kk; 14df57 |
| N2d | 5+25 | **SAT: N2d_k(7) = 25** (1875 pairs, 293 tight); also hand from N2d(7) = 24 | 20261003-002444-b5738f |
| N2e | — | empty at k=7 (hand) | — |
| N2f | 1+29 | **SAT: R2-6_k(7) = 29** (245 pairs, 59 tight); also hand from R2-6(6,7) = 28 and ThC5_k ≤ 24, R3_k ≤ 28, L3S_k ≤ 28 | 20261003-002444-76fef5; 14df57 |

The tight rows of R2-6_k are β=1 (28+1), β=2, β=3, B4P, B4Q, B4S and B5P. B5Q has slack.

## Hand reductions (PROOFS.md; not audited)

- **Lemma U0.** At u = k, a root split with |B| = 1 has α ≤ k−2 by (P). So A is a u = k−1 instance, and the row
  costs F(k−1)+1. **There is no marker core at u = k.** At u = k−1 the same row needed the straddle gate (the
  cores H1-6, MC and N2d-M).
- **Theorem U (all k ≥ 7).** Every row of the G(6,k,k) table closes, given:
  - G(6,k−2,k) and G(6,k−1,k);
  - T(4,k,k), T(5,k,k) and G(5,k,k);
  - N2d_k and R2-6_k;
  - L3S_k (only for N2e, k ≥ 8).
- **N2d_k ⟸ N2d(k)** (the u = k−1 version) together with audited Θ, Lemma 2, two/three cups, T(4,k,k), G(5,k,k)
  and 5kk Lemma 9. Every row has slack ≤ 0. This adds no new leaf.
- **R2-6_k ⟸ R2-6(k−1), N2d_k, ThC5_k, R3_k and L3S_k.** The marker leaves DM and L2 disappear.
- **N2e ⟸ L3S**, at u = k−1 and at u = k, with slack C(k−5,2). Its B is exactly an L3S instance. So the a6 leaf
  "N2e at k = 8, 9" is not an independent core.
- Arithmetic is checked for k = 7..40 in `arith_uk.py`.

## General-k leaves still missing

1. The u = k−1 theorem G(6,k−1,k), with its leaves: H1-6 (R1, R2), N2d-M, MC (DM, L2), ThC5(k), R3(k) and L3S(k).
2. T(5,k,k), the state (5,k,k).
3. ThC5_k, R3_k and L3S_k. Each one's β=1 row closes by U0. Their remaining rows are the same difficulty as at
   u = k−1: for ThC5 the naive bound fails in row "N2, β=3, A ⊆ Y∪Z" at both u. R3_k additionally needs an
   L3-cup lemma at u = k.

## Proof idea and obstacle

- **Why the bound is 30 (= the u = k−1 bound + 1).** The A-side never sees the extra cup length, since
  α ≤ k−1−β ≤ k−2. The +1 is carried by B: a point (β=1), a cup one longer (β=2, using F(k−1) − F(k−2) = k−2),
  or recursively a u = k sub-instance.
- **This is not a profile-free law.** Two cup zones with cross caps ≤ c gain 2 for c ≥ 4 (`probe_cups.py`,
  k = 5, 6, 7). The +1 needs the cap coupling that the table uses.
- **Obstacle.** u = k adds no new difficulty, but it inherits every u = k−1 difficulty:
  - the self-similar marker leaves (a marker nested in a marker, or a marker inside a cup);
  - the three-block a=6 lemmas ThC5, R3 and L3S, which have no hand proof at either u.

  No fixed structure yet carries the reservoir C(k−3,3) through those blocks.

## Files

`PROOFS.md` (hand tables); `arith_uk.py`; `mkprof.py`, `run_list.sh`, `quick.py`, `probe_cups.py`; logs `o_t_*.txt`,
`o_inputs_ds.txt`. `zdp.py`, `hyb.py`, `psat.py`, `hrun*.py` and `pcache/` are copied from r26u1 with paths changed.
Job 20261003-002444-162b8c (direct G(5,7,7) n=23 SAT) was cancelled undecided after ~16 min and replaced by the DS run.
