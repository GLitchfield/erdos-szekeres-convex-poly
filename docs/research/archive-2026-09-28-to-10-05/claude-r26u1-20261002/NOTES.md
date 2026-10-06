# R2-6 at u = k−1 (claude-r26u1-20261002)

**Bottom line.** R2-6(6,7) holds for decomposable sets: 29 points are impossible and 28 is attained.
- Marker case (B = {b}): |A| <= 27.
- N2d(7) = 24.
- No counterexample was found.

All computation is diagnostic (CaDiCaL via pysat, no DRAT, not Lean). Hand proofs are in `PROOFS.md`.

## SAT verdicts (decomposable, k = 7)

| statement | claim | result | job |
|---|---|---|---|
| R2-6(6,7) | <= 28 | **max 28; 29 UNSAT** (272 split pairs certified, 64 tight) | 20261002-231750-699433 |
| marker case V = A << {b} | \|A\| <= 27 | **max 27; 28 UNSAT** (b inside P, inside Q, at the cut) | same; tables 20261002-235624-f85215, 20261002-235812-033a69 |
| N2d(7) | <= 24 | **max 24; 25 UNSAT** | 20261002-221715-9c6dc8 |
| H1-6(7) = DG(6,6,7) | <= 28 | follows from a6u1 Theorem D (hand, unaudited) plus the rows above. Direct run: 2895 of 2897 pairs certified, 0 violations, then cancelled as optional | 20261002-231759-fb21a3 |
| sub-lemmas | — | T(5,6,7) = 25, R3 = 27, L3S <= 26 (inside the R2-6 run); ThC5 = 23 (killset run) | same |

**Direct label-SAT shards failed.** Over (p, min A, max A), only 134–176 of 435 shards per cut were decided (job
20261002-214523-3ffcd9). Each shard asks SAT to prove a *sum* of two extremal bounds at once.

## Method: Lemma DS (decoupled split, proved by hand)

For a root split S = A << B:
- the caps of S that meet B are exactly [a] + D + [a′] with D a cap of B; cups are dual;
- strong(S) = max(strong A, strong B, cup A + cap B).

So each part sees only the first and last point of the other part in each zone. This gives the exact recursion
M(π) = max over 11 per-zone patterns and α of M(π_A) + M(π_B).

How it is run:
- the children are decided by profile SAT (`psat.py`), and every model is re-checked with `lib6`;
- `hrun3.py` certifies the root.

Validation:
- the recursion agrees with direct SAT on 5 known profiles and on 1,995 random ones (0 mismatches);
- 9,734 cached maxima were re-checked by direct SAT (0 mismatches).

## Hand results (PROOFS.md)

1. **Lemma DS** and the split recursion.
2. **Theorem R (all k >= 7).** R2-6(k−1) follows from Lemma 11, ZR, ES and T5 together with five sub-lemmas: MC(k),
   N2d(k), ThC5(k), R3(k) and L3S(k). All rows have slack 0 (`arith.py`).
   - **New:** cup(A) = k−2 forces |B| = 1 by (P). So the marker core is exactly V = A << {b}.
3. **Theorem MC-P.** b lies only in 3-caps, so it can be absorbed into every cap-type block. This reduces MC(k) to
   four leaves:
   - DM, a double marker;
   - L2, where B1 is a (k−2)-cup around b;
   - L6 and L7, where b lies inside a cup block (these need b ∈ P).

   At k = 7, DM (26) and L2 (22) are tight, and L6/L7 have slack.
4. **Lemma L2-abs.** L2 closes by absorbing y⁻ or y⁺ (the B1-points next to b), unless A1 has both a left
   (k−3)-cup ending in the gap (y⁻, y⁺) and a right (k−3)-cup starting there. It replays on 63 sampled
   configurations with 0 failures.

## Proof idea, and how far it got

- **Kill sets.** The bound is attained in seven root rows at once: B2, B3, B4P, B4Q, B4S, the marker row and B5P.
  This matches the kill-set count of 30 words minus the 2 words killed by the P-gate.
- **One-point marker cost.** A marker kills exactly one top word at u = k−1. This held in all 62 sampled profiles
  with the marker in a 4cf block. Inside an end cup block it usually costs more.
- **Upper bound only.** The two-sided rule T − |K_cap| − |K_cup| was never exceeded in 2,168 profiles, but it is
  not exact when gates overlap (`tks.py`).
- **Failed shortcut.** The refined Lemma M dichotomy "E or F is a cup" is false in the marker core at n = 10–16,
  even with the strong-set condition (`efcup.py`). A proof of the one-point loss must be size-sensitive or global.

The reduction is complete. Its leaves are proved only at k = 7, by SAT.

## Exact missing statements (general k)

Here V is an R2-6(k−1) set.
1. **DM(k):** if V = (A1 << {y}) << {b} and cup(A1) = k−2, then |A1| <= R(k) − 2.
2. **L2(k):** if V = (A1 << B1) << {b}, with B1 a (k−2)-cup and min B1 < b < max B1, then |A1| <= R_{k−2}(k) − 1.
   After Lemma L2-abs, only the two-cup configuration remains.
3. **ThC5(k), R3(k), L3S(k)** and **N2d-M(k)**, as stated in PROOFS.md §2.

**Obstacle.** Each absorption step leaves self-similar leaves: a marker nested in a marker (DM), or a marker inside a
cup (L2). The straddle core (audited Lemma 7) would finish L2, but it needs all (k−3)-cups to straddle one common
gap, and here they straddle one of two. The kill-set picture predicts the loss of exactly one point, but no lemma
yet carries it.

Reusable code: `zdp.py`, `hyb.py`, `psat.py`, `hrun3.py` and the cache in `pcache/`.
