# Hand reductions at u = k (claude-a6uk-20261003)

Notation, basic facts and lemma numbers are those of `runs/claude-audit-6k2k-20261002/AUDITED-PROOF-6k2k.md`:
(M), (C) gains, (P) α + β ≤ k−1, (D), reflection; Lemma 1 (ES), Lemma 2 (classic5, (v−1)²), Lemma 3 (Z6),
Lemma 4 (ZR), Lemma 5 (Θ), Lemma 11 (R2-6 at u = k−2). "jcf" = no j-cap. U = A << B is a root split,
α = cup(A), β = cap(B), a± = min/max A, x₀/x₁ = min/max of the whole set.

At u = k the cup hypothesis "no k-cup" is implied by "no strong k-set" (a cup is strong), so every u = k statement
below has **no cup hypothesis at all**.

Inputs (cited, with their status):
- G(6,k−2,k) = C(k−1,3)+C(k−3,3) (audit 6k2k, hand) and Lemma 11 R_{k−2}(k) = C(k−1,3)+C(k−4,2) (same audit).
- G(6,k−1,k) = C(k−1,3)+(k−2)+C(k−3,3): the u = k−1 theorem (open for general k; k = 7: a6/a6u1/r26u1 + SAT, and
  directly certified here, job 20261003-004527-8a814e).
- T(4,k,k) = 1+C(k−1,2) (Baek, audit 5kk (E1)); G(5,k,k) = 1+C(k−1,2)+C(k−3,2) (audit 5kk Theorem B);
  R2_k := audit 5kk Lemma 9 (P cup | Q 4cf, 5cf, no strong k-set): C(k−1,2)+k−3; audit 5kk Lemma 3 (two cups,
  no 4-cap, no u-cup: 2u−3) and Lemma 4 (three cups: 3u−6). These hold in every signotope / decomposable set.
- T(5,k,k) = C(k−1,3)+k−1: the decomposable state (5,k,k) (input; k = 7 SAT-certified here).
- u = k−1 cores (r26u1 Theorem R, a6u1 Theorem N): R(k) = R2-6(k−1) = C(k−1,3)+(k−2)+C(k−4,2);
  N(k) = N2d(k) = C(k−1,2)+C(k−3,2)+C(k−4,2); ThC5(k) = C(k−1,2)+C(k−3,2)+(k−5); R3(k) = C(k−1,3)+2k−7;
  L3S(k) = R(k) − C(k−4,3).
- Subscript k denotes the same family at u = k (no cup hypothesis), e.g. N2d_k, R2-6_k, ThC5_k, R3_k, L3S_k.

All row arithmetic is checked for k = 7..40 by `arith_uk.py` (`arith_uk_out.txt`).

---

## 1. Lemma U0 (no marker core at u = k)

**Statement.** Let F be any of the families below (G(6,·,k), N2d, R2-6, ...), i.e. a block cap-freeness profile
plus "no strong k-set", decomposable. If the root split of a u = k instance V has |B| = 1, then A is a u = k−1
instance of F, so |V| ≤ F(u = k−1) + 1.

*Proof.* β = 1, so (P) gives α ≤ k−2: A has no (k−1)-cup. A ⊆ V inherits the block cap-freeness and the
strong-set condition, and is decomposable (a root part). ∎

**Why this matters.** At u = k−1 the same row needs |A| ≤ F(k−1) − 1 while (P) only gives "no (k−1)-cup", so the
singleton b must cost a point through the cup gate "every (k−2)-cup straddles b". That is the marker core (H1-6,
MC, N2d-M), the hardest part of every u = k−1 table. At u = k the target is one larger and (P) alone suffices.

Likewise the β = 2 row: B is a cup (≤ k−1 points), α ≤ k−3, so A is a u = k−2 instance and
|V| ≤ F(k−2) + (k−1). This equals F(k−1) + 1 whenever F(k−1) − F(k−2) = k−2 (the top Pascal-tail term
C(k−2,k−3)), which holds for G(6,·,k), R2-6, N2d (via Θ(k−2)) and R3.

---

## 2. Theorem U: the G(6,k,k) table (every k ≥ 7)

**Statement.** Let U be decomposable, U = L|R with L, R 5cf, U 6cf, no strong k-set. Then
|U| ≤ G(6,k,k) = C(k−1,3)+(k−1)+C(k−3,3) = G(6,k−1,k)+1, given the inputs of §0 and N2d_k (§3), R2-6_k (§4),
and, for k ≥ 8, L3S_k (§5).

*Proof.* L or R empty: T(5,k,k) ≤ G. Otherwise configurations NN, BN (mirror), N1, N2 as in the audit.

| row | condition | A | B | slack |
|---|---|---|---|---|
| NN1 | β = 2 (α ≤ k−3 by (P)) | G(6,k−2,k) | cup: k−1 | 0 |
| NN1′ | \|B\| = 1 (α ≤ k−2) | G(6,k−1,k) (Lemma U0) | 1 | 0 |
| NN2 | β = 3 | Z6(k−3) | T(4,k,k) | 0 |
| NN3 | β = 4, A ⊆ L | C(k−3,3) | T(5,k,k) | 0 |
| NN4 | β = 4, a⁺ ∈ R | Z6(k−4) | G(5,k,k) (sides at a⁺ 4cf by x₀+D+a⁺, a⁺+D) | −3 at k=7, −6 at k=8, decreasing |
| N1a | β = 3 | Z6(k−3) | T(4,k,k) | 0 |
| N1b | β = 2 | G(6,k−2,k) | cup: k−1 | 0 |
| N1c | \|B\| = 1 (**the u = k marker case**) | G(6,k−1,k) (Lemma U0) | 1 | 0 |
| N2a | β ≤ 2 (α ≤ k−3 by x₀+C+x₁) | G(6,k−2,k) | cup: k−1 | 0 |
| N2b | β = 3 | Z6(k−3) | T(4,k,k) | 0 |
| N2c | β = 4, A 5cf | C(k−3,3) | T(5,k,k) | 0 |
| N2d | β = 4, A has a 5-cap (a⁻ ∈ L, a⁺ ∈ R) | Z6(k−4) | **N2d_k** on P₁\|P₂\|P₃ | 0 |
| N2e | β = 5, A has a 5-cap (k ≥ 8) | Z6(k−5) | **L3S_k** (§5) | −C(k−5,2) |
| N2f | β = 5, A 5cf (reflect so a⁻ ∈ L) | C(k−4,3) | **R2-6_k** on B∩(<a⁻) \| B∩(>a⁻) | 0 |

The block hypotheses of N2d, N2f are verbatim those of audit §5 (gains D+a⁻, a⁻+D+a⁺, a⁺+D, a⁻+D); the cup
hypothesis there is simply dropped. N2e is empty at k = 7 (a 5-cap needs α ≥ 2, but α ≤ k−6 = 1). ∎

**Rows closed by hand at k = 7 given inputs:** all except N2d, N2f. Inputs needed at k = 7: G(6,5,7) = 24 (audited),
G(6,6,7) = 29, T(4,7,7) = 16, T(5,7,7) = 26, G(5,7,7) ≤ 25 (true value 22).

---

## 3. Proposition N_k: N2d_k ⟸ N2d(k) (every k ≥ 7)

**Statement.** Let V = X|Y|Z, blocks 4cf, V 5cf, no strong k-set, decomposable. If N2d(k) (the u = k−1 version)
holds, then |V| ≤ N(k)+1 = C(k−1,2)+C(k−3,2)+C(k−4,2)+1.

*Proof.* A block empty: V is two 4cf blocks, 5cf: G(5,k,k) ≤ N(k)+1. Otherwise x₀ ∈ X, x₁ ∈ Z; root split.

| config | row | A | B | slack (k=7; general) |
|---|---|---|---|---|
| N1 (β ≤ 2 by x₀+D+x₁) | \|B\| = 1 | N2d(k) (Lemma U0) | 1 | 0 |
| N1 | β = 2 | Θ(k−2) | cup k−1 | 0 |
| N2 (α ≤ k−3 by x₀+C+x₁) | β ≤ 2 | Θ(k−2) | cup k−1 | 0 |
| N2 | β = 3, A in ≤ 2 adjacent blocks | Lemma 2: (k−4)² | T(4,k,k) | 0 |
| N2 | β = 3, A meets X and Z | Θ(k−3) | three cups B∩(<a⁻) ⊆ X, (a⁻,a⁺), (>a⁺) ⊆ Z, B 4cf: 3k−6 | −(k−7) |
| N2 | β = 4, A in one block | C(k−4,2) | G(5,k,k) (two 4cf sides at a⁺) | 0 |
| N2 | β = 4, A in two adjacent blocks (X,Y; Y,Z by reflection) | Lemma 2: (k−5)² | R2_k: B∩(<a⁻) ⊆ X cup, B∩(>a⁻) 4cf | −(k−5) |
| N2 | β = 4, A meets X and Z | Θ(k−4) | three cups: 3(k−1) | −3 at k=7 |
| NN (β ≤ 3 by x₀+D) | \|B\| = 1 | N2d(k) | 1 | 0 |
| NN | β = 2 | Θ(k−2) | cup k−1 | 0 |
| NN | β = 3, A ⊆ X∪Y | (k−4)² | T(4,k,k) | 0 |
| NN | β = 3, A meets Z | Θ(k−3) | two cups B∩(<a⁺) (x₀+D+a⁺), B∩(>a⁺) ⊆ Z: 2k−3 | −(2k−10) |

BN is the mirror of NN. Block facts: D+a⁻ inside a 4cf block, a⁻+D+a⁺ a 5-cap, a⁺+D inside Z, x₀+D a cap. ∎

So **N2d_k has no leaf of its own**: at every k it costs exactly what N2d(k) costs (whose own leaf is N2d-M(k),
a6u1 Theorem N).

---

## 4. Proposition R_k: the R2-6 table at u = k (every k ≥ 7)

**Statement.** V = P|Q, P 4cf, Q 5cf, V 6cf, no strong k-set, decomposable ⇒ |V| ≤ R(k)+1, given R2-6(k−1),
N2d_k, ThC5_k, R3_k, L3S_k (each u = k value = u = k−1 value + 1).

| row | condition | A | B | slack |
|---|---|---|---|---|
| P = ∅ / Q = ∅ | — | — | T(5,k,k) / T(4,k,k) | <0 |
| B1 | β = 1 | R2-6(k−1) (Lemma U0) | 1 | 0 |
| B2 | β = 2 | Lemma 11: R_{k−2} | cup k−1 | 0 |
| B3 | β = 3 | ZR(k−3) | T(4,k,k) | 0 |
| B4P | β = 4, A ⊆ P | C(k−4,2) | T(5,k,k) | 0 |
| B4Q | β = 4, A ⊆ Q | C(k−3,3) | N2d_k (§3) | 0 |
| B4S | β = 4, straddle | ZR(k−4) | ThC5_k | 0 |
| B5P | β = 5, A ⊆ P | C(k−5,2) | R3_k | 0 |
| B5Q | β = 5, A ⊆ Q | C(k−4,3) | L3S_k | 0 |
| B5S | β = 5, straddle (k ≥ 8) | ZR(k−5) | \|F\| ≤ k−2 plus ThC5_k | −2 at k=8 |

Block hypotheses are those of r26u1 Theorem R; the only change is |F| ≤ k−2 in B5S (an F-cup of length k−1
extends to a k-cup or a 6-cap). **The marker core MC(k) of Theorem R (and its leaves DM, L2) does not occur:**
row B1 is Lemma U0. ∎

Partial further step (hand): R3_k ⟸ R3(k), ThC5_k and an L3-cup lemma at u = k (row β = 5, A ⊆ W); the other
rows of R3_k close with slack 0 using Lemma 10, ZR_cup, T(4,k,k), T(5,k,k), G(5,k,k) and (R-a). For ThC5 the naive
bound of row "N2, β = 3, A ⊆ Y∪Z" ((k−4)² plus the 4cf bound for B) exceeds the target by C(k−4,2)−(k−5) already
at u = k−1, so ThC5 needs a new idea at both u.

---

## 5. N2e reduces to L3S (u = k−1 and u = k)

In row N2e (β = 5, A has a 5-cap, so a⁻ ∈ L, a⁺ ∈ R), B = P₁|P₂|P₃ with P₁ = B∩(<a⁻) ⊆ L, P₂ = B∩(a⁻,a⁺),
P₃ = B∩(>a⁺) ⊆ R: each block 4cf (D+a⁻, a⁻+D+a⁺, a⁺+D), P₁∪P₂ 5cf (D+a⁺ would be a 6-cap), P₂∪P₃ 5cf (a⁻+D),
B 6cf. That is exactly the L3S hypothesis. With α ≤ k−6:
- u = k−1: Z6(k−5) + L3S(k) = G(6,k−1,k) − C(k−5,2);
- u = k: Z6(k−5) + L3S_k(k) = G(6,k,k) − C(k−5,2).

So the a6 leaf "N2e at k = 8, 9 (u = k−1), k = 8..10 (u = k)" is not an independent core: it follows from L3S,
which R2-6 needs anyway.

---

## 6. Why the u = k bound is the u = k−1 bound plus one

- In every row, A's cup bound comes from (P) (α ≤ k−1−β ≤ k−2) or from the u = k−2 theorem; A never sees the
  extra allowed cup length. The +1 is carried by B: a single point (β = 1), a cup one longer (β = 2), or a u = k
  sub-instance whose bound is itself +1 (β ≥ 3), recursively.
- This is not a profile-free law: two cup zones with cross caps ≤ c ≥ 4 gain **2** from u = k−1 to u = k
  (`probe_cups.py`, k = 5, 6, 7), because two independent (k−1)-cups fit. The +1 needs the cap coupling that the
  root-split table exploits (e.g. 4cf coupling: cupblock 2k−4 vs 2k−5).
