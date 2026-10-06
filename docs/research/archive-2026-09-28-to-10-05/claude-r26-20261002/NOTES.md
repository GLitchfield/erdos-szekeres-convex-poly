# R2-6, decomposable (claude-r26-20261002)

**Result.** R2-6 at u = k−2 is proved by hand for all k ≥ 6: |V| ≤ C(k−1,3)+C(k−4,2).
- This was the open row N2f of the a6 table. So the decomposable a=6, u=k−2 gate, hence (6,5,7), now has a paper proof.
- The no-strong-set hypothesis is used only through (P): α+β ≤ k−1.
- u = k−1 and u = k remain open; see the obstacle at the end.

**Notation.** V = P|Q has the root split A<<B, with α = cup(A), β = cap(B) and a± = min/max A.
- For a cap D ⊆ B, the sets D+a⁻, a⁻+D and a⁻+D+a⁺ are caps. These fix the cap profile of every part below.
- **ZR(w):** a set with 4cf P-part, 5cf Q-part, 6cf and no w-cup has ≤ C(w+1,3)+C(w−1,2) points; if the P-part is a cup, ≤ C(w+1,3)+(w−2).
  - *Proof:* Z = first points of 5-caps lies in P. Z plus a second point is a cup, and V∖Z is 5cf.

## New lemmas (hand)
**Lemma M.** Let A = A_L|A_R with A_L 4cf and A_R 5cf (6cf not needed). Suppose A has no (m+1)-cup, m ≥ 3, and every m-cup straddles a gap h. Then E has no 3-cap or F has no 4-cap (E/F = first/last points of m-cups).
- *Proof:* audit-567 Lemma 5, with the F-cap (f,q′,p′,p″).
- (S3): d₂ ∈ A_R, since (p,q,e,d₂) is a 4-cap; c″ ∈ A_L, since (c″,f,q′,p′,p″) is a 5-cap.
- Lemma X: (p,q,e,c″) ⊆ A_L. Lemma X′: (d₂,f,q′,p′,p″) ⊆ A_R.
- Cases 1–3 are unchanged.

**Lemma L3.** Let U = X|Y|Z with blocks 4cf, X∪Y and Y∪Z 5cf, U 6cf and no v-cup. Then |U| ≤ C(v,2)+2C(v−1,2); if X is a cup, ≤ C(v,2)+C(v−1,2)+(v−2).
- F = first points of 5-caps lies in X, and W = U∖F is 5cf.
- Z₁ = first points of 4-caps of W lies in (X∖F)∪Y. Z₂ = first points of 4-caps inside Z₁ lies in X∖F.
- |W∖Z₁| ≤ C(v,2) and |Z₁∖Z₂| ≤ C(v−1,2).
- **Key step:** F∪Z₂ ⊆ X has no (v−1)-cup …g′g.
  - If g ∈ F, extending by the 5-cap's second point gives a v-cup or a 6-cap.
  - If g ∈ Z₂ with 4-cap (g,e₂,e₃,e₄) ⊆ Z₁, we get a v-cup or the 5-cap (g′,g,e₂,e₃,e₄) inside X∪Y.

## Case table, u = k−2 (v = k−2)
| case | A | B | slack |
|---|---|---|---|
| β≤2 | Lemma M at b₀∈B (all (k−3)-cups straddle b₀): \|F\| ≤ C(k−3,2) or \|E\| ≤ k−4; remainder ZR(k−3) | cup ≤ k−3 | 0 |
| β=3 | ZR(k−3) | 4cf: C(k−2,2) | 0 |
| β=4, A⊆P | C(k−4,2) | 5cf: C(k−1,3) | 0 |
| β=4, A⊆Q | C(k−3,3) | Θ: B∩P \| B∩Q∩(<a⁻) \| B∩(>a⁻) | 0 |
| β=4, straddle | ZR(k−4) | Θ-cup: (<a⁻)\|(a⁻,a⁺)\|(>a⁺) | 0 |
| β=5, A⊆P | C(k−5,2) | R₃: B∩(<a⁻) cup \| rest 5cf | 0 |
| β=5, A⊆Q | C(k−4,3) | L3 | C(k−4,2)−(k−4) |
| β=5, straddle | ZR(k−5) | cup ≤ k−4, plus Θ-cup | >0 |

- **R₃ (cup|5cf) ≤ C(k−1,3)+k−5** uses the same table with the cup form of ZR. Differences:
  - β=4 straddle and β=5 straddle: one B-point before a⁻, rest Lemma 2 = (k−3)²;
  - β=5, A⊆P: 1+C(k−1,3);
  - β=5, A⊆Q: L3-cup.
- Some rows are empty: β=5 at k=6; β=4 straddle at k=6; β=5 straddle at k=7.
- Inputs: ES, Lemma 2, Lemma 7, Θ, (P), (M)/(C). Arithmetic is checked for k = 6..80 (`arith_out.txt`).

## Evidence (diagnostic only, `sat_results.txt`)
- **L3:** exact without the strong-set condition, for u = 4, 5, 6 (L3 and L3-cup).
- **Lemma M:** UNSAT for m = 3–5, and the instances are non-vacuous.
- **Replay:** `r6replay.py` re-checks every claim on 2,866 decomposable instances at k = 6–9 (1,559 of them at the target size), with 0 failures.

## u = k−1 and u = k
- **R2-6(k−1) rows that close:** β≤2 non-marker, β=3, and β=4 with A⊆P (T(5,k−1,k)).
- **Still needed for R2-6(k−1):**
  - the β=1 marker case, which is tight at k = 6, 7;
  - Θ₂(5,k−1,k): it closes by hand (Lemma 6, Theorem A, Lemma 4) except for its own marker case;
  - Θ₃(5,k−1,k): a marker case, plus a four-cup lemma (4k−14, SAT-exact at k = 6–8);
  - R₃(k−1) and L3(k−1) for small k.
- **u = k:** the β=1 row reduces to R2-6(k−1), β=2 is now closed, and Θ₂(5,k,k) follows by hand from Θ₂(5,k−1,k). So u = k inherits the u = k−1 cores.

## Sharpest obstacle
At u = k−1 every core has a marker case V = A<<{b}: when all (k−2)-cups straddle b, we need |A| ≤ bound−1.
- **E-branch.** Lemma M closes it exactly: E is a cup of ≤ k−3 points, and A∖E is bounded by R2-6(k−2).
- **F-branch.** F is only 4cf, so this fails. In 23 of 127 tight k=6 models, every hitting set of the (k−2)-cups has k−2 points.

**Partial fix.** Root-split A = A₁<<B₁.
- If b lies in a 4cf block Y, then Y∪{b} stays in the same family (b adds only 3-caps), and its bound saves 1.
- This closes β₁ = 3 and β₁ = 4 with A₁ ⊆ P.
- It fails for the double marker B₁ = {y}, where even the E-branch is 1 short, and when b falls inside a cup block.
