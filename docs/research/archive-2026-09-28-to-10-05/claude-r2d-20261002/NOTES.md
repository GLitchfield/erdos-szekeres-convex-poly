# Decomposable R2 at u = k: proved for every k ≥ 6 (claude-r2d-20261002)

**Claim.** Let V = P|Q be decomposable, with P a cup left of Q and Q 4-cap-free. If V has no 5-cap, no k-cup
and no strong k-set, then |V| ≤ T* := 1 + C(k−1,2) + k−4 = C(k−3,2) + 3k−8. The proof is by hand, uses no
induction on |V|, and does not need the extra N2e structure.

**SAT check (diagnostic).**
- General R2 is UNSAT at k = 6, n = 14 and at k = 7, n = 20, for every |P| (`cupside_sat.py`).
- The decomposable encoding (`dsat.py`) is likewise UNSAT at those sizes. It is SAT at 13 and 19, with
  |P| ∈ [k−4, k−1].
- The k = 8, n = 27 run was stopped after 3 minutes, so k = 8 is not checked by SAT.

## Toolkit
- **Setup.** Root split V = A << B. α = cup A, β = cap B, x₀ = min V, x₁ = max V, a^± = min/max A.
- **Earlier results.** (M), (C), (P) α+β ≤ k−1, ES, and Lemmas 3, 4 and 6 from the audit. Baek T(4,k,k) =
  1+C(k−1,2). The cupblock lemma: two cups with no 4-cap and no strong k-set have ≤ 2k−4 points (by hand).
- **Z′.** A set made of a cup followed by a 4-cap-free set, with no 5-cap and no u-cup, has ≤ C(u,2)+u−2
  points. The 4-cap first points lie in the cup, and with one more point they form a cup.
- **Lemma R1-dec (new).** Let U = K₁|K₂|K₃ be three decomposable cups with no 4-cap and no strong k-set, k ≥ 6.
  Then |U| ≤ 3k−8. Proof by β:
  - **β = 1:** Lemma 4 with u = k−1 bounds A by 3k−9.
  - **β = 2:**
    - If A misses a block, Lemma 3 gives 2k−7, plus k−1 for B.
    - Otherwise |B| ≤ 3: at most one B-point left of a⁻, one right of a⁺, and one between (else a b b′ a′ is
      a 4-cap). Lemma 4 with u = k−2 bounds A.
  - **β = 3:** A lies inside every 3-cap of B, so B∩(−∞,a⁺) and B∩(a⁻,∞) are cups.
    - A in one block: A is a cup of size ≤ k−4, and the cupblock lemma gives 2k−4 for B.
    - A in two blocks: 2k−9 for A, and |B| ≤ k.
    - A in three blocks: |B| ≤ 3.

## Case table
Notation: M = B∩(a⁻,a⁺) is a cup, Y = B∩Q∩(−∞,a⁻), X = B∩(a⁻,∞). "SAT max" is the per-case maximum at
k = 6/7, where T* = 13/19.

| case | bound on A | bound on B | gap to T* | SAT max |
|---|---|---|---|---|
| β=1 | **Lemma 6** | 1 | 0 | tight |
| β=2 | Z′(k−2) | cup k−1 | 0 | tight |
| β=3, AA | impossible (x₀+D+x₁) | | | |
| β=3, AB, A⊆P | cup k−4 | **Baek** | 0 | tight |
| β=3, AB, a⁺∈Q | Z′(k−3) | two cups, **cupblock** | −1 | 12/18 |
| β=3, BA | Z′(k−3) | 2k−3 (†) | 0 | 11/16 |
| β=3, BB, A⊆P | cup | **Baek** | 0 | tight |
| β=3, BB, a⁻∈P, a⁺∈Q | Z′(k−3) | {x₀} + M\|B∩(a⁺,∞), **cupblock** | 0 | tight |
| β=3, BB, A⊆Q | ES C(k−3,2) | P\|Y\|X, **R1-dec** | 0 | tight |
| β=4, BB, A⊆P | cup k−5 | 1 + **Baek** (4-caps start at x₀) | 0 | tight |
| β=4, BB, a⁻∈P, a⁺∈Q | Z′(k−4) | 1 + Lemma 3 | −(k−4) | –/15 |
| β=4, BB, A⊆Q | ES C(k−4,2) | 3k−6 (‡) | −(k−6) | 12/17 |

**Why the listed parts are cups.** Each of the following would otherwise create a forbidden cap:
- x₀+D+a⁺ would be a 5-cap.
- a^±+D or D+a^± would be a 4-cap inside Q.
- When a⁻ ∈ P, mixed-cup ends force B∩(−∞,a⁻) = {x₀}.

**The case list is exhaustive.**
- β = 4 forces BB.
- AB with A⊆Q is impossible, and so is BA with A⊆P.

**(†) Case β=3, BA.** A 3-cap of B inside Q would give a 4-cap D+x₁ in Q, so every 3-cap of B starts in P.
Let Z₃ be these first points. Then B∖Z₃ is a cup, and Z₃ together with one more point is a cup.

**(‡) Case β=4, BB, A⊆Q.**
- P∪Y and Y∪X have no 4-cap, so the cupblock lemma applies to each and gives 3k−5.
- Equality would force |P| = |X| = k−1 and |Y| = k−3. That extreme is impossible:
  - By Lemma 3(c), p_{k−1}·Y·x₁ is a (k−1)-cup.
  - (p_{k−2},y₁,y₂) is a cap; otherwise p_{k−2}·Y·x₁ with apex p_{k−1} is a strong k-set.
  - Hence p₁…p_{k−2}y₁ is a cup.
  - Finally, (p₁,p_{k−1},y₁) is either a cup, giving the k-cup p₁p_{k−1}·Y·x₁, or a cap, which closes a strong
    k-set.

## Why it holds
- A 3-cap of B confines A to its span. The cup P and the 4-cap-free Q then leave three regimes:
  1. A ⊆ P is a short cup, and B is Baek-bounded.
  2. A straddles the gap: A takes the Z′ surplus, and B collapses to x₀ plus a two-cup block.
  3. A ⊆ Q is classic, and B is a three-cup block.
- The surplus k−4 comes from Lemma 6 (β=1), from Z′ (β=2), or from the short cup A ⊆ P (β ≥ 3).
- R2 contains R1 as its tight case "β=3, BB, A⊆Q", so R1 is unavoidable here. Its decomposable form has the short
  proof above.

## Evidence (diagnostic, not Lean)
- `replay.py` checks every claim and bound per case, including the R1-dec steps. It found 0 violations on:
  - 3,712 SAT-sampled instances at k = 6, 7, 8, covering every sub-case at sizes T*−3..T* (`replay_out.txt`);
  - 2,093 random greedy instances (`replay_greedy_out.txt`).
- R1-dec is UNSAT at 3k−7 for every size vector at k = 6, 7, and its replay finds 0 violations
  (`r1replay_out.txt`).
