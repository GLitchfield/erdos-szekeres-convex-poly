# The decomposable two-side bound at (6, 6, 7): audited proof

Audit run `claude-audit-667-20261003`, 2026-10-03. This is an independent, adversarial audit of the sources listed
in §9.

**Verdict: COMPLETE-WITH-REPAIRS, for the correct value G(6,6,7) = 29.**
- **The value.** The two-side bound is G(6,6,7) = T(5,6,7) + C(4,3) = 25 + 4 = 29 = lowerPascalTailReservoir 6 6 7 − 1.
  - It is **not 28**. 28 is DG(6,6,7), the H1-6 bound on |A| (that is, G − 1), and it is also the value of R2-6(6,7).
  - **29 is attained.** I verified 42 explicit decomposable 29-point sets that satisfy every hypothesis (§10.1), so "G(6,6,7) ≤ 28" is false.
  - The coordinator's correction to 29 agrees with this.
- **What is proved.** |U| ≤ 29 for every decomposable U satisfying the (6,6,7) two-side hypotheses. This is exactly what the gate `SingletonLowerPascalTailGate 6 6 7` needs.
  - The proof is by hand, modulo the black boxes of §0.3.
  - Those are: T(5,6,7); the audited a = 5 two-side bound H(7) = 21; the audited G(6,5,7) = 24; and two SAT verdicts, N2d(7) ≤ 24 and R2-6(6,7) ≤ 28.
- **The new hand results are all correct.** Every one was re-derived line by line, and every 4-point step was checked:
  - Lemmas A1–A3 (absorption);
  - Theorems P, D and N;
  - Lemma DS;
  - Theorems R and MC-P;
  - Lemma L2-abs.

  Theorem D is valid only at k = 7 (§4.4). Theorems R and MC-P are correct as reductions, but they are not needed here, because R2-6(6,7) is a black box.
- **Repairs (§9).** None changes a statement or a bound.
  - The (6,6,7) case table, which the a6 notes give only as a summary, is written out row by row.
  - A subset-decomposability lemma is supplied; every absorption step uses it.
  - Adjoining the deep-below point q is justified, with a proof that no strong 7-set passes through q. Theorem D needs both.
  - Theorem D is restated as two direct applications of the black boxes, in place of "the same table applies to the dual".
  - The strong-set notion is bridged (audit 5kk, Lemma B).
  - NN4 needs H(7): with classic5 alone the row fails by 1 at k = 7.
- **Redundancy.**
  - N2d(7) ≤ 24 also follows from Theorem N together with the SAT verdict N2d-M(7) ≤ 23. That route does not use Lemma DS. I re-confirmed N2d-M(7) ≤ 23 with the audited 6k2k encoder: 24 points UNSAT, 23 SAT (§10.3).
  - A direct Lemma-DS SAT run of G(6,6,7) ≤ 29 (coordinator, job 20261003-004527-8a814e, `runs/claude-a6uk-20261003/o_t_g667.txt`) is a further diagnostic cross-check. The hand proof does not use it.
- **Replay.** 6,797 replays of this proof on decomposable instances, with 0 failures (§10). Every row of every table occurs at least once.

---

## 0. Setting, statement, gate, black boxes

The notation and basic facts are those of audit 6k2k (`runs/claude-audit-6k2k-20261002/AUDITED-PROOF-6k2k.md`, §0–§1), restated briefly here.

**Colourings and chains.**
- Points are listed in x-order. A triple x<y<z is a cup or a cap.
- **4-point rule (signotope).** For a<b<c<d, the sequence χ(abc), χ(abd), χ(acd), χ(bcd) changes value at most once.
- **Cups and caps.** A t-cup or t-cap is defined by its consecutive triples. Sets of at most two points are both.
- **Cap-free.** "jcf" means j-cap-free.
- **Strong sets.** These are Lean's `IsStrongPolygonSet`: χ(ijk) = χ(ijl) and χ(ikl) = χ(jkl) for all i<j<k<l. Equivalently, they are cup-cap sets (audit 5kk, Lemma B).
- **Decomposable sets.** These are Lean's `IsDecomposableOn` over an abstract `TripleColoring`.

**Root splits.**
- A root split is U = A << B. Its defining property is (M): a triple meeting both parts is a cup iff its middle point lies in the lower part A.
- Notation: x₀ = min U, x₁ = max U, a⁻ = min A, a⁺ = max A, α = cup(A), β = cap(B).

> **Theorem 667.** Let U be decomposable, split at a gap into U = L|R (either side may be empty), and suppose:
> - (H1) L and R have no 5-cap;
> - (H2) U has no 6-cap;
> - (H3) U has no 6-cup;
> - (H4) U has no strong 7-set.
>
> Then |U| ≤ G := 29.

### 0.1 Arithmetic

All values are from `decomposableThreshold` and `lowerPascalTailReservoir` (Lean), computed in `witness29.py`.

**Thresholds and the target.**
- T(6,6,7) is the window Σ_{j=1}^{4} C(5,j) = 30, since a + u = 12 > k + 3.
- Reservoir = 30 + 1 − C(4,4) = 30, so **G = reservoir − 1 = 29**.
- G = T(5,6,7) + C(4,3) with T(5,6,7) = Σ_{j=2}^{4} C(5,j) = 25 = C(6,3) + 5.
- In general, G(6,k−1,k) = C(k−1,3) + (k−2) + C(k−3,3).

**The two 28s.**
- DG(6,6,7) = G − 1 = T(5,5,7) + 2C(4,3) = 20 + 8 = 28. This is the H1-6 bound on |A|.
- R2-6(6,7) = T(5,6,7) + C(3,2) = 28.

**Values used at k = 7.**

| quantity | value |
|---|---|
| G(6,5,7) | 24 |
| H(7) | 21 |
| N2d(7) | 24 |
| Z6(4) = C(5,3) + C(4,3) | 14 |
| Z6(3) | 5 |
| ES (4cf, no 6-cup) = C(6,2) | 15 |

### 0.2 The gate `SingletonLowerPascalTailGate 6 6 7`

The argument is that of 6k2k §0.2.
- **Setting.** {q} lies deep below `upper` = U, and |U| = 30. {q} ∪ U has no 6-cap, no 6-cup and no strong 7-set.
- **Hypotheses.** Put L = U∩(<q) and R = U∩(>q).
  - A 5-cap D ⊆ L gives the 6-cap D+q, and a 5-cap D ⊆ R gives q+D. So (H1) holds.
  - (H2)–(H4) hold for the subset U.
- **Conclusion.** Theorem 667 gives |U| ≤ 29 < 30.
- **The point q.** In the gate form q is given. Theorem D (§4) uses it, and in the theorem form it can be adjoined (Lemma Q, §1).

### 0.3 Black boxes (used as stated; nothing else is cited)

| name | statement (all decomposable, k = 7) | source | used in |
|---|---|---|---|
| **T5** = T(5,6,7) | no 5-cap, no 6-cup, no strong 7-set ⇒ ≤ 25 | decomposable Theorem 8 state | NN3, N2c; Thm P (NN β₁=4, A₁⊆L; N2 β₁=4, A₁ 5cf) |
| **H(7)** | V = V₁\|V₂ split at a gap, both sides 4cf, V 5cf, no 6-cup, no strong 7-set ⇒ ≤ 21 | audit 567 Theorem = audit 5kk Theorem A (audited, all k ≥ 6) | NN4; Thm P (NN β₁=4, a₁⁺∈R); Thm N |
| **G(6,5,7)** | (6,5,7) two-side hypotheses ⇒ ≤ 24 | audit 6k2k Theorem (audited, no citations) | NN1, N1b, N1c′; Thm P |
| **N2d(7)** [SAT] | V = X\|Y\|Z with 4cf blocks (possibly empty), V 5cf, no 6-cup, no strong 7-set ⇒ ≤ 24 | r26u1, job 20261002-221715-9c6dc8 (Lemma-DS recursion). Alternative: Theorem N + N2d-M(7) | N2d; Thm P (N2 β₁=4, 5-cap); Thm D (R1) |
| **R2-6(6,7)** [SAT] | V = P\|Q, P 4cf, Q 5cf, V 6cf, no 6-cup, no strong 7-set ⇒ ≤ 28 | r26u1, job 20261002-231750-699433 (Lemma-DS recursion; 272 root pairs, 0 violations) | N2f; Thm P (N2 β₁=5); Thm D (R2) |
| N2d-M(7) [SAT, optional] | A with blocks as for N2d (variable cuts), A 5cf, no 6-cup, every 5-cup straddles a gap h, no strong 7-set ⇒ ≤ 23 | a6u1 `vcut.py`; re-confirmed here with enc6 | only on the Theorem N route to N2d(7) |

**Scope of the SAT verdicts.**
- The root profiles were read in `hrun.py` and `profiles_k7.pkl`:
  - R2-6 is `P2(3,4,5,5)` with s = 6;
  - N2d is `P3blocks(3,4,5)` with s = 6.
- Both have no required counts, so empty parts are covered. The strong notion is cup-cap, which is equivalent to Lean's (5kk Lemma B and its converse, §1).

**Other dependencies.**
- **No circularity.** By `decomposableStateUpper_of_lower_gates_at` (strong induction on a+u), T(5,6,7) depends on the lower gates (5,6,7) and (6,5,7) (the latter as the colour-dual upper gate). It does not depend on (6,6,7). I read the Lean statement but did not audit its proof.
- **Also cited (audited, not black boxes):**
  - 6k2k Lemmas 1–11 (ES, classic5, Z6, ZR, Θ, L3, the straddle core, Marker6, Lemma M, R₃, R2-6 at u = k−2);
  - 567 Lemmas 3, 4 and 6, used only by Theorem N.

---

## 1. Basic facts

From 6k2k §1, all re-checked:
- (M), the mixed-triple rule;
- (F0), decomposable sets are signotopes;
- (F1), a cup is a cup set;
- (C), gains: for a cap D ⊆ B and a, a′ ∈ A outside its span, a+D, D+a′ and a+D+a′ are caps, and dually for cups;
- (P), coupling: α + β ≤ k − 1 = 6;
- (D), decoupling: a cup meeting A has B-points only at its two ends, a cap meeting B has A-points only at its ends, and a strong set meeting both parts has at most α + β points;
- the extension step;
- reflection.

New or newly needed facts follow.

**(Sub) Subsets of decomposable sets are decomposable.**
- *Proof.* Induct on the derivation of U.
  - A singleton is clear.
  - For U = A << B and a non-empty S ⊆ U: if S ⊆ A or S ⊆ B, apply induction. Otherwise S = (S∩A) << (S∩B). Both parts are decomposable by induction. `HasDeepBelowSplit` holds because it is the disjointness of the parts together with (M) on mixed triples, and those are mixed triples of U. ∎
- *Remarks.*
  - Audit 5kk §0 states this in label form ("restrict the labels").
  - I found no Lean lemma for it (grep of `ErdosSzekeres/Decomposable.lean`).
  - Every absorption step below needs it: B₁ ∪ {b}, A₁ ∪ {q}, B∖F, A₁ ∪ {y±}.

**(Dual) Colour duality.** Let χ\* be χ with every colour swapped; in labels, flip every bit.
- If U = A << B for χ, then U = B << A for χ\*, because a mixed triple is a χ\*-cup iff its middle point is in B.
- By induction, decomposable sets map to decomposable sets.
- The 4-point rule is preserved.
- Cups and caps are exchanged.
- The strong-set conditions χ(ijk) = χ(ijl) and χ(ikl) = χ(jkl) are invariant.
- (Lean has the corresponding state duality, `decomposableStateUpper_comm`.)

**(SB) Strong-set bridge.**
- Audit 5kk Lemma B: in a signotope, a cup-cap set is middle-determined, hence strong. I re-checked its six 4-point instances.
- Conversely, let S be strong with |S| ≥ 3. Then S is middle-determined. The points of cup type, together with min S and max S, form a cup; the points of cap type, likewise, form a cap.
- So "no strong k-set" means the same under both definitions. This matters because H(7) and 567 Lemma 6 are stated with cup-cap sets.

**(Q) The deep-below point.** Let U satisfy (H1)–(H4) at (6,6,7), and let F = {q} << U, with q placed in the L|R gap.
- In the gate this F is given. In the theorem form it is a new decomposable colouring: q has label 0…, and U keeps its labels prefixed by 1.
- **Shapes through q.** By (M), (x,q,y) is a cup, while (q,x,y) and (x,y,q) are caps.
  - **(Q1)** Every cup through q is a 3-cup with q in the middle. Every cap through q has q as an endpoint.
  - **(Q2)** F has no 6-cap, by (H1) and (H2): D+q with D ⊆ L, and q+D with D ⊆ R. F has no 6-cup, by (Q1) and (H3).
  - **(Q3)** F has no strong 7-set. Let S ∋ q be strong with |S| ≥ 3. Every interior point x ≠ q of S is the middle of a triple (q,x,y) or (y,x,q) inside S, which is a cap. So, because S is middle-determined, every interior point of S∖{q} has cap type, and S∖{q} is a cap of U. Hence |S| ≤ 1 + 5 = 6.
- The a6u1 notes assert the strong-set part of (Q3) without proof. It is the only new ingredient Theorem D needs.

**Reflection.** Reversing the x-order preserves (M), decomposability, cups, caps and strong sets, and swaps L and R.

---

## 2. Cited lemmas (audited; statements as used)

From audit 6k2k:

| lemma | statement used |
|---|---|
| L1 ES | no v-cup and no c-cap ⇒ ≤ C(v+c−4, c−2) |
| L2 classic5 | two 4cf sides, 5cf, no v-cup ⇒ ≤ (v−1)² |
| L3 Z6 | two 5cf sides, 6cf, no v-cup ⇒ ≤ C(v+1,3) + C(v,3) |
| L4 ZR | 4cf \| 5cf, 6cf, no w-cup ⇒ ≤ C(w+1,3) + C(w−1,2) |
| L5 Θ | three 4cf blocks, 5cf, no v-cup (v ≥ 3) ⇒ ≤ C(v,2) + C(v−1,2) + C(v−2,2) |
| L8 Marker6 | 5cf sides, 6cf, no (m+1)-cup, every m-cup straddles a gap h ⇒ ≤ 2C(m+1,3) |
| L11 | R2-6 at u = k−2: ≤ C(k−1,3) + C(k−4,2), which is 23 at k = 7 |

From audit 567 (signotope lemmas; strong sets via (SB)):

| lemma | statement used |
|---|---|
| L3 | two consecutive cups with 4cf union and no u-cup ⇒ ≤ 2u − 3 |
| L4 | three consecutive cups with 4cf union, no u-cup, u ≥ 4 ⇒ ≤ 3u − 6 |
| L6 (R2) | cup \| 4cf, 5cf union, no (k−1)-cup, no strong k-set (k ≥ 5) ⇒ ≤ C(k−1,2) + k − 4 |

---

## 3. Proof of Theorem 667 (the G(6,6,7) table)

**Degenerate cases.**
- If L = ∅ or R = ∅, then U is 5cf, and T5 gives |U| ≤ 25.
- If |U| ≤ 2, there is nothing to prove.

**General case.** Otherwise x₀ ∈ L and x₁ ∈ R. Take the root split U = A << B.
- A and B are decomposable.
- Every subset of U inherits (H1)–(H4) and is decomposable by (Sub).

### NN: x₀ ∈ A, x₁ ∈ B

β ≤ 4, since x₀+D is a cap. α ≤ 4, since C+x₁ is a cup and there is no 6-cup.

| row | condition | bound for A | bound for B | total |
|---|---|---|---|---|
| NN1 | β ≤ 2 | A is a (6,5,7) instance: sides 5cf, 6cf, no 5-cup, no strong 7-set. **G(6,5,7)**: 24 | B is a cup: 5 | **29** |
| NN2 | β = 3 | α ≤ 3 by (P). Z6(4): 14 | B 4cf. ES: 15 | **29** |
| NN3 | β = 4, A ⊆ L | α ≤ 2, A 5cf. ES: C(4,3) = 4 | B 5cf. **T5**: 25 | **29** |
| NN4 | β = 4, a⁺ ∈ R | α ≤ 2, so A is a cap: 5 | see below. **H(7)**: 21 | 26 |

**NN4, the bound for B.** B is two-sided at a⁺:
- B∩(<a⁺) is 4cf, because x₀+D+a⁺ is a cap and every point of B lies after x₀;
- B∩(>a⁺) ⊆ R is 4cf, because a⁺+D ⊆ R.

B is 5cf, has no 6-cup and no strong 7-set. *With Lemma 2 alone, B ≤ 25 and the total is 30. So H(7) is genuinely needed at k = 7.*

**BN** is NN after reflection.

### N1: x₀, x₁ ∈ A

β ≤ 3, since x₀+D+x₁ is a cap.

| row | condition | bound for A | bound for B | total |
|---|---|---|---|---|
| N1a | β = 3 | α ≤ 3. Z6(4): 14 | 4cf: 15 | **29** |
| N1b | \|B\| ≥ 2, β ≤ 2 | β = 2, so α ≤ 4 by (P). (6,5,7) instance: **G(6,5,7)** 24 | cup: 5 | **29** |
| N1c′ | \|B\| = 1, α ≤ 4 | **G(6,5,7)**: 24 | 1 | 25 |
| N1c | \|B\| = 1, α = 5 | **H1-6(7)**: 28 (§4) | 1 | **29** |

### N2: x₀, x₁ ∈ B

α ≤ 3, since x₀+C+x₁ is a cup. β ≤ 5.

| row | condition | bound for A | bound for B | total |
|---|---|---|---|---|
| N2a | β ≤ 2 | Z6(4): 14 | 5 | 19 |
| N2b | β = 3 | Z6(4): 14 | 15 | **29** |
| N2c | β = 4, A 5cf | α ≤ 2: 4 | **T5**: 25 | **29** |
| N2d | β = 4, A has a 5-cap | α ≤ 2, so A is a cap: 5 | see below. **N2d(7)**: 24 | **29** |
| N2e | β = 5, A has a 5-cap | empty: α ≤ 1 gives \|A\| ≤ 1 | — | — |
| N2f | β = 5 | \|A\| = 1, A = {a} | see below. **R2-6(6,7)**: 28 | **29** |

**N2d, the bound for B.**
- The 5-cap of A crosses L|R, so a⁻ ∈ L and a⁺ ∈ R.
- The blocks P₁ = B∩(<a⁻) ⊆ L, P₂ = B∩(a⁻,a⁺) and P₃ = B∩(>a⁺) ⊆ R are 4cf, by D+a⁻ ⊆ L, a⁻+D+a⁺ and a⁺+D ⊆ R.
- B is 5cf.

**N2f, the bound for B.** Reflect so that a ∈ L. Then:
- P = B∩(<a) ⊆ L is 4cf, by D+a;
- Q = B∩(>a) is 5cf, by a+D;
- B is 6cf.

**Exhaustiveness.**
- The four configurations cover every position of x₀ and x₁.
- NN: β ≤ 2, β = 3, or β = 4 with A ⊆ L or a⁺ ∈ R.
- N1: β = 3; β = 2 with |B| ≥ 2; or |B| = 1, split by α ≤ 4 or α = 5.
- N2: β ≤ 2, 3, 4 or 5, with A 5cf or not.
- **All k.** The same table works for every k ≥ 7, with these entries: G(6,k−2,k) + (k−2), Z6(k−3) + C(k−1,2), C(k−3,3) + T5(k), Z6(k−4) + H(k), Z6(k−4) + N2d(k), C(k−4,3) + R2-6(k−1,k), and DG(k) + 1 for N1c. Only the inputs H1-6(k), N2d(k), R2-6(k−1,k) and (for k ≥ 8) N2e(k) are open there. `arith667.py` checks the arithmetic for k = 7..40.

∎ (given §4)

---

## 4. The marker case H1-6(7): |A| ≤ 28

**Setting.**
- U = A << {b} satisfies (H1)–(H4), with x₀, x₁ ∈ A (so b is interior to span A) and cup(A) = 5.
- F = {q} << U as in (Q).

**Facts.**
- **(b)** Every 5-cup of A straddles b, because C+b and b+C would be 6-cups by (M).
- **Lemma A1 (a6u1).** Every cap of U through b with at least 3 points is a 3-cap (y, b, y′) with y < b < y′.
  - *Proof.* By (M), (w,x,b) and (b,x,y) with w, x, y ∈ A are cups. ∎
  - **Absorption.** For Y ⊆ A, the set Y ∪ {b} has the same t-caps as Y for every t ≥ 4, on every interval. It is decomposable (Sub), and it inherits no 6-cup and no strong 7-set from U. So any bound whose hypotheses are block-wise t-cap-freeness with t ≥ 4, plus no 6-cup and no strong 7-set, applies to Y ∪ {b}, and Y loses one point.
  - Dually, by (Q1), q can be absorbed into cup-free blocks in the dual colouring.
- **Lemma A2.** If Y ⊆ A is a cup and b ∉ span Y, then Y ∪ {b} is a cup by (M). Hence |Y| ≤ 4.
- **Lemma A3.** Let A = A₁ << B₁, with x₀ ∈ A₁, x₁ = max A ∈ B₁, B₁ a cup with |B₁| ≥ 2, and y₁ = min B₁ < b. Then A₁ has no 5-cup, and every 4-cup of A₁ straddles y₁.
  - C+x₁ is a cup, so |C| ≤ 4.
  - If a 4-cup C lies left of y₁, then C+y₁+b is a 6-cup: (c,c′,y₁) is a cup by (M) in A, and (c,y₁,b) is a cup by (M) in U.
  - If C lies right of y₁, then y₁+C+x₁ is a 6-cup. ∎

### 4.1 Theorem P (primal reduction; every k ≥ 7)

Run the table of §3 on the root split A = A₁ << B₁, with target G − 1 (28 at k = 7). The marker b is absorbed into B₁ wherever the bound for B₁ is a block-cap lemma. Write BM = B₁ ∪ {b}. α₁ + β₁ ≤ 6 by (P) in A.

The numbers below are for k = 7. The general-k forms are in `arith667.py`.

**NN** (α₁ ≤ 4 and β₁ ≤ 4):

| row | bound for A₁ | bound for B₁ | total ≤ 28 |
|---|---|---|---|
| \|B₁\| = 1 | G(6,5,7): 24 | 1 | 25 |
| β₁ = 2, b < y₁ | 24 | Lemma A2: 4 | 28 |
| β₁ = 2, b > y₁ | Lemma A3 + Marker6 (m = 4; sides 5cf, 6cf): 2C(5,3) = 20 | cup: 5 | 25 |
| β₁ = 3 | α₁ ≤ 3. Z6(4): 14 | BM 4cf (A1). ES: 15 − 1 = 14 | 28 |
| β₁ = 4, A₁ ⊆ L | α₁ ≤ 2, A₁ 5cf: 4 | BM 5cf. **T5** − 1: 24 | 28 |
| β₁ = 4, a₁⁺ ∈ R | 5 | two-sided at a₁⁺ (x₀+D+a₁⁺; a₁⁺+D ⊆ R). **H(7)**: 21 | 26 |

**BN** is NN after reflection. The mirrored A3 straddles y_s = max B₁, using b+y_s+C and x₀+C+y_s.

**N1** (β₁ ≤ 3):

| row | bound for A₁ | bound for B₁ | total ≤ 28 |
|---|---|---|---|
| β₁ = 3 | Z6(4): 14 | BM 4cf: 14 | 28 |
| β₁ = 2, b ∉ span B₁ | α₁ ≤ 4. G(6,5,7): 24 | A2: 4 | 28 |
| β₁ = 2, \|B₁\| ≤ 4 | 24 | 4 | 28 |
| \|B₁\| = 1, α₁ ≤ 4 | 24 | 1 | 25 |

What remains in N1:
- **(R1)** B₁ is a 5-cup with min B₁ < b < max B₁.
- **(R2)** B₁ = {y} and α₁ = 5.

**N2** (α₁ ≤ 3):

| row | bound for A₁ | bound for B₁ | total ≤ 28 |
|---|---|---|---|
| β₁ ≤ 2 | 14 | 5 | 19 |
| β₁ = 3 | 14 | BM 4cf: 14 | 28 |
| β₁ = 4, A₁ 5cf | α₁ ≤ 2: 4 | **T5**(BM) − 1: 24 | 28 |
| β₁ = 4, A₁ has a 5-cap | 5 | BM with blocks at a₁± (4cf, b absorbed). **N2d(7)** − 1: 23 | 28 |
| β₁ = 5 | A₁ = {a}, reflected to a ∈ L: 1 | BM∩(<a) ⊆ L 4cf, BM∩(>a) 5cf, BM 6cf. **R2-6(6,7)** − 1: 27 | 28 |

At k ≥ 8 the row "β₁ = 5 with a 5-cap in A₁" (N2e) is non-empty and needs an N2e(k) bound. At k = 7 it is empty.

**Theorem P.** At every k ≥ 7, given G(6,k−2,k), T5(k), H(k), N2d(k), R2-6(k−1,k), and N2e(k) for k ≥ 8, every row closes with |A| ≤ G − 1 except (R1) and (R2). ∎ (re-derived; correct)

### 4.2 Theorem D, case (R2), k = 7

Here A = A₁ << {y} with cup(A₁) = 5, so |A| = |A₁| + 1. Reflect F so that y < b. Put V = A₁ ∪ {q} ⊆ F, P = V∩(<y) and Q = V∩(>y). In the dual χ\*:

| claim | why |
|---|---|
| P is 4cf\* (no 4-cup) | A 4-cup C ⊆ A₁ left of y gives the 6-cup C+y+b: (c,c′,y) is a cup by (M) in A, (c,y,b) by (M) in U. q lies in no 4-cup (Q1). |
| Q is 5cf\* | y+C would be a 6-cup in A. q as before. |
| V is 6cf\* | A has no 6-cup, and (Q1). |
| V has no 6-cup\* | V has no 6-cap, by (Q2). |
| no strong 7-set | (Q3). |
| V\* is decomposable | (Dual) and (Sub). |

**R2-6(6,7)**, applied to V\* split at y, gives |A₁| + 1 ≤ 28, so |A| ≤ 28. ∎

### 4.3 Theorem D, case (R1), k = 7

Here B₁ = Y = (y₁ < … < y₅) is a 5-cup with y₁ < b < y₅. α₁ ≤ 6 − 2 = 4 by (P).
- **α₁ ≤ 3.** A₁ has no 4-cup and no 6-cap. ES gives |A₁| ≤ C(6,4) = 15, so |A| ≤ 20.
- **α₁ = 4.** Put V = A₁ ∪ {q}, with blocks V∩(<y₁), V∩(y₁,y₅) and V∩(>y₅).
  - Each block is 4cf\*: a 4-cup C in it would give one of the 6-cups C+y₁+b, y₁+C+y₅, b+y₅+C. The triples (c,y₁,b) and (b,y₅,c) are cups by (M) in U; the triples inside A are cups by (M) in A. q is absorbed, by (Q1).
  - V is 5cf\*, since α₁ = 4 and (Q1).
  - V has no 6-cup\* (Q2) and no strong 7-set (Q3), and V\* is decomposable.
  - **N2d(7)** gives |A₁| + 1 ≤ 24, so |A| ≤ 23 + 5 = 28. ∎

**Conclusion.** H1-6(7) holds: |A| ≤ 28. Row N1c of §3 closes.

### 4.4 Duality bookkeeping: why only k = 7

**The dual instance.**
- Primal A is a DG(6, k−1, k) instance:
  - the cap gate from q has sides 5cf and A 6cf (a = 6);
  - the cup gate from b has no (k−1)-cup and every (k−2)-cup straddling b (u = k−1).
- In χ\*:
  - b becomes a lower singleton, giving the cap\* gate. Its sides have no (k−2)-cap\* and A has no (k−1)-cap\*, so a\* = k−1.
  - q becomes an upper singleton, giving the cup\* marker: no 6-cup\* (u\* = 6).
- So A\* is a **DG(k−1, 6, k)** instance, and this equals DG(6, k−1, k) iff k = 7.

**What the dual sets are for general k.**
- (R2): P\* has no (k−3)-cup, Q\* no (k−2)-cup, V\* no (k−1)-cup and no 6-cap. That is an "R2-(k−1)" instance at u\* = 6, which equals R2-6(6,7) only at k = 7.
- (R1): the blocks have no (k−3)-cup and V\* has no 6-cap. That is an N2d-type instance at u\* = 6, which equals N2d(7) only at k = 7.

**Checks that the flip behaves as claimed.**
- The flip swaps every colour (checked on every replayed F).
- It maps decomposable to decomposable (Dual).
- It preserves strong sets.
- The H1-6 hypotheses map exactly onto the instances above.
- The a6u1 claim "the root split becomes A\* = B₁\* << A₁\*, configuration N2, β\* = α₁" is also right. The direct form above does not need it.

---

## 5. Theorem N (N2d(k) ⟸ N2d-M(k); every k ≥ 7)

**Statement.** Let V = X|Y|Z have 4cf blocks and be decomposable, 5cf, with no (k−1)-cup and no strong k-set. Then |V| ≤ N(k) = C(k−1,2) + C(k−3,2) + C(k−4,2), which is 24 at k = 7, provided that N2d-M(k) holds: in V = A << {b} with b interior and cup(A) = k−2, |A| ≤ N(k) − 1.

**Proof** (re-derived; every gain was re-checked).
- If a block is empty, V is two-sided 4cf and H(k) applies. With one block only, ES gives C(k−1,2).
- Otherwise x₀ ∈ X and x₁ ∈ Z. Take the root split V = A << B.

**N1** (x₀, x₁ ∈ A). B is a cup, since x₀+D+x₁ ≤ 4.

| row | bound | total |
|---|---|---|
| \|B\| ≥ 2 | α ≤ k−3. Θ(k−2) + (k−2) | = N |
| \|B\| = 1, α ≤ k−3 | Θ(k−2) + 1 | ≤ N |
| \|B\| = 1, α = k−2 | **N2d-M** | — |

**N2** (x₀, x₁ ∈ B; α ≤ k−4):

| row | bound | slack |
|---|---|---|
| β ≤ 2 | Θ(k−3) + k − 2 | 3k − 12 |
| β = 3, A ⊆ X∪Y or A ⊆ Y∪Z | Lemma 2 (v = k−3): (k−4)², plus ES C(k−1,2) | 0 |
| β = 3, A meets X and Z | see below. Θ(k−3) + 3k − 9 | k − 5 |
| β = 4 (α ≤ k−5), A in one block | B two-sided at a⁺ (D+a⁺, a⁺+D). ES C(k−4,2) + H(k) | 0 |
| β = 4, A meets X and Y | see below. (k−5)² + C(k−1,2) + k − 4 | k − 5 |
| β = 4, A meets Y and Z | mirror of the previous row | k − 5 |
| β = 4, A meets X and Z | three cups (D+a⁻, a⁻+D+a⁺, a⁺+D). 3(k−2) + Θ(k−4) | 4k − 23 |

- **β = 3, A meets X and Z.** B∩(<a⁻) ⊆ X, B∩(a⁻,a⁺) and B∩(>a⁺) ⊆ Z are cups, by D+a⁻, a⁻+D+a⁺ and a⁺+D. B is 4cf, so 567 Lemma 4 (three cups) gives 3k − 9.
- **β = 4, A meets X and Y.** B∩(<a⁻) ⊆ X is a cup and B∩(>a⁻) is 4cf (a⁻+D). 567 Lemma 6 gives C(k−1,2) + k − 4.

**NN** (α ≤ k−3, β ≤ 3):

| row | bound | slack |
|---|---|---|
| β ≤ 2 | Θ(k−2) + k − 2 | 0 |
| β = 3, A ⊆ X∪Y | (k−4)² + C(k−1,2) | 0 |
| β = 3, A meets Z | B∩(<a⁺) is a cup (x₀+D+a⁺) and B∩(>a⁺) ⊆ Z is a cup. 567 Lemma 3: 2k − 5, plus Θ(k−3) | 2k − 9 |

**BN** is NN after reflection.

**Exhaustiveness** holds over the configurations, β, and the set of blocks that A meets.

At k = 7, N2d-M(7) ≤ 23 (SAT, two independent encoders) gives N2d(7) ≤ 24 without Lemma DS. ∎ (correct)

---

## 6. The r26u1 results (re-derived; not needed for Theorem 667, since R2-6(6,7) is a black box)

### 6.1 Lemma DS (the basis of the SAT recursion behind R2-6(6,7) and N2d(7))

Let U = A << B.

**(1) Caps.** The caps of U are the caps of A together with the sequences [a]+D+[a′], where D is a non-empty cap of B, a is absent or an A-point before min D, and a′ is absent or an A-point after max D. Dually, the cups of U are the cups of B together with the sequences [b]+C+[b′].
- **⊆.** By (D), a cap meeting B has A-points only at its ends. Re-derived: an interior A-point next to a B-point is the middle of a mixed consecutive triple, which is a cup by (M); and the nearest-B-point argument excludes any other interior A-point. Its B-part is a subsequence of a cap, hence a cap by (F1).
- **⊇.** Every new consecutive triple of [a]+D+[a′] is mixed, with its middle point in B. This includes (a,d,a′) when |D| = 1. So it is a cap.

**(S) Strong sets.** strong(U) = max(strong A, strong B, α + β).
- ≤ follows from (D).
- ≥ follows from (P), since C ∪ D is middle-determined.

**(2) Profiles.** For zone profiles, the constraints on caps of U that meet B become, on B's sub-zone pair (ρ₁, ρ₂), the bound
min(Cp[z₁][z₂], Cp[y][z₂] − 1 for y ∈ L, Cp[z₁][y′] − 1 for y′ ∈ R, Cp[y][y′] − 2, s − α).
- L is the set of zones that hold an A-point before min D: the earlier zones occupied by A, together with z₁ when σ₁ ∈ {0, +}. R is defined symmetrically.
- This is exactly the set of admissible (a, a′) placements. Existence of one A-point per zone suffices, because any A-point of an earlier zone precedes min D.
- `zdp.refine` implements this formula.

**Corollary (split recursion).** For upper bounds only the direction "U satisfies π ⇒ A satisfies π_A and B satisfies π_B" is needed, and it holds.
- **The interleavings.** The 14 interleavings of f_A ≤ l_A and f_B ≤ l_B give 8 structures with both parts present. Together with E, "A only" and "B only" that is 11, as claimed.
- **Range of α.** The written range max(1, s − maxCp)..min(s−1, maxCu) can be empty, namely when s − maxCp > maxCu. The code (`hyb.children`) then uses α = max(1, hi). That choice is sound, because in that case the strong constraint is slack. The PROOFS text omits this fallback (a note, not an error).
- **Merging zones** is exact, because the zone boundaries are free.

**Brute-force check (`ds_check.py`).** 110,347 random decomposable sets with n ≤ 9, with 0 failures. It checked:
- (1) as a set equality, for caps and cups;
- (S) against the brute-force Lean strong maximum;
- the direction (2) of `zdp.refine` on random zonings.

**Verdict.** Correct.

### 6.2 Theorem R (R2-6 at u = k−1 ⟸ MC, N2d, ThC5, R3, L3S; every k ≥ 7)

Every row was re-derived. The gains are those of 6k2k Lemma 11:
- D+a⁻ ⊆ P makes B∩(<a⁻) a cup;
- a⁻+D+a⁺ and a⁺+D ⊆ Q make the other blocks 4cf;
- a⁻+D makes B∩(>a⁻) 5cf;
- in B5Q, X∪Y = B∩(<a⁻) is 5cf and Y∪Z ⊆ Q.

The new observation is correct: α = k−2 forces |B| = 1, since two points of B form a 2-cap and (P) applies. So B1 and B1m split cleanly.

**B5S** (k ≥ 8):
- F ⊆ B∩(<a⁻), because B∩(<a⁺) and B∩(>a⁻) are 5cf. B∩(<a⁻) ⊆ P is a cup.
- By the extension step (B 6cf, no (k−1)-cup), F has no (k−2)-cup.
- B∖F has the ThC5 blocks.

**Arithmetic.** These identities were checked for k = 7..40:
- ZR(k−3) + C(k−1,2) = R;
- C(k−3,3) + N = R;
- ZR(k−4) + ThC5 = R;
- C(k−5,2) + R3 = R;
- L3S = R − C(k−4,3);
- B5S has slack C(k−4,2) − 3.

**Verdict.** Correct as a reduction.

### 6.3 Theorem MC-P

V = A << {b}, cup(A) = k−2, target R − 1. Absorbing b with Lemma A1 and (Sub) is valid in every block-cap row:
- B3: 4cf;
- B4P: 5cf;
- B4Q: N2d blocks;
- B5Q: L3S blocks;
- B4S and B5P: cup blocks, absorbable when b ∉ span X by A2(b).

The leaves are DM, L2, L6 and L7, exactly as stated. L6 and L7 need b ∈ span X ⊆ P.

**Verdict.** Correct as a reduction.

### 6.4 Lemma L2-abs

(i)
- y± is upper relative to A₁, so every cap through it is a 3-cap.
- A₁ ∪ {y±} keeps the hypotheses "P-part 4cf, Q-part 5cf, 6cf", is strong-free, and is decomposable by (Sub).
- So Lemma 11 applies when there is no (k−2)-cup.

(ii)/(iii)
- C+y⁻+b is a cup, so C+y⁻ has at most k−3 points.
- y⁻+C+y′ would be a (k−1)-cup in A, so max C > y_{k−2}.
- The converse holds by (M).
- (iii) is the mirror, using b+y⁺+C.

(iv) Every (k−3)-cup C of A₁ contains B₁⁻ or B₁⁺ in its span:
- no point of B₁⁻ lies after max C (C+y′+b);
- no point of B₁⁺ lies before min C (b+y+C);
- B₁ cannot have points both before min C and after max C (y+C+y′).

The conclusion follows.

**Verdict.** Correct (replayed on 6 L2 leaves at k = 7).

---

## 7. Arithmetic (k = 7; general k in `arith667.py`, checked for k = 7..40, 0 failures)

| table | target | rows with slack 0 at k = 7 |
|---|---|---|
| Theorem 667 | 29 | NN1, NN2, NN3, N1a, N1b, N1c, N2b, N2c, N2d, N2f |
| Theorem P | 28 | NN absorb, NN β₁=3, NN β₁=4 A₁⊆L, N1 β₁=3, N1 absorb/short, N2 β₁=3, N2 β₁=4 (both), N2 β₁=5 |
| Theorem N | 24 | N1 \|B\|≥2, N2 β=3 adjacent, N2 β=4 one block, NN β≤2, NN β=3 A⊆X∪Y |
| Theorem R | 28 | B2, B3, B4P, B4Q, B4S, B5P, B5Q |
| MC-P | 27 | the same rows |

Rows with slack at k = 7:
- Theorem 667: NN4 −3, N1c′ −4, N2a −10, one-sided −4.
- Theorem P: rows with |B₁| = 1 −3, Marker6 row −3, NN β₁=4 a₁⁺∈R −2.
- (R1) with α₁ ≤ 3: |A| ≤ 20.

---

## 8. Hypothesis, parameter and circularity audit

**Dependency order.**
1. (M), (F0), (F1), (C), (P), (D), (Sub), (Dual), (SB), (Q).
2. The 6k2k and 567 lemmas.
3. Lemmas A1–A3.
4. Theorem P.
5. Theorem D.
6. Theorem 667.

Theorem N is an alternative route to N2d(7). Theorems R and MC-P and Lemma L2-abs are not used. There is no induction on |U|, and no appeal to G(6,6,7) itself.

**Decomposability is used for:**
- root splits of U, A and the black-box sets;
- (P);
- the black boxes, applied to B, B₁ ∪ {b} or (A₁ ∪ {q})\*, each decomposable by (Sub) and (Dual).

**Gaps.**
- The L|R gap is used for:
  - the side conditions (Z6, Marker6, the 6k2k Theorem on A or A₁);
  - the gains inside L or R (NN3, NN4, N2d, N2f, Theorem P);
  - (Q).
- The marker gap at b is separate:
  - (R2) uses it for P\*|Q\* at y and the 6-cups C+y+b;
  - (R1) uses it through y₁ < b < y₅;
  - Lemma A3 uses its own gap at y₁.

**The strong condition** enters only through (P), (Q3) and the black boxes. Its notion is bridged by (SB).

**Holds for all k vs only k = 7.**

| part | scope |
|---|---|
| Lemmas A1–A3, Theorem P, the (6,k−1,k) table of §3, Theorem N, Lemma DS, Theorems R and MC-P, L2-abs | all k ≥ 7, as stated, with their inputs |
| Theorem D, and hence H1-6 by hand | **only k = 7** (§4.4) |
| inputs that are SAT-only at k = 7 | N2d(7) (or N2d-M(7)) and R2-6(6,7) |
| inputs open for k ≥ 8 | H1-6(k), N2d(k), R2-6(k−1,k), N2e(k) |

---

## 9. Findings against the sources

**Sources.**
- a6: `runs/claude-a6-20261002/NOTES.md` (the u = k−1 table).
- a6u1: `runs/claude-a6u1-20261002/{NOTES,PROOFS}.md`.
- r26u1: `runs/claude-r26u1-20261002/{NOTES,PROOFS}.md`.

### Errors

1. **The value "G(6,6,7) = 28" (task statement) is wrong; it is 29.** 28 is DG(6,6,7) (H1-6) and R2-6(6,7). The sources themselves use the right formula (a6: "G = C(k−1,3) + k−2 + C(k−3,3)"; a6u1: target |A| ≤ G − 1 = 28). The 42 explicit 29-point instances refute "≤ 28".

No mathematical error was found in any new theorem.

### Gaps repaired (no statement or bound changes)

2. **a6, u = k−1 table.** Only a status list is given.
   - §3 writes out every row with its bound, including N2a, the split N1c′/N1c, the reflection in N2f, and the empty N2e.
   - NN4 needs H(7): Z6(3) + (k−2)² = 30 > 29 at k = 7.
3. **Subset decomposability (Sub).** It is used implicitly by every absorption step in a6u1 and r26u1. It was not in the 6k2k audit, and no Lean lemma for it was found. Supplied, with a proof.
4. **a6u1 Theorem D.**
   - The "no strong 7-set" claim for A₁\* ∪ {q\*} is unproved. Supplied as (Q3).
   - In the theorem (non-gate) form, q must be adjoined. Supplied as (Q).
   - "The same table applies to the dual" is replaced by two direct applications: R2-6(6,7) on (A₁ ∪ {q})\* split at y, and N2d(7) on (A₁ ∪ {q})\* with blocks at y₁ and y₅. The bounds are the same.
5. **a6u1 Theorem P "all k"** also needs an N2e(k) bound for k ≥ 8. The a6u1 input list mentions N2e; PROOFS calls the row empty, which holds only at k = 7.
6. **Strong-set notion.** H(7) (567) and 567 Lemma 6 use cup-cap sets, while the theorem uses Lean's. Bridged by (SB), via 5kk Lemma B and its converse.
7. **r26u1 Lemma DS corollary.** The α range can be empty. The code's fallback α = max(1, hi) is sound, but it is undocumented.

### Checked and correct as stated

- Lemmas A1, A2 and A3 (both cases).
- Every row of Theorem P (the NN, BN, N1 and N2 tables).
- Theorem D (R1) and (R2): every primal 6-cup argument and the bookkeeping of §4.4.
- Theorem N, every row and slack.
- Lemma DS (1), (S) and (2).
- Theorem R: every row, the B1/B1m split, and B5S.
- MC-P: rows and leaves.
- L2-abs (i)–(iv).
- The identities DG = G − 1 = T(6,k−1,k) − C(k−3,4) − 1, and DG(a,u,k) = T(a−1,u−1,k) + C(k−3,a−3) + C(k−3,u−3) at (6,k−1,k).
- **Not audited (not used):** a6u1 §6, "N2d-M by absorption", including L1 for k ≤ 8.

---

## 10. Computational evidence (diagnostic only; own code, lib6 and enc6 read-only, not Lean, no DRAT)

Every Python run took under one minute. Scripts and outputs are in this directory.

### 10.1 Value

`witness29.py` → `witness29_out.txt`.
- T(6,6,7) = 30, reservoir 30, G = 29, DG = 28.
- Each of the 42 tight 28-point H1-6 models of a6u1 (used as data) gives U = A << {b} with 29 points.
- lib6 verifies, for each U:
  - sides 5cf, U 6cf, no 6-cup, strong ≤ 6;
  - also F = {q} << U: no 6-cap, no 6-cup, strong ≤ 6.

### 10.2 Replay of this proof

**Script.** `replay667.py` (with `run_data.py`, `sample667.py`, `embed29.py`; summary in `agg.py` → `agg_out.txt`).
- The actual root split picks the row of Theorem 667, P, D, N, R or MC-P.
- Every structural claim and every black-box hypothesis is asserted on the actual subsets. This includes:
  - (Q1)–(Q3) on F;
  - the colour swap of the flip;
  - each dual instance's hypotheses in χ\*;
  - Lemma A1, the A3 straddle, and the L2-abs (i)–(iv) equivalences.
- Each bound is asserted on the actual part sizes.
- The recursion goes: N1c → P → D → R / MC / N, and N2d / N2f → N / R.

**Inputs.**
- Own SAT samples of Theorem 667 at n = 8..28, steered to every row and to (R1), (R1 with α₁ = 4) and (R2).
- The a6u1 k = 7 data: 377 DG cores, including the 42 tight ones; 358 N2d sets; 298 N2d-M cores.
- Two tight 29-point N2f instances built from (R2) duals.

**Result.** **6,797 top-level replays, 0 failures.**
- Every row is hit, for example: main N1c 845; P R1 122 (1 with α₁ ≤ 3, 121 with α₁ = 4 → N2d); P R2 207 (→ R2-6); N2d-M leaf 538; MC leaves DM 36, L2 6, L6 1, L7 2; every Theorem R row (B1m 310, …, B5P 79).
- Tight sizes are reached in N1c (29) and N2f (29).

### 10.3 Black-box cross-check

`indep_n2dm.py` re-encodes N2d-M(7) with the audited 6k2k encoder (variable cuts and marker in one CNF).
- n = 24: **UNSAT** in 30 s.
- n = 23: SAT, and the model was re-checked by lib6.
- This independently confirms the a6u1 verdict (`vcut.py`).
- R2-6(6,7) and N2d(7) at 25 are too slow for direct SAT within one minute, so they rest on the r26u1 Lemma-DS recursion.

### 10.4 Lemma DS

`ds_check.py` → `ds_check_out.txt`. 110,347 random decomposable sets, 0 failures (see §6.1).

### 10.5 Arithmetic

`arith667.py` → `arith667_out.txt`. All five tables were checked for k = 7..40, with 0 failures.
