# The decomposable two-side bound at (5, k, k): audited proof

Audit run `claude-audit-5kk-20261002`, 2026-10-02. Independent, adversarial audit of the sources listed in §9.

**Verdict: COMPLETE-WITH-REPAIRS.**
- The u = k argument assembled from the sources is correct for every k ≥ 6. No lemma is applied
  outside its hypotheses, and nothing is circular.
- The "induction H_{k−1}" of the a5c table is an application of the (5, k−1, k) theorem (Theorem A
  below), at the same k. That theorem is proved independently, without induction (audit 567, re-checked
  here). It is not the (5, k−1, k−1) bound, and it is not an induction on |U|.
- New lemmas re-derived by hand: Z′ (Lemma 7), R1-dec (Lemma 8), and decomposable R2 at u = k
  (Lemma 9, the full case table). Each source proof is right in substance. Six steps were compressed or
  unjustified as written and are repaired here (§9). None of these changes a statement.
- Lemma B is a definitional bridge the sources omit: a cup-plus-cap set is a strong polygon set in Lean's
  sense. It is proved here by hand.
- **Citations:** Baek's Theorem 2.7, and the two-cup-block ("cupblock") lemma 2k−4 as a Lean theorem.
  Caveat (§2): in this checkout I found the cupblock lemma in Lean only for k = 5..9. The appendix
  re-checks its paper proof.
- **No step of the proof rests on computation.** Section 10 is diagnostic only.

---

## 0. Setting, statement, gate

Points are listed in x-order, and x<y refers to that order. For x<y<z, χ(x,y,z) ∈ {cup, cap}.

- **Signotope.** The colouring satisfies the **4-point rule**: for a<b<c<d, the sequence χ(abc), χ(abd), χ(acd),
  χ(bcd) changes value at most once.
- **Cups and caps.** A *t-cup* is x₁<…<x_t whose consecutive triples are all cups; a *t-cap* likewise. Sets of at
  most two points are both. cup(S) and cap(S) are the largest sizes inside S.
- **Cup-cap sets.** A *cup-cap set* is C ∪ D, where C is a cup and D a cap, both running from l = min to r = max,
  with C ∩ D = {l, r}. Its size is |C| + |D| − 2. A cup is a cup-cap set (take D = {l, r}).
- **Strong sets (Lean `IsStrongPolygonSet`).** For all i<j<k<l in S: χ(ijk) = χ(ijl) and χ(ikl) = χ(jkl). Subsets
  of strong sets are strong.
- **Two-side hypotheses (5, u, k).** U is split at a gap into U = L|R (L left of the gap, R right of it; either may
  be empty):
  - (H1) cap(L) ≤ 3 and cap(R) ≤ 3;
  - (H2) cap(U) ≤ 4;
  - (H3_u) cup(U) ≤ u − 1;
  - (H4) U contains no strong set of size k.
- **Classic sets.** X ⊆ U is *classic* if X∩L and X∩R have no 4-cap and X has no 5-cap. Every subset of U is
  classic and inherits (H3_u) and (H4).
- **Decomposable colourings.** Points carry binary labels; a triple is a cup iff its middle point has bit 0 at the
  first coordinate where the three labels differ (labels distinct). This is the same class as Lean's
  `IsDecomposableOn`: a binary split tree gives path labels, and conversely.
  - Every subset of a decomposable set is decomposable (restrict the labels).
  - Reversing the x-order keeps the labels and the middle points, so it maps a decomposable set to a decomposable
    set. It preserves cups, caps, cup-cap sets and strong sets, and swaps L and R.
- **Root split.** Let d be the first coordinate at which the labels of U are not all equal. Put A = {bit 0 at d} and
  B = {bit 1 at d}; we write U = A << B. For |U| ≥ 2 both parts are non-empty.
  - The proof uses only the *deep-below* property (M) below, together with the decomposability of A and B. Any
    split with these properties works.
- **Notation.** x₀ = min U, x₁ = max U, a⁻ = min A, a⁺ = max A, α = cup(A), β = cap(B).

> **Theorem B (the target).** Let k ≥ 6. Let U be decomposable and satisfy (H1), (H2), (H3_k), (H4). Then
> |U| ≤ G(k) := T(4,k,k) + C(k−3,2) = 1 + C(k−1,2) + C(k−3,2) = k² − 5k + 8.

> **Theorem A (used inside Theorem B).** Let k ≥ 6. Let U be decomposable and satisfy (H1), (H2), (H3_{k−1}), (H4).
> Then |U| ≤ H(k) := C(k−1,2) + C(k−3,2) = k² − 5k + 7 = G(k) − 1.

### 0.1 The gate `SingletonLowerPascalTailGate 5 k k`

The definition is in `ErdosSzekeres/StructuralChargingPascalTails.lean`. Suppose `upper` is decomposable, `{q}`
lies deep below `upper`, `|upper| = lowerPascalTailReservoir 5 k k`, and {q} ∪ upper has no 5-cap, no k-cup and no
strong k-set. The gate asserts that this is impossible. Theorem B gives it:

- Put U = upper. L = the points of U before q and R = those after q (q is a point outside U, so this is a gap).
- **(H1).** A crossing triple is a cup iff its middle point is q. So for a 4-cap D ⊆ L, every triple of D ∪ {q}
  is a cap: the triples inside D by (F1) below, and (dᵢ, dⱼ, q) because its middle point is in U. That is a
  5-cap; the case of R is symmetric.
- **(H2), (H3_k), (H4)** hold because U is a subset of {q} ∪ upper. (A Lean cup or cap set has all triples of
  one colour; by (F1) this is the same as the consecutive-triple definition.)
- Theorem B then gives |U| ≤ G(k), which is less than the reservoir. The computation is below.

**Reservoir arithmetic.** For k ≥ 5, a + u = k + 5 ≥ k + 4, so `decomposableThreshold 5 k k` is the window
Σ_{j=k−5}^{k−2} C(k−2, j) = C(k−2,3) + C(k−2,2) + (k−2) + 1. Hence

reservoir − 1 = C(k−2,3) − C(k−3,3) + C(k−2,2) + (k−1) = C(k−3,2) + C(k−1,2) + 1 = G(k),

using C(k−2,3) − C(k−3,3) = C(k−3,2) and C(k−2,2) + (k−2) = C(k−1,2). For example, k = 6 gives G = 14 and
reservoir 15; k = 7 gives 22 and 23. `arith5.py` checks this for k = 6..200.

---

## 1. Basic facts

**(M) Mixed triples.** If a triple meets both A and B, it is a cup iff its middle point lies in A.

*Proof.* The labels of U agree before coordinate d, and the triple has both bits at d. ∎

**(F0) Decomposable colourings are signotopes.**

*Proof.* Induct on |U| through the root split.
- A 4-tuple inside A or inside B is covered by induction.
- A mixed 4-tuple has, by (M), one of the colour sequences below. "·" is the free colour of the unique triple
  inside one part; the B-heavy patterns are the same with cup and cap exchanged.
  - AAAB: ·, cup, cup, cup
  - BAAA: cup, cup, cup, ·
  - ABAA: cap, cap, ·, cup
  - AABA: cup, ·, cap, cap
  - AABB: cup, cup, cap, cap
  - ABAB: cap, cap, cup, cup
  - ABBA: cap, cap, cap, cap
  - BAAB: cup, cup, cup, cup
  - BABA: cup, cup, cap, cap
  - BBAA: cap, cap, cup, cup
- Each sequence changes at most once, whatever "·" is. ∎

**(F1) Cups are cup sets.** If x₁<…<x_t is a cup, every triple of it is a cup. Hence a set is a cup iff no three of
its points form a cap, and every subset of a cup is a cup. The same holds for caps.

*Proof.* Induct on t; t = 3 is trivial. For t ≥ 4, every triple avoiding x_t or avoiding x₁ is a cup by
induction, so only the triples (x₁, x_j, x_t) remain.
- For j < t−1, the 4-point rule on (x₁, x_j, x_{t−1}, x_t) reads cup, ?, ?, cup, so both unknowns are cups.
- For j = t−1, use (x₁, x₂, x_{t−1}, x_t) in the same way. ∎

**(F2) Cup-cap sets.**
- **(a)** If C is a cup and D a cap, both from l to r, then C ∩ D = {l, r}. A common interior point x would make
  χ(l,x,r) both a cup and a cap, by (F1).
- **(b)** Deleting an interior point of C or of D leaves a cup-cap set, by (F1).

**Lemma B (cup-cap sets are strong; new, the bridge to Lean).** In a signotope, every cup-cap set S = C ∪ D is
middle-determined: a triple (a, x, b) of S is a cup if x ∈ C° = C ∖ {l, r}, and a cap if x ∈ D° = D ∖ {l, r}.
Consequently S is strong, since χ(ijk), χ(ijl) share the middle point j and χ(ikl), χ(jkl) share k.

*Proof.* Exchanging cup and cap preserves the 4-point rule, so it suffices to take x ∈ C°. Let a < x < b in S.
Everything happens inside {l, a, x, b, r}; facts marked C or D come from (F1) applied to the cup C or the cap D.
- **a, b ∈ C.** (a,x,b) is a cup by (F1).
- **a = l, b ∈ D°.** The 4-point rule on l<x<b<r reads ?, cup (C), cap (D), ?. Two changes are forbidden, so
  χ(l,x,b) = cup and χ(x,b,r) = cap.
- **a ∈ C°, b ∈ D°.**
  - The previous case gives χ(x,b,r) = cap.
  - The rule on l<a<b<r reads ?, cup, cap, ?, so χ(a,b,r) = cap.
  - Then the rule on a<x<b<r reads ?, cup (C), cap, cap, so χ(a,x,b) = cup.
- **a ∈ D°, b ∈ C.** This is the mirror image of the two previous cases.
- **a, b ∈ D°.**
  - The rule on l<a<x<r reads ?, cap, cup, ?, so χ(l,a,x) = cap.
  - The rule on l<x<b<r gives χ(l,x,b) = cup.
  - The rule on l<a<x<b reads cap, cap (D), cup, ?, so χ(a,x,b) = cup. ∎

**Consequence.** By Lemma B and the monotonicity of strong sets, (H4) excludes every cup-cap set of size ≥ k. All
"strong k-set" contradictions below exhibit a cup-cap set of size ≥ k.

**(F3) 4-cap-free propagation.** Let X have no 4-cap.
- If (w,x,y) is a cap in X, then (x,y,z) is a cup for every z ∈ X with z > y.
- If (x,y,z) is a cap, then (w,x,y) is a cup for every w ∈ X with w < x.

**(C) Gaining points across the split.**
- Let D ⊆ B be a cap and a, a′ ∈ A. If a < min D, then a+D is a cap. If a′ > max D, then D+a′ is a cap. If both,
  then a+D+a′ is a cap.
- Dually, let C ⊆ A be a cup and b, b′ ∈ B. Then b+C, C+b′ and b+C+b′ are cups whenever b and b′ lie outside the
  span of C on the corresponding sides.

*Proof.* The only new consecutive triples are mixed, and their middle points lie in B (respectively A). Apply
(M). ∎

**(P) Coupling.** If U (any decomposable set with a root split) has no strong k-set, then α + β ≤ k − 1.

*Proof.* Take a largest cup C of A and a largest cap D of B. Let l = min(C∪D) and r = max(C∪D).

| where l and r lie | the cup | the cap |
|---|---|---|
| both in D | d₁ + C + d_β | D |
| l in C, r in D | C + d_β | c₁ + D |
| l in D, r in C | d₁ + C | D + c_α |
| both in C | C | c₁ + D + c_α |

- Each entry is a cup or a cap by (C).
- The cup and the cap run from l to r and share only l and r.
- So C ∪ D is a cup-cap set of size α + β. The degenerate sizes α = 1 and β = 1 are covered by the same table.
- By Lemma B and (H4), α + β ≤ k − 1. ∎

---

## 2. Cited results

**(E1) Baek, Theorem 2.7 (external citation).** arXiv:2206.04260; formalized as `theorem main` in
`/home/gavin/git/erdos-tuza-valtr/ErdosTuzaValtr/Main/Main.lean`.
- **Statement.** For n ≥ 0 and any finite S, if |S| ≥ C(n+2,2) + 2, then S has a 4-cap or an (n+3)-gon.
- **Applicability.** The model `Config` is an arbitrary ternary predicate on a linear order, so it applies to our
  colourings.
- **What a gon is.** An (n+3)-gon is a cap list and a cup list with common first and last points and lengths
  summing to n+5. In a signotope the interiors are disjoint by (F2a), so it is a cup-cap set of size n+3. A
  k-cup is one by `ncup_is_ngon`.
- **Form used (k ≥ 6, n = k−3).** If X has no 4-cap and satisfies (H4), then |X| ≤ T(4,k,k) := 1 + C(k−1,2).

**(E2) Two-cup-block ("cupblock") lemma (Lean-closed, cited).**
- **Statement.** Let k ≥ 5 and X = P ∪ Q, where P < Q are cups, X is a signotope, X has no 4-cap and no strong
  k-set. Then |X| ≤ 2k − 4.
- **Lean form.** `DiagonalCupBlocksForce4kk k` (`ErdosSzekeres/StructuralChargingPascalCupBlocks.lean`): blocks of
  sizes (k−2, k−1) or (k−1, k−2) contain a 4-cap, a k-cup or a strong k-set.
- **Counting step.** If |P| + |Q| ≥ 2k − 3, then either a part has ≥ k points (a k-cup), or both have ≤ k − 1 and
  P ∪ Q contains such a sub-block.
- **Status.** The caller states that this is closed in Lean for every k ≥ 5. In this checkout I found
  `diagonalCupBlocksForce4kk_five/six/seven/eight` and the k = 9 certificate
  (`DiagonalCupBlocksK9Certificate.lean`), but no theorem for general k. If the general theorem is not on the
  branch that consumes this proof, the paper proof in the Appendix (re-checked) is the fallback.
- **Use here.** Only inside Lemma 8 (β = 3, one block) and Lemma 9 (β = 3 BB mixed, and (‡)).

---

## 3. Lemmas valid in every signotope

### Lemma 1 (Erdős–Szekeres for no 4-cap, in layer form)
**Statement.** Let X have no 4-cap. Put Lay_j = {x : the longest cup of X ending at x has j points}. Then Lay_j is
a cup with at most j points, so if X has no v-cup then |X| ≤ C(v,2). The mirror statement holds for the rows
F_j = {x : the longest cup *starting* at x has j points}.

*Proof.*
- Lay₁ = {min X}.
- Let j ≥ 2, and suppose x<y<z in Lay_j form a cap. Let w be the point before x on a j-cup ending at x.
  - If (w,x,y) were a cup, y would end a (j+1)-cup.
  - So (w,x,y,z) is a 4-cap, a contradiction.
- So Lay_j is a cup by (F1). It ends at a point whose longest cup has j points, so |Lay_j| ≤ j. ∎

### Lemma 2 (Z bound, classic two-side)
**Statement.** Let X be classic with no v-cup (v ≥ 2). Then |X| ≤ (v−1)².

*Proof.* Let Z be the set of first points of 4-caps of X.
- A 4-cap of X meets both sides, so its first point is in L. Hence Z ⊆ X∩L has no 4-cap.
- X∖Z has no 4-cap, so |X∖Z| ≤ C(v,2) by Lemma 1.
- Z has no (v−1)-cup. Suppose z₁<…<z_{v−1} were one, and let (z_{v−1}, a, b, c) be a 4-cap.
  - If v−1 ≥ 2 and (z_{v−2}, z_{v−1}, a) is a cap, then (z_{v−2}, z_{v−1}, a, b, c) is a 5-cap.
  - Otherwise z₁…z_{v−1}a is a v-cup.
- So |Z| ≤ C(v−1,2) by Lemma 1, and |X| ≤ (v−1)². ∎

### Lemma 3 (two cups)
**Statement.** Let X = x₁<…<x_a and Y = y₁<…<y_b be cups with X < Y, and suppose X∪Y has no 4-cap and no u-cup.
- (a) If a, b ≥ 1, then X+y₁ is a cup or x_a+Y is a cup.
- (b) a + b ≤ 2u−3.
- (c) If a = u−1, then x_a+Y is a cup; if b = u−1, then X+y₁ is a cup.

*Proof.*
- (a) If a, b ≥ 2, then (x_{a−1}, x_a, y₁) and (x_a, y₁, y₂) are not both caps, since they would form a 4-cap. If
  a = 1 or b = 1, one of the two sets has only two points.
- (b) By (a), a ≤ u−2 or b ≤ u−2, and both are ≤ u−1.
- (c) Otherwise X+y₁, respectively x_a+Y, would be a u-cup. ∎

### Lemma 4 (three cups)
**Statement.** Let P < Q < R be cups with sizes p, q, r, with no 4-cap and no u-cup in P∪Q∪R, where u ≥ 4. Then
p + q + r ≤ 3u − 6.

*Proof.* Each part has ≤ u−1 points; if all have ≤ u−2 we are done.
- **q = u−1.**
  - Lemma 3(c) gives the cups P+q₁ and q_b+R. They are separated, since q₁ < q_b.
  - Lemma 3(b) then gives (p+1)+(r+1) ≤ 2u−3.
- **q ≤ u−2 and p = u−1.**
  - Lemma 3(c) on P|Q and on P|R gives that p_a+Q and p_a+R are cups. Hence r ≤ u−2.
  - It remains to rule out q = r = u−2 ≥ 2. Apply Lemma 3(a) to Q|R.
    - If Q+r₁ is a cup, then p_a q₁…q_b r₁ is a u-cup.
    - If q_b+R is a cup, then P | (q_b+R) is a block of 2u−2 points, against Lemma 3(b).
- **q, p ≤ u−2 and r = u−1.** This is the mirror image. ∎

### Lemma 5 (marker lemma)
**Statement.** Let A have 4-cap-free sides A∩L, A∩R and no (m+1)-cup, with m ≥ 3. Let h be a gap of A (not
necessarily the L|R gap) such that every m-cup of A has points on both sides of h. Let E and F be the sets of first
and last points of the m-cups.
- **(WE)** E or F contains no 3-cap.
- **(Bound)** If A also has no 5-cap, then |A| ≤ m(m−1).

*Proof of WE.* Suppose (p,q,e) is a 3-cap with e ∈ E, and (f,q′,p′) a 3-cap with f ∈ F. Let D = (e, d₂, …, d_m)
and C = (…, c′, c″, f) be m-cups, where c′ = c_{m−2} and c″ = c_{m−1}.
- **(S1)** (x,e,d₂) is a cap for every x < e, and (c″,f,y) is a cap for every y > f. Otherwise x+D or C+y is an
  (m+1)-cup.
- **(S2)** e < h < f.
- **(S3)** By (S1), (p,q,e,d₂) and (c″,f,q′,p′) are 4-caps. Each must cross L|R, so p, c″ ∈ L and d₂, p′ ∈ R.
  Hence c″ < d₂.
- **(S4)** No m-cup lies on one side of h. Therefore:
  - (i) (c′,c″,y) is a cap for c″ < y < h;
  - (ii) (x,d₂,d₃) is a cap for h < x < d₂;
  - (iii) (c′,c″,d₂) and (c″,d₂,d₃) are not both cups, since c₁…c″d₂…d_m would have 2m−2 ≥ m+1 points.
- **Lemma X.** e < c″ together with (c″,d₂,d₃) a cap is impossible.
  - The rule on e<c″<d₂<d₃ reads ?, ?, cup, cap, so χ(e,c″,d₂) = cup.
  - The rule on q<e<c″<d₂ reads ?, cap, ?, cup, so χ(q,e,c″) = cap.
  - Then (p,q,e,c″) is a 4-cap inside L.
- **Lemma X′.** d₂ < f together with (c′,c″,d₂) a cap is impossible.
  - The rule on c′<c″<d₂<f reads cap, cup, ?, ?, so χ(c″,d₂,f) = cup.
  - The rule on c″<d₂<f<q′ reads cup, ?, cap, ?, so χ(d₂,f,q′) = cap.
  - Then (d₂,f,q′,p′) is a 4-cap inside R.
- **Cases**, by (S4iii):
  1. **(c′,c″,d₂) is a cup, so (c″,d₂,d₃) is a cap.**
     - e = c″ is impossible, since (e,d₂,d₃) is a cup.
     - If c″ < e, the rule on c′<c″<e<d₂ reads ?, cup, ?, cap, so χ(c′,c″,e) = cup. This contradicts (S4i).
     - If e < c″, Lemma X applies.
  2. **(c″,d₂,d₃) is a cup, so (c′,c″,d₂) is a cap.**
     - d₂ = f contradicts (S1).
     - If f < d₂, the rule on c″<f<d₂<d₃ reads cap, ?, cup, ?, so χ(f,d₂,d₃) = cup. This contradicts (S4ii).
     - If d₂ < f, Lemma X′ applies.
  3. **Both are caps.**
     - Lemmas X and X′, with e ≠ c″ and f ≠ d₂, give c″ < e < h < f < d₂.
     - (S4i) gives χ(c′,c″,e) = cap. The rule on c′<c″<e<f reads cap, cup, ?, ?, so χ(c″,e,f) = cup.
     - (S1) gives χ(c″,f,d₂) = cap, and (S4ii) gives χ(f,d₂,d₃) = cap.
     - The rule on e<f<d₂<d₃ then gives χ(e,f,d₂) = cup.
     - Now c″<e<f<d₂ reads cup, ?, cap, cup: two changes, a contradiction. ∎

*Proof of the bound.*
- Let X ∈ {E, F} be 3-cap-free. Then X is a cup lying on one side of h, so |X| ≤ m−1.
- A∖X has no m-cup, since every m-cup starts in E and ends in F.
- Lemma 2 with v = m gives |A∖X| ≤ (m−1)². So |A| ≤ m(m−1). ∎

### Lemma 6 (R2 for u = k−1)
**Statement.** Let k ≥ 5 and m = k−1. Let V = P|Q with P < Q, where P is a cup and Q has no 4-cap. Suppose V has
no 5-cap, no m-cup and no strong k-set. Then |V| ≤ C(m,2) + m − 3 = C(k−1,2) + k − 4.

*Proof.* We have |P| ≤ m−1.
- **Step 0.** If |P| ≤ m−3, then |Q| ≤ C(m,2) by Lemma 1.
- **Step 1.** Let |P| ≥ m−2. Put Z° = {p₁,…,p_{m−2}}, z = p_{m−2} and W = V∖Z°.
  - W has no 4-cap. Such a 4-cap would have to be (p_{m−1},a,b,c).
  - If (p_{m−2},p_{m−1},a) is a cap, that gives a 5-cap. If it is a cup, p₁…p_{m−1}a is an m-cup.
- **Step 2 (rows).** For x ∈ W, let β′(x) be the size of the longest cup of W starting at x, and F_j = {β′ = j}.
  - F_j = ∅ for j ≥ m.
  - F_j is a cup with ≤ j points (Lemma 1, mirror form).
- **Step 3 (labels).**
  - An edge (x,y) of W is *free* if no w < x in W makes (w,x,y) a cap.
  - α′(x) is the size of the longest cup of W from x with a free first edge, or 1 if there is none.
  - **Claim 3a.** Let x<y lie in F_j, with j ≥ 2.
    - (i) For a j-cup (y,e,…), (x,y,e) is a cap; otherwise x starts a (j+1)-cup.
    - (ii) (x,y) is free. A cap (w,x,y) would make (x,y,e) a cup by (F3).
    - (iii) α′(x) > α′(y). Prepend x to y's realising cup; (x,y,d₂) is not a cap because (y,d₂) is free.
    - Hence a row with exactly j points carries α′ = j, …, 1 from left to right.
  - **Claim 3b.** If α′(y) = s ≥ 2 is realised by (y,d₂,…) and x < y, then (x,y,d₂) is a cup. In particular, if
    α′(y) = m−2, every W-point left of y lies in F_{m−1}.
- **Step 4 (Lemma C): |F_{m−1}| + |F_{m−2}| ≤ 2m−4.** Suppose otherwise. Then F = F_{m−1} and G = F_{m−2} are full,
  with α′(f_i) = m−i and α′(g_i) = m−1−i.
  - (a) f₂ < g₁, by Claim 3b at f₂.
  - (b) (x,f₁,f₂) is a cap for every x ∈ Z°; otherwise x+F is an m-cup.
  - (c) (f₁,f₂,g₁) is a cap. Otherwise f₁f₂ followed by g₁'s realising (m−2)-cup is an m-cup (Claim 3b).
  - (A1) f_{m−1} < g_{m−2}. Suppose not, and let δ be the second point of a cup from f_{m−1}.
    - (g_{m−2},f_{m−1},δ) is a cap.
    - So (g_{m−3},g_{m−2},f_{m−1}) is a cup, since otherwise there is a 4-cap.
    - Then G + f_{m−1} is an (m−1)-cup from g₁, a contradiction.
  - (A2) (f₁,f_{m−1},g_{m−2}) is a cap.
    - (f_{m−2},f_{m−1},g_{m−2}) is a cap, since otherwise F+g_{m−2} is an m-cup.
    - By (F3), (f_{m−1},g_{m−2},v) is a cup for every v > g_{m−2}.
    - So a cup (f₁,f_{m−1},g_{m−2}) would extend through an (m−2)-cup from g_{m−2} to an m-cup.
  - **Case B: (p_{m−3},z,g₁) is a cup.** Then Z°+g₁ is an (m−1)-cup and (p₁,f₁,f₂,g₁) is a 4-cap. Together they
    form a cup-cap set of size k.
  - **Case A: (p_{m−3},z,g₁) is a cap.**
    - (z,g₁,g₂) is a cup; otherwise (p_{m−3},z,g₁,g₂,δ′) is a 5-cap by Claim 3a(i). So zg₁…g_{m−2} is an
      (m−1)-cup.
    - (p_{m−3},z,f₁) is a cup; otherwise (p_{m−3},z,f₁,f₂,δ″) is a 5-cap by (b) and Claim 3a(i).
    - So Z°+f₁ is an (m−1)-cup, and (z,f₁,y) is a cap for every y > f₁.
    - Then (z,f₁,f_{m−1},g_{m−2}) is a 4-cap, by (A1) and (A2). With zg₁…g_{m−2} it forms a cup-cap set of size
      k. ∎(C)
- **Step 5.** |W| ≤ C(m−2,2) + 2m − 4 = C(m,2) − 1. So |V| ≤ (m−2) + C(m,2) − 1. ∎

Lemma 6 uses m ≥ 4 for the points p_{m−3}, g₂ and g_{m−3}.

### Lemma 7 (Z′: a cup followed by a 4-cap-free set; new relative to audit 567)
**Statement.** Let X = X_P | X_Q, where X_P < X_Q, X_P is a cup and X_Q has no 4-cap. Suppose X has no 5-cap and no
u-cup, with u ≥ 2. Then |X| ≤ C(u,2) + max(u−2, 0).

*Proof.* Let Z be the set of first points of 4-caps of X.
- A 4-cap whose first point lies in X_Q lies inside X_Q, which is impossible. So Z ⊆ X_P, and Z is a cup.
- X∖Z has no 4-cap, since such a 4-cap's first point would be in Z. So |X∖Z| ≤ C(u,2) by Lemma 1.
- If Z ≠ ∅, let z = max Z with a 4-cap (z,a,b,c).
  - If |Z| ≥ 2 and z′ precedes z in Z, then (z′,z,a) is a cup, since otherwise (z′,z,a,b,c) is a 5-cap.
  - So Z+a is a cup, and |Z| + 1 ≤ u − 1.
- Hence |X| ≤ C(u,2) + (u−2). ∎

Lemma 2 is the analogue for two 4-cap-free sides; Lemma 7 replaces the left side by a cup and gains a linear rather
than a quadratic surplus. The statement was SAT-checked for u = 3..6 on general signotopes (§10).

---

## 4. Theorem A: the (5, k−1, k) bound (audit 567, re-checked)

Hypotheses (H1), (H2), (H3_{k−1}), (H4); target H(k). Every lemma below is applied to subsets of U. Those are
classic and inherit (H3_{k−1}) and (H4).

**Degenerate cases.**
- If L = ∅ or R = ∅, U has no 4-cap, and |U| ≤ C(k−1,2) by Lemma 1.
- If |U| ≤ 2 there is nothing to prove.

So let |U| ≥ 3, x₀ ∈ L and x₁ ∈ R. The configurations are NN (x₀∈A, x₁∈B), BN (its mirror image), N1 (x₀,x₁∈A) and
N2 (x₀,x₁∈B).

### Configuration NN (x₀ ∈ A, x₁ ∈ B)

β ≤ 3, since x₀+D would be a 5-cap. α ≤ k−3, since C+x₁ is a cup.

| case | condition | bound on A | bound on B | total |
|---|---|---|---|---|
| NN1 | β ≤ 2 | Lemma 2, v = k−2: (k−3)² | B is a cup: k−2 | H |
| NN2 | β = 3, A ⊆ L | α ≤ k−4 by (P) and A is 4-cap-free; Lemma 1: C(k−3,2) | Lemma 1: C(k−1,2) | H |
| NN3 | β = 3, a* = max A ∈ R | Lemma 2, v = k−3: (k−4)² | Lemma 3, u = k−1: 2k−5 | H−(k−4) |

In NN3, B∩(−∞,a*) is a cup, since x₀+D+a* would be a 5-cap. B∩(a*,∞) ⊆ R is a cup, since a*+D would be a 4-cap
in R.

### Configuration N1 (x₀, x₁ ∈ A)

B is a cup, since x₀+D+x₁ would be a 5-cap.
- **N1a: |B| ≥ 2.** β = 2, so α ≤ k−3 by (P). Then |A| ≤ (k−3)² by Lemma 2, and |B| ≤ k−2. Total: H.
- **N1b: B = {b}.**
  - Every (k−2)-cup C of A satisfies min C < b < max C; otherwise C+b or b+C is a (k−1)-cup.
  - Lemma 5 applies with m = k−2 ≥ 4 and h the gap at b. Hence |A| ≤ (k−2)(k−3) = H − 1. Total: H.

### Configuration N2 (x₀, x₁ ∈ B)

α ≤ k−4, since x₀+C+x₁ is a cup, and β ≤ 4.

| case | condition | bound on A | bound on B | total |
|---|---|---|---|---|
| N2a | β ≤ 2 | Lemma 2: (k−4)² | cup: k−2 | H−(2k−7) |
| N2b | β = 3, A 4-cap-free | Lemma 1: C(k−3,2) | Lemma 1: C(k−1,2) | H |
| N2c | β = 3, A has a 4-cap | Lemma 2: (k−4)² | three cups, Lemma 4, u = k−1: 3k−9 | H |
| N2d | β = 4, A has a 4-cap | α ≤ k−5; Lemma 2, v = k−4: (k−5)² | Lemma 3: 2k−5, plus k−2 | H−(2k−11) |
| N2e | β = 4, A 4-cap-free | Lemma 1: C(k−4,2) | Lemma 6: C(k−1,2)+k−4 | H |

- **N2c.** A 4-cap of A crosses L|R, so a⁻ ∈ L and a⁺ ∈ R. The parts P₁ = B∩(−∞,a⁻), P₂ = B∩(a⁻,a⁺) and
  P₃ = B∩(a⁺,∞) are cups:
  - a 3-cap in P₁ gives the 4-cap D+a⁻ in L;
  - a 3-cap in P₂ gives the 5-cap a⁻+D+a⁺;
  - a 3-cap in P₃ gives the 4-cap a⁺+D in R.
- **N2d.** In addition, P₁∪P₂ has no 4-cap, since D+a⁺ would be a 5-cap.
- **N2e.** If a⁻ ∈ R, reflect; so assume a⁻ ∈ L. Then:
  - P = B∩(−∞,a⁻) ⊆ L is a cup, since D+a⁻ would be a 4-cap in L;
  - Q = B∩(a⁻,∞) has no 4-cap, since a⁻+D would be a 5-cap.
  - So Lemma 6 applies to B = P|Q. ∎(Theorem A)

---

## 5. The two new a = 4 lemmas

### Lemma 8 (R1-dec: three decomposable cups)
**Statement.** Let k ≥ 6. Let W = K₁ ∪ K₂ ∪ K₃, where K₁ < K₂ < K₃ are cups, some possibly empty, and W is
decomposable. Suppose W has no 4-cap and no strong k-set (so by Lemma B, no cup-cap set of size ≥ k, and in
particular no k-cup). Then |W| ≤ 3k − 8.

*Proof.* Use the root split W = A << B. Then β ≤ 3, α + β ≤ k−1 by (P), and A_i = A ∩ K_i.

**Two facts used throughout.**
- **(i) Points before a⁻ and after a⁺.** Suppose A meets K₁. Then a⁻ ∈ K₁, so every point of W left of a⁻ lies in
  K₁. Two B-points b < b′ < a⁻ would make (b,b′,a⁻) a cap by (M), inside the cup K₁. Hence |B∩(−∞,a⁻)| ≤ 1.
  The mirror statement holds for B∩(a⁺,∞) when A meets K₃.
- **(ii) Points between a⁻ and a⁺.** |B∩(a⁻,a⁺)| ≤ 1, since a⁻ b b′ a⁺ would be a 4-cap by (M).

**β = 1.**
- B is one point, and α ≤ k−2.
- A = A₁|A₂|A₃ has no 4-cap and no (k−1)-cup. Lemma 4 with u = k−1 ≥ 5 gives |A| ≤ 3k−9.
- Total ≤ 3k−8.

**β = 2.** B is a cup, so |B| ≤ k−1, and α ≤ k−3.
- **A misses a block.** A is at most two separated cups with no (k−2)-cup. Lemma 3 with u = k−2 gives
  |A| ≤ 2k−7. Total ≤ 3k−8.
- **A meets all three blocks.** By (i) and (ii), |B| ≤ 3. Lemma 4 with u = k−2 ≥ 4 gives |A| ≤ 3k−12.
  Total ≤ 3k−9.

**β = 3.** α ≤ k−4. For every 3-cap D of B, A lies strictly inside the span of D: a point of A left of D or right
of D would extend D to a 4-cap by (C). Hence:
- B∩(−∞,a⁺) and B∩(a⁻,∞) contain no 3-cap, so both are cups.

Three subcases:
- **A in one block.** A is a cup, so |A| ≤ k−4. B is the two cups B∩(−∞,a⁺) and B∩(a⁺,∞); the second is a cup
  because it lies inside B∩(a⁻,∞). B has no 4-cap and no strong k-set, so (E2) gives |B| ≤ 2k−4. Total ≤ 3k−8.
- **A in two blocks K_i, K_j (i < j).** A is two separated cups with no (k−3)-cup. Lemma 3 with u = k−3 ≥ 3 gives
  |A| ≤ 2k−9. Moreover |B| ≤ k:
  - if i = 1, then |B∩(−∞,a⁻)| ≤ 1 by (i), and B∩(a⁻,∞) is a cup of size ≤ k−1;
  - if (i,j) = (2,3), then |B∩(a⁺,∞)| ≤ 1 by (i), and B∩(−∞,a⁺) is a cup of size ≤ k−1.
  - Total ≤ 3k−9.
- **A in three blocks.** |B| ≤ 3 by (i) and (ii), and each A_i is a cup of size ≤ k−4. Total ≤ 3k−9. ∎

The bound is attained: SAT at 3k−8 and UNSAT at 3k−7 for every size vector, k = 6, 7, 8 (§10).

### Lemma 9 (decomposable R2 at u = k)
**Statement.** Let k ≥ 6. Let V = P|Q be decomposable, where P < Q, P is a cup and Q has no 4-cap. Suppose V has no
5-cap, no k-cup and no strong k-set. Then

|V| ≤ T* := 1 + C(k−1,2) + k − 4 = C(k−3,2) + 3k − 8 = C(k−4,2) + 4k − 12.

*Proof.*
- **Degenerate cases.** If Q = ∅, then |V| ≤ k−1. If P = ∅, then V has no 4-cap and |V| ≤ 1 + C(k−1,2) by (E1).
  Both are ≤ T*. If |V| ≤ 2 there is nothing to prove.
- **Setup.** Take the root split V = A << B. We have x₀ ∈ P and x₁ ∈ Q, α + β ≤ k−1 by (P), and β ≤ 4.
- **Position of A.** Write "A ⊆ P", "A ⊆ Q" or "mixed" (a⁻ ∈ P and a⁺ ∈ Q).
- **A recurring fact.**
  - **(R-a) Points of B before a⁻ when a⁻ ∈ P.** All points left of a⁻ lie in P. Two B-points b < b′ < a⁻ would
    make (b,b′,a⁻) a cap inside the cup P. So B∩(−∞,a⁻) ⊆ {x₀}, with equality when x₀ ∈ B.

**β = 1.**
- B is one point, and α ≤ k−2.
- A = (A∩P)|(A∩Q) satisfies Lemma 6 with m = k−1 ≥ 5. It has no 5-cap, no (k−1)-cup and no strong k-set.
- So |A| ≤ C(k−1,2) + k − 4, and the total is ≤ T*.

**β = 2.**
- B is a cup, so |B| ≤ k−1, and α ≤ k−3.
- Lemma 7 with u = k−2 gives |A| ≤ C(k−2,2) + k − 4.
- Total: C(k−2,2) + 2k − 5 = T*.

**β = 3.** Then α ≤ k−4. The configurations are named by the parts containing (x₀, x₁): AA, AB, BA, BB.
- **AA is impossible.** A 3-cap D of B gives the 5-cap x₀+D+x₁.
- **AB, A ⊆ P.**
  - A is a cup with |A| ≤ k−4.
  - B has no 4-cap, so (E1) gives |B| ≤ 1 + C(k−1,2).
  - Total: T*.
- **AB, mixed.** (A ⊆ Q is impossible, since x₀ ∈ A∩P.)
  - B∩(−∞,a⁺) is a cup, since x₀+D+a⁺ would be a 5-cap.
  - B∩(a⁺,∞) ⊆ Q is a cup, since a⁺+D would be a 4-cap in Q.
  - Lemma 3 with u = k gives |B| ≤ 2k−3; (E2) would give 2k−4, but it is not needed.
  - Lemma 7 with u = k−3 gives |A| ≤ C(k−3,2) + k − 5.
  - Total ≤ C(k−3,2) + 3k − 8 = T*.
- **BA.** (A ⊆ P is impossible, since x₁ ∈ A∩Q.)
  - A 3-cap D of B inside Q would give the 4-cap D+x₁ in Q. So every 3-cap of B starts in P.
  - Let Z₃ be the set of first points of 3-caps of B.
    - B∖Z₃ has no 3-cap, so it is a cup of size ≤ k−1.
    - Z₃ ⊆ P is a cup. Let z = max Z₃, with 3-cap (z,d₂,d₃).
    - If z′ precedes z in Z₃, then (z′,z,d₂) is a cup, since otherwise (z′,z,d₂,d₃) is a 4-cap in B. So Z₃+d₂ is
      a cup, and |Z₃| ≤ k−2.
  - Hence |B| ≤ 2k−3. With Lemma 7 (u = k−3) for A, the total is C(k−3,2) + 3k − 8 = T*.
- **BB, A ⊆ P.** As in AB, A ⊆ P: |A| ≤ k−4 and |B| ≤ 1 + C(k−1,2) by (E1). Total: T*.
- **BB, mixed.**
  - By (R-a), B∩(−∞,a⁻) = {x₀}.
  - M = B∩(a⁻,a⁺) is a cup, since a⁻+D+a⁺ would be a 5-cap.
  - B∩(a⁺,∞) ⊆ Q is a cup, since a⁺+D would be a 4-cap in Q.
  - B∖{x₀} = M | B∩(a⁺,∞) has no 4-cap (β = 3) and no strong k-set. (E2) gives |B∖{x₀}| ≤ 2k−4.
  - With Lemma 7 (u = k−3) for A, the total is C(k−3,2) + k − 5 + 1 + 2k − 4 = T*.
- **BB, A ⊆ Q.**
  - A is 4-cap-free with α ≤ k−4, so |A| ≤ C(k−3,2) by Lemma 1.
  - P ⊆ B. Put Y = B∩Q∩(−∞,a⁻) and X = B∩(a⁻,∞) ⊆ Q.
  - Y is a cup, since D+a⁻ would be a 4-cap in Q. X is a cup, since a⁻+D would be a 4-cap in Q.
  - B = P|Y|X is three cups with no 4-cap (β = 3) and no strong k-set, and it is decomposable. Lemma 8 gives
    |B| ≤ 3k−8.
  - Total: T*.

**β = 4.**
- β = 4 forces BB: if x₀ ∈ A, then x₀+D is a 5-cap for a 4-cap D of B; similarly for x₁.
- α ≤ k−5.
- **(R-b′)** For every 4-cap D of B, A lies strictly inside the span of D, since otherwise a+D or D+a is a 5-cap.

Three subcases:
- **A ⊆ P.**
  - By (R-a), B∩(−∞,a⁻) = {x₀}.
  - By (R-b′), every 4-cap D of B has min D < a⁻, so min D = x₀.
  - Hence B∖{x₀} has no 4-cap, and (E1) gives |B| ≤ 2 + C(k−1,2).
  - A is a cup with ≤ k−5 points. Total: T*.
- **Mixed.**
  - By (R-a) and (R-b′), B∩(−∞,a⁻) = {x₀} and every 4-cap of B starts at x₀. So B∖{x₀} has no 4-cap.
  - B∖{x₀} = M | B∩(a⁺,∞) is two cups (as for β = 3), so Lemma 3 with u = k gives |B∖{x₀}| ≤ 2k−3.
  - Lemma 7 with u = k−4 gives |A| ≤ C(k−4,2) + k − 6. (At k = 6 the case is empty: A meets P and Q, so α ≥ 2,
    but α ≤ k−5 = 1.)
  - Total ≤ C(k−4,2) + 3k − 8 = T* − (k−4).
- **A ⊆ Q.**
  - |A| ≤ C(k−4,2) by Lemma 1.
  - With Y and X as for β = 3, B = P ∪ Y ∪ X, and Y and X are cups.
  - P∪Y = B∩(−∞,a⁻) has no 4-cap, since D+a⁻ would be a 5-cap. Y∪X ⊆ Q has no 4-cap.
  - By (E2), |P|+|Y| ≤ 2k−4 and |Y|+|X| ≤ 2k−4. With |X| ≤ k−1 this gives |B| ≤ 3k−5.
  - For k ≥ 7 this is enough: C(k−4,2) + 3k − 5 ≤ T* = C(k−4,2) + 4k − 12.
  - For every k ≥ 6, (‡) below sharpens the bound to 3k−6, which gives T* − (k−6).

**(‡) |B| = 3k−5 is impossible.**
- Equality forces |P| = |X| = k−1 and |Y| = k−3 ≥ 3. Write P = p₁…p_{k−1}, Y = y₁…y_{k−3} and ξ = min X.
- Lemma 3(c), with u = k, on P|Y and on Y|X gives that p_{k−1}+Y and Y+ξ are cups. So p_{k−1}·Y·ξ is a
  (k−1)-cup.
- (p_{k−2}, p_{k−1}, ξ) is a cap, since otherwise P+ξ is a k-cup. *(The sources leave this step implicit.)*
- (p_{k−2}, y₁, y₂) is a cap. Otherwise p_{k−2}·Y·ξ is a (k−1)-cup from p_{k−2} to ξ, and with the cap
  (p_{k−2}, p_{k−1}, ξ) it forms a cup-cap set of size k.
- By (F3) in the 4-cap-free set P∪Y, (p_{k−3}, p_{k−2}, y₁) is a cup. So p₁…p_{k−2}y₁ is a (k−1)-cup.
- Finally consider (p₁, p_{k−1}, y₁):
  - if it is a cup, then p₁ p_{k−1}·Y·ξ is a k-cup;
  - if it is a cap, then with the cup p₁…p_{k−2}y₁ it forms a cup-cap set of size k.
- Both are contradictions. ∎(Lemma 9)

**Exhaustiveness.** All of the following are covered:
- β ∈ {1,2,3,4};
- for β = 3, the four (x₀, x₁) configurations, with AA impossible, A ⊆ Q impossible in AB, and A ⊆ P impossible
  in BA;
- for β = 4, BB only, with the three positions of A.

---

## 6. Theorem B: the (5, k, k) bound

Let k ≥ 6, and let U be decomposable with (H1), (H2), (H3_k), (H4).
- **Degenerate cases.** If L = ∅ or R = ∅, then U has no 4-cap and |U| ≤ 1 + C(k−1,2) ≤ G by (E1). (Lemma 1's
  C(k,2) is not enough at k = 6.) If |U| ≤ 2 there is nothing to prove.
- **General case.** Let |U| ≥ 3, x₀ ∈ L and x₁ ∈ R, and take the root split U = A << B. BN is NN after reflection.

### Configuration NN (x₀ ∈ A, x₁ ∈ B)

β ≤ 3, since x₀+D would be a 5-cap. α ≤ k−2, since C+x₁ is a cup.

- **NN1: β ≤ 2.** B is a cup, so |B| ≤ k−1.
  - **NN1a: |B| ≥ 2.** β = 2, so α ≤ k−3 by (P), and Lemma 2 with v = k−2 gives |A| ≤ (k−3)².
    Total: (k−3)² + k − 1 = G.
  - **NN1b: B = {x₁}.**
    - Every cup C of A extends to the cup C+x₁, so A has no (k−1)-cup.
    - A is decomposable and satisfies (H1), (H2), (H3_{k−1}) and (H4) for the same gap.
    - **Theorem A** gives |A| ≤ G − 1. Total: G.
- **NN2: β = 3 and A ⊆ L.**
  - A has no 4-cap by (H1), and α ≤ k−4 by (P). So |A| ≤ C(k−3,2) by Lemma 1.
  - B has no 4-cap, so (E1) gives |B| ≤ 1 + C(k−1,2).
  - Total: G.
- **NN3: β = 3 and a* = max A ∈ R.**
  - B∩(−∞,a*) is a cup, since x₀+D+a* would be a 5-cap.
  - B∩(a*,∞) ⊆ R is a cup, since a*+D would be a 4-cap in R.
  - Lemma 3 with u = k gives |B| ≤ 2k−3.
  - Lemma 2 with v = k−3 gives |A| ≤ (k−4)².
  - Total: G − (k−5) ≤ G. ((E2) would give G − (k−4), but it is not needed.)

### Configuration N1 (x₀, x₁ ∈ A)

B is a cup, since x₀+D+x₁ would be a 5-cap. So |B| ≤ k−1.
- **N1a: |B| ≥ 2.** β = 2, so α ≤ k−3, and |A| ≤ (k−3)². Total: G.
- **N1b: B = {b}.**
  - (P) with β = 1 gives α ≤ k−2. Concretely, C+b, b+C, or C with the apex b is a cup-cap set of size α+1.
  - So A satisfies the hypotheses of Theorem A, and |A| ≤ G − 1. Total: G.

### Configuration N2 (x₀, x₁ ∈ B)

α ≤ k−3, since x₀+C+x₁ is a cup, and β ≤ 4 by (H2).

- **N2a: β ≤ 2 (so β = 2).** B is a cup, so |B| ≤ k−1, and |A| ≤ (k−3)² by Lemma 2. Total: G.
- **N2b: β = 3 and A has no 4-cap.**
  - α ≤ k−4, so |A| ≤ C(k−3,2) by Lemma 1.
  - |B| ≤ 1 + C(k−1,2) by (E1).
  - Total: G.
- **N2c: β = 3 and A has a 4-cap.**
  - That 4-cap crosses L|R, so a⁻ ∈ L and a⁺ ∈ R.
  - P₁ = B∩(−∞,a⁻) ⊆ L, P₂ = B∩(a⁻,a⁺) and P₃ = B∩(a⁺,∞) ⊆ R are cups, as in Theorem A.
  - B = P₁|P₂|P₃ is decomposable, with no 4-cap (β = 3) and no strong k-set. **Lemma 8** gives |B| ≤ 3k−8.
  - α ≤ k−4, so |A| ≤ (k−4)² by Lemma 2.
  - Total: (k−4)² + 3k − 8 = G.
- **N2d: β = 4 and A has a 4-cap.**
  - α ≤ k−5 by (P). A 4-cap in A needs α ≥ 2, so the case is empty at k = 6.
  - For k ≥ 7: a⁻ ∈ L and a⁺ ∈ R, and P₁, P₂, P₃ are cups.
  - P₁∪P₂ has no 4-cap, since D+a⁺ would be a 5-cap. Lemma 3 with u = k gives |P₁∪P₂| ≤ 2k−3.
  - |P₃| ≤ k−1, and |A| ≤ (k−5)² by Lemma 2 with v = k−4.
  - Total: G − (2k−13) ≤ G − 1.
- **N2e: β = 4 and A has no 4-cap.**
  - α ≤ k−5, so |A| ≤ C(k−4,2) by Lemma 1.
  - If a⁻ ∈ R, reflect. This keeps N2e and gives a⁻ ∈ L.
  - P = B∩(−∞,a⁻) ⊆ L is a cup, since D+a⁻ would be a 4-cap in L.
  - Q = B∩(a⁻,∞) has no 4-cap, since a⁻+D would be a 5-cap.
  - B = P|Q is decomposable, with no 5-cap, no k-cup and no strong k-set. **Lemma 9** gives
    |B| ≤ 1 + C(k−1,2) + k − 4.
  - Total: C(k−4,2) + (k−4) + 1 + C(k−1,2) = G. ∎(Theorem B)

---

## 7. Case tables (u = k)

`arith5.py` checks every row for k = 6..200 (`arith5_out.txt`).

**Theorem B, target G = k² − 5k + 8.**

| case | when | bound on A | bound on B | total − G |
|---|---|---|---|---|
| one-sided | L or R empty | — | Baek (E1): 1+C(k−1,2) | −C(k−3,2) |
| NN1a | x₀∈A, x₁∈B, \|B\| ≥ 2, β = 2 | Lemma 2, v=k−2: (k−3)² | cup: k−1 | 0 |
| NN1b | \|B\| = 1 | **Theorem A**: G−1 | 1 | 0 |
| NN2 | β=3, A ⊆ L | Lemma 1: C(k−3,2) | Baek: 1+C(k−1,2) | 0 |
| NN3 | β=3, A meets R | Lemma 2, v=k−3: (k−4)² | Lemma 3: 2k−3 | −(k−5) |
| N1a | x₀,x₁∈A, \|B\| ≥ 2 | Lemma 2: (k−3)² | cup: k−1 | 0 |
| N1b | \|B\| = 1 | **Theorem A**: G−1 | 1 | 0 |
| N2a | x₀,x₁∈B, β = 2 | Lemma 2: (k−3)² | cup: k−1 | 0 |
| N2b | β=3, A 4-cap-free | Lemma 1: C(k−3,2) | Baek | 0 |
| N2c | β=3, A has a 4-cap | Lemma 2: (k−4)² | **Lemma 8 (R1-dec)**: 3k−8 | 0 |
| N2d | β=4, A has a 4-cap (k ≥ 7) | Lemma 2, v=k−4: (k−5)² | 2k−3 + (k−1) | −(2k−13) |
| N2e | β=4, A 4-cap-free | Lemma 1: C(k−4,2) | **Lemma 9 (R2-dec)**: T* | 0 |

**Lemma 8 (R1-dec), target 3k−8.**

| case | bound on A | bound on B | total − (3k−8) |
|---|---|---|---|
| β=1 | Lemma 4, u=k−1: 3k−9 | 1 | 0 |
| β=2, A misses a block | Lemma 3, u=k−2: 2k−7 | cup: k−1 | 0 |
| β=2, A meets all blocks | Lemma 4, u=k−2: 3k−12 | 3 | −1 |
| β=3, one block | cup: k−4 | (E2): 2k−4 | 0 |
| β=3, two blocks | Lemma 3, u=k−3: 2k−9 | k | −1 |
| β=3, three blocks | 3(k−4) | 3 | −1 |

**Lemma 9 (R2-dec), target T* = 1 + C(k−1,2) + k − 4.**

| case | bound on A | bound on B | total − T* |
|---|---|---|---|
| β=1 | Lemma 6: C(k−1,2)+k−4 | 1 | 0 |
| β=2 | Lemma 7, u=k−2 | cup: k−1 | 0 |
| β=3 AB, A⊆P | cup: k−4 | Baek | 0 |
| β=3 AB, mixed | Lemma 7, u=k−3 | Lemma 3: 2k−3 | 0 |
| β=3 BA | Lemma 7, u=k−3 | 2k−3 (Z₃ argument) | 0 |
| β=3 BB, A⊆P | cup: k−4 | Baek | 0 |
| β=3 BB, mixed | Lemma 7, u=k−3 | 1 + (E2): 2k−3 | 0 |
| β=3 BB, A⊆Q | Lemma 1: C(k−3,2) | **Lemma 8**: 3k−8 | 0 |
| β=4, A⊆P | cup: k−5 | 1 + Baek | 0 |
| β=4, mixed (k ≥ 7) | Lemma 7, u=k−4 | 1 + Lemma 3: 2k−2 | −(k−4) |
| β=4, A⊆Q | Lemma 1: C(k−4,2) | (E2)+(‡): 3k−6 | −(k−6) |

---

## 8. Hypothesis, parameter and circularity audit

**Dependency order (no cycles).** Each item uses only earlier ones:
1. (M), (F0)–(F3), (C), Lemma B, (P);
2. Lemmas 1–7;
3. the cited results (E1), (E2);
4. Theorem A (Lemmas 1–6);
5. Lemma 8 (Lemmas 3–4, (E2), (P));
6. Lemma 9 (Lemmas 1, 3, 6, 7, 8, (E1), (E2), (P));
7. Theorem B (Theorem A, Lemmas 1–3, 8, 9, (E1)).

**The "induction H_{k−1}" (task item 2).**
- In NN1b and N1b, the a5c table writes "induction gives H_{k−1}". It means H_u with u = k−1, i.e.
  T(4,k−1,k) + C(k−3,2) = C(k−1,2) + C(k−3,2).
- That is Theorem A at the same k. A inherits every hypothesis, and gains (H3_{k−1}) from C+x₁, respectively from
  (P) with β = 1.
- Theorem A uses no induction on |U| and no smaller parameter. So the appeal is well-founded.
- No step uses (5,k−1,k−1), and no step recurses on |U|.

**Gaps.**
- Every "4-cap inside L or R" argument uses the L|R gap: Lemma 2, Lemma 5 (S3), Theorem A (N2c–N2e),
  Theorem B (NN3, N2c–N2e).
- The marker gap h of Lemma 5 is the position of b (Theorem A, N1b), a different gap. Lemma 5's proof keeps the two
  apart.
- Lemmas 7, 8 and 9 refer to their own splits: P|Q, and K₁|K₂|K₃. They never use L|R.
- When Lemma 8 or 9 is called from Theorem B, the P₁|P₂|P₃ split (N2c) and the P|Q split (N2e) are at a⁻ and a⁺.
  The hypotheses at those splits are proved in place.

**No 5-cap** is used by:
- Lemmas 2, 5 (bound), 6, 7 and 9;
- every cap-gain step;
- R1-dec only implicitly, since there the condition is "no 4-cap".

**No strong k-set (H4)** is used through:
- (P) and Lemma B;
- the explicit cup-cap contradictions in Lemma 6 and (‡);
- (E1) (through cup-cap sets) and (E2) (in Lean's strong-set sense, which is exactly the hypothesis).

**Parameter ranges, k ≥ 6.**

| result | parameter | value |
|---|---|---|
| Lemma 2 | v | k−2, k−3, k−4 ≥ 2 |
| Lemma 3 | u | k, k−1, k−2, k−3 ≥ 3 |
| Lemma 4 | u | k−1 ≥ 5, k−2 ≥ 4 |
| Lemma 5 | m | k−2 ≥ 4 |
| Lemma 6 | m | k−1 ≥ 5 |
| Lemma 7 | u | k−2, k−3 ≥ 3, k−4 (case empty at k = 6) |
| (E2) | k | k ≥ 6 > 5 |
| (E1) | n | n = k−3 ≥ 3 |
| (‡) | \|Y\| | k−3 ≥ 3 |

Small-k exceptions:
- N2d (Theorem B) is empty at k = 6.
- β = 4 mixed (Lemma 9) is empty at k = 6.
- (‡) is needed only at k = 6.

---

## 9. Findings against the sources

Sources:
- a5c: `runs/claude-twoside-a5c-20261002/NOTES.md`
- r2d: `runs/claude-r2d-20261002/NOTES.md`
- cupblock: `runs/claude-cupblock-20261002/NOTES.md`
- r1r2: `runs/claude-r1r2-20261002/NOTES.md`
- h1: `runs/claude-h1-20261002/NOTES.md`
- audit 567: `runs/claude-audit-567-20261002/AUDITED-PROOF.md`

**Gaps found and repaired.** None changes a statement or a bound.

1. **a5c, N2 with β = 4 and A having a 4-cap.**
   - The table gives (k−5)² + (3u−4). For u = k at k = 6 this is 15 > G = 14.
   - Repair: the case is empty at k = 6, since α ≤ k−5 = 1 contradicts a 4-cap in A. For k ≥ 7 the slack is
     2k−13 ≥ 1.
2. **a5c, N1 with |B| = 1, u = k.** The table does not say why A has no (k−1)-cup when b is interior. The reason is
   (P) with β = 1: C plus the apex b is a cup-cap set of size α+1.
3. **r2d / R1-dec, β = 2.** "|B| ≤ 3 … else a b b′ a′ is a 4-cap" justifies only the middle part.
   - Repair (fact (i) of Lemma 8): A meets K₁, so a⁻ ∈ K₁, and two B-points before a⁻ give a cap (M) inside
     the cup K₁. The same holds at K₃.
4. **r2d / R1-dec, β = 3.**
   - "Two blocks: |B| ≤ k" is unproved in the notes; the proof is in Lemma 8.
   - "Three blocks" gives no bound on A. Lemma 4 with u = k−3 would need k ≥ 7, so the repair uses the trivial
     3(k−4).
5. **r2d, (‡).**
   - The apex step needs (p_{k−2}, p_{k−1}, ξ) to be a cap, which the notes do not say. Repair: otherwise P+ξ is a
     k-cup.
   - In (‡) the notes write x₁ for min X, while elsewhere x₁ = max V.
   - (‡) is needed only at k = 6; for k ≥ 7, 3k−5 suffices.
6. **r2d, β = 4, mixed ("1 + Lemma 3").** Lemma 3 needs B∖{x₀} to be 4-cap-free, which the notes do not state.
   Repair: (R-b′) and (R-a) make every 4-cap of B start at x₀.
7. **Bridge between definitions (all sources).** The sources argue with cup-cap sets, while the gate and the Lean
   cupblock lemma use `IsStrongPolygonSet`. The cupblock notes take "the two definitions agree" as given.
   - Repair: Lemma B proves the needed direction (cup-cap ⇒ strong) by hand, using only the 4-point rule.
   - `lemB_check.py` confirms both directions on every signotope with n ≤ 6.

**Simplifications.**
- **a5c NN3 and r2d β = 3 AB mixed** cite the cupblock lemma; Lemma 3 (2k−3) suffices. (E2) is needed only in
  Lemma 8 (β = 3, one block) and Lemma 9 (β = 3 BB mixed, and (‡) at k = 6).
- **R1 on general signotopes (r1r2)** is not needed: B is decomposable, and Lemma 8 is a complete hand proof. The
  r1r2 route rests on SAT for its base k ≤ 7 and on Claim D3 (stated for M ≥ 7). Claim D3 was not audited here,
  because nothing depends on it.
- **Theorem A** is exactly the audit-567 proof. Lemmas 5 and 6 were re-checked line by line, including every
  4-point-rule instance.

**Checked and found correct as stated.**
- Z′ (Lemma 7).
- R1-dec at β = 1 and in the β = 3 one-block case.
- Every row of the r2d case table, apart from items 5 and 6.
- The exhaustiveness claims in r2d.
- The reduction of N2e to R2 and of N2c to R1.
- The H1 / marker lemma (h1, as Lemma 5).
- The cupblock paper proof (Appendix), including the base case k = 5.

**Lean status caveat.** As noted in §2, the general-k cupblock theorem was not found in this checkout.

---

## 10. Computational evidence (diagnostic, not part of the proof)

All scripts and outputs are in this directory and are this audit's own code.
- **Interpreter.** SAT runs use `runs/etv-cc-20260930/.venv/bin/python` (pysat CaDiCaL 1.9.5); the replays also run
  with `python3`.
- **Status.** Nothing here is Lean-certified, and no DRAT proofs were produced.

**Library and encoder validation.**
- `lemB_check.py` (`lemB_out.txt`) enumerates all signotopes with n ≤ 6: 2, 8, 62 and 908 of them.
  - Results: F1 holds; the 4-law and the middle-determined definitions agree; cup-cap ⇔ strong.
  - 0 failures on 39,170 subsets.
- `test_enc5.py` (`test_enc5_out.txt`) checks the CNF encoder `enc5.py` against brute force.
  - On 400 random decomposable colourings with colours fixed, the CNF agrees with the hypotheses: 0 mismatches.
  - Model counts: 62 and 908 signotopes, and 62 and 718 decomposable colourings, at n = 5, 6. The latter match a
    direct enumeration of all split trees.
- `test_canon.py` (`test_canon_out.txt`) checks the canonical-label symmetry breaking.
  - None of 600 random decomposable colourings (n ≤ 16) is excluded.
  - The model counts are still 62 and 718.

**SAT (own encoder).** UNSAT at bound+1; SAT at the bound shows the bound is attained.

| check | instance | result | file |
|---|---|---|---|
| Theorem B, decomposable, k = 6 | n = 15, gaps 0..7 (8..15 by reflection) | all UNSAT, ≤ 1 s each | `sat_main_k6.txt` |
| Theorem B, decomposable, k = 6 | n = 14 | SAT for gaps 3..7, models re-verified | `sat_main_k6.txt` |
| Theorem B, decomposable, k = 7 | n = 23, g = 11 | **undetermined** at 200k conflicts (36 s) | `sat_main_k7.txt` |
| R1-dec (Lemma 8) | 3k−7, every size vector, k = 6, 7, 8 | UNSAT; SAT at 3k−8 | `sat_lemmas_small.txt`, `_k7a`, `_k6b` |
| R2-dec (Lemma 9) | T*+1, every \|P\|, k = 6, 7 | UNSAT; SAT at T* for \|P\| ≥ 2 / ≥ 3 | `sat_lemmas_k6b.txt`, `_k7b` |
| Lemma 6 (decomposable) | C(k−1,2)+k−3, k = 6, 7 | UNSAT; SAT at one less | `sat_lemmas_k6b.txt`, `_k7b` |
| Z′ (Lemma 7), general signotopes | C(u,2)+u−1, u = 3..6, every \|P\| | UNSAT; SAT at one less | `sat_lemmas_small.txt`, `_k7a` |
| cupblock (E2), decomposable | 2k−3, k = 6, 7 | UNSAT; SAT at 2k−4 | `sat_lemmas_small.txt`, `_k7a` |
| Baek (E1), decomposable | C(k−1,2)+2, k = 6, 7 | UNSAT; SAT at one less | `sat_lemmas_small.txt`, `_k7a` |

`sat_sanity_out.txt` checks non-vacuity:
- Dropping only the polygon constraint makes the R1-dec instances (3k−7, k = 6, 7, 8) and the R2-dec instances
  (T*+1, k = 6, 7) satisfiable. So their UNSAT results come from the polygon constraint.
- Those models contain convex k-sets, as they must.

**Replay of this proof** (`replay5.py`; drivers `run_replay.py`, `run_replay_lem.py`).
- **What is replayed.** The proof is replayed case by case on each instance and its mirror image.
  - Each case of Theorem B, of Lemma 8 and of Lemma 9 is identified from an actual deep-below split.
  - Every structural claim is checked, and every lemma's hypotheses and conclusion are checked on the actual subset.
  - NN1b and N1b recurse into a replay of Theorem A's table, including the marker straddle and WE.
- **Inputs.**
  - 589 tight decomposable (5,6,6) instances, |U| = 14 (`runs/claude-twoside-a5b-20261002/dect566.pkl`): 1,178
    replays (`replay_tight_out.txt`).
  - SAT-sampled instances near the bounds (`sampler.py`; root split steered by assumptions):
    - main: k = 6 (n = 11..14) and k = 7 (n = 19..22);
    - R2-dec: k = 6 (n ≤ 13) and k = 7 (n ≤ 19);
    - R1-dec: k = 6, 7, 8 (up to 3k−8).
  - Random greedy decomposable instances (`greedy5.py`): k = 6, 7, 8, 9, with up to 14, 18, 21 and 25 points.
- **Result.** 0 violations in about 16,700 replays (`replay_tight_out.txt`, `replay_samples_out.txt`).
  - Every case of every table is exercised: N2d 416 times, β = 4 mixed 25 times, NN1b 162 times, R2-dec β=3 BA
    70 times.
  - The only exception is R1-dec "β = 3, three blocks", which no generator produced. Its proof is a two-line count.
- **Limits.** The k = 7 near-tight SAT samples are few: 28 main replays, 150 R2-dec and 222 R1-dec. The full k = 7
  theorem is not SAT-checked.

---

## Appendix: the cupblock lemma (E2), paper proof re-checked

Setting:
- U = P|Q, where P = p₁…p_a and Q = q₁…q_b are cups with P < Q, and U has no 4-cap.
- "Convex" means a cup-cap set.
- With no 4-cap, a convex set is a cup, or a cup C from l ∈ P to r ∈ Q plus one apex x with (l,x,r) a cap.
- The claim, for k ≥ 5: if U has no convex k-set, then |U| ≤ 2k−4.

**Moves (insertions that keep a cup).**
- (M1) Insert into C a point of P below its second-to-last P-point; all new consecutive triples lie in P.
- (M2) Prepend p₁, p₂ when C has ≥ 2 P-points, all ≥ p₃.
- (M1′) and (M2′) are the mirror moves on Q.

**Claim D.** Let 𝒟 = {p₂, q_{b−1}}. If S ⊆ U∖𝒟 is convex with |S| ≥ 5, then U has a convex set of size |S|+1.
- **S a cup with h P-points and g Q-points.** If h ≥ 3, insert p₂ by (M1); if g ≥ 3, insert q_{b−1}. Otherwise
  |S| ≤ 4.
- **S = C ∪ {x}, where C has c P-points and g Q-points.**
  - If c ≥ 2 and s₁ ≥ p₃, then {p₁, p₂} ∪ C is a cup with |S|+1 points. So c ≥ 2 forces s₁ = p₁.
  - If c ≥ 3, insert p₂. This keeps l and r, so the apex survives. The mirror argument applies on Q.
  - What remains is c, g ≤ 2, hence |S| ≤ 5. Equality forces C = {p₁, s, t, q_b}, with s ≥ p₃ and t ≤ q_{b−2}.
  - If (p₂,s,t) is a cup, insert p₂. If (s,t,q_{b−1}) is a cup, insert q_{b−1}.
  - Otherwise p₂ s t q_{b−1} is a 4-cap, a contradiction.

**Base case k = 5.** Take |P| = 4 and |Q| = 3.
- (a) If some (p₃,p₄,q) is a cup, then P+q is a 5-cup. So assume (p₃,p₄,q) is a cap for every q.
- (b) By (F3), (p₄,q,q′) is a cup for all q < q′.
- (c) If (p₁,p₄,q₁) is a cup, then {p₁,p₄,q₁,q₂,q₃} is a 5-cup.
- (d) If (p₃,q₁,q₂) is a cup, then the cup p₃q₁q₂q₃ with the apex p₄ (cap (p₃,p₄,q₃)) is convex.
- (e) Otherwise (p₂,p₃,q₁) is a cup, since there is no 4-cap. Then the cup p₁p₂p₃q₁ with the apex p₄ is convex,
  using the cap (p₁,p₄,q₁) from (c).
- The (3,4) case follows by reversal. A block with ≥ 7 points contains a 5-cup or a (4,3) or (3,4) sub-block. So
  |U| ≤ 6.

**Induction (k ≥ 6).** Suppose U has no convex k-set.
- If it also has no convex (k−1)-set, induction gives |U| ≤ 2k−6.
- Otherwise its largest convex set has k−1 ≥ 5 points. By Claim D, U∖𝒟 has no convex (k−1)-set, and U∖𝒟 is
  again a two-cup block. So |U| ≤ 2 + 2(k−1) − 4 = 2k−4. ∎
