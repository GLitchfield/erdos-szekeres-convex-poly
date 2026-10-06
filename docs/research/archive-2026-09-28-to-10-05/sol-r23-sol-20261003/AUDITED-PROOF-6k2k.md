# The decomposable two-side bound at (6, k−2, k): audited proof

Audit run `claude-audit-6k2k-20261002`, 2026-10-02. This is an independent, adversarial audit of the sources listed
in §9.

**Verdict: COMPLETE-WITH-REPAIRS.**
- Assembled from the sources, the u = k−2 argument is a complete and correct paper proof for every k ≥ 7, and the
  first instance (6,5,7) is included.
- Every lemma (D, Z6, Marker6, Θ, ZR, Lemma M, L3, R₃, R2-6 at u = k−2) was re-derived by hand. I re-checked each
  of its uses at the new parameters.
- There is no circularity, and no lemma is used outside its hypotheses.
- The repairs (§9) fill in compressed or unstated steps:
  - the straddle argument behind N1b;
  - a missing hypothesis of Marker6;
  - the reflection and gains in N2f;
  - the Θ-cup variant that R₃ needs at β = 4 with A ⊆ Q (with the plain Θ that row fails for every k ≥ 7);
  - the F-set argument of R2-6 at β = 5, straddle;
  - a cleaner bound for N2e. The Θ₆ alternative in the a6 table is unproved, and on its own it fails at k = 8.

  No repair changes a statement or a bound.
- **No citation is needed.** Baek's Theorem 2.7, the two-cup-block lemma and the audited a = 5 gates are not used.
  - Each T that occurs at u = k−2 is a classical Erdős–Szekeres binomial, proved here (Lemma 1).
  - "No strong k-set" is used only through the coupling inequality (P), which is proved here directly from the
    deep-below split.
- **No step of the proof rests on computation.** §10 is diagnostic only.

---

## 0. Setting, statement, gate

Points are listed in x-order, and x<y refers to that order. For x<y<z, χ(x,y,z) ∈ {cup, cap}.

- **Signotope.** The colouring satisfies the **4-point rule**: for a<b<c<d, the sequence χ(abc), χ(abd), χ(acd),
  χ(bcd) changes value at most once.
- **Cups and caps.** A *t-cup* is x₁<…<x_t whose consecutive triples are all cups; a *t-cap* likewise. Sets of at
  most two points are both. cup(S) and cap(S) are the largest sizes inside S.
- **Cap-free.** "S is jcf" means S has no j-cap (cap(S) ≤ j−1). A 3cf set is a cup.
- **Notation.** For a sequence K and a point x beyond its end, K+x is the sequence extended by x; x+K is defined
  likewise.
- **Strong sets.** These are Lean's `IsStrongPolygonSet`: for all i<j<k<l in S, χ(ijk) = χ(ijl) and
  χ(ikl) = χ(jkl).
- **Decomposable sets.** These are Lean's `IsDecomposableOn`: a singleton, or lower ∪ upper with both parts
  decomposable and `HasDeepBelowSplit lower upper`.
  - The split property: a triple meeting both parts is a cup iff its middle point is in lower. That is property (M)
    below.
  - The equivalent label description is the one in audit 5kk §0. A triple is a cup iff the middle label has bit 0
    at the first differing coordinate.
- **Root split.** For a decomposable U with |U| ≥ 2, a root split U = A << B is the last constructor of a derivation
  (A = lower, B = upper). Both parts are decomposable and non-empty. Any such split works below.
- **Notation.** x₀ = min U, x₁ = max U, a⁻ = min A, a⁺ = max A, α = cup(A), β = cap(B).

> **Theorem (decomposable (6, k−2, k) two-side bound).** Let k ≥ 7, and let U be decomposable, split at a gap into
> U = L|R (either side may be empty). Suppose:
> - (H1) L and R have no 5-cap;
> - (H2) U has no 6-cap;
> - (H3) U has no (k−2)-cup;
> - (H4) U has no strong k-set.
>
> Then |U| ≤ G(k) := C(k−1,3) + C(k−3,3).

### 0.1 Arithmetic identities and the regimes of T

`decomposableThreshold a u k` (`ErdosSzekeres/Decomposable.lean`) is C(a+u−4, a−2) when a+u ≤ k+3 (classic), and
the window Σ_{j=k−a}^{u−2} C(k−2, j) otherwise.

- **T(5,k−2,k)** is classic, since a+u = k+3. It equals C(k−1,3), so G = T(5,k−2,k) + C(k−3,3).
- **T(6,k−2,k)** is the window, since a+u = k+4. It equals C(k−2,4) + C(k−2,3) + C(k−2,2), the terms
  j = k−6, k−5, k−4. For k ≥ 7 there is no truncation, since k−6 ≥ 1.
- **T(4,k−2,k)** is classic and equals C(k−2,2). Only the Erdős–Szekeres bound of Lemma 1 is used for it.

`lowerPascalTailReservoir 6 (k−2) k` = T(6,k−2,k) + 1 − C(k−3,4) (`StructuralChargingPascalTails.lean`). So

reservoir − 1 = C(k−2,4) − C(k−3,4) + C(k−2,3) + C(k−2,2) = C(k−3,3) + C(k−1,3) = G(k).

For example, k = 7 gives G = 24 and reservoir 25. `arith6.py` checks the identities and regimes for k = 7..40.

### 0.2 The gate `SingletonLowerPascalTailGate 6 (k−2) k`

- **Setting.** {q} lies deep below `upper` (q is the lower part), `upper` is decomposable, |upper| = reservoir, and
  {q} ∪ upper has no 6-cap, no (k−2)-cup and no strong k-set.
- **Split.** Put U = upper, L = the points of U before q and R = those after q.
- **(H1).** A crossing triple is a cup iff its middle point is q. So for a 5-cap D ⊆ L, the sequence D+q is a cap:
  its last triple has middle point in U. That is a 6-cap. Symmetrically, q+D is a 6-cap for D ⊆ R.
- **(H2)–(H4)** hold for the subset U.
  - Lean's cup and cap sets are all-triples sets. By (F1) these are the same as the consecutive-triple notion.
- **Conclusion.** The Theorem gives |U| ≤ G = reservoir − 1, which contradicts |U| = reservoir.

---

## 1. Basic facts

**(M) Mixed triples.** For a root split U = A << B, a triple meeting both A and B is a cup iff its middle point lies
in A. This is the definition of `HasDeepBelowSplit`.

**(F0) Decomposable sets are signotopes.**
- Induct through the root split; a 4-tuple inside A or inside B is covered by induction.
- For a mixed 4-tuple, (M) fixes every triple except possibly one, and each pattern changes at most once. The ten
  patterns are listed in audit 5kk (F0).
- The same fact is in Lean as `IsDecomposableOn.turnSequenceAllowed`.

**(F1) Cups are cup sets.** In a signotope, every triple of a t-cup is a cup, and likewise for caps.
- So a set is a cup iff no triple of it is a cap.
- Subsets of cups are cups.
- *Proof.* Induct on t; only (x₁,x_j,x_t) is new. For j < t−1, use the 4-point rule on (x₁,x_j,x_{t−1},x_t). For
  j = t−1, use it on (x₁,x₂,x_{t−1},x_t). Both read cup, ?, ?, cup. ∎

**(C) Gains.** Let D ⊆ B be a cap and a, a′ ∈ A.
- If a < min D, then a+D is a cap. If a′ > max D, then D+a′ is a cap. If both hold, a+D+a′ is a cap.
- Dually, a cup C ⊆ A gains points of B outside its span: b+C, C+b′ and b+C+b′ are cups.
- *Proof.* Every new consecutive triple is mixed, and its middle point is in B (respectively A). Apply (M). ∎

**(P) Coupling.** If a decomposable U = A << B has no strong k-set, then α + β ≤ k − 1.

*Proof.* Let C ⊆ A be a largest cup and D ⊆ B a largest cap. Then C ∪ D is *middle-determined*: a triple of C ∪ D is
a cup iff its middle point lies in C.
- A triple inside C is a cup by (F1), and a triple inside D is a cap.
- A mixed triple is decided by (M).

Hence C ∪ D is strong, because χ(ijk) and χ(ijl) share the middle point j, and χ(ikl) and χ(jkl) share k. Its size is
α + β. ∎

This is Lean's `HasDeepBelowSplit.containsStrongPolygonSet_of_cup_cap`.

**(D) Decoupling (a6 source).** This fact is not used in the proof. It was re-derived as part of the audit.
- **Statement.** A cup meeting A has B-points only at its two ends. A cap meeting B has A-points only at its ends.
- **Proof of the statement.**
  - An interior B-point of a cup that is adjacent in the cup to an A-point is the middle of a mixed consecutive
    triple, and that triple is a cap by (M).
  - So a run of interior B-points could only touch B-points, and therefore extends to an end of the cup.
  - The point next to such a run is then an interior B-point adjacent to an A-point, which is impossible. So the runs
    have length at most 1 and sit at the ends.
- **A strong set S meeting A and B has |S| ≤ α + β.**
  - Strong sets are middle-determined: the 4-index law lets each endpoint vary while the middle point stays fixed.
  - An interior A-point x of S is the middle of a mixed triple (b,x,max S) or (min S,x,b), hence of cup type.
  - Likewise every interior B-point is of cap type.
  - So S∩A is a cup and S∩B a cap. (This is Lean's `isStrongPolygonSet_iff_inter_cup_cap`.)
- **Checked.** `selftest6.py` checks (D) and the recursion strong(U) = max(strong(A), strong(B), α+β) on 1,500 random
  decomposable sets, with 0 failures.

**Reflection.** Reversing the x-order keeps every triple's middle point. So it preserves (M), decomposability, cups,
caps and strong sets, and it swaps L and R.

---

## 2. Z-lemmas (valid in every signotope)

All of them use the same move, the **extension step**. Let z₁<…<z_s be a cup and (z_s, a, …) a t-cap.
- If (z_{s−1}, z_s, a) is a cup, then z₁…z_s a is an (s+1)-cup.
- Otherwise (z_{s−1}, z_s, a, …) is a (t+1)-cap.

### Lemma 1 (Erdős–Szekeres)

If X has no v-cup and no c-cap (v ≥ 2, c ≥ 3), then |X| ≤ ES(v,c) := C(v+c−4, c−2). In particular:
- a 4cf set with no v-cup has at most C(v,2) points;
- a 5cf set with no v-cup has at most C(v+1,3) points.

*Proof.* The base cases hold:
- c = 3: X is a cup, so |X| ≤ v−1;
- v = 2: |X| ≤ 1.

For v ≥ 3 and c ≥ 4, let Z be the set of first points of (c−1)-caps.
- X∖Z has no (c−1)-cap.
- Z has no (v−1)-cup and no c-cap. A (v−1)-cup ending at z ∈ Z, extended by the second point of a (c−1)-cap from z,
  gives a v-cup or a c-cap.
- Pascal's rule gives ES(v,c−1) + ES(v−1,c) = ES(v,c). ∎

### Lemma 2 (classic5; template Lemma 2)

Let X be split at a gap into two 4cf sides, with X 5cf and no v-cup. Then |X| ≤ (v−1)² = C(v,2) + C(v−1,2).

*Proof.* Let Z be the set of first points of 4-caps.
- A 4-cap must meet both sides, so Z lies in the left side and is 4cf.
- X∖Z is 4cf.
- Z has no (v−1)-cup, by the extension step and X 5cf.
- Lemma 1 bounds both parts. ∎

### Lemma 3 (Z6)

Let X be split at a gap into two 5cf sides, with X 6cf and no v-cup. Then |X| ≤ Z6(v) := C(v+1,3) + C(v,3).

*Proof.* Let Z be the set of first points of 5-caps.
- A 5-cap meets both sides, so Z lies in the left side and is 5cf.
- X∖Z is 5cf, so it has at most C(v+1,3) points.
- Z has no (v−1)-cup, by the extension step and X 6cf, so it has at most C(v,3) points. ∎

### Lemma 4 (ZR)

Let X = X_P | X_Q (split at a gap), with X_P 4cf, X_Q 5cf, X 6cf and no w-cup (w ≥ 2). Then
|X| ≤ ZR(w) := C(w+1,3) + C(w−1,2). If X_P is a cup, then |X| ≤ ZR_cup(w) := C(w+1,3) + (w−2).

*Proof.* Let Z be the set of first points of 5-caps.
- A 5-cap starting in X_Q lies in X_Q, so Z ⊆ X_P.
- X∖Z is 5cf, so it has at most C(w+1,3) points.
- Z has no (w−1)-cup, by the extension step and X 6cf.
- Z is 4cf, so it has at most C(w−1,2) points. If X_P is a cup, so is Z, and |Z| ≤ w−2. ∎

### Lemma 5 (Θ, and its cup form Θ_cup)

Let X | Y | Z be consecutive blocks, each 4cf, whose union W is 5cf with no v-cup (v ≥ 3). Then
|W| ≤ Θ(v) := C(v,2) + C(v−1,2) + C(v−2,2). If X is a cup, then |W| ≤ Θ_cup(v) := C(v,2) + C(v−1,2) + (v−3).

*Proof.* Let Z₁ be the set of first points of 4-caps of W, and Z₂ the set of first points of 4-caps inside Z₁.
- A 4-cap is inside no block. If it started in Z it would lie in Z. So Z₁ ⊆ X ∪ Y.
- A 4-cap inside Z₁ ⊆ X ∪ Y is not inside Y, so Z₂ ⊆ X.
- W∖Z₁ is 4cf, so it has at most C(v,2) points.
- Z₁ has no (v−1)-cup, by the extension step and W 5cf. With Z₁∖Z₂ 4cf, this gives at most C(v−1,2) points.
- Z₂ has no (v−2)-cup: extending by a 4-cap inside Z₁ gives a (v−1)-cup in Z₁ or a 5-cap.
- Z₂ ⊆ X is 4cf, so it has at most C(v−2,2) points. If X is a cup, Z₂ is a cup with at most v−3 points. ∎

*(Θ_cup is used under the name "Θ-cup" in the r26 source, but no source states it; it is supplied here.)*

### Lemma 6 (L3, and L3_cup; r26 source)

Let X | Y | Z be consecutive blocks with:
- each block 4cf;
- X ∪ Y and Y ∪ Z 5cf;
- U = X ∪ Y ∪ Z 6cf with no v-cup (v ≥ 3).

Then |U| ≤ L3(v) := C(v,2) + 2C(v−1,2). If X is a cup, then |U| ≤ L3_cup(v) := C(v,2) + C(v−1,2) + (v−2).

*Proof.* Let F be the set of first points of 5-caps of U.
- A 5-cap is inside neither X∪Y nor Y∪Z, so it meets X and Z. Hence F ⊆ X.
- W = U∖F is 5cf.

Let Z₁ be the set of first points of 4-caps of W, and Z₂ the set of first points of 4-caps inside Z₁.
- As in Lemma 5, Z₁ ⊆ (X∖F) ∪ Y and Z₂ ⊆ X∖F.
- |W∖Z₁| ≤ C(v,2).
- |Z₁∖Z₂| ≤ C(v−1,2): Z₁ has no (v−1)-cup, by the extension step and W 5cf.

**Key step: F ∪ Z₂ (⊆ X) has no (v−1)-cup.** Let g′…g be one, with last point g.
- **g ∈ F.** Take a 5-cap (g, e₂, …, e₅). If (g′, g, e₂) is a cup, the cup extends to a v-cup. Otherwise
  (g′, g, e₂, …, e₅) is a 6-cap.
- **g ∈ Z₂.** Take a 4-cap (g, e₂, e₃, e₄) ⊆ Z₁. If (g′, g, e₂) is a cup, we get a v-cup. Otherwise the 5-cap
  (g′, g, e₂, e₃, e₄) has all its points in X ∪ (X∖F) ∪ Y = X ∪ Y, which is 5cf.

F ∪ Z₂ is 4cf, so it has at most C(v−1,2) points; if X is a cup, at most v−2. Finally,
U = (W∖Z₁) ⊔ (Z₁∖Z₂) ⊔ (F ∪ Z₂). ∎

---

## 3. Marker lemmas

**Setting.** A has no (m+1)-cup, where m ≥ 3. h is a gap of A such that every m-cup of A has points on both sides
of h. E and F are the sets of first and last points of the m-cups. Since every m-cup straddles h:
- E lies left of h and F lies right of h;
- neither E nor F contains an m-cup;
- A ∖ E and A ∖ F have no m-cup.

### Lemma 7 (straddle core; template Lemma 5, abstracted)

**Hypotheses.**
- e ∈ E with an m-cup D = (e, d₂, …, d_m), and f ∈ F with an m-cup C = (c₁, …, c′, c″, f), where c′ = c_{m−2} and
  c″ = c_{m−1}.
- K is a cap of A with |K| ≥ 2 ending at e; its second-to-last point is q.
- K′ is a cap of A with |K′| ≥ 2 starting at f; its second point is q′.
- (S1) holds automatically: (x,e,d₂) is a cap for every x < e, and (c″,f,y) is a cap for every y > f, since otherwise
  x+D or C+y is an (m+1)-cup. So K+d₂ and c″+K′ are caps.
- Assume in addition:
  - (a) c″ < d₂;
  - (b) if e < c″, then K+c″ is not a cap;
  - (c) if d₂ < f, then d₂+K′ is not a cap.

**Conclusion.** These hypotheses are contradictory.

*Proof.* The template proof, with K and K′ in place of its two 3-caps.
- **(S2)** e < h < f.
- **(S4)**
  - (i) (c′,c″,y) is a cap for c″ < y < h; otherwise c₁…c″y is an m-cup left of h.
  - (ii) (x,d₂,d₃) is a cap for h < x < d₂.
  - (iii) (c′,c″,d₂) and (c″,d₂,d₃) are not both cups. Otherwise, by (a), c₁…c″d₂…d_m is a cup with
    2m−2 ≥ m+1 points.
- **X.** e < c″ with (c″,d₂,d₃) a cap is impossible.
  - The rule on e<c″<d₂<d₃ reads ?, ?, cup, cap, so χ(e,c″,d₂) = cup.
  - The rule on q<e<c″<d₂ reads ?, cap (S1), ?, cup, so χ(q,e,c″) = cap.
  - Then K+c″ is a cap, against (b).
- **X′.** d₂ < f with (c′,c″,d₂) a cap is impossible.
  - The rule on c′<c″<d₂<f reads cap, cup, ?, ?, so χ(c″,d₂,f) = cup.
  - The rule on c″<d₂<f<q′ reads cup, ?, cap (S1), ?, so χ(d₂,f,q′) = cap.
  - Then d₂+K′ is a cap, against (c).
- **Case 1: (c′,c″,d₂) is a cup, so (c″,d₂,d₃) is a cap.**
  - e = c″ is impossible, since (e,d₂,d₃) is a cup.
  - If c″ < e, the rule on c′<c″<e<d₂ reads ?, cup, ?, cap (S1), so (c′,c″,e) is a cup. This contradicts (S4i),
    since e < h.
  - If e < c″, X applies.
- **Case 2: (c″,d₂,d₃) is a cup, so (c′,c″,d₂) is a cap.**
  - d₂ = f contradicts (S1).
  - If f < d₂, the rule on c″<f<d₂<d₃ reads cap (S1), ?, cup, ?, so (f,d₂,d₃) is a cup. This contradicts (S4ii),
    since f > h.
  - If d₂ < f, X′ applies.
- **Case 3: both are caps.**
  - X, X′, e ≠ c″ and f ≠ d₂ give c″ < e < h < f < d₂.
  - (S4i) gives χ(c′,c″,e) = cap. The rule on c′<c″<e<f reads cap, cup, ?, ?, so χ(c″,e,f) = cup.
  - χ(c″,f,d₂) = cap by (S1), and χ(f,d₂,d₃) = cap by (S4ii).
  - The rule on e<f<d₂<d₃ reads ?, ?, cup, cap, so χ(e,f,d₂) = cup.
  - Now c″<e<f<d₂ reads cup, ?, cap, cup, which has two changes. ∎

Every 4-point instance was re-checked. Lemma 7 does not use the length of K or K′ beyond q and q′.

### Lemma 8 (Marker6; a6 source)

Let A have 5cf sides A∩L and A∩R with respect to a gap L|R, no (m+1)-cup (m ≥ 3), and every m-cup straddling h.
- **(WE6)** Either no 4-cap of A ends in E, or no 4-cap of A starts in F. In particular, E or F is 4cf.
- **(Bound)** If A is also 6cf, then |A| ≤ C(m,2) + Z6(m) = 2C(m+1,3).

*Proof of WE6.* Let K be a 4-cap ending at e ∈ E and K′ a 4-cap starting at f ∈ F.
- K+d₂ and c″+K′ are 5-caps by (S1), so each meets both sides. Hence min K ∈ L, d₂ ∈ R, c″ ∈ L and max K′ ∈ R. This
  gives (a).
- (b): K+c″ would be a 5-cap from min K ∈ L to c″ ∈ L, hence inside L.
- (c): d₂+K′ would be a 5-cap from d₂ ∈ R to max K′ ∈ R, hence inside R.
- Lemma 7 then gives a contradiction.

*Proof of the bound.*
- Let X ∈ {E, F} be 4cf. X has no m-cup, so |X| ≤ C(m,2) by Lemma 1.
- A∖X has no m-cup and is two-sided 5cf and 6cf, so Lemma 3 with v = m applies.
- C(m,2) + C(m+1,3) + C(m,3) = 2C(m+1,3). ∎

*The a6 statement omits "A 6cf", which the bound needs (through Z6). At its single use, N1b, A ⊆ U is 6cf.*

### Lemma 9 (Lemma M; r26 source)

Let A = A_P | A_Q be split at a gap, with A_P 4cf and A_Q 5cf (6cf is not needed). Suppose A has no (m+1)-cup
(m ≥ 3) and every m-cup straddles h.
- **(WM)** Either no 3-cap of A ends in E, or no 4-cap of A starts in F. In particular, E is a cup or F is 4cf.
- **(Bound)** If A is also 6cf, then |A| ≤ C(m,2) + ZR(m). If A_P is a cup, then |A| ≤ C(m,2) + ZR_cup(m).

*Proof of WM.* Let K be a 3-cap ending at e ∈ E and K′ a 4-cap starting at f ∈ F.
- K+d₂ is a 4-cap, so it is not inside A_P; hence d₂ ∈ A_Q.
- c″+K′ is a 5-cap, so it is not inside A_Q; hence c″ ∈ A_P. This gives (a).
- (b): K+c″ would be a 4-cap ending at c″ ∈ A_P, hence inside A_P.
- (c): d₂+K′ would be a 5-cap starting at d₂ ∈ A_Q, hence inside A_Q.
- Lemma 7 then gives a contradiction.

*Proof of the bound.*
- If E is a cup, then |E| ≤ m−1 ≤ C(m,2). If F is 4cf, then |F| ≤ C(m,2).
- The rest has no m-cup and satisfies the hypotheses of Lemma 4 with w = m. ∎

*The asymmetry matters:*
- the mirrored claim "no 4-cap ends in E or no 3-cap starts in F" is false;
- "E or F has no 3-cap" is false even at a = 6.

Both are SAT-refuted in §10.

---

## 4. R₃ and R2-6 (decomposable, u = k−2)

**Common hypotheses (k ≥ 7).** V = P|Q is split at a gap, V is decomposable, and:
- V has no 6-cap;
- V has no (k−2)-cup;
- V has no strong k-set.

**Root split.** V = A << B. By (P), α + β ≤ k−1. Position of A: "A ⊆ P", "A ⊆ Q", or "straddle" (a⁻ ∈ P and
a⁺ ∈ Q). All counts below use these gains for a cap D of B:
- D+a⁻ is a cap when D < a⁻;
- a⁻+D, and similarly a⁺+D, are caps when D > a⁻ (respectively D > a⁺);
- a⁻+D+a⁺ is a cap when D ⊆ (a⁻,a⁺).

**β ≤ 2 (marker step, used by both lemmas).**
- B has no 3-cap, so it is a cup with at most k−3 points.
- Let C be a (k−3)-cup of A. A point b ∈ B to the right of C gives the (k−2)-cup C+b by (C), and a point to the left
  gives b+C. So B lies inside the span of C.
- Hence every (k−3)-cup of A straddles h := the gap at b₀ = min B.

### Lemma 10 (R₃: cup | 5cf)

Under the common hypotheses, with P a cup and Q 5cf: |V| ≤ R₃(k) := C(k−1,3) + k − 5.

*Proof.* If P = ∅, then V is 5cf and |V| ≤ C(k−1,3) by Lemma 1. If Q = ∅, then V is a cup and |V| ≤ k−3. Otherwise
take the root split.

**Fact (R-a).** If a⁻ ∈ P, then |B∩(−∞,a⁻)| ≤ 1. Two B-points b < b′ < a⁻ would make (b,b′,a⁻) a cap by (M), inside
the cup P.

**Cases.**
- **β ≤ 2.** Lemma 9 applies with m = k−3, A_P = A∩P (a cup) and A_Q = A∩Q (5cf). A is 6cf.
  - |A| ≤ C(k−3,2) + C(k−2,3) + (k−5), and |B| ≤ k−3.
- **β = 3.** α ≤ k−4.
  - Lemma 4 (cup form, w = k−3) gives |A| ≤ C(k−2,3) + (k−5).
  - B is 4cf with no (k−2)-cup, so |B| ≤ C(k−2,2).
- **β = 4.** α ≤ k−5.
  - **A ⊆ P.** A is a cup, so |A| ≤ k−5. B is 5cf, so |B| ≤ C(k−1,3).
  - **A ⊆ Q.** A is 5cf, so |A| ≤ C(k−3,3).
    - Split B into the blocks B∩P | B∩Q∩(<a⁻) | B∩(>a⁻).
    - B∩P is a cup. B∩Q∩(<a⁻) is 4cf, since D+a⁻ ⊆ Q would be a 5-cap. B∩(>a⁻) is 4cf, since a⁻+D ⊆ Q would be a
      5-cap. B is 5cf.
    - **Θ_cup**(k−2) gives |B| ≤ C(k−2,2) + C(k−3,2) + (k−5).
  - **Straddle.** By (R-a), |B∩(<a⁻)| ≤ 1.
    - B∩(>a⁻) splits at a⁺ into two 4cf sides: (a⁻,a⁺) by a⁻+D+a⁺, and (>a⁺) ⊆ Q by a⁺+D. It is 5cf.
    - Lemma 2 gives (k−3)².
    - Lemma 4 (cup form, w = k−4) gives |A| ≤ C(k−3,3) + (k−6).
- **β = 5.** α ≤ k−6.
  - **A ⊆ P.** |A| ≤ k−6, and |B∩(<a⁻)| ≤ 1 by (R-a). B∩(>a⁻) is 5cf (a⁻+D), so it has at most C(k−1,3) points.
  - **A ⊆ Q.** A is 5cf, so |A| ≤ C(k−4,3).
    - The blocks are as for β = 4. B∩P∪B∩Q∩(<a⁻) = B∩(<a⁻) is 5cf, since D+a⁻ would be a 6-cap. B∩(>a⁻) ⊆ Q, so
      Y∪Z ⊆ Q is 5cf. B is 6cf.
    - **L3_cup**(k−2) gives |B| ≤ C(k−2,2) + C(k−3,2) + (k−4).
  - **Straddle.** This needs α ≥ 2, hence k ≥ 8.
    - |B∩(<a⁻)| ≤ 1, and Lemma 2 applies to B∩(>a⁻) (5cf via a⁻+D, sides as before): (k−3)².
    - Lemma 4 (cup form, w = k−5) gives |A| ≤ C(k−4,3) + (k−7).

Totals are in §6.1. Every row is at most R₃(k) for all k ≥ 7. ∎

### Lemma 11 (R2-6 at u = k−2)

Under the common hypotheses, with P 4cf and Q 5cf: |V| ≤ R26(k) := C(k−1,3) + C(k−4,2).

*Proof.* If P = ∅, then |V| ≤ C(k−1,3). If Q = ∅, then |V| ≤ C(k−2,2). Otherwise take the root split.

- **β ≤ 2.** Use the marker step and Lemma 9 with m = k−3, A_P = A∩P (4cf) and A_Q = A∩Q (5cf). A is 6cf.
  - |A| ≤ C(k−3,2) + C(k−2,3) + C(k−4,2), and |B| ≤ k−3.
- **β = 3.** α ≤ k−4.
  - Lemma 4 (w = k−3) gives |A| ≤ C(k−2,3) + C(k−4,2).
  - B is 4cf: |B| ≤ C(k−2,2).
- **β = 4.** α ≤ k−5.
  - **A ⊆ P.** A is 4cf: |A| ≤ C(k−4,2). B is 5cf: |B| ≤ C(k−1,3).
  - **A ⊆ Q.** A is 5cf: |A| ≤ C(k−3,3).
    - The blocks are B∩P (4cf), B∩Q∩(<a⁻) (4cf, by D+a⁻ ⊆ Q) and B∩(>a⁻) (4cf, by a⁻+D ⊆ Q). B is 5cf.
    - Θ(k−2) gives |B| ≤ C(k−2,2) + C(k−3,2) + C(k−4,2).
  - **Straddle.** Lemma 4 (w = k−4) gives |A| ≤ C(k−3,3) + C(k−5,2).
    - The blocks are B∩(<a⁻), B∩(a⁻,a⁺) and B∩(>a⁺).
    - B∩(<a⁻) ⊆ P is a cup, since D+a⁻ ⊆ P would be a 4-cap.
    - B∩(a⁻,a⁺) is 4cf, by a⁻+D+a⁺.
    - B∩(>a⁺) ⊆ Q is 4cf, by a⁺+D.
    - B is 5cf, so Θ_cup(k−2) gives |B| ≤ C(k−2,2) + C(k−3,2) + (k−5).
- **β = 5.** α ≤ k−6.
  - **A ⊆ P.** A is 4cf: |A| ≤ C(k−5,2).
    - B∩(<a⁻) ⊆ P is a cup, since D+a⁻ ⊆ P would be a 4-cap.
    - B∩(>a⁻) is 5cf, by a⁻+D. B is 6cf, has no (k−2)-cup and no strong k-set.
    - B is decomposable: it is a part of the root split. So **Lemma 10** gives |B| ≤ C(k−1,3) + k − 5.
  - **A ⊆ Q.** A is 5cf: |A| ≤ C(k−4,3).
    - The blocks are X = B∩P, Y = B∩Q∩(<a⁻) and Z = B∩(>a⁻), each 4cf as for β = 4.
    - X∪Y = B∩(<a⁻) is 5cf, by D+a⁻. Y∪Z ⊆ Q is 5cf. B is 6cf.
    - **L3**(k−2) gives |B| ≤ C(k−2,2) + 2C(k−3,2).
  - **Straddle.** This needs α ≥ 2, hence k ≥ 8. Lemma 4 (w = k−5) gives |A| ≤ C(k−4,3) + C(k−6,2).
    - B∩(<a⁻) ⊆ P is a cup. B∩(a⁻,a⁺) and B∩(>a⁺) are 4cf. B∩(<a⁺) is 5cf (D+a⁺) and B∩(>a⁻) is 5cf (a⁻+D).
    - Let F be the set of first points of 5-caps of B. Such a cap is inside neither B∩(<a⁺) nor B∩(>a⁻), so it
      meets B∩(<a⁻) and B∩(>a⁺). Hence F ⊆ B∩(<a⁻), and F is a cup.
    - F has no (k−3)-cup, by the extension step and B 6cf. So |F| ≤ k−4.
    - B∖F is 5cf, with the three blocks above (the first a cup). Θ_cup(k−2) gives
      |B∖F| ≤ C(k−2,2) + C(k−3,2) + (k−5).

Totals are in §6.1. Every row is at most R26(k) for all k ≥ 7. ∎

**Exhaustiveness (Lemmas 10 and 11).**
- β ∈ {1,…,5}, since V is 6cf.
- For β ≥ 4, A is in exactly one of the positions A ⊆ P, A ⊆ Q, straddle.
- For β ≤ 3, the position is irrelevant.
- The empty cases are: β = 5 straddle at k = 7 (both lemmas); β = 5 needs k−6 ≥ 1, so it cannot occur at k = 6.

---

## 5. Proof of the Theorem

- **Degenerate cases.** If L = ∅ or R = ∅, then U is 5cf and |U| ≤ C(k−1,3) ≤ G. If |U| ≤ 2 there is nothing to
  prove.
- **General case.** Let x₀ ∈ L, x₁ ∈ R, and take the root split U = A << B. Every subset of U inherits (H1)–(H4).
- **Configurations.**
  - NN: x₀ ∈ A, x₁ ∈ B.
  - BN: x₀ ∈ B, x₁ ∈ A. Reflect to get NN.
  - N1: x₀, x₁ ∈ A.
  - N2: x₀, x₁ ∈ B.

### NN (x₀ ∈ A, x₁ ∈ B)

β ≤ 4, since x₀+D is a cap. α ≤ k−4, since C+x₁ is a cup.

- **NN1: β ≤ 2.**
  - B is a cup, so |B| ≤ k−3.
  - A is two-sided 5cf and 6cf with no (k−3)-cup. Lemma 3 gives |A| ≤ Z6(k−3).
- **NN2: β = 3.**
  - |A| ≤ Z6(k−3).
  - B is 4cf with no (k−2)-cup, so |B| ≤ C(k−2,2).
- **NN3: β = 4 and A ⊆ L.**
  - α ≤ k−5 by (P). A ⊆ L is 5cf, so |A| ≤ C(k−3,3).
  - B is 5cf, so |B| ≤ C(k−1,3).
- **NN4: β = 4 and a⁺ ∈ R.**
  - α ≤ k−5, so Lemma 3 gives |A| ≤ Z6(k−4).
  - B splits at a⁺ into two 4cf sides:
    - B∩(<a⁺) is 4cf by x₀+D+a⁺; every point of B is greater than x₀ = min U.
    - B∩(>a⁺) ⊆ R is 4cf by a⁺+D ⊆ R.
  - B is 5cf, so Lemma 2 gives (k−3)².

### N1 (x₀, x₁ ∈ A)

β ≤ 3, since x₀+D+x₁ is a cap.

- **N1a: β = 3.**
  - α ≤ k−4 by (P), so |A| ≤ Z6(k−3).
  - |B| ≤ C(k−2,2).
- **N1b: β ≤ 2.**
  - B is a cup, so |B| ≤ k−3.
  - **Straddle (repair).** Every (k−3)-cup C of A contains all of B in its span; otherwise C+b or b+C is a (k−2)-cup
    by (C). So every (k−3)-cup straddles the gap at b₀ = min B.
  - **Lemma 8** applies with m = k−3 ≥ 4: A is two-sided 5cf, 6cf and has no (k−2)-cup. Hence |A| ≤ 2C(k−2,3).

### N2 (x₀, x₁ ∈ B)

α ≤ k−5, since x₀+C+x₁ is a cup, and β ≤ 5.

- **N2a: β ≤ 2.** |A| ≤ Z6(k−4) and |B| ≤ k−3.
- **N2b: β = 3.** |A| ≤ Z6(k−4) and |B| ≤ C(k−2,2).
- **N2c: β = 4 and A 5cf.** |A| ≤ C(k−3,3) and |B| ≤ C(k−1,3).
- **N2d: β = 4 and A has a 5-cap.**
  - That 5-cap crosses L|R, so a⁻ ∈ L and a⁺ ∈ R.
  - The blocks P₁ = B∩(<a⁻) ⊆ L, P₂ = B∩(a⁻,a⁺) and P₃ = B∩(>a⁺) ⊆ R are 4cf, by D+a⁻ ⊆ L, a⁻+D+a⁺ and a⁺+D ⊆ R.
  - B is 5cf, so Θ(k−2) gives |B| ≤ C(k−2,2) + C(k−3,2) + C(k−4,2).
  - |A| ≤ Z6(k−4).
- **N2e: β = 5 and A has a 5-cap.**
  - α ≤ k−6 by (P). A 5-cap in A needs α ≥ 2, so the case is empty at k = 7.
  - |A| ≤ Z6(k−5).
  - P₁ is 4cf (as in N2d), so |P₁| ≤ C(k−2,2).
  - P₂ ∪ P₃ splits at a⁺ into two 4cf sides, and it is 5cf by a⁻+D. Lemma 2 gives (k−3)².
  - *(Repair: this bound alone suffices for all k ≥ 8. The a6 alternative "Θ + C(k−3,2)" is unproved there, and on
    its own it fails at k = 8, by 1.)*
- **N2f: β = 5 and A 5cf.**
  - α ≤ k−6, so |A| ≤ C(k−4,3).
  - If a⁻ ∈ R, reflect. This keeps N2, β and "A 5cf", and the new a⁻ is the old a⁺ ∈ old R = new L. So a⁻ ∈ L.
  - P = B∩(<a⁻) ⊆ L is 4cf, by D+a⁻ ⊆ L.
  - Q = B∩(>a⁻) is 5cf, by a⁻+D.
  - B is 6cf, has no (k−2)-cup and no strong k-set, and is decomposable (a part of the root split).
  - **Lemma 11** gives |B| ≤ C(k−1,3) + C(k−4,2).

**Exhaustiveness.**
- The four configurations cover all positions of x₀ and x₁.
- NN: β ≤ 2, β = 3, or β = 4 with A ⊆ L or a⁺ ∈ R.
- N1: β ≤ 3.
- N2: β ≤ 2, β = 3, or β ∈ {4,5} with A 5cf or not.

Every row is at most G (§6). ∎

---

## 6. Case tables and arithmetic (all k ≥ 7)

Identities used: C(k−1,3) = C(k−2,3) + C(k−2,2); C(k−2,2) + C(k−3,2) = (k−3)²; C(k−4,2) + C(k−5,2) = (k−5)². Each
slack below is (row total) − target, in closed form. `arith6.py` checks every row numerically for k = 7..40
(`arith6_out.txt`).

**Theorem, target G = C(k−1,3) + C(k−3,3).**

| row | A | B | slack |
|---|---|---|---|
| L or R empty | — | Lemma 1: C(k−1,3) | −C(k−3,3) |
| NN1 β≤2 | Z6(k−3) | cup: k−3 | −C(k−3,2) |
| NN2 β=3 | Z6(k−3) | C(k−2,2) | 0 |
| NN3 β=4, A⊆L | C(k−3,3) | C(k−1,3) | 0 |
| NN4 β=4, a⁺∈R | Z6(k−4) | Lemma 2: (k−3)² | −C(k−4,2) |
| N1a β=3 | Z6(k−3) | C(k−2,2) | 0 |
| N1b β≤2 | Marker6: 2C(k−2,3) | k−3 | 0 |
| N2a β≤2 | Z6(k−4) | k−3 | −(k−3)² − C(k−4,2) + (k−3) |
| N2b β=3 | Z6(k−4) | C(k−2,2) | −C(k−3,2) − C(k−4,2) |
| N2c β=4, A 5cf | C(k−3,3) | C(k−1,3) | 0 |
| N2d β=4, A 5-cap | Z6(k−4) | Θ(k−2) | 0 |
| N2e β=5, A 5-cap (k≥8) | Z6(k−5) | C(k−2,2) + (k−3)² | 2k−7−(k−5)² = −(k−4)(k−8) |
| N2f β=5, A 5cf | C(k−4,3) | R2-6: C(k−1,3)+C(k−4,2) | 0 |

For N2e: (k−5)² − (2k−7) = (k−4)(k−8), which is ≥ 0 for k ≥ 8, so the slack is ≤ 0 (and 0 at k = 8).

### 6.1 Lemma tables

**R2-6, target C(k−1,3) + C(k−4,2).**

| row | A | B | slack |
|---|---|---|---|
| β≤2 | Lemma M: C(k−3,2)+ZR(k−3) | k−3 | 0 |
| β=3 | ZR(k−3) | C(k−2,2) | 0 |
| β=4 A⊆P | C(k−4,2) | C(k−1,3) | 0 |
| β=4 A⊆Q | C(k−3,3) | Θ(k−2) | 0 |
| β=4 straddle | ZR(k−4) | Θ_cup(k−2) | 0 |
| β=5 A⊆P | C(k−5,2) | R₃: C(k−1,3)+k−5 | 0 |
| β=5 A⊆Q | C(k−4,3) | L3(k−2) | −(k−4)(k−7)/2 |
| β=5 straddle (k≥8) | ZR(k−5) | (k−4) + Θ_cup(k−2) | −C(k−6,2) − (2k−13) |

**R₃, target C(k−1,3) + k − 5.**

| row | A | B | slack |
|---|---|---|---|
| β≤2 | Lemma M (cup): C(k−3,2)+ZR_cup(k−3) | k−3 | 0 |
| β=3 | ZR_cup(k−3) | C(k−2,2) | 0 |
| β=4 A⊆P | k−5 | C(k−1,3) | 0 |
| β=4 A⊆Q | C(k−3,3) | **Θ_cup**(k−2) | 0 |
| β=4 straddle | ZR_cup(k−4) | 1 + (k−3)² | 0 |
| β=5 A⊆P | k−6 | 1 + C(k−1,3) | 0 |
| β=5 A⊆Q | C(k−4,3) | L3_cup(k−2) | 1 − C(k−4,2) |
| β=5 straddle (k≥8) | ZR_cup(k−5) | 1 + (k−3)² | −C(k−4,2) − 1 |

---

## 7. Hypothesis, parameter and circularity audit

**Dependency order (no cycles).**
1. Basic facts: (M), (F0), (F1), (C), (P).
2. Lemmas 1–6 (Z-lemmas, valid in every signotope).
3. Lemma 7, then Lemmas 8 and 9.
4. Lemma 10 (R₃), using Lemmas 1, 2, 4, 5 (Θ_cup), 6 (L3_cup), 9, and (P).
5. Lemma 11 (R2-6), using Lemmas 1, 4, 5, 6, 9, 10, and (P).
6. The Theorem, using Lemmas 1, 2, 3, 5, 8, 11, and (P).

There is no induction on |U| and no appeal to a smaller (a, u, k).

**Decomposability.**
- It is used only for root splits (Theorem, Lemmas 10 and 11) and for (P).
- Lemma 11 is applied to B, and Lemma 10 to a B-part; both are parts of a root split, hence decomposable. No
  "subsets are decomposable" step is needed.
- Reflection preserves decomposability.

**Gaps.**
- The L|R gap is used in:
  - Lemmas 2 and 3 when applied to subsets of U;
  - Lemma 8 (sides 5cf);
  - NN3, NN4, N2d, N2e and N2f (gains inside L or R).
- The marker gap h (at min B) is a different gap. Lemma 7 keeps it separate from the side gap.
- Lemmas 10 and 11 use their own P|Q gap; the internal splits are at a⁻ and a⁺. Each split's hypotheses are proved
  in place.

**Strong sets.** (H4) is used only through (P), at every root split. No row needs Baek, the two-cup-block lemma or
any a = 5 gate.

**Parameters (k ≥ 7).**

| result | parameter | value |
|---|---|---|
| Lemma 3 | v | k−3, k−4, k−5 (k ≥ 8) |
| Lemma 2 | v | k−2 ≥ 5 |
| Lemma 8 | m | k−3 ≥ 4 |
| Lemma 9 | m | k−3 ≥ 4 |
| Lemma 4 | w | k−3, k−4, k−5 (straddle only, k ≥ 8) |
| Lemmas 5, 6 | v | k−2 ≥ 5 |

Small-k emptiness:
- N2e is empty at k = 7.
- β = 5 straddle (Lemmas 10 and 11) is empty at k = 7.

---

## 8. What is cited

Nothing. The proof is self-contained from the 4-point rule and the definitions.

- **Templates.** Audit 567's Lemma 2 and Lemma 5 are re-proved here as Lemma 2 and Lemma 7 (with the 4-point
  instances re-checked).
- **Lean facts that coincide with steps of the proof** (convenient for formalization; mentioned only):
  - `IsDecomposableOn.turnSequenceAllowed` = (F0);
  - `HasDeepBelowSplit.containsStrongPolygonSet_of_cup_cap` = (P);
  - `isStrongPolygonSet_iff_inter_cup_cap` = the strong-set part of (D), which is unused.
- **Not used:** Baek's Theorem 2.7, the two-cup-block lemma, and the audited a = 5 gates.

---

## 9. Findings against the sources

Sources:
- a6: `runs/claude-a6-20261002/NOTES.md`
- r26: `runs/claude-r26-20261002/NOTES.md`
- audit 567 and audit 5kk (templates)

### Gaps found and repaired

None of these changes a statement or a bound.

1. **a6, N1b.** "Marker6, m = k−3" needs every (k−3)-cup of A to straddle a fixed gap, which the notes do not argue.
   - The notes have β ≤ 2, so |B| can exceed 1.
   - Repair: all of B lies in the span of each (k−3)-cup (C+b, b+C). Take h at min B.
2. **a6, Marker6 statement.** The bound |A| ≤ 2C(m+1,3) needs A 6cf (through Z6), which is not stated. It holds at
   the only use.
3. **a6, N2e.**
   - The table's min(Θ+C(k−3,2), C(k−2,2)+(k−3)²) relies on an unstated "Θ₆" lemma (three blocks, 6cf union), which
     appears only as a comment in `cases.py`.
   - Θ₆ alone gives G+1 at k = 8.
   - Repair: use only C(k−2,2) + (k−3)², with P₁ 4cf and P₂∪P₃ classic5 at a⁺. It suffices for every k ≥ 8, with
     slack −(k−4)(k−8).
   - Θ₆ is in fact provable (F = first points of 5-caps lies in P₁), but it is not needed.
4. **a6, N2f.** The reflection (to get a⁻ ∈ L) and the gains "P 4cf, Q 5cf" are not written out. Supplied in §5.
5. **a6, NN4.** "B classic5 at a⁺" needs both sides 4cf. Supplied: x₀+D+a⁺, and a⁺+D ⊆ R.
6. **r26, R₃ at β = 4 with A ⊆ Q.**
   - The notes list the R₃ table as "the same table with the cup form of ZR" and give other differences.
   - With the plain Θ this row exceeds R₃ by C(k−4,2) − (k−5) ≥ 1 for every k ≥ 7.
   - Repair: B∩P ⊆ P is a cup, so **Θ_cup** applies. That lemma is stated and proved here (Lemma 5).
7. **r26, R2-6 at β = 5, straddle.** "cup ≤ k−4, plus Θ-cup" is unexplained. Supplied:
   - F (first points of 5-caps) ⊆ B∩(<a⁻);
   - |F| ≤ k−4 by the extension step;
   - B∖F is 5cf, with the first block a cup.
8. **r26, β ≤ 2 rows of R₃.** The cup form of Lemma M's bound is used, giving slack 0. The notes do not write this out.

### Checked and found correct as stated

- (D) both parts; it is unused.
- Z6, Θ, ZR (both forms), L3 (both forms, including the key step), and Lemma M with its asymmetric (S3) placement.
- Marker6 WE: Lemma X yields a 5-cap in L, and X′ one in R.
- Every row of both u = k−2 tables apart from the items above.
- The identity G = T(5,k−2,k) + C(k−3,3) = T(6,k−2,k) − C(k−3,4) = reservoir − 1, and the regimes.
- The claim that "no strong k-set" is used only through (P).

### Simplifications

- Lemma B (cup-cap ⇒ strong) is not needed: (P) is proved directly, since C ∪ D is middle-determined.
- Lemma 7 isolates the common core of Marker6 and Lemma M, so both reduce to checking (a), (b) and (c).

---

## 10. Computational evidence (diagnostic only; own code, not Lean-certified, no DRAT)

**Setup.**
- The scripts are in this directory. SAT runs use pysat CaDiCaL 1.9.5 from `runs/etv-cc-20260930/.venv`.
- Every Python run was kept to about one minute or less, except the cubes and the probe noted below.

**Library and encoder validation.**
- `lib6.py` is the colouring and chain library. `selftest6.py` checks it on 1,500 random decomposable sets with
  n ≤ 9, with 0 failures. It covers:
  - the 4-point rule;
  - the chain DPs against brute force;
  - strong (cup-cap) maxima against Lean's 4-index strong definition (brute force);
  - the deep-below recursion for strong sets;
  - the (D) claims.
- `enc6.py` is the CNF encoder. `test_enc6.py` validates it:
  - model counts of 8, 62 and 908 signotopes and 8, 62 and 718 decomposable colourings at n = 4, 5, 6 (the 62 and
    718 match audit 5kk);
  - decoded labels reproduce χ;
  - the CNF agrees with brute force on 300 fixed colourings.

**SAT checks of the lemmas** (general signotopes, every gap or block split). In every check below, UNSAT at bound + 1
and SAT at the bound, so each bound is exact at these parameters.

| lemma | instance | result | file |
|---|---|---|---|
| Z6 | v = 3, 4 | n = 6, 15 UNSAT; n = 5, 14 SAT | `sat_small_out.txt` |
| ZR | w = 3, 4, 5 | UNSAT at 6, 14, 27; SAT at 5, 13, 26 | `sat_small_out.txt`, `sat_mid_out.txt` |
| ZR_cup | w = 4, 5 | UNSAT at 13, 24; SAT at 12, 23 | `sat_small_out.txt`, `sat_mid_out.txt` |
| Θ | v = 4, 5 | UNSAT at 11, 20; SAT at 10, 19 | `sat_small_out.txt`, `sat_mid_out.txt` |
| Θ_cup | v = 4, 5 | UNSAT at 11, 19; SAT at 10, 18 | `sat_small_out.txt`, `sat_mid_out.txt` |
| L3 | v = 4, 5 | UNSAT at 13, 23; SAT at 12, 22 | `sat_small_out.txt`, `sat_mid_out.txt` |
| L3_cup | v = 4, 5 | UNSAT at 12, 20; SAT at 11, 19 | `sat_small_out.txt`, `sat_mid_out.txt` |
| Marker6 bound | m = 3, n = 9 | UNSAT for all 80 (gap, h) | `sat_small_out.txt` |
| Marker6 bound | m = 4, n = 21 | UNSAT for all 440 (gap, h); n = 20 SAT | `sat_marker6_m4_out.txt` |
| Marker6 WE (strong form) | m = 3, n = 8, 10; m = 4, n = 11, 12 | all UNSAT | `sat_small_out.txt`, `sat_mid_out.txt` |
| Lemma M (strong form) | m = 3, n = 8, 10; m = 4, n = 11–13; m = 5, n = 13 | all UNSAT | `sat_small_out.txt`, `sat_mid_out.txt` |
| R₃ | k = 7, n = 23, \|P\| = 1..4 | UNSAT (\|P\| ≥ 5 impossible, \|P\| = 0 trivial); n = 22 SAT at \|P\| = 2 | `sat_r_k7_small.txt` |
| R2-6 | k = 7, n = 24, \|P\| = 0..10 | UNSAT (cubes at \|P\| = 6..10); \|P\| ≥ 11 impossible; n = 23 SAT at \|P\| = 3 | `sat_r_k7_small.txt`, `sat_r2_k7_cubes.txt` |

**Non-vacuity.**
- The mirrored Lemma M is SAT at m = 3 and m = 4.
- "E or F has no 3-cap" at a = 6 is SAT.
- So the asymmetric statements are sharp.

**Run-time caveats.**
- The R2-6 cubes at |P| = 6..8 took 47–109 s each, run 12 in parallel, which exceeds the one-minute guideline.
- A probe of the whole decomposable (6,5,7) theorem at n = 25, gap 12 (`sat_main_k7_probe.txt`):
  - the root patterns N1, BN and NN are UNSAT;
  - the N2 pattern was **not determined**: the interrupt failed, and I stopped the process by hand after about
    4 minutes;
  - other gaps were not run.
- The full (6,5,7) SAT is therefore **not** claimed.

**Replay of this proof** (`replay6.py`).
- **What is checked.** Every case of the Theorem, Lemma 10 and Lemma 11 is identified from the actual root split.
  For each, the following are asserted on the actual subsets:
  - every structural claim (gains, block cap-freeness, Z, Z₁, Z₂, F ⊆ X, the key step of L3);
  - every lemma's hypotheses and conclusion;
  - the strong WE forms;
  - (P).

  Lemma 11 recurses into Lemma 10, and N2f recurses into Lemma 11, including the reflected branch.
- **Inputs.**
  - Own SAT samples of the decomposable Theorem (`sample_main.py`, `smain_*.pkl`):
    - k = 7 for n = 6..24, including n = 24 = G;
    - k = 8 and k = 9 for n = 6..15;
    - k = 8 for n = 24..30.
  - 1,410 tight Theorem instances at k = 7 (|U| = 24) built from the r26 tight R2-6 models by inserting one
    deep-below point (`run_embed.py`).
  - The r26 R2-6 and R₃ sample files, used as data only (`run_data.py`).
- **Result.** **43,331 replays, 0 failures** (`replay_all_out.txt`, `run_embed_out.txt`, `data_out_*.txt`).
  - Every Theorem row occurs at k = 7, 8, 9. N2e occurs only for k ≥ 8, as it must.
  - Every Lemma 10 and 11 row occurs, with β = 5 straddle at k = 8, 9.
  - At k = 7 the size G = 24 is attained in every slack-0 row of the Theorem: NN2, NN3, N1a, N1b, N2c, N2d, N2f
    (`tight_summary_out.txt`).
  - Every lemma bound is attained (slack 0) in some replay, except L3 (minimum slack 1).
