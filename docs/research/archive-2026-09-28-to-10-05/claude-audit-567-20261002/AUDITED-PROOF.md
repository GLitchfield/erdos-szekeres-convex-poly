# The decomposable two-side bound at (5, k−1, k): audited proof

Audit run `claude-audit-567-20261002`, 2026-10-02.

**Verdict: COMPLETE-WITH-REPAIRS.**
- The u = k−1 argument assembled from the five source runs is correct. No lemma is applied outside its
  hypotheses, and no step is circular. Every case closes for all k ≥ 6.
- No case is missing from the argument. Three trivial rows are absent from the a5c table, but its replay script
  handles them (§7, item 4).
- The repairs fill in arguments that the sources state only in compressed or computational-sounding form (§7).
  None changes a statement.
- The u = k−1 proof needs none of the following: R1, the two-cup-block ("cupblock") lemma 2k−4 (Lean or
  otherwise), the a=4 diagonal bound, Baek's theorem, or any induction on |U|.
- **No step of the proof below rests on computation.** The computations in §8 are diagnostic cross-checks only.

---

## 0. Setting

Points are listed in x-order, and x<y refers to that order. For x<y<z, χ(x,y,z) ∈ {cup, cap}.

- **Signotope.** The colouring satisfies the **4-point rule**: for a<b<c<d, the sequence χ(abc), χ(abd), χ(acd),
  χ(bcd) changes value at most once.
- **Cups and caps.** A *t-cup* is x₁<…<x_t whose consecutive triples are all cups; a *t-cap* likewise. Sets of at
  most two points are both. cup(S) and cap(S) are the largest sizes inside S.
- **Strong sets.** A *strong set* is C ∪ D, where C is a cup and D a cap, both running from l = min to r = max,
  with C ∩ D = {l, r}. Its size is |C| + |D| − 2.
- **Two-side hypotheses (5, k−1, k).** U is split at a gap into U = L|R, where L is the set of points left of the
  gap and R the set right of it. They are:
  - (H1) cap(L) ≤ 3 and cap(R) ≤ 3;
  - (H2) cap(U) ≤ 4;
  - (H3) cup(U) ≤ k−2;
  - (H4) U has no strong set of size k.
- **Classic sets.** A set X ⊆ U is *classic* if X∩L and X∩R have no 4-cap and X has no 5-cap. Every subset of U
  is classic and satisfies (H3) and (H4).
- **Decomposable colourings.** Points carry binary labels. A triple is a cup iff its middle point has bit 0 at the
  first coordinate where the three labels differ. For this to be defined, no three points share a label; distinct
  labels are the usual convention.
- **Root split.** Let d be the first coordinate at which the labels of U are not all equal. Then A = {bit 0 at d}
  and B = {bit 1 at d}. For |U| ≥ 3 such a d exists and both parts are non-empty. We write U = A << B.
- **Notation.** x₀ = min U and x₁ = max U. α = cup(A) and β = cap(B).

> **Theorem.** Let k ≥ 6, and let U be decomposable and satisfy (H1)–(H4). Then
> |U| ≤ H(k) := C(k−1,2) + C(k−3,2) = T(4,k−1,k) + C(k−3,2) = k² − 5k + 7.

**Remark (gate form).** Let q lie far below U in the gap, i.e. {q} << U.
- By (M) below, a cap through q has q as an endpoint, and q followed by a cap of R is a cap.
- A cup through q has at most 3 points.
- So U ∪ {q} is 5-cap-free iff (H1) and (H2) hold, and U ∪ {q} has no (k−1)-cup iff (H3) holds.
- This is the equivalence stated in the task.

---

## 1. Basic facts

**(M) Mixed triples.** If a triple meets both A and B, it is a cup iff its middle point lies in A.

*Proof.* All labels of U agree before coordinate d, and the triple has both bits at d. ∎

**(F0) Decomposable colourings are signotopes.**

*Proof.* By induction on |U| through the root split.
- A 4-tuple inside A or inside B is covered by induction.
- A mixed 4-tuple has, by (M), the following colour sequences. Here "·" is the free colour of the unique triple
  lying inside one part, and the B-heavy patterns are the same with cup and cap exchanged.
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

**(F1) Cups are cup sets.** If x₁<…<x_t is a cup, then every triple of it is a cup. Hence a set is a cup iff no
three of its points form a cap, and every subset of a cup is a cup. The same holds for caps.

*Proof.* Induct on t; the case t=3 is trivial. Let t ≥ 4. By induction, every triple avoiding x_t or avoiding x₁
is a cup, so only the triples (x₁, x_j, x_t) remain.
- For j < t−1, apply the 4-point rule to (x₁, x_j, x_{t−1}, x_t). Its sequence is cup, ?, ?, cup, so both
  unknowns are cups.
- For j = t−1, apply it to (x₁, x₂, x_{t−1}, x_t) in the same way. ∎

**(F2) Strong sets.**
- (a) If C is a cup and D a cap, both from l to r, then C ∩ D = {l, r} automatically. A common interior point x
  would make χ(l,x,r) both a cup and a cap, by (F1).
- (b) Deleting an interior point of C or of D leaves a strong set, by (F1). So (H4) also excludes strong sets of
  every size ≥ k.

**(F3) 4-cap-free propagation.** Suppose X has no 4-cap.
- If (w,x,y) is a cap in X, then (x,y,z) is a cup for every z ∈ X with z > y.
- Symmetrically, if (x,y,z) is a cap, then (w,x,y) is a cup for every w ∈ X with w < x.

**(C) Gaining points across the split.** Let D ⊆ B be a cap and let a, a′ ∈ A.
- If a < min D, then a+D is a cap. If a′ > max D, then D+a′ is a cap.
- If a < min D and a′ > max D, then a+D+a′ is a cap.
- Dually, let C ⊆ A be a cup and b, b′ ∈ B. Then b+C, C+b′ and b+C+b′ are cups whenever b and b′ lie outside
  the span of C on the corresponding sides.

*Proof.* The only new consecutive triples are mixed, and their middle points lie in B (respectively in A). Apply
(M). ∎

**(P) Coupling.** α + β ≤ k − 1.

*Proof.* Take a largest cup C of A and a largest cap D of B. Let l = min(C∪D) and r = max(C∪D).

| where l and r lie | the cup | the cap |
|---|---|---|
| both in D | d₁ + C + d_β | D |
| l in C, r in D | C + d_β | c₁ + D |
| l in D, r in C | d₁ + C | D + c_α |
| both in C | C | c₁ + D + c_α |

- Each entry is a cup or a cap by (C).
- Each cup and cap runs from l to r, and the pair shares only l and r.
- So C ∪ D is a strong set of size α + β. (The degenerate cases α = 1 or β = 1 are covered by the same table.)
- By (H4) and (F2b), α + β ≤ k − 1. ∎

---

## 2. Lemmas valid in every signotope

### Lemma 1 (Erdős–Szekeres for no 4-cap, in layer form)

**Statement.** Let X have no 4-cap. For j ≥ 1, let Lay_j = {x : the longest cup of X ending at x has j points}.
Then Lay_j is a cup with at most j points. Hence if X also has no v-cup, |X| ≤ 1 + 2 + … + (v−1) = C(v,2).

The mirror statement holds for the rows F_j = {x : the longest cup *starting* at x has j points}.

*Proof.*
- Lay₁ = {min X}.
- Let j ≥ 2, and suppose x<y<z in Lay_j form a cap. Let w be the point just before x on a j-cup ending at x.
  - If (w,x,y) were a cup, y would end a (j+1)-cup.
  - So (w,x,y) is a cap, and (w,x,y,z) is a 4-cap, which is a contradiction.
- So no three points of Lay_j form a cap, and Lay_j is a cup by (F1).
- That cup ends at max Lay_j, whose longest cup has j points, so |Lay_j| ≤ j. ∎

### Lemma 2 (Z bound, classic two-side)

**Statement.** Let X be classic (with respect to L|R) with no v-cup, where v ≥ 2. Then |X| ≤ (v−1)².

*Proof.* Let Z be the set of first points of 4-caps of X.
- Each 4-cap of X meets both X∩L and X∩R, since each side is 4-cap-free. So its first point lies in L, and
  Z ⊆ X∩L; in particular Z has no 4-cap.
- X∖Z has no 4-cap, so |X∖Z| ≤ C(v,2) by Lemma 1.
- Z has no (v−1)-cup. Suppose z₁<…<z_{v−1} were a cup in Z, and let (z_{v−1}, a, b, c) be a 4-cap.
  - If v−1 ≥ 2 and (z_{v−2}, z_{v−1}, a) is a cap, then (z_{v−2}, z_{v−1}, a, b, c) is a 5-cap.
  - Otherwise z₁…z_{v−1}a is a v-cup. (For v = 2 this is the 2-cup {z₁, a}.)
  - Both are contradictions.
- So |Z| ≤ C(v−1,2) by Lemma 1, and |X| ≤ C(v,2) + C(v−1,2) = (v−1)². ∎

### Lemma 3 (two cups, no polygon condition)

**Statement.** Let X = x₁<…<x_a and Y = y₁<…<y_b be cups with X < Y, and suppose X∪Y has no 4-cap and no
u-cup. Then:
- (a) for a, b ≥ 1, X+y₁ is a cup or x_a+Y is a cup;
- (b) a + b ≤ 2u−3;
- (c) if a = u−1, then x_a+Y is a cup; if b = u−1, then X+y₁ is a cup.

*Proof.*
- (a) If a, b ≥ 2, then (x_{a−1}, x_a, y₁) and (x_a, y₁, y₂) are not both caps, since that would be a 4-cap. If a
  = 1 or b = 1, one of the two sets has only two points.
- (b) By (a), a ≤ u−2 or b ≤ u−2, and both are ≤ u−1. (If a or b is 0, then a + b ≤ u−1.)
- (c) X+y₁, respectively x_a+Y, would be a u-cup. ∎

### Lemma 4 (three cups, no polygon condition)

**Statement.** Let P < Q < R be cups with sizes p, q, r, and suppose P∪Q∪R has no 4-cap and no u-cup, where u ≥ 4.
Then p + q + r ≤ 3u − 6.

*Proof.* Each part has at most u−1 points. If all have at most u−2, we are done.

- **q = u−1.**
  - Lemma 3(c) on P|Q shows that P+q₁ is a cup (it is {q₁} if p = 0). Lemma 3(c) on Q|R shows that q_b+R is a
    cup.
  - These two cups are separated, since q₁ < q_b.
  - Lemma 3(b) gives (p+1) + (r+1) ≤ 2u−3, so p + q + r ≤ 3u−6.
- **q ≤ u−2 and p = u−1.**
  - Lemma 3(c) on P|Q and on P|R shows that p_a+Q and p_a+R are cups. Hence r ≤ u−2.
  - If q ≤ u−3 or r ≤ u−3 we are done, so let q = r = u−2 ≥ 2. Apply Lemma 3(a) to Q|R.
    - If Q+r₁ is a cup, then p_a q₁ … q_b r₁ is a cup with q+2 = u points. Its consecutive triples come from the
      cup p_a+Q, from Q, and from Q+r₁. This is a contradiction.
    - If instead q_b+R is a cup, it has u−1 points, and P | (q_b+R) is a two-cup block with 2u−2 > 2u−3 points.
      This contradicts Lemma 3(b).
- **q ≤ u−2, p ≤ u−2 and r = u−1.** This is the mirror image of the previous case. ∎

The bound 3u−6 is attained for u = 4..8 (SAT, §8).

### Lemma 5 (marker lemma)

**Statement.** Let A have 4-cap-free sides A∩L and A∩R and no (m+1)-cup, with m ≥ 3. Let h be a gap in the
x-order of A such that every m-cup of A has a point on each side of h.

Here h need not be the gap of L|R: the proof uses L|R only for 4-caps and h only for m-cups.

Let E be the set of first points and F the set of last points of the m-cups.
- **(WE)** E or F contains no 3-cap.
- **(Bound)** If A also has no 5-cap, then |A| ≤ m(m−1).

*Proof of WE.* Suppose (p,q,e) is a 3-cap with e ∈ E, and (f,q′,p′) is a 3-cap with f ∈ F. (Only e ∈ E and f ∈ F
are used.) Let D = (e, d₂, …, d_m) be an m-cup, and C = (…, c′, c″, f) another, with c′ = c_{m−2} and
c″ = c_{m−1}.

- **(S1)** (x,e,d₂) is a cap for every x < e, and (c″,f,y) is a cap for every y > f. Otherwise x+D or C+y would
  be an (m+1)-cup.
- **(S2)** e < h < f, because D and C straddle h.
- **(S3)** (p,q,e,d₂) and (c″,f,q′,p′) are 4-caps, by (S1).
  - Each 4-cap has its first point in L and its last point in R. So p, c″ ∈ L and d₂, p′ ∈ R.
  - Hence c″ < d₂.
- **(S4)** No m-cup lies entirely on one side of h. Therefore:
  - (i) (c′,c″,y) is a cap for every y with c″ < y < h;
  - (ii) (x,d₂,d₃) is a cap for every x with h < x < d₂;
  - (iii) (c′,c″,d₂) and (c″,d₂,d₃) are not both cups. Otherwise c₁…c″d₂…d_m would be a (2m−2)-cup, and
    2m−2 ≥ m+1.

**Lemma X.** e < c″ together with (c″,d₂,d₃) a cap is impossible.
- The 4-point rule on e<c″<d₂<d₃ reads ?, ?, cup, cap, where χ(e,d₂,d₃) is a cup by (F1). So χ(e,c″,d₂) is a
  cup.
- The 4-point rule on q<e<c″<d₂ reads ?, cap (S1), ?, cup. So χ(q,e,c″) is a cap.
- Then (p,q,e,c″) is a 4-cap inside L, since p, c″ ∈ L. This contradicts the hypothesis on the sides.

**Lemma X′.** d₂ < f together with (c′,c″,d₂) a cap is impossible.
- The 4-point rule on c′<c″<d₂<f reads cap, cup (F1), ?, ?. So χ(c″,d₂,f) is a cup.
- The 4-point rule on c″<d₂<f<q′ reads cup, ?, cap (S1), ?. So χ(d₂,f,q′) is a cap.
- Then (d₂,f,q′,p′) is a 4-cap inside R, which is a contradiction.

**Cases.** By (S4iii), at most one of (c′,c″,d₂) and (c″,d₂,d₃) is a cup.

1. **(c′,c″,d₂) is a cup, so (c″,d₂,d₃) is a cap.**
   - e = c″ is impossible, since (e,d₂,d₃) is a cup.
   - If c″ < e, the 4-point rule on c′<c″<e<d₂ reads ?, cup, ?, cap, where the last entry is (S1) with x = c″.
     So χ(c′,c″,e) is a cup. But c″ < e < h, so it is a cap by (S4i).
   - If e < c″, Lemma X applies.
2. **(c″,d₂,d₃) is a cup, so (c′,c″,d₂) is a cap.**
   - d₂ = f contradicts (S1).
   - If f < d₂, the 4-point rule on c″<f<d₂<d₃ reads cap (S1), ?, cup, ?. So χ(f,d₂,d₃) is a cup. But h < f < d₂,
     so it is a cap by (S4ii).
   - If d₂ < f, Lemma X′ applies.
3. **Both are caps.**
   - Lemma X and e ≠ c″ give c″ < e. Lemma X′ and f ≠ d₂ give f < d₂; here f = d₂ is impossible because (c′,c″,f)
     is a cup.
   - So c″ < e < h < f < d₂, and:
     - (c′,c″,e) is a cap by (S4i);
     - the 4-point rule on c′<c″<e<f reads cap, cup, ?, ?, so χ(c″,e,f) is a cup;
     - χ(c″,f,d₂) is a cap by (S1), and χ(f,d₂,d₃) is a cap by (S4ii);
     - the 4-point rule on e<f<d₂<d₃ reads ?, ?, cup, cap, so χ(e,f,d₂) is a cup.
   - Now the 4-point rule on c″<e<f<d₂ reads cup, ?, cap, cup. That is two changes, a contradiction. ∎

*Proof of the bound.*
- Let X ∈ {E, F} contain no 3-cap. By (F1), X is a cup.
- Every point of E lies left of h and every point of F right of h, by the straddle hypothesis. If |X| ≥ m, X would
  contain an m-cup on one side of h. So |X| ≤ m−1.
- Every m-cup has its first point in E and its last point in F, so A∖X has no m-cup.
- Lemma 2 with v = m gives |A∖X| ≤ (m−1)². So |A| ≤ m(m−1). ∎

### Lemma 6 (R2 for u = k−1)

**Statement.** Let k ≥ 5 and m = k−1. Let V = P|Q, where P < Q, P is a cup and Q has no 4-cap. Suppose V has no
5-cap, no m-cup and no strong k-set. Then |V| ≤ C(m,2) + m − 3 = C(k−1,2) + k − 4.

*Proof.* We have |P| ≤ m−1.

**Step 0.** If |P| ≤ m−3, then |Q| ≤ C(m,2) by Lemma 1, and we are done.

**Step 1.** Let |P| ≥ m−2. Put Z° = {p₁,…,p_{m−2}}, z = p_{m−2} and W = V∖Z°, so that W∩P ⊆ {p_{m−1}}.
- W has no 4-cap. Such a 4-cap is not inside Q, so its first point is p_{m−1}; call it (p_{m−1},a,b,c).
  - If (p_{m−2},p_{m−1},a) is a cap, it extends to a 5-cap.
  - If it is a cup, then p₁…p_{m−1}a is an m-cup.

**Step 2 (rows).** For x ∈ W, let β′(x) be the size of the longest cup of W starting at x, and F_j = {β′ = j}.
- F_j = ∅ for j ≥ m.
- By the mirror form of Lemma 1, F_j is a cup with at most j points; in particular |F₁| ≤ 1.

**Step 3 (labels).**
- An edge (x,y) of W, with x < y, is **free** if no w ∈ W with w < x makes (w,x,y) a cap.
- α′(x) is the size of the longest cup of W that starts at x with a free first edge, or 1 if there is none. So
  1 ≤ α′(x) ≤ β′(x).
- **Claim 3a.** Let x < y lie in one row F_j, with j ≥ 2.
  - (i) For a j-cup (y, e, …) starting at y, (x,y,e) is a cap. Otherwise x starts a (j+1)-cup.
  - (ii) (x,y) is free. Suppose instead (w,x,y) were a cap. Then by (F3) (W has no 4-cap), (x,y,e) would be a
    cup, against (i).
  - (iii) α′(x) > α′(y). Let (y, d₂, …, d_t) realise α′(y).
    - If t = 1, the free edge (x,y) gives α′(x) ≥ 2.
    - If t ≥ 2, then (y,d₂) is free, so (x,y,d₂) is not a cap. So x+(y,d₂,…) is a cup whose first edge (x,y) is
      free by (ii), and α′(x) ≥ t+1.
  - Consequently, a row with exactly j points carries α′ = j, j−1, …, 1 from left to right.
- **Claim 3b.** Let α′(y) = s ≥ 2, realised by (y, d₂, …), and let x ∈ W with x < y. Then (x,y,d₂) is a cup, so x
  starts an (s+1)-cup. In particular, if α′(y) = m−2, every point of W left of y lies in F_{m−1}.

**Step 4 (Lemma C): |F_{m−1}| + |F_{m−2}| ≤ 2m − 4.**

Suppose otherwise. Then F = F_{m−1} = (f₁<…<f_{m−1}) and G = F_{m−2} = (g₁<…<g_{m−2}) are both full, and by Claim
3a, α′(f_i) = m−i and α′(g_i) = m−1−i.

- **(a) f₂ < g₁.** By Claim 3b at y = f₂, every W-point left of f₂ lies in F, and g₁ ∉ F.
- **(b)** (x,f₁,f₂) is a cap for every x ∈ Z°. Otherwise x+F is an m-cup.
- **(c) (f₁,f₂,g₁) is a cap.** Let (g₁,e₂,…,e_{m−2}) realise α′(g₁) = m−2. By Claim 3b, (f₂,g₁,e₂) is a cup. If
  (f₁,f₂,g₁) were a cup, then f₁f₂g₁e₂…e_{m−2} would be an m-cup.
- **(A1) f_{m−1} < g_{m−2}.** Suppose instead g_{m−2} < f_{m−1}, and let δ be the second point of an (m−1)-cup
  starting at f_{m−1}.
  - (g_{m−2},f_{m−1},δ) is a cap, since otherwise g_{m−2} starts an m-cup.
  - (g_{m−3},g_{m−2},f_{m−1}) is then a cup, since otherwise (g_{m−3},g_{m−2},f_{m−1},δ) is a 4-cap in W.
  - So g₁…g_{m−2}f_{m−1} is an (m−1)-cup, contradicting β′(g₁) = m−2.
- **(A2) (f₁,f_{m−1},g_{m−2}) is a cap.**
  - (f_{m−2},f_{m−1},g_{m−2}) is a cap, since otherwise F+g_{m−2} is an m-cup; this uses (A1).
  - By (F3), (f_{m−1},g_{m−2},v) is a cup for every v ∈ W with v > g_{m−2}.
  - If (f₁,f_{m−1},g_{m−2}) were a cup, then f₁, f_{m−1} followed by an (m−2)-cup starting at g_{m−2} would be an
    m-cup.
- **Case B: (p_{m−3},z,g₁) is a cup.** Then Z° ∪ {g₁} is an (m−1)-cup from p₁ to g₁, and (p₁,f₁,f₂,g₁) is a
  4-cap by (a)–(c). Together they form a strong set of size (m−1) + 4 − 2 = k. Contradiction.
- **Case A: (p_{m−3},z,g₁) is a cap.**
  - (z,g₁,g₂) is a cup. Otherwise, with δ′ the second point of an (m−2)-cup from g₂, (g₁,g₂,δ′) is a cap by
    Claim 3a(i), and (p_{m−3},z,g₁,g₂,δ′) is a 5-cap.
  - So z g₁ … g_{m−2} is an (m−1)-cup.
  - (p_{m−3},z,f₁) is a cup. Otherwise, with δ″ the second point of an (m−1)-cup from f₂,
    (p_{m−3},z,f₁,f₂,δ″) is a 5-cap, by (b) and Claim 3a(i).
  - So Z° ∪ {f₁} is an (m−1)-cup, and (z,f₁,y) is a cap for every y > f₁.
  - Then (z,f₁,f_{m−1},g_{m−2}) is a 4-cap, by this fact, (A2) and (A1). Together with the cup z g₁ … g_{m−2} it
    forms a strong k-set. Contradiction. ∎(Lemma C)

**Step 5.**
- |W| ≤ Σ_{j ≤ m−3} j + (2m−4) = C(m−2,2) + 2m − 4 = C(m,2) − 1.
- Hence |V| = (m−2) + |W| ≤ C(m,2) + m − 3. ∎

Lemma 6 uses m ≥ 4 for the points p_{m−3}, g₂, g_{m−3} and the second points of the various cups.

---

## 3. Proof of the theorem

If L = ∅ or R = ∅, then U has no 4-cap, so |U| ≤ C(k−1,2) < H by Lemma 1. If |U| ≤ 2 there is nothing to prove.
From now on, |U| ≥ 3, x₀ ∈ L and x₁ ∈ R.

The pair (x₀ ∈ A or B, x₁ ∈ A or B) gives four configurations:
- **NN:** x₀ ∈ A and x₁ ∈ B.
- **BN:** x₀ ∈ B and x₁ ∈ A. Reflecting the x-order preserves decomposability (same labels), cups, caps and strong
  sets, and swaps L and R. So BN is NN after reflection.
- **N1:** x₀, x₁ ∈ A, so B lies inside the span of A.
- **N2:** x₀, x₁ ∈ B, so A lies inside the span of B.

Within each configuration, the subcases are exhaustive as listed. All lemmas are applied to subsets of U, which are
classic and satisfy (H3) and (H4).

### Configuration NN (x₀ ∈ A, x₁ ∈ B)

- β ≤ 3: if D ⊆ B were a 4-cap, x₀+D would be a 5-cap by (C).
- α ≤ k−3: for a largest cup C of A, C+x₁ is a cup by (C).

**NN1: β ≤ 2.**
- B has no 3-cap, so B is a cup by (F1), and |B| ≤ k−2 by (H3).
- A has no (k−2)-cup, so |A| ≤ (k−3)² by Lemma 2 with v = k−2.
- Total: (k−3)² + k − 2 = **H**.

**NN2: β = 3 and A ⊆ L.**
- A has no 4-cap (H1), and α ≤ k−4 by (P). So |A| ≤ C(k−3,2) by Lemma 1.
- B has no 4-cap and no (k−1)-cup, so |B| ≤ C(k−1,2) by Lemma 1.
- Total: **H**.

**NN3: β = 3 and A meets R.** Let a* = max A ∈ R, B₁ = B ∩ (−∞, a*) and B₂ = B ∩ (a*, ∞) ⊆ R.
- B₁ is a cup. A 3-cap D ⊆ B₁ satisfies x₀ < D < a*, so x₀+D+a* is a 5-cap by (C).
- B₂ is a cup. A 3-cap D ⊆ B₂ gives the 4-cap a*+D inside R.
- B has no 4-cap and no (k−1)-cup, so |B| ≤ 2(k−1) − 3 = 2k−5 by Lemma 3.
- α ≤ k−4 by (P), so |A| ≤ (k−4)² by Lemma 2 with v = k−3.
- Total: (k−4)² + 2k − 5 = H − (k−4) < H.

### Configuration N1 (x₀, x₁ ∈ A)

B is a cup: a 3-cap D ⊆ B would give the 5-cap x₀+D+x₁ by (C).

**N1a: |B| ≥ 2.**
- β = 2, so α ≤ k−3 by (P), and |A| ≤ (k−3)² by Lemma 2.
- |B| ≤ k−2.
- Total: **H**.

**N1b: B = {b}.** This is case H1 of the sources.
- Every (k−2)-cup C of A satisfies min C < b < max C. Otherwise C+b or b+C would be a (k−1)-cup by (C).
- So Lemma 5 applies to A with m = k−2 ≥ 4 and h the gap of A at b. Its hypotheses hold: A has 4-cap-free sides
  with respect to L|R, no (k−1)-cup and no 5-cap.
- Hence |A| ≤ (k−2)(k−3) = H − 1.
- Total: **H**.

### Configuration N2 (x₀, x₁ ∈ B)

- α ≤ k−4: x₀+C+x₁ is a cup by (C).
- β ≤ 4 by (H2).
- Write a⁻ = min A and a⁺ = max A.

**N2a: β ≤ 2.**
- B is a cup, so |B| ≤ k−2.
- |A| ≤ (k−4)² by Lemma 2 with v = k−3.
- Total: H − (2k−7) < H.

**N2b: β = 3 and A has no 4-cap.**
- |A| ≤ C(k−3,2) by Lemma 1, since α ≤ k−4.
- |B| ≤ C(k−1,2) by Lemma 1.
- Total: **H**.

**N2c: β = 3 and A has a 4-cap.**
- That 4-cap crosses L|R, so a⁻ ∈ L and a⁺ ∈ R.
- Put P₁ = B∩(−∞,a⁻) ⊆ L, P₂ = B∩(a⁻,a⁺) and P₃ = B∩(a⁺,∞) ⊆ R. Each is a cup:
  - a 3-cap D in P₁ gives the 4-cap D+a⁻ inside L;
  - a 3-cap D in P₃ gives the 4-cap a⁺+D inside R;
  - a 3-cap D in P₂ gives the 5-cap a⁻+D+a⁺.
- B has no 4-cap and no (k−1)-cup, so |B| ≤ 3(k−1) − 6 = 3k−9 by Lemma 4 with u = k−1 ≥ 5.
- |A| ≤ (k−4)² by Lemma 2.
- Total: (k−4)² + 3k − 9 = **H**.

**N2d: β = 4 and A has a 4-cap.**
- α ≤ k−5 by (P).
- As in N2c, P₁, P₂ and P₃ are cups, with a⁻ ∈ L and a⁺ ∈ R.
- P₁∪P₂ = B∩(−∞,a⁺) has no 4-cap, since D+a⁺ would be a 5-cap. So |P₁∪P₂| ≤ 2k−5 by Lemma 3.
- |P₃| ≤ k−2.
- |A| ≤ (k−5)² by Lemma 2 with v = k−4 ≥ 2.
- Total: (k−5)² + 3k − 7 = H − (2k−11) < H for k ≥ 6.

**N2e: β = 4 and A has no 4-cap.**
- α ≤ k−5 by (P), so |A| ≤ C(k−4,2) by Lemma 1.
- If a⁻ ∈ R, then A ⊆ R. Reflect: this stays in N2e and gives A ⊆ L. So assume a⁻ ∈ L.
- Then P = B∩(−∞,a⁻) ⊆ L is a cup, since a 3-cap D in P gives the 4-cap D+a⁻ inside L.
- Q = B∩(a⁻,∞) has no 4-cap, since a⁻+D would be a 5-cap.
- So B = P|Q satisfies Lemma 6, and |B| ≤ C(k−1,2) + k − 4.
- Total: C(k−4,2) + (k−4) + C(k−1,2) = C(k−3,2) + C(k−1,2) = **H**. ∎

---

## 4. Case table (u = k−1)

All bounds hold for every k ≥ 6 (`arith.py` checks k = 5..60).

| case | when | bound on A | bound on B | total − H |
|---|---|---|---|---|
| one-sided | L or R empty | — | — | −(k−3)(k−4)/2 |
| NN1 | x₀∈A, x₁∈B, β≤2 | Z, v=k−2: (k−3)² | cup: k−2 | 0 |
| NN2 | β=3, A⊆L | ES: C(k−3,2) | ES: C(k−1,2) | 0 |
| NN3 | β=3, A meets R | Z, v=k−3: (k−4)² | two cups: 2k−5 | −(k−4) |
| N1a | x₀,x₁∈A, \|B\|≥2 | Z: (k−3)² | cup: k−2 | 0 |
| N1b | \|B\|=1 | marker, m=k−2: (k−2)(k−3) | 1 | 0 |
| N2a | x₀,x₁∈B, β≤2 | Z: (k−4)² | cup: k−2 | −(2k−7) |
| N2b | β=3, A 4-cap-free | ES: C(k−3,2) | ES: C(k−1,2) | 0 |
| N2c | β=3, A has a 4-cap | Z: (k−4)² | three cups: 3k−9 | 0 |
| N2d | β=4, A has a 4-cap | Z, v=k−4: (k−5)² | 2k−5 + k−2 | −(2k−11) |
| N2e | β=4, A 4-cap-free | ES: C(k−4,2) | R2: C(k−1,2)+k−4 | 0 |

The only small-k constraint is N2d, which needs k ≥ 6. At k = 5, N2 with β = 4 is empty anyway, since α ≥ 1.

**The grid is exhaustive.** The parameters are: where x₀ and x₁ lie, β, where A lies relative to the gap (⊆ L,
⊆ R, or meeting both), and whether A has a 4-cap.

- **NN.** x₀ ∈ A∩L, so "A ⊆ R" cannot occur, and β = 4 is impossible.
  - β ≤ 2 gives NN1, for every position of A and either 4-cap status.
  - β = 3 gives NN2 if A ⊆ L and NN3 otherwise.
- **BN.** This is NN after reflection.
- **N1.** x₀, x₁ ∈ A, so A meets both sides. β ≤ 2, and β = 1 exactly when |B| = 1. This gives N1a and N1b.
- **N2.**
  - β ≤ 2 gives N2a.
  - β = 3 gives N2b if A has no 4-cap, at any position. If A has a 4-cap, A meets both sides and this is N2c.
  - β = 4 with a 4-cap in A means A meets both sides: N2d. With A 4-cap-free, A ⊆ L or A meeting both gives N2e
    directly, and A ⊆ R gives N2e after reflection.

α is never a case parameter. It enters only through (P) and through the cup bounds of (C).

---

## 5. Why the bound holds

- **The coupling (P).** A cup of A and a cap of B always form a convex set. So the hard instances force A into the
  classic regime, where Z is exact, and leave the polygon condition to act on B alone.
- **What B looks like.** By the cap-gain facts (C), B is a single cup, a 4-cap-free set, two or three cups, or a
  cup followed by a 4-cap-free set.
- **Where the polygon condition enters.** Only Lemma 6 (case N2e) uses (H4) on B. Elsewhere it enters only through
  (P).
- **The single-point case.** The case N1b (one high point inside A) is the only one where the bound needs a
  structural fact about A beyond its cup length. That fact is the marker lemma: the m-cups' first or last points
  form a short cup.
- **Tightness.** Seven case types meet H with equality in their bounds.

---

## 6. Hypothesis and circularity audit

- **Gaps.**
  - Every application of "sides 4-cap-free" refers to the L|R gap. This covers the Z bound, P₁ ⊆ L and P₃ ⊆ R in
    N2c–N2e, B₂ ⊆ R in NN3, and the 4-caps in WE.
  - The straddle gap h in N1b is the position of b, a different gap. Lemma 5's proof keeps the two apart: (S2)
    uses h, (S3) uses L|R.
- **No 5-cap** is used by Lemma 2, by the bound part of Lemma 5, by Lemma 6 and by the cap-gain arguments.
  - It holds for every subset of U.
  - WE itself does not use it.
- **No strong k-set** is used only through (P) and Lemma 6.
- **No circularity.** There is no induction on |U| and no appeal to the theorem at smaller parameters.
  - The u = k rows of the source table use induction to H_{k−1}, but they are not needed here.
  - The H1 chain recursion ("nested singletons") is not needed either, since Lemma 5 bounds A directly.
- **Parameter ranges for k ≥ 6.**
  - Lemma 2 is used with v ∈ {k−2, k−3, k−4}, all ≥ 2.
  - Lemma 3 is used with u = k−1, Lemma 4 with u = k−1 ≥ 5, and Lemma 5 with m = k−2 ≥ 4.
  - Lemma 6 is used with m = k−1 ≥ 5.

---

## 7. Findings against the sources

**Gaps found and repaired.** None is fatal.

1. **Three-cup bound** (a5c toolkit, "dichotomy plus a size-vector check").
   - The pairwise dichotomies with sizes alone do not exclude the size vector (u−1, u−2, u−2). Every pairwise
     condition is consistent with it.
   - Lemma 4 closes this with the chained cup p_a+Q+r₁ and the extended block P | (q_b+R).
   - This step was underspecified, not wrong.
2. **Lemma C, "α′ strictly decreases along a row"** (r2b).
   - The justification "the alternative is a 4-cap (w,x,y,d₂)" is compressed. Claim 3a gives the full argument: a
     cap ending at (x,y) forces (x,y,e) to be a cup, and then x would start a (j+1)-cup.
   - Two side conditions are made explicit: rows with j ≥ 2, and |F₁| ≤ 1.
   - "E is g₁'s (m−2)-cup with α′-label 1" means the α′-realising cup of g₁.
3. **WE** (h1). "Two coincidence checks" means e ≠ c″ and f ≠ d₂. Both are written out here, together with every
   4-point-rule instance.
4. **Missing rows in the a5c case table** (all trivial).
   - The table has no row for N2 with β ≤ 2, none for the one-sided case, and none for the reflection used in N2e
     when A ⊆ R.
   - `cases.py` does handle all three. They are N2a, the one-sided case, and the reflection step in N2e here.

**Simplifications.**

5. **NN3.** The sources cite the cupblock lemma (2k−4). For u = k−1, the polygon-free bound 2k−5 (Lemma 3)
   suffices, so the Lean cupblock lemma is not needed.
6. **N2e.** The sources split off α = k−5 as "R2 needed". With Lemma 6 proved for u = k−1, one application covers
   every α ≤ k−5.
7. **R1.** It concerns u = k only (3k−8) and is not used.

**Checked and found correct as stated.**
- Lemma 1 and Lemma 2 (Z).
- The cap-gain facts (C).
- (P), including degenerate sizes.
- The NN, N1 and N2 subcases of the a5c table for u = k−1.
- The H1 reduction: every (k−2)-cup straddles b.
- Lemma C (a)–(c), (A1), (A2) and Cases A and B, with every needed point existing for m ≥ 4.

---

## 8. Computational evidence (diagnostic, not part of the proof)

Every script is in this directory; outputs sit next to them.
- **Interpreters.** Pure Python and the SAT checks run with `runs/etv-cc-20260930/.venv/bin/python` (pysat
  CaDiCaL 1.9.5). The replays also run with `python3`.
- **Status.** Nothing below is Lean-certified, and no DRAT proofs were produced.

**Library and encoder validation.**
- `selftest.py`, `selftest2.py` (`selftest_out.txt`):
  - checked the helper functions in `alib.py` against brute force on about 27,000 random decomposable sets with
    n ≤ 9 (time-boxed loop; the exact count is in the output file);
  - checked the 4-point rule for decomposable colourings on the same sets;
  - checked the chain-end and chain-start statistics on 3,000 sets.
  - 0 failures.
- `test_enc.py` (`test_enc_out.txt`) checked the independent CNF encoder (`aenc.py`) against `alib.py` semantics:
  - it reproduces the signotope counts 62 and 908 at n = 5, 6;
  - on 300 random signotopes, the no-cup, no-cap and no-strong-set constraints agree with `alib.py`, with 0
    mismatches.

**Replay of this proof on decomposable instances** (`audit_cases.py`, `audit_rand.py`).
- At each case the replay checks every lemma hypothesis, every lemma conclusion, the internal steps (Z parts,
  three-cup cases, WE and the deletion, rows, α′ monotonicity, Lemma C) and the final arithmetic.
- Tight instances from `runs/claude-twoside-a5b-20261002` (`audit_cases_out.txt`):
  - (5,5,6), n = 13: 1,384 distinct instances (`dect556_a.pkl` is a subset of `dect556.pkl`);
  - (5,6,7), n = 21: 10 instances;
  - each instance and its mirror image, 3,088 runs in total.
  - 0 violations. Every hypothesis was re-verified, including no strong k-set and the colouring recomputed from the
    labels.
- Random template-driven greedy decomposable sets (`rand_out_11..16.txt`):
  - 11,359 sets with k = 6, 7, 8;
  - every case type is exercised: N1b 2,450, N2c 2,537, N2d 442, N2e 358, NN3 1,112;
  - WE outcomes: only E cap-free 317, only F cap-free 290, both 1,843;
  - 0 violations.

**SAT on general signotopes** (`sat_lemmas.py`, independent encoding). "SAT at one less" confirms the bound is
attained, so the UNSAT result is not vacuous.

All results are in `sat_summary.txt`.

| check | instance | result |
|---|---|---|
| two cups (Lemma 3) | 2u−2 points, u = 4..7 | UNSAT |
| three cups (Lemma 4) | 3u−5 points, u = 4..8, every size vector | UNSAT; SAT at 3u−6 |
| Z (Lemma 2) | (v−1)²+1 points, v = 3..6, every gap | UNSAT; SAT at one less |
| marker (Lemma 5) | m(m−1)+1 points, m = 3, 4, 5, every (gap, h) | UNSAT; SAT at one less |
| R2, u = k−1 (Lemma 6) | C(k−1,2)+k−3 points, k = 6, 7, 8, every \|P\| | UNSAT; SAT at one less |
| theorem, general signotopes | k = 6: 14 points, every gap | UNSAT; 13 points SAT |
| theorem, general signotopes | k = 7: 22 points, every gap | UNSAT in 35 s; 21 attained by the tight (5,6,7) instances above |

- The k = 7 row is (5,6,7), and it holds even without decomposability.
- k = 8 (32 points) was not attempted. One easy gap took 9.5 s, and the middle gaps are expected to exceed the
  one-minute guideline.

**Lemma internals on general signotopes.** `lemma_models.py` sampled SAT models of each lemma's hypotheses at the
extremal size and one below, and replayed every proof step: Lemma 6 at k = 6, 7, Lemma 5 at m = 4, 5, Lemma 4 at
u = 5, 6, and Lemma 2 at v = 5, 6. Result: 0 violations (`lemma_models_out_*.txt`).
- The models include a full top row with Lemma C tight, for example (|F_{m−1}|, |F_{m−2}|) = (5, 3) at k = 7.
- They also include all three WE outcomes.

**Existing replays re-run.**
- `runs/claude-twoside-a5c-20261002/cases.py`: 0 violations.
- `runs/claude-r2b-20261002/replay_k1.py`: every Case A and Case B prediction holds.
