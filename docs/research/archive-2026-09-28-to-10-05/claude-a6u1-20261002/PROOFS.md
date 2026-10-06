# Hand proofs (claude-a6u1-20261002)

Notation and basic facts are those of the audit `runs/claude-audit-6k2k-20261002/AUDITED-PROOF-6k2k.md`.
- (M): for a root split, a mixed triple is a cup iff its middle point is in the lower part.
- (C): gains across a split.
- (P): α + β ≤ k−1.
- Lemmas 1–8 of that file: ES, classic5, Z6, ZR, Θ, L3, the straddle core, Marker6.

"jcf" means no j-cap. 4cf therefore means cap ≤ 3.

Inputs, cited and not re-proved here:
- G(6,k−2,k) = C(k−1,3) + C(k−3,3) (audit 6k2k).
- H(k) = C(k−1,2) + C(k−3,2): the a=5 two-side bound at u = k−1 (audit 567). Its Lemmas 3, 4 and 6 (two cups 2u−3,
  three cups 3u−6, R2 = C(k−1,2) + k−4) are cited too.
- T(5,k−1,k) = C(k−1,3) + k−2: the one-sided a=5 threshold.
- The open u = k−1 cores N2d(k), N2e(k) (k = 8, 9 only) and R2-6(k−1,k), used as black boxes.

## 1. H1-6 is the doubly gated problem DG

The full configuration is F = [q < [A < b]].
- The point q gives a **cap gate** at g: A∩L and A∩R are 5cf, and A is 6cf.
- The point b gives a **cup gate** at h: A has no (k−1)-cup, and every (k−2)-cup straddles h.
- A ∪ {b} has no strong k-set.
- b is interior to span(A); otherwise U is in row NN1 with |B| = 1, which has slack.

Target: |A| ≤ G−1, where G = G(6,k−1,k). By arithmetic (`arith.py`, k = 6..59):

G−1 = T(5,k−2,k) + C(k−3,3) + C(k−3,k−4) = T(6,k−1,k) − C(k−3,4) − 1.

The general form is DG(a,u,k) = T(a−1,u−1,k) + C(k−3,a−3) + C(k−3,u−3).
- At a = 5 this is H1's bound (k−2)(k−3).
- DG is symmetric in a and u. At k = 7, DG(6,6,7) = 28 is self-dual.

## 2. Absorption

**Lemma A1.** In U = A << {b}, every cap through b with at least 3 points is a 3-cap (y,b,y′) with y < b < y′.

*Proof.* By (M), a triple of b and two A-points is a cap iff b is its middle point.
- If b were an endpoint of a cap with ≥ 3 points, the end triple would have its middle point in A.
- If (w,y,b,…) were a cap, the triple (w,y,b) would have its middle point in A.
∎

Consequence: for Y ⊆ A, the set Y ∪ {b} = [Y < b] is decomposable, it has the same t-caps as Y for every t ≥ 4 on every
interval, and its cups and strong sets are those of U. So **any lemma whose hypotheses are interval-wise t-cap-freeness
with t ≥ 4, "no (k−1)-cup" and "no strong k-set" applies to Y ∪ {b} when it applies to Y**, and it bounds |Y| by its
value minus 1.

The same holds for a chain of nested upper singletons: every cap through a marker has 3 points. It also holds dually
for q, which only makes 3-cups.

**Lemma A2.** If Y ⊆ A is a cup and b ∉ span(Y), then Y ∪ {b} is a cup (by (M)), so |Y| ≤ k−3.

**Lemma A3 (NN1-R).** Suppose A = A1 << B1, x0 ∈ A1, x1 = max A ∈ B1, B1 = (y1<…<ys) is a cup with s ≥ 2, and
y1 < b. Then every (k−3)-cup of A1 straddles y1, and A1 has no (k−2)-cup.

*Proof.* For any cup C of A1, C + x1 is a cup by (M) in A, so |C| ≤ k−3. Let C be a (k−3)-cup.
- If max C < y1, then C + y1 + b is a (k−1)-cup. The triple (c,y1,b) is a cup by (M) in U, since y1 ∈ A.
- If min C > y1, then y1 + C + x1 is a (k−1)-cup.
∎

Marker6 (Lemma 8 of 6k2k) with m = k−3 gives |A1| ≤ 2C(k−2,3) = G(6,k−2,k) − (k−3). Hence
|A| ≤ G(6,k−2,k) + 1 ≤ G−1.

## 3. Theorem P (primal reduction, every k ≥ 7)

Run the G(6,k−1,k) table on A = A1 << B1. Below, f1 bounds A1 and f2 bounds B1; the target is G−1. BN is the mirror
of NN.

**NN** (α1 ≤ k−3 by C+x1):
- |B1| = 1: G(6,k−2,k) + 1.
- β1 = 2 with b < y1: Lemma A2.
- β1 = 2 with b > y1: Lemma A3.
- β1 = 3: Z6(k−3) + [C(k−1,2) − 1], with B1∪{b} 4cf.
- β1 = 4, A1 ⊆ L: C(k−3,3) + [T(5,k−1,k) − 1].
- β1 = 4, a1⁺ ∈ R: Z6(k−4) + H(k), which has slack.

**N1:**
- β1 = 3: Z6(k−3) + C(k−1,2) − 1.
- β1 = 2: either B1∪{b} is a cup (A2), or |B1| ≤ k−3, which gives G(6,k−2,k) + k−3 = G−1. Otherwise **(R1) N1b-R**:
  B1 is a (k−2)-cup with b inside its span.
- |B1| = 1 with α1 ≤ k−3: G(6,k−2,k) + 1. Otherwise **(R2)**: B1 = {y} and α1 = k−2.

**N2** (α1 ≤ k−4):
- β1 ≤ 2: slack.
- β1 = 3: Z6(k−3) + C(k−1,2) − 1.
- β1 = 4, A1 5cf: C(k−3,3) + T5 − 1.
- β1 = 4, A1 has a 5-cap: Z6(k−4) + N2d(k) − 1, with blocks at a1±.
- β1 = 5, A1 5cf: C(k−4,3) + R2-6(k−1,k) − 1.
- β1 = 5, A1 has a 5-cap: N2e, which is empty at k = 7.

Every row closes except (R1) and (R2). Each identity was checked numerically by `replay7.py`.

## 4. Duality, and Theorem D (k = 7)

Flipping every label bit gives a decomposable F* on the same points.
- Every triple's colour is swapped.
- The strong-set definition is invariant under the swap.
- Root splits swap their lower and upper parts.
- F* = [[b* < A*] < q*].

So A* has cap gate b* (at h) and cup marker q* (at g). In general this is a DG(k−1,6,k) instance; **only at k = 7 is
it again a DG(6,6,7) instance**, so the same table applies, with q* absorbed by Lemma A1 (dual form). The root split
becomes A* = B1* << A1*, which is configuration N2, and β* = cup(A1) = α1.

**(R2), α1 = 5.** A* = {y*} << A1* is dual N2f, with {y*} 5cf*.
- Reflect so that y < h.
- P* = A1*∩(<y*) is 4cf*. Primally: a 4-cup C < y < h would give the 5-cup C+y left of h.
- Q* = A1*∩(>y*) is 5cf*.
- A1* ∪ {q*} is 6cf*, has no 6-cup* (since A ∪ {q} has no 6-cap) and no strong 7-set, and is decomposable.
- R2-6(6,7) gives |A1| + 1 ≤ 28, so |A| ≤ 28.

**(R1)** (Y a 5-cup, y1 < h < y5, and α1 ≤ 4 by (P)).
- α1 ≤ 2: A1 is a cap, so |A| ≤ 5 + 5.
- α1 = 3: dual N2b gives |A1| + 1 ≤ C(6,2).
- α1 = 4: Y* is a 5-cap* crossing h, so this is dual N2d.
  - The blocks A1*∩(<y1), A1*∩(y1,y5) and A1*∩(>y5) are 4cf*. Primally: C+y1+b, y1+C+y5 and b+y5+C would be
    6-cups.
  - A1* is 5cf*.
  - q* is absorbed, and N2d(7) gives |A1| ≤ 23. With |Y| = 5, |A| ≤ 28.
- **Both views fail together only if B1 is a cup or singleton around b and A1 is a cap or singleton around q**, which
  means |A| ≤ 10.

**Theorem D.** At k = 7, H1-6 (|A| ≤ 28) follows from the inputs together with N2d(7) and R2-6(6,7).

## 5. Theorem N (N2d ⟸ its marker case, every k ≥ 7)

**Statement.** Let V = X|Y|Z have 4cf blocks, a 5cf union, no (k−1)-cup and no strong k-set, and be decomposable.
Then |V| ≤ N(k) = C(k−1,2) + C(k−3,2) + C(k−4,2).

*Proof.* If a block is empty, H(k) applies. Otherwise x0 ∈ X and x1 ∈ Z. Take the root split V = A << B.

**N1** (x0,x1 ∈ A): B is a cup, by x0+D+x1.
- |B| ≥ 2: then α ≤ k−3, so Θ(k−2) + (k−2) = N.
- |B| = 1: this is the core **N2d-M**.

**N2** (α ≤ k−4):
- β ≤ 2: Θ(k−3) + k−2, slack 3k−12.
- β = 3, A in two adjacent blocks: Lemma 2 gives (k−4)² = C(k−3,2) + C(k−4,2), plus C(k−1,2).
- β = 3, A meets X and Z: B∩(<a⁻) ⊆ X, B∩(a⁻,a⁺) and B∩(>a⁺) ⊆ Z are cups, by D+a⁻, a⁻+D+a⁺ and a⁺+D. Three
  cups with B 4cf give 3k−9 (Lemma 4), plus Θ(k−3); slack k−5.
- β = 4 (α ≤ k−5). B is two-sided at a⁺ (D+a⁺ and a⁺+D would be 5-caps).
  - A in one block: C(k−4,2) + H(k) = N.
  - A meets two adjacent blocks, say X and Y: B∩(<a⁻) ⊆ X is a cup and B∩(>a⁻) is 4cf. Lemma 6 (R2) gives
    C(k−1,2) + k−4, plus (k−5)²; slack k−5.
  - A meets X and Z: B is three cups, so 3(k−2) + Θ(k−4); slack 4k−23.

**NN** (α ≤ k−3, β ≤ 3 by x0+D):
- β ≤ 2: Θ(k−2) + k−2 = N.
- β = 3, A ⊆ X∪Y: (k−4)² + C(k−1,2).
- β = 3, A meets Z: B∩(<a⁺) is a cup (x0+D+a⁺) and B∩(>a⁺) ⊆ Z is a cup, so 2k−5 + Θ(k−3); slack 2k−9.

BN is the mirror of NN. ∎

## 6. N2d-M by absorption

Rerun the N2d table on A = A1 << B1 with marker b. Every row closes (b is absorbed into the 4cf, two-sided or R2 bound
of B1, or the row has slack ≥ 1 for k ≥ 6) except three leaves.

**(L1) NN, B1 a (k−2)-cup, y1 < b.** The (k−3)-cups of A1 straddle y1, as in Lemma A3.
- E (first points) is 4cf: by (S1) a 4-cap in E extends to a 5-cap.
- E has no (k−3)-cup, so |A1| ≤ Θ(k−3) + C(k−3,2).
- This is ≤ Θ(k−2) − 1 iff C(k−3,2) ≤ 3k−13, i.e. **k ≤ 8: proved for k = 7, 8**.

**(L2) N1, B1 a (k−2)-cup around b.** A1 must lose 1 below Θ(k−2). Open by hand.

**(L3) N1, B1 = {y}: the double marker.** Open by hand.

The crude bounds overshoot (L2) by 1 at k = 7. (L2) and (L3) live in the classic regime (a = 5, no (k−2)-cup), but
the strong-set condition is still needed: the classic three-block marker allows 14 > 13 at k = 6.
