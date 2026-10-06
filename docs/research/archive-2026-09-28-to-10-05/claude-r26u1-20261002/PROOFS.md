# Hand proofs (claude-r26u1-20261002)

Notation and basic facts are those of `runs/claude-audit-6k2k-20261002/AUDITED-PROOF-6k2k.md`:
- (M): a triple meeting both parts of a root split U = A << B is a cup iff its middle point is in A;
- (C): gains across a split; (P): cup(A) + cap(B) <= k-1 when U has no strong k-set;
- (D): a cap of U meeting B has A-points only at its two ends (dually for cups), and
  strong(U) = max(strong A, strong B, cup A + cap B);
- "jcf" means no j-cap; R_{k-2}(k) := C(k-1,3) + C(k-4,2) is R2-6 at u = k-2 (audited Lemma 11);
- T5(k) := T(5,k-1,k) = C(k-1,3) + k-2 (the one-sided a = 5 theorem, cited as done);
- ZR(w) = C(w+1,3) + C(w-1,2) (audited Lemma 4).

Target of this file: **R2-6 at u = k-1**, i.e. R(k) := T5(k) + C(k-4,2) = C(k-1,3) + (k-2) + C(k-4,2)
(R(7) = 28, R(8) = 47).

---

## 1. Lemma DS (decoupled split) and the exact split recursion

**Zone profiles.** Fix consecutive x-intervals (zones) Z_0 < ... < Z_{m-1}. A *profile* is a pair of upper-triangular
integer matrices Cp, Cu together with a strong limit s and required counts req_z. A set S *satisfies* the profile if
every cap of S whose first point is in Z_i and last point in Z_j has at most Cp[i][j] points, the same for cups with
Cu, S has no strong (s+1)-set, and |S ∩ Z_z| >= req_z. (One- and two-point sets count as caps and cups, so
Cp[i][i] < 1 forces Z_i empty, and Cp[i][j] <= 1 for i < j forbids a point in each of Z_i, Z_j.) Every hypothesis set
used in this project (block cap-freeness, "no u-cup", "every (k-2)-cup straddles h", ...) is such a profile.

**Lemma DS.** Let U be decomposable with root split U = A << B, and fix zones. For a zone z let f_A^z, l_A^z be the
first and last point of A in Z_z (when A ∩ Z_z is nonempty), and similarly f_B^z, l_B^z. Give every point x of B in
Z_z the *sub-zone* sigma(x) = "-" if x < f_A^z, "0" if f_A^z < x < l_A^z, "+" if x > l_A^z, and "u" if A ∩ Z_z is
empty; give the points of A sub-zones relative to f_B^z, l_B^z in the same way. Then:

1. The caps of U are the caps of A and the sequences [a] + D + [a'] where D is a nonempty cap of B, a is absent or a
   point of A before min D, and a' is absent or a point of A after max D. Dually, the cups of U are the cups of B and
   the sequences [b] + C + [b'] with C a nonempty cup of A and b, b' points of B outside C.
2. U satisfies a profile (Cp, Cu, s) iff, with alpha := cup(A),
   - A satisfies Cp_A = Cp (on A's sub-zones), and Cu_A[rho1][rho2] = the minimum of alpha, Cu[z1][z2],
     Cu[y][z2] - 1 (y in L), Cu[z1][y'] - 1 (y' in R) and Cu[y][y'] - 2 (y in L, y' in R), where rho_i = (z_i, sigma_i),
     L = {y < z1 : B ∩ Z_y nonempty} ∪ ({z1} if sigma1 in {0,+}), R = {y > z2 : B ∩ Z_y nonempty} ∪ ({z2} if
     sigma2 in {-,0}), and the sub-zones are relative to B's thresholds;
   - B satisfies the mirror profile: Cu_B = Cu, and Cp_B given by the same formula from Cp, with A in place of B and
     s - alpha in place of alpha;
   - both have no strong (s+1)-set.

*Proof.* (1) is (D) together with (C): an interior A-point of a cap meeting B would be the middle of a mixed
consecutive triple, a cup by (M); conversely every new consecutive triple of a + D + a' is mixed with its middle in B,
hence a cap. Dually for cups.

(2) By (1), the caps of U meeting B are exactly the sequences [a] + D + [a']. Fix such a D with first point in
sub-zone rho1 = (z1, sigma1) and last point in rho2 = (z2, sigma2). The cap [a] + D + [a'] has first zone zone(a) (or
z1) and last zone zone(a') (or z2). A point a of A precedes min D iff either its zone is < z1, or its zone is z1 and
f_A^{z1} < min D, i.e. sigma1 in {0, +}. So the set of zones of admissible a's is exactly L, and the constraints for
all admissible (a, a') together say |D| <= the stated minimum. Caps inside A are unchanged, which gives Cp_A = Cp;
cups are dual. By (D), strong(U) <= s iff strong(A), strong(B) <= s and cup(A) + cap(B) <= s; the latter is
cap(B) <= s - alpha. ∎

**Corollary (split recursion).** Let M(pi) be the largest decomposable set satisfying pi. Then

M(pi) = max( 1 [if sum req <= 1], max over patterns and alpha of M(pi_A) + M(pi_B) ),

where, per zone, the *pattern* is the interleaving of f_A, l_A, f_B, l_B. The 14 interleavings give 11 distinct
sub-zone structures (E; A only; B only; A before B; B before A; ABAB; BABA; ABA with a single B-point; ABBA with
>= 2 B-points; BAB; BAAB). In each, the sub-zones that contain a threshold point get required count 1 (2 for the
"0" sub-zone of ABBA/BAAB), a single-point sub-zone gets diagonal limit 1, and a zone's own required count is
distributed over its sub-zones. alpha ranges over max(1, s - max Cp) .. min(s-1, max Cu): for the actual
alpha* = cup(A), alpha = max(alpha*, s - max Cp) is in range and satisfies both caps.

*Proof.* Every U with |U| >= 2 has a root split. Its actual pattern is one of the 14, and by Lemma DS A satisfies
pi_A and B satisfies pi_B, with the required counts met by the threshold points. So |U| = |A| + |B| is bounded by
the right side. Only this direction is needed for upper bounds. The converse (every pair of solutions interleaves
consistently) holds by placing, in each zone, A's "-" points, then B's points, then A's "0" points, then the rest;
it is used only for the lower bound, which the SAT witnesses give directly. ∎

**Normalisation (exact).** Zones whose diagonal limit is < 1 are dropped (and the profile is infeasible if such a
zone is required). Off-diagonal limits <= 1 are equivalent to 1. Two adjacent zones i, i+1 are merged when their rows
and columns agree in Cp and Cu and Cp[i][i] = Cp[i][i+1] = Cp[i+1][i+1] (same for Cu); their required counts add.

**What the computation certifies.** `hyb.children` implements the Corollary, `psat.py` decides "is there a
decomposable set of size n satisfying pi" by SAT. Zone boundaries are free variables, the colouring comes from
canonical binary labels (model counts 8, 62, 718 at n = 4, 5, 6 match audit 5kk), and every SAT model is re-checked
with the audited `lib6.Inst`. M(root) <= N therefore follows from: Lemma DS, the encoder's completeness (every valid
set is a model), and CaDiCaL's UNSAT answers (no DRAT). Validation:
- the split recursion agrees with direct profile SAT on T(5,5,6) = 14, R2-6(4,6) = 11, R2-6(5,6) = 15,
  N2d(6) = 14 and DG(6,5,6) = 14;
- it agrees on 1,283 + 712 random small profiles with required counts 0..3 (`o_hval3.txt`, `o_hval4.txt`; 0
  mismatches);
- 9,734 cached split-derived maxima (values <= 21) were re-checked by direct profile SAT, with 0 mismatches
  (`o_tcache2.txt`).

The certification (`hrun3.py target`) bounds each child pair as follows: the smaller side is computed exactly, and
the larger side is certified by UNSAT at the needed size, by recursive splitting, or by **coarsening dominance**.
Coarsening dominance uses the fact that merging zones (taking the max limit, dropping required counts) only enlarges
the class, so a cached bound for the coarsening bounds the profile. Reflection and duality (flipping every label
bit) preserve M, and cache keys are canonical under both.

---

## 2. Theorem R: the R2-6 table at u = k-1 (every k >= 7)

**Statement.** Let V = P|Q be decomposable, P 4cf, Q 5cf, V 6cf, no (k-1)-cup, no strong k-set. Then
|V| <= R(k), provided the following sub-lemmas hold at k (all decomposable, no (k-1)-cup, no strong k-set):
- **MC(k)** (marker core): if V = A << {b} is such an R2-6 instance, then |A| <= R(k) - 1;
- **N2d(k)**: three consecutive 4cf blocks with a 5cf union have <= C(k-1,2) + C(k-3,2) + C(k-4,2) points;
- **ThC5(k)**: blocks cup | 4cf | 4cf with a 5cf union have <= C(k-1,2) + C(k-3,2) + (k-5) points;
- **R3(k)**: blocks cup | 5cf with a 6cf union have <= T5(k) + (k-5) points;
- **L3S(k)**: blocks X|Y|Z, each 4cf, X∪Y and Y∪Z 5cf, union 6cf, have <= R(k) - C(k-4,3) =
  C(k-2,2) + C(k-3,2) + 2C(k-4,2) + (k-2) points.
The inputs are T5(k), audited Lemma 11 (R_{k-2}), ZR, ES (audited Lemma 1) and (P).

*Proof.* P = ∅ gives T5(k); Q = ∅ gives C(k-1,2). Otherwise take the root split V = A << B, with alpha = cup(A),
beta = cap(B), alpha + beta <= k-1 by (P). The gains are those of audited Lemma 11 (D+a⁻, a⁻+D, a⁻+D+a⁺).

| row | condition | bound for A | bound for B | slack |
|---|---|---|---|---|
| B1 | beta = 1, alpha <= k-3 | R_{k-2} (Lemma 11) | 1 | -(k-3) |
| **B1m** | beta = 1, alpha = k-2 | **MC(k)** | 1 | 0 |
| B2 | beta = 2 (so alpha <= k-3) | R_{k-2} | cup: k-2 | 0 |
| B3 | beta = 3, alpha <= k-4 | ZR(k-3) | 4cf: C(k-1,2) | 0 |
| B4P | beta = 4, A ⊆ P | 4cf: C(k-4,2) | 5cf: T5(k) | 0 |
| B4Q | beta = 4, A ⊆ Q | 5cf: C(k-3,3) | **N2d(k)** on B∩P, B∩Q∩(<a⁻), B∩(>a⁻) | 0 |
| B4S | beta = 4, a⁻ ∈ P, a⁺ ∈ Q | ZR(k-4) | **ThC5(k)** on B∩(<a⁻), (a⁻,a⁺), (>a⁺) | 0 |
| B5P | beta = 5, A ⊆ P | C(k-5,2) | **R3(k)** on B∩(<a⁻), B∩(>a⁻) | 0 |
| B5Q | beta = 5, A ⊆ Q | C(k-4,3) | **L3S(k)** on B∩P, B∩Q∩(<a⁻), B∩(>a⁻) | 0 |
| B5S | beta = 5, straddle (k >= 8) | ZR(k-5) | (k-3) + ThC5(k) | <= -3 |

- **Why beta = 1 splits as B1/B1m.** A cup of A of length k-2 together with any two points of B would be a strong
  k-set by (P) (two points form a 2-cap). So alpha = k-2 forces |B| = 1: the marker core is exactly V = A << {b}.
  Conversely beta = 2 forces alpha <= k-3, so A is an R2-6 instance at u = k-2 (Lemma 11).
- **Block hypotheses** (the same gains as in audited Lemma 11):
  - B4Q: D+a⁻ ⊆ Q and a⁻+D ⊆ Q give the two Q-blocks 4cf;
  - B4S: D+a⁻ ⊆ P makes B∩(<a⁻) a cup, a⁻+D+a⁺ and a⁺+D ⊆ Q make the other two 4cf;
  - B5P: D+a⁻ ⊆ P makes B∩(<a⁻) a cup, a⁻+D makes B∩(>a⁻) 5cf;
  - B5Q: X∪Y = B∩(<a⁻) is 5cf by D+a⁻, Y∪Z ⊆ Q;
  - B is 5cf when beta = 4 and 6cf when beta = 5.
- **B5S.** F, the set of first points of 5-caps of B, lies in B∩(<a⁻), since B∩(<a⁺) and B∩(>a⁻) are 5cf. So F is a
  cup, and by the extension step (B 6cf) F has no (k-2)-cup, so |F| <= k-3. B∖F is 5cf with the ThC5 blocks.
- **Arithmetic.** `arith.py` checks every row for k = 7..40. The identities are
  ZR(k-3) + C(k-1,2) = R, C(k-3,3) + N2d = R, ZR(k-4) + ThC5 = R and C(k-5,2) + R3 = R. ∎

**Status of the sub-lemmas.**
- N2d(k): reduces by hand to its marker case N2d-M (a6u1 Theorem N).
- MC(k): see §3.
- ThC5, R3, L3S: open by hand for general k.
- At k = 7 every sub-lemma is SAT-decided (NOTES.md). There A is a single point in B5P and B5Q, and B5S is empty.

---

## 3. The marker core MC(k): absorption reduces it to four leaves

**Setting.** V = A << {b} is an R2-6(k-1) instance (P 4cf, Q 5cf, 6cf, no (k-1)-cup, no strong k-set,
decomposable) with cup(A) = k-2. **Target:** |A| <= R(k) - 1. Since A ∪ {b} has no (k-1)-cup, no (k-2)-cup of A
lies entirely on one side of b.

**Lemma A1 (a6u1).** Every cap of V through b with at least 3 points is a 3-cap (y, b, y') with y < b < y'.

**Lemma A2.**
- (a) Let X be a set of points of A lying in one x-interval I, with b ∈ I. For every t >= 4, X ∪ {b} has the same
  t-caps as X. It is decomposable, and its cups and strong sets are those of V.
- (b) If X is a cup and b ∉ span(X), then X ∪ {b} is a cup.

*Proof.* (a) follows from Lemma A1, plus the fact that subsets of decomposable sets are decomposable (restrict the
labels). (b) Every new triple has b at an end and its middle point in A, so by (M) for V it is a cup. ∎

So b can be **absorbed**: if a lemma bounds a block-structured set whose blocks are t-cap-free with t >= 4 (or cups
not containing b in their span), it bounds B1 ∪ {b} as well, and B1 loses one point.

**Theorem MC-P.** Let A = A1 << B1 be the root split (alpha1 + beta1 <= k-1). Run the table of Theorem R on A and
absorb b into B1. Every row closes with |A| <= R - 1 except these four leaves:

| leaf | row of A's table | situation | needed |
|---|---|---|---|
| **DM** | B1m | B1 = {y}, cup(A1) = k-2: every (k-2)-cup of A1 straddles both y and b (double marker) | \|A1\| <= R - 2 |
| **L2** | B2 | B1 is a (k-2)-cup with min B1 < b < max B1 | \|A1\| <= R_{k-2} - 1 |
| **L6** | B4S | b lies inside span(X), X = B1∩(<a1⁻) the cup block of cup\|4cf\|4cf | \|B1∪{b}\| <= ThC5(k) |
| **L7** | B5P | b lies inside span(X), X = B1∩(<a1⁻) the cup block of cup\|5cf | \|B1∪{b}\| <= R3(k) |

*Proof (row by row).*
- **Degenerate.** If A ∩ P = ∅, A is 5cf and |A| <= T5 <= R - 1. If A ∩ Q = ∅, |A| <= C(k-1,2).
- **B1** (beta1 = 1, alpha1 <= k-3): |A| <= R_{k-2} + 1 <= R - 1.
- **B2** (beta1 = 2, so B1 is a cup and A1 has no (k-2)-cup).
  - If b ∉ span(B1), Lemma A2(b) gives |B1| <= k-3, so |A| <= R_{k-2} + k-3 = R - 1.
  - If |B1| <= k-3, the same bound holds.
  - Otherwise we are in leaf L2.
- **B3.** B1 ∪ {b} is 4cf with no (k-1)-cup, so |B1| <= C(k-1,2) - 1.
- **B4P.** B1 ∪ {b} is 5cf: T5 - 1.
- **B4Q.** B1 ∪ {b}, with b put into the block of its position, has three 4cf blocks and a 5cf union: N2d - 1.
- **B4S.** If b ∉ span(X), B1 ∪ {b} has the ThC5 block structure: ThC5 - 1. Otherwise we are in leaf L6.
- **B5P.** Likewise with R3, or leaf L7.
- **B5Q.** B1 ∪ {b} keeps the L3S structure (blocks 4cf, adjacent unions 5cf): L3S - 1.
- **B5S** (k >= 8). The row has slack <= -3.

The arithmetic is that of Theorem R, minus 1. ∎

**Remarks.**
- If b ∈ Q, then L6 and L7 cannot occur, because X ⊆ P. So MC with b ∈ Q reduces to DM and L2 alone.
- **DM** is the same problem with two nested markers. Each nested upper singleton makes only 3-caps (Lemma A1), so
  iterating Theorem MC-P would absorb the whole chain at once. Its leaves would again be cup-block rows of L2/L6/L7
  type. This iteration is a sketch only and was not carried out.
- **L2.** Write B1⁻ = B1∩(<b) and B1⁺ = B1∩(>b). A1 has cups of A1 extended by B1-points and by b: y + C + y' + b is a
  cup when max C < y' < b. So every (k-3)-cup C of A1 contains B1⁻ or B1⁺ in its span. A1 is therefore an
  R2-6(u=k-2) instance with a "two-alternative" cup gate. §5 reduces this leaf further by hand.

---

## 4. Status at k = 7 (SAT, decomposable; diagnostic, not Lean)

All values below come from the split recursion of §1 with profile SAT (`hrun3.py target`, shared cache `pcache/`).

**Theorem R rows** (job 20261002-231750-699433, `o_t_r26.txt`). M(R2-6(6,7)) <= 28 is certified, with 64 tight
pairs. Tight rows:
- B2: 5 + 23;
- B3: 13 + 15;
- B4P: 3 + 25;
- B4Q: 4 + 24;
- B4S: 5 + 23;
- B1m (the marker core): 1 + 27, with b inside P, inside Q, or at the cut;
- B5P (A = {a}): 1 + 27.

B5Q has slack: L3S(7) <= 26. The sub-lemma values at k = 7 are T5 = 25, N2d = 24, ThC5 = 23, R3 = 27 (attained) and
L3S <= 26.

**Theorem MC-P leaves** (jobs 20261002-235624-f85215 for mcQ and 20261002-235812-033a69 for mcP). MC(7) <= 27 in
both cases (b in Q, b in P).
- **DM is tight**: |A1| = 26 = R - 2 is attained.
- **L2 is tight**: |A1| = 22 = R_{k-2} - 1 is attained.
- **L6 and L7 have slack**: every such child pair sums to <= 26.
So DM and L2 are the essential leaves.

**What is proved by hand and what is not.**
- Lemma DS, Theorem R (as a reduction) and Theorem MC-P (as a reduction) are proved by hand here.
- MC(k), ThC5(k), R3(k), L3S(k), and N2d-M(k) (for N2d), are proved for k = 7 only, by SAT.
- For general k they remain open (see NOTES.md, "Missing statements").

---

## 5. A partial reduction of leaf L2 (hand)

**Setting.** We are in L2: V = A << {b}, A = A1 << B1, with B1 = (y_1 < ... < y_{k-2}) a cup and y_1 < b < y_{k-2}.
- alpha1 <= k-3, so A1 is an R2-6 instance at u = k-2.
- y⁻ := max(B1 ∩ (<b)) and y⁺ := min(B1 ∩ (>b)).
- **Needed:** |A1| <= R_{k-2} - 1.

**Lemma L2-abs.**
- (i) If A1 ∪ {y⁻} has no (k-2)-cup, or A1 ∪ {y⁺} has no (k-2)-cup, then |A1| <= R_{k-2} - 1.
- (ii) A1 ∪ {y⁻} has a (k-2)-cup iff some (k-3)-cup C1 of A1 has min C1 > y⁻ and max C1 > y_{k-2}.
- (iii) Symmetrically, A1 ∪ {y⁺} has a (k-2)-cup iff some (k-3)-cup C2 of A1 has max C2 < y⁺ and min C2 < y_1.
- (iv) In the remaining case, max C2 and min C1 both lie strictly between y⁻ and y⁺. In particular A1 has points
  in that gap.

*Proof.*
- (i) Since y⁻ ∈ B1 is upper relative to A1, every cap of A1 ∪ {y⁻} through y⁻ has A1-points only at its ends,
  so it is a 3-cap (a, y⁻, a'). Hence A1 ∪ {y⁻} keeps the hypotheses "P-part 4cf, Q-part 5cf, 6cf". It is
  decomposable and has no strong k-set, being a subset of V. If it also has no (k-2)-cup, audited Lemma 11 gives
  |A1| + 1 <= R_{k-2}. The same argument works for y⁺.
- (ii) A cup through y⁻ is C + y⁻ or y⁻ + C with C a cup of A1.
  - C + y⁻ + b is a cup of V: its last triple has middle point y⁻ ∈ A. So |C + y⁻| <= k-3.
  - If y⁻ + C has k-2 points and some y' ∈ B1 lies after max C, then y⁻ + C + y' is a (k-1)-cup of A, which is
    impossible. So max C > y_{k-2}.
  - Conversely, y⁻ + C is always a cup, by (M) in A.
- (iii) is symmetric to (ii).
- (iv) As noted in §3, every (k-3)-cup of A1 contains B1∩(<b) or B1∩(>b) in its span.
  - C2 ends before y⁺, so it must contain B1∩(<b), giving max C2 > y⁻.
  - Likewise min C1 < y⁺. ∎

So L2 is open only when A1 has a "left" (k-3)-cup ending in the gap (y⁻, y⁺) and a "right" (k-3)-cup starting
there. This resembles the straddle core (audited Lemma 7), but here not every (k-3)-cup straddles one gap, so
Lemma 7's step (S4) is unavailable. That is the precise point where the argument stops.
