# Audit of the 10-03 hand proofs (claude-audit-day-20261003)

Each step was re-derived by hand. 4-point and mixed-triple steps were checked against the signotope rule and (M).
Claims were replayed with independent code (`dlib.py`), with 0 failures unless stated. Diagnostic, not Lean.

**1. Lemma S and the lock (rectify §3): CORRECT.**
- **Hypothesis.** X = A<<B is decomposable. Only DS and (M) are used.
- **Strong formula.** The upper bound is DS. For the lower bound, A-cup ∪ B-cap is middle-determined under every
  interleaving.
- **(S1)** Sliding B past A only lowers the extension indicators.
- **Repair.** For a nested root, locked ⟺ the outer child carries X's number. The core condition follows. Locked ⇒
  every non-nested placement raises that number.
- **New proof of the path form.** An unlocked root un-nests through adjacent swaps, none of which raises any
  parameter. Write f(p,q) for cup X; it falls as p rises and rises with q. Let M = cup A and c₀ ≥ M+1.
  - c₀ ≥ M+2: raise q.
  - No max A-cup starts after min B: raise q.
  - No max A-cup ends before max B: lower p.
  - Otherwise, compress B, then shift the block right. A max cup stays left of max B, and no max cup fits inside
    one gap, so f = M+1 throughout.
- **(S3)** "Sorting" means compressing, which is monotone. The rotation lemma is verified.
- **Replay, n ≤ 8:** 243,100 root splits and 168,236 nested roots.

**2. Tower draft (§3–4.6): CORRECT-WITH-REPAIRS.** Two steps tagged [P] are false as stated.
- **Tower Closure Lemma: correct.** It needs cap X_j = β at every level (so cup Z_j ≤ lo), and lifted points
  strictly right of L*(X₀).
- **§4.5(b): fails at lo = 0.**
  - Counterexample: labels (100,0,101,11), k = 4. Lifting z = 1 into C's band 1 = {0,2} gives the 3-cup (0,1,2),
    whose limit is 2.
  - Repair: at lo = 0, also require band 1 to lie on one side of z. The §4.6 single-point claim needs the same
    repair. (a) and (c) are correct.
- **Reserve: false in concatenation with lifts.**
  - Counterexample: labels (01,11,000,101,001,1000,1001), k = 6, Z = {2,4}, with cap C < cap Y. The tower condition
    holds, yet (0,2,4,5) is a 4-cup in band 2, whose limit is 3.
  - It is correct with no lifts, or in absorption.
- **Wide–wide** needs the invariant F ≤ k−1−β_Y. The menu keeps it.
- **Keep: correct.**
- **Schema: sound.** Closure is checked exactly, so the [C] results stand.

**3. Lemma D and the L4₀/L2₀ reductions (q23): CORRECT** as partial reductions. The residuals are marked OPEN, and
"s = 5 complete" rests on SAT runs I did not re-audit.
- **Hypotheses.** X = A<<B is decomposable, and s = strong X ≥ 3. L2₀ also needs X cored. Lemma F uses
  Fp∩Lu = ∅.
- **Repairs:**
  - R′ follows from R(i), in a stronger form: Fp∩B and Fu∩A are never both nonempty.
  - Case (β) uses R(i).
  - In (β-AA), the classes keep their A-parts, using max B.
  - "p ≥ 5" assumes |B| ≥ 2.
- **Replay:** n ≤ 8 exhaustive (C2–C6 under weakened hypotheses), plus a 360-set corpus with N = 10–12.

**4. Cored structure and case R ⟺ PSL⁺(B) (hypergraph §Q18, §Q15): CORRECT-WITH-REPAIRS.**
- **(a)–(d)** hold on any signotope with L* < R*. They use neither decomposability nor k.
- **Cored-frame lemma.** cup F ≤ α−1 needs the exchange argument of (c).
- **Case R ⟺ PSL⁺(B).**
  - Hypotheses: cap B = cap X = β, cup A = k−1−β, α+β ≥ k+2.
  - Repair: step (c) also needs strong A ≤ k−2. This holds because a strong set inside A has |G|+2 ≤ cup A + cap A
    ≤ k−1.
  - The equivalence holds for each T separately: 3.13M (root, T) pairs.

**5. Three-band reformulation and the one-swap half (bandrule §Q9h): CORRECT-WITH-REPAIRS.**
- **Reformulation: correct.** It is arithmetic at α+β = k+2. Checked on 18.4M partitions.
- **One-swap lemma [C]** holds only for some orientation. A fixed orientation fails 287 times at n = 6, e.g.
  labels (0,100,1011,10100,11,10101).
- **The proved half covers only condition (i) for β-caps.** The cap's first point is ≤ L*, so it lies in M and can
  be dropped. Drops can break (ii): labels (1,000,001,010,011).

**6. W ⇒ PSL and W ⟺ the one-step lemma (lattice §Q21): CORRECT.**
- **Hypotheses:** strong X ≤ k−1, α, β ≥ 2, α+β ≥ k+1.
- **Blocking count.** Blocking takes β−1 red points and α−1 blue points. A gon violation needs k−2 ≥ β−1 points of
  one colour.
- **Where the window enters.** It is used only in OS ⇒ W, where a gon must fit in one level-(α+β−3) domain.
- **Replay:** n ≤ 6 over every pinning: 1,476 instances; W, OS and PSL hold in all of them.

**7. R25 "BRL+ ⇒ BDL" (§1–7, 11, 33): CORRECT** as a conditional reduction. BRL+ remains open.
- **Structure.** The measure is |X|, and the trichotomy is exhaustive.
- **BRL+ use.** BRL+ (the §33 form) is applied only to the smaller B, whose hypotheses §4 verifies. The flipped
  form follows by duality.
- **Weaker conclusion suffices:** the bottom band lies off span A.
- **Repairs (expository):**
  - (Sub) is used without being stated.
  - §3's "B classic" subcase is vacuous.
  - F = ∅ when cap A < β.
- **Replay, n ≤ 7:** 1.26M partitions; BRL+ was invoked 1,664 times and held every time.

Code and outputs are `item*`/`o_item*` in this directory. Job IDs are in the es log entry.
