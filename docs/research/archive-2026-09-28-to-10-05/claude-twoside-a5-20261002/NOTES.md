# Two-side bound, a = 5 (claude-twoside-a5-20261002)

**Status: no proof.** SAT confirms the bound on general signotopes through (5,6,7). Pascal splits exist everywhere tested, but no canonical E exists among pointwise rules. The obstruction is the *size* of E, not hitting the maximum sets. K = maxconv(U), c = longest cup. Everything is diagnostic (Python, CaDiCaL via pysat, no certificates) unless marked **proof**.

## 1. Sanity check (`sanity.txt`, `sat567_n22_probe.txt`)
The encodings `tsat.py` and `tsat3.py` match the DFS generator `ts.py` on model counts. G is attained, and G+1 is UNSAT for every split |L| = 0..n, at (5,4,5) G=7, (5,5,5) 8, (5,5,6) 13, (5,6,6) 14 and (5,6,7) 21. For (5,6,7) the hardest splits took 21–124 s.
- (5,7,7) attains 22 and (5,7,8) attains 31; G+1 is undetermined at small budgets.
- **No counterexample**: decomposability is not needed at these parameters.

## 2. Splits exist and are rigid
A strict split exists in all 217 instances: 157 tight ones (K = 5, 6, 7) and 60 non-tight ones (`split.py`, `satsplit.py`).
- Strict: E_L and E_R are cups; E has no 4-cap and conv E ≤ K-1; E meets every strong K-set, and every (K-1)-cup when c = K-1.
- In every tight instance every split has |E| = 2K-4. So E is itself a tight two-cup block: there is no slack.

## 3. Proved lemmas
- **(L1) Layer lemma, proof.** In a 4-cap-free set, Lay_j = {x : the longest cup ending at x has j points} is a cup with at most j points.
  - If x<y<z in Lay_j were a cap, let w precede x on a longest cup ending at x. Then (w,x,y) is a cap, else y would end a (j+1)-cup, so wxyz is a 4-cap.
  - Hence |L| ≤ C(c_L+1, 2).
- **(L2) Reduction, proof.** Take u = k-1, so c ≤ K-1. If both sides have cups of at most K-2 points, then |U| ≤ 2C(K-1,2) = G-1.
  - So only the case where a side contains a (K-1)-cup has content.
  - Equivalently, the total cup-layer deficiency is at least 2K-3.
- **(L3) Cup-killing, proof.** Let E⁰ = {x ∈ L : x ends no 3-cap of L} ∪ {y ∈ R : y starts no 3-cap of R}, which is two cups. Every cup of at least 3 points in U\E⁰ extends by one point.
  - If its first two points lie in L, the first one ends a 3-cap (w,v,y_1); v can be prepended, since otherwise w,v,y_1,y_2 is a 4-cap.
  - The mirror argument appends a point when the last two lie in R. The mixed case is impossible.
  - **Hence for c = K-1**, every strong K-set that avoids E⁰ is a (K-2)-cup plus a gap-crossing 4-cap.
- **Diagnostic:** E⁰ together with the second cap layers meets every strong K-set and every (K-1)-cup in 172/172 instances. Hitting is easy; doing it with 2K-4 points is not.

## 4. Negative results
- **No pointwise rule (SAT, `sigsat2.py`).** Give each point 13 statistics:
  - the longest cup or cap ending or starting at it, within its side and within U;
  - the largest strong set with it as left or right end;
  - its indices in the cap-end and cap-start layer decompositions of its side.

  No lookup table on these signatures gives a valid split on all 20 tight (5,6,7) instances. With the 8 chain statistics alone it is UNSAT on all 147 tight instances (`sigsat.py`).
- **Specific rules that fail** (`rules*.py`, `maxblock.py`, `layerhit.py`):
  - E_L = Lay_2(L): 53/140 (Lay_2 inside E_L on both sides: 117/147).
  - The second cap layers.
  - E⁰: it meets every strong K-set in 100/162 instances, but also has at most 2K-4 points in only 16.
  - The literal D-analogue, E⁰ of U minus its two extreme points.
  - Second points of longest side cups.
  - One point per cup layer.
  - Transversal cups.
  - Maximum two-cup sub-blocks: only a few percent are valid.
  - E ⊆ E⁰ ∪ E¹: fails in 27/187.
- **E_L depends on R.** In tight567[18], L is extremal in the Erdős–Szekeres sense (15 points) and |R| = 6.
  - E_L must be a 5-cup whose removal leaves c_L = 4. Of the 21 such cups, 15 work.
  - Both classical choices fail for every E_R: L's outer cap-end layer and its outer cap-start layer.

## 5. Obstacle and next steps
At a=4 a canonical 2-point set meets every maximum set. At a=5 the analogue must be a tight a=4 block coupled across the gap; hitting is local by (L3), and the coupling comes from the size requirement.

Next steps:
1. Prove that a split exists without making it canonical, for example by induction on |R| with an exchange step, or by charging deficiency through (L2). By (L2), only the case where a side has a (K-1)-cup matters.
2. Restrict to decomposable U, which is all the gate needs.
3. Certify (5,6,7) by SAT as an `es job` with DRAT output.

Evidence (this directory): `ts.py`, `tsat*.py`, `gen*.py`, `*.pkl`, `split.py`, `satsplit.py`, `fast.py`, `layers.py`, `rules*.py`, `sigsat*.py`.
