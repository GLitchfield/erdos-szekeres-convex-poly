# Two-side bound a=5, second attempt (claude-twoside-a5b-20261002)

**Status: no proof** of the existence of E and no other route to the bound. New: two cross-gap lemmas (proved), a proved reduction of where E is needed, 1,983 more tight instances with splits, and about ten refuted rules. Diagnostic unless marked **proof**.

Notation:
- c = cup(U), K = maxconv(U).
- Lay_i(L): the points whose longest L-cup ending there has i points; Lay'_j(R) is the mirror.
- F, G: the longest U-cup ending, resp. starting, at a point.
- Pred(x): the second-to-last points of longest cups ending at x; Succ is the mirror.
- T = Lay_c(L) ∪ Lay'_c(R).

## 1. Proved
- **(A) Cross-gap cup lemma, proof.** For i, j ≥ 2, the set {x ∈ Lay_i(L) : G(x) ≤ j} ∪ {y ∈ Lay'_j(R) : F(y) ≤ i} is a cup.
  - For x<x' in Lay_i and w ∈ Pred(x), (w,x,x') is a cap (as in L1).
  - (x',y,z) is a cap for z ∈ Succ(y), since otherwise x' starts a (j+1)-cup.
  - So a cap (x,x',y) would give the 5-cap w x x' y z. The mirror argument handles (x,y,y').
  - In particular **T is a cup, so |T| ≤ c.**
- **(B) Layer blocks, proof.** Each Lay_i(L) | Lay'_j(R) is a two-cup block with no 4-cap: w x x' y y' would be a 5-cap.
- **(C) Hard core, proof.** If min(c_L,c_R) ≤ K-3, the bound follows from L1 (when c = K-1) or from the a=4 diagonal bound on the larger side (when c = K, an input). If c = K-1 and both are ≤ K-2, L2 applies. So **E is needed only when min(c_L,c_R) ≥ K-2.**
- **Accounting (c = K-1).** The bound says the total layer deficiency is at least 2K-3. (A) supplies K-1 of it at the top. The other K-2 must come from the polygon constraint, and below the top (A) is never tight.

## 2. Evidence
- **Splits exist** in all 1,983 tight decomposable instances: (5,5,6) ×1,384, (5,6,6) ×589, (5,6,7) ×10 (`decgen.py`, `dect*.pkl`, `allsplit.py`).
- **(A) and (B):** no violation in 467+ instances (`xy.py`, `cumdef.py`).
- **Profile pattern (c = K-1).** Let D_j be the deficiency at levels ≥ j. All instances satisfy D_c ≥ c and D_{c-t} ≥ c+t+1. Here t = 0 is (A) and t = c-2 is the bound. This is bookkeeping only.

## 3. Refuted
- **E ∋ p_1.** True in all 147 stored instances, but false on the mirror of tight556[45] (`mir.py`).
- **E ⊇ Lay_2(L) ∪ Lay'_2(R)** (the literal analogue of D). Fails in 0.3–8.5% of decomposable and 20% of general tight instances, including hard-core ones (`d2core.py`).
- **Structural choices for E** (`h2.py`, `h3.py`, `relaxed.py`, `h10.py`–`h12.py`, `hooks.py`). Each fails on stored instances:
  - E ⊇ T (fails even with a freely chosen cut);
  - one point per layer;
  - E inside the top levels;
  - inner/outer pairings;
  - hooks of the grid.
- **Endpoint hitting** fails in about 3/4 of instances (`h8.py`).
- **Splits that keep k fail about half the time:** U-B 4-cap-free, B 4-cap-free with no (k-3)-cup. Even "the 4-caps have a transversal of at most C(k-3,2) points" fails (`h4.py`, `h9.py`).
- **No pointwise rule** on the hard core: 73 general and 143 decomposable instances (`sigcore.py`).
- **No local exchange.** Valid splits of U-q lie up to 7 points from any split of U. The hit count over maximum admissible blocks has strict local maxima in 9/10 instances (`exch.py`, `localsearch.py`).
- **No common point** of all maximum cups in 30/60 tight (5,6,6) instances (`common.py`).

## 4. Obstacle
A valid E behaves like a cut through both staircases: removing it lowers almost every layer index by exactly one (`shift.py`). The cuts are coupled across the gap: an outer E_L goes with an inner E_R, and the reverse (`compat.py`).
- Hitting tools (L3, (A)) are local.
- The only size tool is the a=4 lemma on E.
- Nothing yet ties the polygon constraint to deficiency below the top level.

**Next steps.**
1. Prove the t = 1 profile step: |T| + |Lay_{c-1}(L)| + |Lay'_{c-1}(R)| ≤ 3c-4.
2. Or work the decomposable case through the root split A << B. When cap B + cup A = K, every union of a maximum cap of B with a maximum cup of A is a K-gon. So E∩B must hit every maximum cap of B, or E∩A every maximum cup of A, which gives a recursion.

Run with `runs/etv-cc-20260930/.venv/bin/python`; helpers are in `base.py` and `genc.py`.
