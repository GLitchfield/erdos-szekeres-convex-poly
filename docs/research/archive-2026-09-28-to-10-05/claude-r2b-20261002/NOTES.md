# R2: proved for u = k-1, open for u = k (claude-r2b-20261002)

**Status.**
- **u = k-1:** proved by hand for every k ≥ 5. Each step is also checked by SAT and replay.
- **u = k:** open.

**Notation.**
- m = u = k-1.
- Z° = (p_1..p_{m-2}), the first m-2 points of P, and z = p_{m-2}.
- W = U \ Z°.
- β'(x) is the longest cup in W that starts at x. Row F_j = {β' = j}.

## Reduction
- If |P| ≤ m-3, then |U| ≤ m-3 + C(m,2) by Erdős–Szekeres.
- Otherwise W is 4-cap-free. A 4-cap in W would start at p_{m-1} and give a 5-cap or an m-cup.
- Each F_j is a cup with at most j points. A 3-cap in F_j gives a 4-cap or a longer cup.
- **Lemma C:** |F_{m-1}| + |F_{m-2}| ≤ 2m-4.
- Hence |W| ≤ C(m-2,2) + 2m-4 = C(m,2) - 1, so |U| ≤ C(m,2) + m-3 = T + k-4. ∎

## Tools
- **Threshold.** Let q lie right of P. Then Z°∪{q} is a cup iff (p_{m-3},z,q) is a cup.
- **Cells.**
  - α'(x) is the longest cup from x whose first edge ends no 3-cap in W.
  - α' strictly decreases along a row; the alternative is a 4-cap (w,x,y,d_2).
  - So a full row has α' = j,…,1. Every W-point left of a point with α' = m-2 lies in F_{m-1}.

## Proof of Lemma C
Suppose F = F_{m-1} = (f_1..f_{m-1}) and G = F_{m-2} = (g_1..g_{m-2}) are both full. Both are cups.
- **(a)** f_2 < g_1. Since α'(f_2) = m-2, every point left of f_2 lies in F, and g_1 does not.
- **(b)** (p_i,f_1,f_2) is a cap for every i. Otherwise p_i∪F is an m-cup.
- **(c)** (f_1,f_2,g_1) is a cap. Otherwise {f_1,f_2}∪E is an m-cup, where E is g_1's (m-2)-cup with α'-label 1.
- **A1.** f_{m-1} < g_{m-2}. Otherwise (g_{m-3},g_{m-2},f_{m-1},d_2) is a 4-cap in W.
- **A2.** (f_1,f_{m-1},g_{m-2}) is a cap.
  - (f_{m-2},f_{m-1},g_{m-2}) is a cap, so (f_{m-1},g_{m-2},v) is a cup for every v.
  - A cup (f_1,f_{m-1},g_{m-2}) would then extend to an m-cup.

**Case B: (p_{m-3},z,g_1) is a cup.** Z°∪{g_1} is an (m-1)-cup, and (p_1,f_1,f_2,g_1) is a 4-cap by (a)–(c). Together they form a strong k-set.

**Case A: (p_{m-3},z,g_1) is a cap.**
- (z,g_1,g_2) is a cup. Otherwise (p_{m-3},z,g_1,g_2,d) is a 5-cap, where d is the 2nd point of g_2's (m-2)-cup and (g_1,g_2,d) is a cap since g_1 ∉ F.
- So z∪G is an (m-1)-cup.
- Z°∪{f_1} is a cup. Otherwise (p_{m-3},z,f_1,f_2,d'_2) is a 5-cap, by (b), where d'_2 is the 2nd point of f_2's (m-1)-cup.
- Hence (z,f_1,y) is a cap for every y.
- By A1 and A2, (z,f_1,f_{m-1},g_{m-2}) is a 4-cap. With z∪G it forms a strong k-set. ∎

**Why it is true.** An (m-2)-cup on the left cannot sit beside two full top rows. It would send a 4-cap from p_1 or z into the head of the second row, and that 4-cap shares its endpoints with a long cup.

## Evidence (diagnostic, not Lean)
- **Lemma C.** UNSAT for every |P|, with no assumption on Z (`cvar.py`, `verify_k1.txt`):
  - m = 5 (n ≤ 12);
  - m = 6 (n = 15..18);
  - m = 7 (n = 25). These two runs took about 110 s each, over the 1-minute guideline.
- **Only two kinds of strong sets are needed.** Forbidding only strong sets with left end p_1 or z already gives UNSAT at m = 5, 6, 7 (`gontype.py`).
- **Replay.** `replay_k1.py` checked 455 violators with the strong-set condition dropped. Every predicted fact held.

## u = k: sharpest obstacle
- **What is needed.** It would suffice that |W| ≤ C(k-1,2) = T-1: Baek's bound plus one hole.
- **Why it is hard.**
  - This is the step R2(k,k) = R2(k-1,k) + 1. Like T(4,k,k) = T(4,k-1,k) + 1, it needs Baek-type control of apex-free (k-1)-cups.
  - The deficit is not row-local. In tight samples it sits in different rows, and k=5 Baek-extremal sets have no cell that is always filled.
- **Lemma C does not reach it.** With m = k it gives only C(k,2)-1.
- **Refuted on tight (6,6) samples:**
  - A virtual far-left point in configuration semantics exists in only 42/80 (`omega.py`). Some slot works in all 42 tested cases, but the slot varies (`omega2.py`).
  - Recolouring 4-caps after deleting k-4 points of P fails for every choice in 82/120 (`recolor.py`).
  - Baek-style Δ deletions work in only 8–22% (`deltak.py`).
- **Holds in 120/120 tight samples:** W minus some k-3 points is an (S)(k-1,k-1) set (`hitWk.py`). Proving this would close u = k via Baek at k-1, but I found no canonical choice.
