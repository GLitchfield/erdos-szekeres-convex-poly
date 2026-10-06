# Kill-set rule for cap profiles (claude-killset-20261002)

All results here are diagnostic: pysat/CaDiCaL, with every SAT model re-verified independently. Nothing is Lean-checked.

## 1. Conjecture KS (single-gate rule)
**Setting.**
- Blocks B_1..B_r with cap(B_b) ≤ a−1−d_b. Unions of two or more blocks only satisfy the global bound a−1.
- No u-cup and no strong k-set. The window is a+u ≥ k+4.
- In any order, the blocks are:
  - q ≥ 1 blocks with d = 1 (one of them is the *hub*);
  - at most one *gate* block with d = s, where 2 ≤ s ≤ a−3;
  - p point blocks with d = a−2.

**Labels.** Words of length k−2 over {U, D} with #U ≤ u−2 and #D ≤ a−2; T counts them. The *bottom* words have #D = a−2.

**Kill family K.** K is the set of bottom words w = U^i D^t… such that either
- i ≥ q, or
- i = q−1 and t < s (with no gate, every word with i = q−1).

K is monotone.

**Claim.** max|V| = T − |K| + p (capped at T). Explicitly,

**V = T(a−1,u,k) + Σ_{i=0}^{q−2} C(k−3−i, a−3) + C(k−1−q−s, a−2−s) + p.**

- **Labeling.** The hub holds every non-bottom word. The i-th other d=1 block holds U^i D·*, the gate holds U^{q−1}D^s·*, and each point block holds one word.
- **Regimes.** Equivalently V = T(a−1,u,k) + CL, where CL is the classic value at m = k−a+2:
  CL = Σ_{i<q} ES(a−1, m−i) + ES(a−s, m−q) + p.
  The same CL formula, with u in place of m, is also exact in the classic regime.
- **Specializations.**
  - TS: q = 2.
  - R_s: q = 1 with gate s.
  - Θ_s: q = 2 with gate s−1.
  - Four cups at a=4: 4k−13.
- The value does not depend on the block order.

## 2. Tests
In every row, SAT holds at the KS value and UNSAT at KS+1.

| scope | instances | result |
|---|---|---|
| Sweep of all in-class block profiles: a=4 (r≤5, k=6..8) and a=5 (r≤4; (u,k) = (5,6),(6,6),(5,7),(6,7)); 74 profiles including reorderings | 228 | exact |
| a=4: 11111, 1111, 1121, 12121, 21112, 2112, 212, 22122 (k ≤ 9) | 13 | exact |
| a=5: 123, 133, 313, 213, 321, 1333 at (6,7); 313, 213 at (7,7) | 11 | exact |
| a=6: 124, 412, 1344 at (4,7); 14 → 21 and 414 → 22 at the window (5,7) | 9 | exact |
| general signotopes (subset) | 10 | exact |

That makes 18 new profiles in the final batch (`out_final.txt`).

**Failures outside the class (two or more gates):**

| profile | a; u,k | SAT | rule |
|---|---|---|---|
| 22 | 5; 6,7 | 10 | 9 |
| 122 | 5; 6,7 | 21 | 20 |
| 222 | 5; 6,7 | 15 | 13 |
| 1122 / 2112 | 5; 5,7 | 20 / 19 | 19 |

**Mechanism.**
- A bottom 3-cup is nested inside a cup block, between two upper points (BAB interleaving).
- The upper part then sees that block split in two, under a union bound.
- So any extension past one gate needs union deficiencies.

**Separable constructions fall short even inside the class.**
- `sepdp.py` reproduces R_s, Θ_s and the cup counts.
- It misses pt|cup|pt at a=4: the true value is k+1, the DP gives k.

## 3. Proof idea
**(1) Classic part: iterated endpoint (Pascal) split** (hand sketch, any signotope, gate as the first block).
- Set E_0 = S, and let E_{j+1} be the first points of (a−1)-caps inside E_j.
- **Sizes.** D_j = E_j∖E_{j+1} has no (a−1)-cap and no (m−j)-cup, so |D_j| ≤ ES(a−1, m−j).
- **Position.** No block holds an (a−1)-cap, so each such cap crosses a boundary, and E_j lies in the first q+1−j blocks.
- **End of the peel.** E_q lies in the gate and E_{q+1} = ∅, so |E_q| ≤ ES(a−s, m−q).
- **Result.** The total is CL. Labeling D_j by U^j D is the kill-set labeling.
- **Open.** A gate in the middle is unproved.

**(2) Window.**
- KS satisfies V_Π(a,u,k) = V_Π(a,k−β,k) + T(β+1,u,k) for k−u+1 ≤ β ≤ a−3 (checked for a ≤ 9). So the medium-β root split closes by induction on u.
- β = a−2 with A off the hub reduces to (1).
- **Open:** A meeting the hub, and small β. These are r2a's cores. KS already contains the four-cup block that stalled Θ_3, but r2a's nested-TS case probably leaves the class.

**Refuted shortcut.** The claim was that the first points of (a−1)-caps contain no (k−a+2)-cup. It is false (`lemZ.py`): a counterexample exists at a=4, u=k=7, n=16 = T, and in general signotopes too.

## Files and caveats
- `pf.py` (SAT with variable cuts), `run.py`, `maxsat.py`, `ks.py`, `sepdp.py`, `nestdp.py`, `lp*.py`.
- `bidp.py` (a general interleaving DP) blew up and was abandoned.
- CaDiCaL cannot be interrupted, so the budget option was a no-op.
- Two runs that only tested n > T were stopped.
- Nothing was logged to `es`.
