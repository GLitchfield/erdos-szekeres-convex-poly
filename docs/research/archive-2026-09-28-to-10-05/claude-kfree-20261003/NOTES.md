# Q6: k-free zone profiles (claude-kfree-20261003)

Status tags: **[P]** proved by hand, **[C]** computed (diagnostic, not Lean), **[?]** conjectural.

## 1. Definition
Zones Z_0<…<Z_{m−1}. A profile P=(Cp,Cu) says: a cap (cup) whose first point is in Z_i and last point in Z_j has at most Cp[i][j] (Cu[i][j]) points. N∞(P) is the largest decomposable set satisfying P, with no strong-set condition. Write es(c,d)=C(c+d−2,c−1) for the classical maximum with caps ≤ c and cups ≤ d.

- **Separable class [P].** Cp[i][j]=c−P_i−Q_j and Cu[i][j]=d−R_i−T_j, with P,R nondecreasing and Q,T nonincreasing. Here P_i is the longest chain of external lower-sibling points usable as a prefix of a cap starting in Z_i; Q, R, T are the same for suffixes and for cups.
  - Lemma DS keeps the class closed: P_B(ρ)=max(P_z, 1+P_y), with y the last A-zone before ρ, and dually.
  - The root (no a-cap, no u-cup) is the one-zone profile (a−1,u−1). So **without k, the DS recursion never leaves the separable class.**
  - Block profiles with an interior deficit (122, 222, 2112) are not separable. They are minima of several separable forms ("gated"), which only the coupling cup(A)+cap(B) ≤ k−1 creates.
- **Exact recursion [P].** Seven per-zone patterns dominate all 14 interleavings: E, A, B, AB, BA, A[B]A, B[A]B. All sub-zones are optional and no required counts are needed (ABAB is dominated by AB, and the middle A sub-zone of ABBA only adds constraints).
- **Tools.** `kfc.c` (separable, C) and `kfg.py` (general); SAT cross-checks with `psat`, strong limit off.

## 2. Values
- **Separable class [C].** Exact N∞ equals the best NON-INTERLEAVED (ES-shaped) construction on every profile tested:
  - all 121 distinct profiles from realizable contexts with ≤4 external points, ≤3 levels and c,d ≤ 4 (exact branch and bound);
  - 73 profiles at c=5 (SAT at the construction value, UNSAT one above).
  - 26 profiles at c=5 with values 30–40 are unchecked.
- **Families** (construction formula checked for c,d ≤ 7):
  - one interior upper point: es(c,d)−es(c−2,d);
  - a nested chain U1<U2<…<Ur: es(c,d)−Σ_{i<r} es(c−2,d−i). **[P]** upper bound, with the construction matching;
  - U2U1U2: es−es(c−2,d)−2es(c−2,d−1)−es(c−2,d−2);
  - one lower and one upper point: 2es(c−1,d−1).
- **Kills interact [C].** They are not additive over types (96/336 mixed contexts).
- **Kill-set failing profiles at k=∞ (SAT):**

  | profile | N∞ | value at k=7 | best non-interleaved |
  |---|---|---|---|
  | 22 | 10 | 10 | 10 |
  | 122 | 23 | 21 | 23 |
  | 222 | 15 | 15 | 14 |
  | 1122 | 20 | 20 | 20 |
  | 2112 | 19 | 19 | 18 |

- **Gated block profiles [C]** (SAT; a=4..6, u=4..6, up to 5 blocks):
  - The classic kill-set formula CL (capped at ES(a,u)) is exact on all 133 in-class profiles.
  - The independent-gates extension CL2 = Σ_{i<q}ES(a−1,u−i) + Σ_gates ES(a−s,u−q) + #points is exact on 294 of 315 outside-class profiles.
  - It fails on 21, e.g. 2112 (19 vs 20), 22222 (18 vs 20), and 22 at a=6, u=4 (11 vs 12).
  - 23/522 need a nested optimum (e.g. 222).

## 3. Answer: split
- **On the class that k-free DS actually produces (separable): (a), as a recursion.**
  - Optimal sets have non-interleaved decomposition trees.
  - N∞ obeys a Pascal-type recursion over zone cuts: N(P)=max(1, max over cuts of N(P_left)+N(P_right)). Each child is an interval of zones that gets one boundary extension, and middle zones may be left empty.
  - Families have binomial closed forms. There is no local per-point kill formula.
- **On gated profiles: (b).** Union deficiencies and nesting already exist at k=∞, and they need ≥2 gates. Four of the five kill-set failures have their k-free value as their window value, so they are classical, not window, effects.

## 4. Why, and the obstruction
- **Inflation [P].** Replace each context point e by an ES set of its own budget (c_e,d_e). Chains stay within (c,d), and classical ES then gives |X| ≤ es(c,d)−Σ es(c_e,d_e).
  - Tight for nested chains. Not tight when types mix or an inner point sits between outer points; there the optimum leaves zones empty (L1U2: the zone between the points).
- **Rotation lemma [P].** Let X=A<<B, with A cut as A1|A2 and B lying entirely in the x-gap between A1 and A2. Then the same colouring has a non-interleaved tree, A1<<(B∪A2) or A2<<(A1<<B).
  - So classical nesting is free: A[B]A with B=ES(c−2,d) gives es(c,d).
- **Missing step [?].** For separable P and every interleaved pattern, N_cut(P_A)+N_cut(P_B) ≤ N_cut(P). Equivalently, some optimal construction of a child cuts exactly at its sibling's cluster, so the rotation lemma applies.
- **Gates break this.** Under a binding gate (a second separable form), a nested child's constraints fall on chains the gate already limits, so nesting can win strictly (212 at a=5, u=4: one lower point absorbed in the middle block). Gates also compete for the shared cup budget: the CL2 failures.

## 5. Window implications
- The coupling is exactly what creates gated profiles, and on them the k-free theory already has nesting and union deficiencies: understand these without k first. The separable part is classical and ES-shaped.
- So the general proof needs three parts: (i) the separable cut recursion, (ii) a classical theory of gated profiles (CL2 plus the deficiencies), (iii) the coupling.
- The window rule must reduce to the classical value when the coupling is slack. This happens for 22, 222, 1122 and 2112, and the current rule fails there.

## Files
`kfc.c`, `kf2.py`, `kf3.py`, `kfg.py`, `ctx.py`, `gen_ctx_all.py`, `run_sep.py`, `sat_ctx.py`, `sat_blocks.py`, `sat_cl2.py`, `sat_open.py`.
Outputs: `o_ctx34.txt`, `o_sat_ctx5.txt`, `o_sat_ctx5_hi.txt`, `o_blocks.txt`, `o_cl2.txt`, `o_sat_open.txt`, `o_chk_mis1.txt`, `o_ks_exact.txt`.
