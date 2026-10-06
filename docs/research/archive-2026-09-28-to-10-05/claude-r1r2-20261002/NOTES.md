# R1 (three cups) and R2 (cup | 4-cap-free), claude-r1r2-20261002

## R1: proved for all k >= 4; the base k <= 7 is checked by SAT only

**Statement.** If P|Q|R are cups with no 4-cap and no strong k-set, then |U| <= 3k-8 for every k >= 4 (false at k=3). The bound is tight for k = 4..9. For k = 5..9, the tight size vectors are exactly those with every part in [k-4, k-1].

**Base case (exhaustive SAT).** For k = 4..8 at n = 3k-7, every size vector is UNSAT under two independent encodings: `r1sat.py` (chain variables) and `r1sat_direct.py` (one clause per forbidden set); see `r1_base_sat.txt`. The chain-variable encoding also covers k = 9, 10.

**Claim D3 (by hand).** Let M = conv(U) >= 7, and let F' be the strong M-sets that avoid p2 and r_{-2}. Then some q* in Q lies in every S in F'. So D3 = {p2, q*, r_{-2}} meets every strong M-set, and induction (M = k-1) gives R1 for k >= 8.

Notation: S = C ∪ {x}, with an optional apex x and (l,x,r) a cap; C = C_P ∪ C_Q ∪ C_R with sizes a, h, g; C_Q = c1 < ... < c_h. Each move below gives a strong (M+1)-set, which contradicts maximality.
1. **Ends.** a, g <= 2 (the cupblock moves M1/M2). If a = 2 then C_P = {p1, π} with π >= p3; if g = 2 then C_R = {ρ, r_last}. Hence h >= M-5.
2. **Run.** If h >= 3, every Q-point strictly between c2 and c_{h-1} (other than x) inserts, because all new triples lie in Q. So J = Q[A..B] ⊆ S, with A = idx c2 and B = idx c_{h-1}. Moreover M = a+g+3+(B-A)+ε, where ε = [x ∉ J].
3. **Gaps.** Let a = 2 and let y in Q lie between c1 and c2. If (π,c1,y) is a cap, then no-4-cap makes (p2,π,c1) a cup, and p2 inserts. So (π,c1,y) is a cup, and y inserts unless y = x. The mirror case uses r_{-2}. So each gap lies inside {x}.
4. **Cores.** J*(S) = Q[α..β], where α = idx c1 if a = 2 (else A) and β = idx c_h if g = 2 (else B). If h = 2 (at M = 7 this forces a = g = 2 plus an apex), J* = Q[idx c1..idx c2]. By steps 2–3, J*(S) ⊆ S.
5. **Crossing.** Suppose β(S) < α(S'). Then C_P(S) ∪ {c1} ∪ (Q from c2 to c'_{h'-1}) ∪ {c'_{h'}} ∪ C_R(S') is a cup. Its junction triples come from C or C', or from step 3. By step 2 its size is at least 2M-6 >= M+1 (the h = 2 cases are direct). So the cores pairwise meet.
6. **Helly.** t* = max α(S) lies in every core; q* = q_{t*}.

**Why it is true.** A maximum strong set avoiding p2, r_{-2} is a full Q-interval plus at most 2+2 end points and an apex; disjoint intervals would splice into a longer cup, so all share a Q-point.

**Negative findings.**
- No fixed Q-position works at M = 6. Twenty-five size vectors have blocks whose sets of good q are disjoint, e.g. (3,6,4): {q4} versus {q3} (`positional_cex.pkl`).
- At M = 5, 36 of 1,600 uniformly sampled tight blocks have no good q once p2 and r_{-2} are fixed; some other triple with one point per block always worked (`fixpr_bad.pkl`).
- At M = 6, Claim D3 held in 6,000 samples, but I have no proof.
- **Side result (proved):** |U| <= 3k-7. This follows from the two-cup lemma applied to P|Y, where Y is a longest cup of Q∪R, together with n - lc <= conv - 2 for two-cup blocks.

## R2: not proved

**Formula.** T(4,u,k) = C(u,2) for u <= k-1, and 1+C(k-1,2) for u = k (as in `dec.py`); the brief's "C(u-1,2)" is a typo. SAT confirms that T+k-4 is exact at (u,k) = (3,4), (4,4), (4,5), (5,5), (5,6), (6,6), and that it is attained at (6,7) and (7,7). Extremal |P| ranges over k-4..u-1.

**Proved: |U| <= T+u-2.** Let Z be the left ends of 4-caps; then Z ⊆ P. Z ∪ {a} is a cup (otherwise there is a 5-cap), so |Z| <= u-2, and U\Z is 4-cap-free. So R2 holds when |Z| <= k-4. What remains is the case |Z| in {k-3, k-2}, which needs |U\Z| <= T-(|Z|-k+4).

**Failed routes (diagnostic).**
- A 4-cap transversal of size <= k-4: in 15% of the (6,6) samples the minimum is k-2.
- The step (u,k) -> (u-1,k-1): it always needs exactly k-1 deletions, but "U's top cup-layer plus one P-point" usually fails. That layer is not a cup and can have up to u+4 points.

**Obstacle.** 4-caps that start in P break the layer lemma for U. I have no proof idea for the needed trade-off between |Z| and the 4-cap-free remainder.

## Evidence (diagnostic, not Lean)
- `claimd3_check.py` and `claimd3_m7.py` replay steps 1–6 at M = 6, 7, 8 with 0 failures.
- `r2*.py` contain the R2 diagnostics.
