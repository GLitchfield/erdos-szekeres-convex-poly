# Two-side bound a=5, decomposable, by root-split induction (claude-twoside-a5c-20261002)

**Status: a reduction, not a full proof.**
- u=k: the induction closes except for two a=4 lemmas, R1 and R2. Both are SAT-checked for k ≤ 7, which gives
  **decomposable TwoSide(5,7,7)**. That case was undetermined before.
- u=k-1: one more case remains, H1 (nested high singleton). The sharpest obstacle is chains of such singletons.

Notation: H_u = T(4,u,k)+C(k-3,2); x0, x1 are the extreme points; α = cup A, β = cap B, and α+β ≤ k-1 by (P).

## Toolkit (proved, general signotopes)
- **Z (classic two-side): no v-cup ⇒ ≤ (v-1)^2.**
  - Let Z be the left ends of 4-caps; Z ⊂ L.
  - U-Z is 4-cap-free, so |U-Z| ≤ C(v,2).
  - A cup of Z extends by the 4-cap's second point (else a 5-cap), so |Z| ≤ C(v-1,2).
  - Z proves the bound for u ≤ k-2. For other u, the formula H(5,u,k) = T(4,u,k)+T(4,min(u-1,k-3),k) is only
    conjectured; it matches SAT at 7 more parameter sets.
- **Virtual marker.** If all (v-1)-cups straddle a gap h, a far-above point fits at h, giving (v-1)^2-1.
- **Cup blocks** (no 4-cap, no u-cup). The dichotomy "X+y1 or x_{-1}+Y is a cup" plus a size-vector check gives:
  - two cups ≤ 2u-3;
  - three cups ≤ 3u-6;
  - three cups whose (u-1)-cups straddle one h ≤ 3u-7.
- **Cupblock lemma:** 2k-4.

## Root split U = A << B
Each B-cap gains one point per side that has an A-point, and B∩L gains one more from q. So:
- x0∈A ⇒ cap B ≤ 3 and B_L is a cup;
- B∩(min A, max A) is a cup.

Each case closes as follows; every total is ≤ H_u.

| case | bound |
|---|---|
| NN: x0∈A, x1∈B (mirror by symmetry), β≤2 | (k-3)^2+(u-1); if \|B\|=1 and u=k, induction H_{k-1}=H_k-1 |
| NN, β=3, A⊂L | C(k-3,2)+T(4,u,k) |
| NN, β=3, A meets R | B is a two-cup block: (k-4)^2+(2k-4) |
| N1: B inside span A (B a cup), \|B\|≥2 | as β≤2 |
| N1, \|B\|=1 | u=k: H_{k-1}; u=k-1: **H1** |
| N2: A inside span B (cup A ≤ u-3), β=3, A 4-cap-free | C(k-3,2)+T |
| N2, β=3, A has a 4-cap | B is three cups: (k-4)^2+3k-9 for u=k-1; 3k-8 for u=k (**R1**) |
| N2, β=4, A has a 4-cap | (k-5)^2+(3u-4) |
| N2, β=4, A 4-cap-free | Z gives T+(u-2), enough unless α=k-5, where **R2** is needed |

**Residual lemmas (SAT only):**
- **R1.** Three cups, no 4-cap, conv ≤ k-1 ⇒ ≤ 3k-8. Checked at k=6,7. Deleting {p2, q_mid, r_{-2}} lowered conv in
  230/230 samples, which suggests a Claim-D proof.
- **R2.** P cup | Q 4-cap-free, no 5-cap ⇒ ≤ T(4,u,k)+k-4. Checked at (5,6), (6,6), (6,7), (7,7).

**Corollary (paper + SAT).** Decomposable (5,7,7) ⇐ (5,6,7) (a5 SAT) + R1(7) + R2(7,7).

**Why the bound holds.** The coupling (P) puts A in the classic regime, where Z is exact. The polygon constraint acts
only on the a=4 part B: a cup, a T(4) set, or a two- or three-cup block. Three different splits are tight.

## H1 (u=k-1, U = A << {b}, b interior)
H1 is equivalent to: every (k-2)-cup of A straddles b. Equivalently, a tight set has two (k-2)-cups with
max D1 ≤ min D2. This holds in all 1,394 tight instances with u=k-1.

Root split A = A1 << A2:
- **Non-nested: closed.**
  - β'=3: |A2 ∪ b| ≤ T.
  - β'≤2 and A2 straddles b (transfer): every (k-3)-cup of A1 straddles m = min A2, since otherwise m D x1 or D m b is
    a (k-1)-cup. The virtual marker then gives |A1| ≤ (k-3)^2-1.
- **A2 nested:** needs **TG**: classic two-side whose (v-1)-cups straddle one of two gaps ⇒ ≤ (v-1)^2-1. SAT
  v=4,5,6.
- **A1 nested:** three-cup straddle (proved), or **CS+straddle** ≤ T+k-5 (SAT k=6,7).
- **A2 = {b'}:** two nested high singletons, so the case recurses.

**Obstacle: chains of nested high singletons.** `h1_dbl_tight.pkl` (k=6, nL=6, |U|=13=H) has root
`[[core] << 10R] << 9R`. Its core is nested: a 4-point two-sided part with a 4-cap inside a three-cup block of
7 = 3u-8 points.

**Strengthened family.** U = X ∪ S, where S is the top chain of nested high singletons, kept as passengers (counted
points). Each lemma needs a passenger version:
- T(4): automatic;
- three cups: SAT, t ≤ 2;
- TG, R2: open.

**Closure is not established.** In NN with X2 a (k-2)-cup straddling two passengers, naive accounting overshoots by 1.

**Refuted:**
- "at most one point ends a (k-1)-cup" (4-cap-free sets);
- "all (k-1)-cups share a point".

## Evidence (diagnostic)
- `cases.py`, `cases_rand.py`: every case claim; 0 violations on 2,283 tight and 1,779 random decomposable sets.
- `h1gen.py`, `h1cases.py`: 724 H1 instances; 0 violations.
- SAT:
  - `hsat`, `cupblocks_sat`, `cupblocks_h`: H formula, R1, three-cup straddle;
  - `cupside_sat`, `cs_straddle`: R2;
  - `twogap_sat2`, `es_twogap`: TG;
  - `passengers_sat`;
  - `d3rule`: deletion rules;
  - `y1test`, `commonpt`: the refutations;
  - `sepcups`: separated max cups.

**Next.**
1. Prove R1 (Claim-D), R2 and TG.
2. Then prove passenger versions of the lemmas.
