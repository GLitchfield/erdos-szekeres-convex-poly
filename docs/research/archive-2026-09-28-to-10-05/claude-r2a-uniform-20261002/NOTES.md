# Uniform decomposable R2(a): reduction scheme and obstacle (claude-r2a-uniform-20261002)

**Verdict.** I found no proof that is uniform in a. The root-split induction proves most cases uniformly and reduces R2(a) to one family of three-block lemmas Θ_s at level a−1, plus two side lemmas. Θ_2 closes over TS, R and Θ_2 one level down. Θ_3 needs four-block lemmas, so I found no finite family that closes. All computation is diagnostic (pysat on decomposable labels); nothing is Lean-checked.

## 1. Bound and hypotheses
- **Family R_s.** V = P|Q, cap P ≤ a−1−s, cap Q ≤ a−2, cap V ≤ a−1, no u-cup, no strong k-set.
- **Bound.** R_s(a,u,k) = T(a−1,u,k) + C(k−2−s,a−2−s) for a+u ≥ k+3. Below that it is the Z-bound ES(a−1,u) + ES(a−s,u−1).
  - s=1 is TS and s=2 is R2. s=a−2 is trivial.
  - Gate form: stack s gate points on the P side and one on the Q side.
- **Exact facts** (`arith.py`).
  - R_s satisfies Pascal in (u,k).
  - Label picture: R_s = T(a,u,k) − #{size-(k−a) subsets of [k−2] meeting {1..s}}.
- **SAT checks** (decomposable).
  - Exact at a=5 for (u,k) = (5,6), (6,6), (6,7).
  - a=6 is covered by the a6 run's general SAT.
  - a=7 is not checked (n ≥ 40).
- **P's hypothesis "(a−2)-cap-free" is exactly right.** In N2f with A ⊆ L, B is an R2 instance at the gap a⁻, and the a6 insertion argument realizes every R2 instance this way.

## 2. Uniform reduction (hand proofs)
Root split V = A << B, with β = cap B and α ≤ k−1−β (P). A satisfies the R_s hypotheses; B is (β+1)-cap-free. The induction runs on u (base: the classical Z-bound) and downward on s. The identities are checked in `arith.py` for a ≤ 14, k ≤ 22.

- **k−u+1 ≤ β ≤ a−3.** |V| ≤ R_s(a,k−β,k) + T(β+1,u,k) ≤ R_s, by the splitting identity at level a−1.
- **β = a−2, A ⊆ P.** ES(a−s,k−a+2) + T(a−1,u,k) = R_s. Tight.
- **β = a−1, A ⊆ P.** a⁻ followed by the gate extends caps of B∩(−∞,a⁻) by s+1. So B is a GATE(s+1,1) instance at a⁻, and ES(a−s,k−a+1) + R_{s+1}(a) = R_s. Tight.
- **β ≤ k−u, with a B-point outside [a⁻,a⁺].** A's cups lose one point, so R_s(a,u−1,k) + ES(β+1,u) ≤ R_s.

## 3. What remains
**CORE Θ_s(ℓ).** X|Y|Z with cap X ≤ ℓ−s, cap Y and cap Z ≤ ℓ−2, cap V ≤ ℓ−1, no u-cup, no strong k-set ⟹ |V| ≤ T(ℓ,u,k) − C(k−3,ℓ−2) + C(k−2−s,ℓ−1−s).

- **Where it is needed** (both cases tight):
  - β = a−2, A ⊆ Q: B is a Θ_s(a−1) instance, blocks B∩P | B∩(g,a⁻) | B∩(a⁻,∞).
  - β = a−2, A straddling: B is a Θ_{s+1}(a−1) instance, blocks B∩(−∞,a⁻) | B∩(a⁻,a⁺) | B∩(a⁺,∞).
- **It cannot be avoided:** inserting an extremal A gives R_s(a) ⟹ Θ_s(a−1).
- **Evidence.**
  - Θ_2(4) = 3k−8 (R1-dec, hand proof).
  - Θ_2(5) and Θ_3(5) are SAT-exact at (u,k) = (5,7), with values 19 and 18.
  - Θ_3(5) is SAT-exact at (6,7), value 23.
- **Θ_2 closes** (`coverage_out.txt`, at (ℓ,u,k) = (5,7,7), (5,8,8), (6,9,9)). It uses only Baek, Z, iterated Z, TS(ℓ), R_s(ℓ), Θ_2(ℓ−1) and smaller u.
- **Θ_3 does not close.** Two zero-slack cases remain:
  - a four-block lemma one level down. Four cups with a 4-cap-free union hold exactly 4k−13 points (SAT, k = 6..8).
  - a nested-TS profile.

  R2 needs Θ_3 (the straddle case), so block lemmas with growing block count follow.

**SIDE 1: β = a−1, A ⊆ Q or straddling** (slack ≥ C(k−4,a−4)).
- B has the "lifted" three-block profile: blocks ≤ a−3, pairs ≤ a−2, global ≤ a−1.
- At a=5 the true maximum is 3k−7 (SAT, k = 6..8), against 4k−12 needed. The guess "lifted = Θ(a−1) + 1" would suffice.
- It is unproved for a ≥ 6.

**SIDE 2: markers (u < k).** This is β ≤ k−u with B strictly inside A's span.
- A is an R_s instance whose non-straddling cups are ≤ u−2.
- We need |A| ≤ R_s − ES(β+1,u). This is the R_s analogue of Lemma 5 and H1-6.

## 4. Sharpest obstacle
**What fails.** Θ_s for s ≥ 3 and the r-block lemmas it spawns. Each zero-slack split adds a sibling marker that splits a block, so no finite family closes. This is Workstream B's context bound restricted to interval cap profiles.

**Why I still expect it to be true.** Every value fits a "kill-set" rule: a profile removes a monotone set of bottom-layer labels. R_s removes the sets meeting [s]; Θ_s removes the sets that contain 1 and meet {2..s}. One statement of that form would cover the whole family. I have no proof idea for it.

## 5. Caveats
- **Low-letter oracle undercounts.** The compiled context bound with only 1–3 S letters per run undercounts.
  - GATE(5;2,2) at (6,6) gives oracle 8 and 9, but the SAT maximum is 10 (two 5-cups).
  - This refutes "GATE(a;s,t) = R_{s−t+1}(a−t+1)".
  - I used the oracle only to suggest formulas.
- **Partial coverage.** The coverage checks enumerate splits with ≤ 3 alternations per run and children with ≤ 4 runs.
- **Long runs.** Several runs exceeded 1 minute: Θ_3(5,6,7) chunks took about 3 min. Two runs were stopped unfinished.

**Files.**
- `genc.py`, `tmax.py`, `blk*.py`: SAT.
- `arith.py`: arithmetic, output in `arith_out.txt`.
- `lib2.py`, `cover.py`, `run_all.py`: coverage, output in `coverage_out.txt`.
- `shapes*.py`, `closure*.py`, `gatevals.py`: oracle exploration.
- `g22w.py`, `lift_witness.py`: refutation witness.
