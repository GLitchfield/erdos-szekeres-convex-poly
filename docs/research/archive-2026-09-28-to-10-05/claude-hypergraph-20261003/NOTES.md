# Q12: BDL and PSL as hypergraph colourings (claude-hypergraph-20261003)

**Tags.** [P] proved by hand. [C] computed (pysat/CaDiCaL plus exact Fraction LPs; no DRAT, not Lean). [Conj] conjecture.

**Notation.** J(X) = [k−1−β, α−1]. r_j(S) = max |T| over T ⊆ S with cup T ≤ j+1 and cap T ≤ k−1−j. T_J = Σ_{j∈J} C(k−2,j).

## 1. Obstructions on general signotopes [C]

**BDL fails on non-decomposable signotopes.** These are not counting failures.

| instance | data | found by |
|---|---|---|
| X14 | k=6, n=14, cup 4, cap 5; capacities 1+4+6+4 = 15 | 1 of 190k checks (job 135659-e19d50) |
| three sets | k=7, n=26 = T(7,5,7), cup 4, cap 6; every band at ES capacity | 3 of 90 tight samples of the class (job 135705-76dc77) |

- X14 is deletion-minimal and prime: it has no root split, and its largest decomposable subset has 11 points.
- X14 was re-verified with the audit's `dec.py` backtracker and the 4-point strong DP.
- Every failure has cap = k−1.

**PSL never failed.** 190k checks at k=6 and 6k at k=7, including every BDL counterexample.

**Decomposable control.** Leaf-split growth into the same classes gave 0 BDL and 0 PSL failures:
- 5.4k near-maximal sets, of which 2.9k are tight (72 of these in the failing k=7 class);
- 83k one-point deletions.

**Window bound on general signotopes.** T+1 is UNSAT at (4,6,6), (5,5,6), (5,6,6) and (4,7,7). (5,6,7) is open: I cancelled it after 2M conflicts.

**Verdict.** BDL is not a signotope theorem; decomposability excludes its obstructions. PSL may be a signotope theorem, which would imply ES for signotopes.

## 2. Hall condition and exchange [C]

- **X14 satisfies Hall,** |S| ≤ Σ_j r_j(S), for all 2^14 subsets. So **Hall does not characterize BDL.**
- **Relaxed instances** (about 21k: k ≤ strong, narrowed ranges, random lists; general and decomposable):
  - with k ≤ strong on general sets, Hall caught every failure;
  - elsewhere it missed failures, 63 times on decomposable sets.
- **Matroids.** Exchange fails for every non-trivial band. The smallest case is band 1 ("caps ≤ 3"): I = 2 points, J = a 3-cap, and each I+x is a 3-cup. It also fails for both PSL classes and both frame families, so Edmonds' matroid partition cannot apply.
- **Greene–Kleitman.** R(a,b) = max{|T| : cup ≤ a, cap ≤ b} is never concave, and supermodularity fails on 15/100 samples. There is no shape.

## 3. Fractional relaxation

**[P] The edge LP as posed is always feasible.** x = 1/#bands works, because every edge has ≥ 2 points. For PSL, y = ½ works.

**Conv-hull LP** (fractional partition ⟺ weighted Hall, w(X) ≤ Σ_j max_{T∈F_j} w(T) for all w ≥ 0). [C]
- **X14: feasible.** θ = 14/15, with an exact certificate (15 band sets, coverage ≥ 15/14). This is an integrality gap.
- **k=7 sets: infeasible.**
  - [P] On tight X, a fractional partition is an exact decomposition into maximum band sets.
  - The LP optima are 47/2, 1382/57 and 68/3, all below 26.
  - Violator, checked by MaxSAT: w = 10, with w = 15/2 on 5 points P; this gives θ = 99/98.
  - Reason, **over-demand**: every maximum band-2 set contains 4 points of P and every maximum band-3 set ≥ 2, so 6 > 5.
- **Dual certificates** on the relaxed failures: about 90% are 0/1 Hall sets; the rest are weighted.
- **Explicit point.** The uniform distribution over maximum sets covers only 0.5–0.8. The proportional point x_{v,j} = C(k−2,j)/T_J lies in the rank polytope on every test.

## 4. PSL as a 2-colouring, and the frame form [C]

**PSL.** Bl hits every β-cap and every (k−1)-gon, and contains no α-cup and no (k−1)-gon.
- **The bichromatic version fails** (7% of general, 2.5% of decomposable gon-free instances). So the PSL hypergraph is not balanced, Berge/total-unimodularity colourings are out, and one-sidedness is essential.
- **Seymour/Tarsi deficiency bounds are vacuous,** since |E| ≫ |V|.
- **The canonical classical splits all miss the strong condition** in 34/60 general and 4/17 decomposable window samples.

**Frame Bl ⊇ Fp.** Split Y = X∖Fp as R′ ⊔ E, where R′ contains no gon and E contains no residual C∖Fp.
- **Decomposable** (6000 frames): only 3 are infeasible. All three are unit-propagation obstructions: a 5-gon of Y whose points each complete a cup or gon with Fp. Hall and the edge LP (y(G) ≥ 1, y(H) ≤ |H|−1) are exact there.
- **General** (42 infeasible frames): Hall misses 28 and the edge LP misses 29, but **the conv-hull LP detects all 42**, with weighted duals in 36.
- **Frame lemma:** it held on all 2.3k samples, general signotopes included.

## 5. Consequences and proposal

**Negative.** BDL, fractional BDL, Hall and matroid min–max all fail on general signotopes. A proof of BDL must therefore use decomposability in the integral step; generic hypergraph theorems cannot give it.

**What survives everywhere.**
- PSL.
- **Hall at X:** Φ(X) = Σ_{J(X)} r_j(X) − |X| ≥ 0. It holds with equality on the k=7 sets.
- [Conj] **Density D_j:** r_j(X) ≥ |X|·C(k−2,j)/T_J. It held in 3.9k band instances; the worst ratio is exactly 1, so tight sets reach ES capacity in every band.

**[P] Each of these suffices, and none of them chooses a partition.**
- Φ ≥ 0 implies Theorem 8, because r_j ≤ C(k−2,j) by classical ES.
- D_j for a single j implies Theorem 8.
- |X| ≤ ρ_R + ρ_B (overlap allowed) implies Theorem 8 by induction on k.

**Proposed theorem.** Φ ≥ 0, or D_j, for decomposable k-gon-free X.

**Proof idea.** DS induction on numbers, where each band takes its own maximum set.
- [P, sketch] Φ composes at every node except R/R′: the children's index sets are disjoint inside J(X), and non-tight absorption gives r_{j0}(X) ≥ |A| + r_{j0}(B).

**Obstacle.** Case R.
- [C] The merge r_{j0}(X) ≥ |A| + r_{j0}(B) failed in 200/200 instances.
- [P] Case R reduces to finding a β-cap transversal H ⊆ B with cup(A∪H) ≤ k−β; this is TDF's condition, which fails for 3-band B.
- Whether overlap closes case R is untested.

**Learned.** Decomposability matters for the integral packing of extremal blocks. The counting statements look general.

## Evidence

- **Code:** `sig.py`, `hall.py`, `q1_sweep.py`, `q2*.py`, `frame*.py`, `tight_frac.py`, `cert.py`, `verify_whall.py`, `overdemand.py`, `density*.py`, `dec_target.py`, `prof.py`, `phi_comp.py`.
- **Outputs:** `o_*`; X14 is in `minimal_14_6.json`.
- **Jobs** (prefix 20261003-): 135554-4ab27b, 135659-e19d50, 135705-76dc77, 140056-105644, 141737-307952, 142008-57ea06, 143927-725c2c, 144802-7ff03e, 145307-21340e.

## Q15: choice-free statements through case R (decomposable; code and outputs in `q15/`)

### 1. Composition law

**[P] Exact recursion (Lemma DS).** For T = T_A ⊔ T_B:
- cap T = max(cap T_A, max over caps D of T_B of |D| + [T_A has a point left of D] + [T_A has a point right of D]);
- cup T is the mirror;
- strong T = max(strong T_A, strong T_B, cup T_A + cap T_B).

So r_j, ρ_R and ρ_B of X are max-plus convolutions over zone profiles (cuts at the other part's extreme points): exactly N(P; α, β).

**[P] Φ is superadditive wherever the children's band sets can be disjoint.** r_j is absolute and monotone, the node condition puts J(A) below J(B), and a classical child fits whole into one band of K(Y) = [cup Y − 1, k−1−cap Y]. Verified at 23,080 nodes.
- **Residual nodes:** "B carries" (cap B = cap X and cup B = cup X), its mirror, and two classical children colliding in one band.
- [C] **The residual is unavoidable:** 17% of (X,k) at n=7 have no residual-free tree.
- [C] At residual nodes, absorbing A at no cost fails 11,360 times in 66,567 (n=8). The deficit is always paid by Φ(B) > 0.
- **So Φ does not compose from the children's numbers;** this is the sibling penalty in numeric form.

**PSL slacks.** Taken with each set's own cup and cap, they are superadditive at 99.8% of nodes. But classical children have negative slack, so this gives nothing.

### 2–3. Case R, and the overlap hypothesis [C]

- **Witness W1:** A all blue, R inside B, and Bl∩B allowed to overlap R. It holds at all 38,439 case-R root splits (exhaustive, n ≤ 8) and on 828 samples.
- **It always holds without overlap**, so the hypothesis is refuted.
- In tight case R the optimal (R, Bl) pairs include a partition. Their overlaps lie mostly *outside* B's core (k=6: 8.0k points in the core, 40.9k outside, 18.6k in A).
- **The relief is a monochromatic child.**
  - At every R and R1 node (24,990 + 51,698), X has a PSL split with A entirely blue.
  - At every mirror node, it has one with B entirely red.
  - By SAT, A-blue also works on 850/850 large tight case-R sets (k=6,7,8; n ≤ 49; B with up to 6 bands).
  - The double frame (first β-cap points blue, last points red) fails on 5 of these.

### 4. Reduction

**[P] Case R in the PSL window** (α+β ≥ k+2):
- (a) α ≥ cup A + 3, so cup B = α;
- (b) A lies strictly inside B's cap core (L*, R*), so **B is cored**;
- (c) X has a PSL split with A ⊆ Bl iff **PSL⁺(B)**: every β-cap of B bichromatic, every α-cup red-hit, every (k−1)-gon bichromatic. This uses strong(A∪T) = max(strong A, strong T, cup A + cap T).

**[P] Cored-frame lemma.** In a cored set, the first points F of the β-caps contain no β-cap. So T = F, R = B∖F meets every cap and cup condition of PSL⁺. Only the gon condition remains, and this split fails it on 35% of cored instances.

**[C] CORE: every cored decomposable window set satisfies PSL⁺.**
- It holds on all 228,819 cored (B,k) with n ≤ 8.
- It holds on all 2,121 large cored instances (k=6,7,8; 337 tight).
- PSL⁺ fails only on non-cored sets: 1,346 of 1,935 large non-cored instances fail.
- On general signotopes it held on all 396 cored instances, X14 included (the frame lemma holds for all signotopes).

**[C] HIT, the R1 analogue.** Every max cap and max cup of B is red-hit, and both classes are gon-free. It holds on all 23,284 (B,k) with n ≤ 7; with A's cup context it held at every R1 node.

**Proof shape.**
- The Q10 uniform rules [P] close every node except R, R1 and their mirrors.
- R follows from CORE [P].
- R1 follows from HIT with context [C].

So **PSL reduces to CORE (context-free; the case-R reduction is [P]) and to HIT with A's cup context at R1 ([C]).** The context binds only when cup X = cup A + 2. Both are "classical exchange frame plus repair of the (k−1)-gon condition".

**Statement to prove first: CORE.** HIT-with-context closes R1 the same way.

**Obstacle.** The gon condition couples two chains, as in Q14. It is untested whether {PSL, CORE, HIT} compose jointly. One lead [C, n ≤ 7]: on cored X, PSL⁺ splits with a monochromatic child exist at every R and R′ node.

**Evidence** (jobs, prefix 20261003-):
- exhaustive: 152124-9b596e, 152705-60fbec, 153324-6099f6;
- samples: 152124-dbb455;
- SAT, Lemma W: 152517-662ce6.
- SAT, CORE (totals in `q15/o_core_total.txt`):
  - 153403-62329f, cancelled to shard;
  - 155747-c1d082 and 155747-f7d12c, both killed at the 2G cap by the old gon enumeration;
  - 160732-1781d4 and 160748-a3a15c, rerun with the memory-light `lightgon.py`.

## Q18: toward a proof of CORE (code and outputs in `q18/`)

**Verdict.** CORE is **not proved**. It remains **unrefuted**:
- exhaustive decomposable n ≤ 8 (228,819 cored instances);
- 2,121 large cored decomposable instances (k ≤ 8, n ≤ 50);
- about 1,000 general-signotope instances.

### 1. Structure of cored sets [P]

Notation: F, L are the first and last points of β-caps, L* = max F < R* = min L.
- **(a) Non-extension.** If (f, y, …) is a β-cap, then χ(x, f, y) = cup for every x < f; otherwise x + cap would be a (β+1)-cap. The mirror holds at last points.
- **(b) Zones.** F ⊆ (−∞, L*] and L ⊆ [R*, ∞). Core points start and end no β-cap.
- **(c) Frames.** F and L each contain no β-cap (every β-cap ends ≥ R* > L*) and no α-cup (exchange: no α-cup ends in F, none starts in L).
- **(d) Consequence.** For T ⊇ F, every β-cap stays bichromatic iff T contains no β-cap. A red point x completes a β-cap with F only if x ∈ L; core points never do. So the frame meets everything except the gon condition.

### 2. The repair [C]

Data from exhaustive decomposable n ≤ 8, 217,818 cored (B,k):
- **Frame failures.** The frame leaves a monochromatic (k−1)-gon in 34% of cases. These gons are red (inside B∖F) except in the 46 cases where F itself contains one.
- **Safe points.** Every red gon contains a point that is safe to recolour alone (202,608 of 202,608).
- **No rule.** These all fail on 1–2% of repair instances (n=8):
  - recolouring a named point of each bad gon (first, last, first or last core point, max cap-start, min cup-end), one-shot or iterated;
  - structured repair sets (E = L, the core, or their red-gon parts); even E ⊆ L ∪ core fails 14 times at n ≤ 7.
- **No lookup rule.** colour(x) = g(k, α, β, zone, the four chain lengths at x[, strong-set data]) is UNSAT already at n ≤ 6.
- So the repair is a global constrained hitting-set problem: E ⊆ B∖F must hit every gon of B∖F, while F ∪ E has no α-cup, no β-cap and no gon.

### 3. Proof attempts

- **Frame-extension lemma FEL** ("F gon-free ⇒ some PSL⁺ split has blue ⊇ F"). It is exact on all n ≤ 8, and F or L is always gon-free there. For decomposable sets, F or L gon-free follows [P] from the merge law M: strong(F ∪ L) ≥ strong F + strong L − 2, which held on all 228,819 instances and fails on general signotopes. CORE ⇐ FEL + M was my reduction.
- **FEL is false.** Decomposable counterexample (`q18/fel_counterexample_12_6.json`, brute force over all 2^12 colourings): n=12, k=6, cup 4, cap 4, F and L both gon-free. It has 67 PSL⁺ splits, 12 contain F, none contains L; the reversal violates the F-form. On general signotopes the L-form failed 5 times (k=7, n ≈ 30). So the reduction is void.
- **Large data.** One-frame extension failed once in 1,026 decomposable frame tests (the set above) and 7 times on general signotopes (always the L-frame).
- **Two-frame lemma** ("the F-frame or the L-frame extends") held everywhere [C], including on all 8 failures. It is CORE plus a choice of side, like Q14's four-frame lemma.
- **No signotope-only argument found.** M is false off decomposable sets, and FEL fails there in both forms.

### 4. Composition [C]

At the 682 cored case-R nodes (n ≤ 7), "A monochromatic plus some split of B" always yields PSL⁺(X). But it works for every PSL⁺ split of B at only 102 nodes, and for every HIT or PSL split at none. So PSL, CORE and HIT do not compose from arbitrary inductive-hypothesis splits; this is Q9b's pattern.

### What was learned, and the obstacle

- **What is understood.** Coredness explains the cap and cup conditions completely: (a)–(d) give a proof for every condition except the (k−1)-gon condition.
- **Obstacle.** The gon repair. It needs global coordination: no local rule, lookup rule, structured set or one-sided frame works, exactly as for PSL in Q14.
- **Remaining step.** A genuine existence theorem for the residual hitting-set problem, for example an exchange or alternating-path argument over the two frames, or an LP/Hall argument. The Q12 results suggest the conv-hull LP is the right relaxation to try.

**Evidence** (jobs, prefix 20261003-): 164151-c5c325 (n=8: safe, rules, structure), 164151-3ddd43 (large SAT), 164722-0a6ce1 (F/L laws, n=8). The scripts `lookup.py`, `structE.py`, `comp4.py` and `merge_gen.py` were run directly.

## Q20: the two-frame lemma as a dichotomy (code and outputs in `q20/`)

**Verdict.** The Hex-type abstraction is **not supported**. In every failure, the frame that works does so without using the other frame's obstruction. The two frames never failed together (0 of 1,853 cored instances: 990 general, 863 decomposable), but I found no mechanism behind that.

### 1. Obstructions to a frame [C]

The minimal certificates are minimal unsatisfiable subsets of the residual CNF (frame forced blue).

**Two kinds of failure:**
- **Trivial:** the frame contains a (k−1)-gon (351 instances).
- **Nontrivial:** the frame is gon-free but does not extend. There are 17 on general signotopes (k=6,7; n ≤ 30) and 2 decomposable (n=12 from Q18, n=15).

**Simple certificates (4 of 19, including both decomposable ones).** The forced-red region FR(W) contains a (k−1)-gon. FR(W) is the set of points that alone complete an α-cup, β-cap or gon with W. Example (decomposable n=12):
- L contains the (α−1)-cup (8, 9, 11);
- its left extensions 0, 1, 5, 6, 7 are forced red;
- those five points form a red 5-gon, which then needs a blue point.

**Chains (15 of 19, all general).** These involve 3–51 red gons and 2–54 longer negative clauses:
- β-caps whose frame part is blue forbid pairs of (core, right) points;
- α-cups and gons through the frame force the adjacent core points red;
- the red gons are covered by forced-red points and blocked pairs.

This is a chain of red gons linked through forced points, but long (MUS of 13–51 clauses), not a short path.

### 2. The dichotomy test [C]

- **The extending frame W2 is essentially unconstrained.** In W2-extensions, 400 of the 403 points outside W2 can take either colour. That includes 231 of the 234 points of W1's certificate.
- **Constructions from the obstruction fail.** Each of these fails on every failure tested:
  - W1 entirely red;
  - W2 ∪ (W1's forced-red points) is valid;
  - W1's red-gon points blue inside a W2-extension.
- Those tests ran on the 17 general failures.
- **Density.** In all 19 failures except the n=12 tie, the failing frame is the larger one; in the 17 general ones it has strong(W) = k−2. The other frame is small (strong ≤ 3, usually with an empty forced-red region). But this is not a law:
  - the decomposable n=12 failure has |F| = |L| = 4 and strong(L) = k−3;
  - both frames are saturated (strong ≥ k−2) in 15 instances, and one of them still extends in each.
- **So the obstructions to the two frames are unrelated.** The second frame succeeds because it is sparse or free, not because the first one's obstruction builds anything.

### 3. LP integrality [C]

- On every nontrivial failure with n ≤ 16 (6 cases: four general, both decomposable), the exact conv-hull LP of the residual problem is infeasible (for example θ = 8/7), so there is no integrality gap.
- Hall's 0/1 condition detects 5 of these 6; one needs weights.
- All 133 extending frames are LP-feasible, as they must be.
- At n ≈ 30 the LP was not resolved: θ fell from 1.23 to 1.19 within 15 iterations, then separation stalled.
- So a **fractional two-frame lemma** (the conv-hull LP for F or for L is feasible) is a plausible min–max target. Q12 likewise found the LP exact on frames, but nothing here proves total dual integrality.

### 4. Proof

No dichotomy argument emerged; I attempted no key step, because the data show no blocking/building correspondence. The structure facts (a)–(d) of Q18 remain the proved part.

**Status.**
- **Proof idea:** frame plus repair (CORE); the frames handle every cap and cup condition [P].
- **Learned:** frame failures are large chain obstructions near a dense frame. The other frame's extensions are free, so existence comes from slack, not duality.
- **Obstacle:** the (k−1)-gon repair is a global hitting-set problem with no local, dual or frame-exchange structure found. The best remaining lead is the LP: it was exact on all small failures, so a weighted-Hall min–max for the residual problem could give existence.

**Evidence** (jobs, prefix 20261003-):
- 171520-e94d01 (general corpus);
- 171521-bf25b3 (decomposable corpus);
- 172542-95cc4c (saturation);
- 172533-e3bb4c (large LP, stopped);
- outputs `o_lp_small.json`, `o_lp_small_dec.json`;
- `lp_small.py`, `cert.py`, `classify.py`, `predict.py`, `dich.py` and `freesum.py` were run directly.

## Q22: slack and a probabilistic route (code and outputs in `q22/`)

**Verdict.** Slack exists, but it is **not local**. A Local-Lemma proof of CORE is ruled out, and its failure worsens with both n and k. The fraction of valid colourings decays as n approaches the extremal size.

### 1. Counting [C]

Exact counts over all colourings of the residual Y = B∖W (n ≤ 16; table in `o_table.txt`):
- **Fraction of valid extensions** of the working frame, at fixed k, as n grows toward 2^(k−2):

  | sets | n ≤ 8 | n = 16 |
  |---|---|---|
  | decomposable, k=6 | 0.66 | 0.009 |
  | general, k=6 | 0.37 (n=9) | 0.002 |

  So it decays.
- **Entropy per residual point.** The average stays at h ≈ 0.3–0.9 bits, but the **minimum is 0**: some frames have exactly one valid extension.
- **CORE as a whole is not rigid.** Every cored set with n ≤ 7 has at least 4 PSL⁺ splits. Near-extremal n=14–16 sets have at least 208, about 0.5 bit per point.
- **Near misses of failing frames** (6 small cases): the best colourings violate only 1–6 bad events. In one case, 31 of 2,048 colourings violate exactly one.

### 2. Local Lemma [C]

**Bad events** on the free residual points (forced-red points fixed red): a red gon entirely red; a blue β-cap, α-cup or gon whose free part is entirely blue. Each point is blue with probability q.

**Results:**
- **Standard symmetric LLL:** e·p·(d+1) = 16–137 near the extremal size; it needs ≤ 1.
- **Lopsided LLL [P].** Blue events are increasing and red events decreasing. Conditioning on the variables outside A and applying Harris gives a valid negative-dependency graph in which A depends only on opposite-colour events sharing a point. This halves the degrees, but the ¼-criterion is still 9–18 at k=6, n=16; it needs ≤ 0.25.
- **No bias rescues it.**
  - Optimising q, zone-dependent biases (left/core/right) and fixing forced-red points leave the best criterion at 3–17.
  - The asymmetric LLL never holds near the extremal size.
- **Where it does hold:** only far from the extremal size (e.g. general k=7, n ≤ 15; most sets with n ≤ 8 at k ≥ 6).

### 3. Explanation

**The dependency degree is not bounded: (k−1)-gons are dense in near-extremal sets.** Counts come from a DP using the fact that a strong set is uniquely its lower cup plus its upper cap (validated against enumeration):

| k | n | gons through a point | LLL scale (k−1)·(gons per point)·2^−(k−1) |
|---|---|---|---|
| 5 | 8 | 19 | 4.8 |
| 6 | 16 | 250 | 39 |
| 7 | 32 | 6,000 | ≈ 600 |

The scale grows about 10–15× per step in k. About 4% of all 6-subsets of a 32-point 7-gon-free set are convex.

Lemma DS does not bound how gons overlap: a cup of A and a cap of B combine freely, so the number of gons through a point grows like a product of chain counts.

**What the slack is.** It is global (≥ 200 solutions) while each point carries hundreds of nearly independent constraints. Existence is a coordinated phenomenon, not a sparse-constraint one. This agrees with Q18/Q20: no local rule, and both frames' extensions are free but not locally certifiable.

### 4. Polyhedral (secondary) [P/C]

- The residual hitting-set polytope {x ∈ [0,1]^Y : x(G) ≥ 1 for gons in Y; x(S∖W) ≤ |S∖W| − 1} is **not integral**. Two small failing frames (general, k=6, n=15,16) give a nonempty polytope with no integer point (exact LP).
- Every constraint matrix has an odd 3×3 cycle submatrix, so none is TU or balanced.
- The conv-hull LP (Q12, Q20), not this polytope, is the one that was exact on frames.

### Status

- **Proof idea:** unchanged (frame plus gon repair). The probabilistic and counting route is closed.
- **Learned:** CORE has abundant solutions but no sparse structure, because gons are dense.
- **Obstacle:** the gon repair needs a global existence argument. The only candidate still standing is the conv-hull LP / weighted-Hall min–max, which was exact on all small frames tested.

**Evidence:** job 20261003-174609-b9f88d; scripts `slack.py`, `unique*.py`, `bias.py`, `gondens.py`, `poly.py` (run directly).
