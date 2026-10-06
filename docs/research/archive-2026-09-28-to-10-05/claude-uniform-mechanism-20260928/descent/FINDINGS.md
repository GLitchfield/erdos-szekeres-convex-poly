# Track B findings: Pascal descent of the context bound in k

Run `claude-uniform-mechanism-20260928`, Track B (`claude-code:17de3bb4-…/track-b`), 28 Sept 2026. Node context: `ErdosSzekeres.ctx_bound_prefix_suffix_domination`. (Saved by the coordinator from the subagent's report, with Gavin's approval; the harness blocked the subagent's own write.)

**Verdict.** Conjecture P is **false** on non-extreme contexts, in **both directions**, and also when restricted to thick contexts. The failures are bulk phenomena, not boundary ones. They appear at every k tested (6–9), and one family's defect grows with k (−1, −2, −3, −5). P does **not** reduce `ctx_bound_additive` to extreme-coupling or marker cuts plus parameter boundaries.

What holds is an exact **tree identity** (Theorem 4, proved on paper). Pascal descent is exact per cut tree, up to two corrections: a count of isolated-vertex leaves, and couplings that reach 0. P fails for exactly two reasons:
1. **Isolated vertices.** A leaf with cap limit = cup limit = 1 has no Pascal letter.
2. **Misalignment.** No single cut tree is optimal in both the cap world and the cup world.

"Diagnostic" means an exhaustive computation over bounded abstract contexts with the shared semantics `context-bound-zero-children-v1`. It is not Lean-certified and earns no theorem credit. "Proved" means a paper proof (§3) that has not been checked in Lean.

## 1. Definitions (Lean-style, over `Ctx.Context`)

`B_k(pl,cl)` = `baseOf cl pl k`:
- 0 if a limit is 0;
- 1 if a limit is 1;
- `decomposableThreshold (pl+1) (cl+1) k` otherwise.

```lean
def Context.capRed (σ : Context) : Context :=
  { σ with a := σ.a - 1, u := min σ.u (σ.k - 1), k := σ.k - 1,
    maxima := (List.range σ.maxima.length).map fun i =>
      if σ.sideAt (i+1) = Side.lower then σ.maximumAt (i+1) - 1 else σ.maximumAt (i+1) }
def Context.cupRed (σ : Context) : Context :=
  { σ with a := min σ.a (σ.k - 1), u := σ.u - 1, k := σ.k - 1,
    maxima := (List.range σ.maxima.length).map fun i =>
      if σ.sideAt (i+1) = Side.upper then σ.maximumAt (i+1) - 1 else σ.maximumAt (i+1) }
def Context.NonExtreme (σ : Context) : Prop :=
  σ.WellFormed ∧ 4 ≤ σ.a ∧ 4 ≤ σ.u ∧ σ.a ≤ σ.k - 1 ∧ σ.u ≤ σ.k - 1 ∧
  ∀ m ∈ σ.maxima, 2 ≤ m ∧ m ≤ σ.k - 3
def Context.Thick (σ : Context) : Prop :=   -- p over first positions of runs
  ∀ p ∈ σ.runStarts, 2 ≤ σ.capLimit p p ∧ 2 ≤ σ.cupLimit p p
```

Letters are kept. A maximum that reaches 0 marks a "ghost" level: its letters still extend chains, but its join term never binds.

- **Cut tree** with coupling range `[lo,hi]`: a leaf when `numRuns ≤ 1`; otherwise a node `(block ∈ σ.blocks, orientation o, d ∈ [lo,hi], t₁, t₂)`. Here t₁ and t₂ are trees of `σ.part block o m_o(d)` and `σ.part rest ō m_ō(d)`, with `m_lower(d) = d` and `m_upper(d) = k−1−d`.
- **Value:** `val t` is the sum of the leaves' `base`.
- **Lean bound:** `σ.bound` is the maximum of `val` over trees with range `[1,k−2]` (this is `boundFuel`).
- **`N11(t)`:** the number of leaves with capLimit = cupLimit = 1.
- **`bound⁻`:** the same maximum, but those leaves count 0.
- **`t↓cap`:** coupling d ↦ d−1; a tree of `capRed` with range `[0,k−3]`.
- **`t↓cup`:** coupling d unchanged; a tree of `cupRed` with range `[1,k−2]`, so its upper cup maxima range over `[0,k−3]`.
- **`bound^{cap+}`, `bound^{cup+}`:** the (k−1)-world maxima over those extended ranges.

## 2. Conjectures tested

| # | statement | verdict |
|---|---|---|
| P | `NonExtreme σ → σ.bound = σ.capRed.bound + σ.cupRed.bound` | refuted in both directions |
| P≤ (descent) | `NonExtreme σ → σ.bound ≤ σ.capRed.bound + σ.cupRed.bound` | refuted: isolated vertices, +1 and +2 |
| P≥ (ascent) | `NonExtreme σ → σ.capRed.bound + σ.cupRed.bound ≤ σ.bound` | refuted: misalignment, −1 to −5, growing with k |
| P_thick | P plus `Thick σ` | refuted in both directions |
| AOC | some root cut (K,o,d), d ∈ [2,k−3], is cap-optimal at d−1 and cup-optimal at d | fails on the 4-context `S1LS2US` family from (4,4,5) on; P survives there only through isolated-vertex compensation |
| E0 | `bound^{cap+}(capRed) = capRed.bound` and `bound^{cup+}(cupRed) = cupRed.bound` | no counterexample: 0 gain on every context, all maxima classes, k = 5–7 |
| Thm 4 | tree identity | proved; 214,677 random trees checked directly, 0 violations |
| Cor 5 | single-run Pascal | proved |

## 3. Proofs

Standing hypotheses: `3 ≤ k`, `a, u ≤ k−1`; maxima may be any naturals.

Notation:
- `e_s = chainExt s p q`;
- `J_s = max_{N ∈ levelsOn s 0}(leftExt s N p + rightExt s N q + maximumAt N)`, or 0 if there is no such level;
- `cupLimit = ((u−1) ∸ e_L) ⊓ ((k−1) ∸ max e_L J_L)`, and `capLimit` symmetrically.

Two facts are used throughout. `leftExt`, `rightExt` and `levelsOn` depend only on the word and on `maxima.length`, so the reductions leave them unchanged. Also `leftExt s N p ≤ leftExt s 0 p`.

**Lemma 1.**
- `capRed.capLimit = capLimit ∸ 1` and `capRed.cupLimit = cupLimit` (uses u ≤ k−1).
- Mirror statement for `cupRed` (uses a ≤ k−1).

*Proof.*
- Cap limit: `∸1` commutes with `⊓`.
- Cup limit: a lower join summand `ext_N + M_N` becomes `ext_N + (M_N∸1)`. If M_N ≥ 1 this is one less. If M_N = 0 both are ≤ e_L. Either way `max e (J') = max e (J∸1)`.
  - If `J ≤ e`, both limits equal `(u−1) ∸ e`, since u−1 ≤ k−2.
  - Otherwise `(k−2) ∸ (J−1) = (k−1) ∸ J`. ∎

**Lemma 2.** For nonempty block and rest:
- `(σ.part K s m).capRed = σ.capRed.part K s (m − [s=lower])`;
- the same for `cupRed` with `[s=upper]`.

So a k-cut (K,o,d) maps to the cap-cut (K,o,d−1) and the cup-cut (K,o,d). ∎

**Lemma 3.** For 0 ≤ p, c ≤ k−2: `B_k(p,c) = B_{k−1}(p∸1,c) + B_{k−1}(p,c∸1) + [p=c=1]`.

*Proof.* By cases, using the threshold Pascal rule `T(A,U,K) = T(A−1,U,K−1) + T(A,U−1,K−1)` for 3 ≤ A, U ≤ K. This is binomial Pascal in the choose regime, and a window shift in the window regime. Checked numerically for k ≤ 18. ∎

**Theorem 4.** `val_k(t) = val_{k−1}(t↓cap) + val_{k−1}(t↓cup) + N11(t)` for every tree t with range `[1,k−2]`.

*Proof.* Induction on t, using Lemma 2 at nodes and Lemmas 1 and 3 at leaves. ∎

**Corollary 5.** If numRuns ≤ 1, then `bound = capRed.bound + cupRed.bound + [capLimit = cupLimit = 1]`, with no hypothesis on the maxima.

**Corollary 6.**
- `bound = max_t [val(t↓cap) + val(t↓cup) + N11(t)]`.
- The defect is `bound − cap − cup = N11gain − noncommon + capExtGain + cupExtGain`, where all four terms are ≥ 0.
- `bound⁻ ≤ bound^{cap+} + bound^{cup+}`.
- With E0, descent holds up to isolated vertices. E0 amounts to "ghosting monotonicity", `(ρ.part K lower 0).bound ≤ ρ.bound` and its mirror, because the upper part of a coupling-0 cut has every cap limit 0. It is not proved.

**The brief's sketch.** Its descent sketch is Theorem 4, but it overlooks the (1,1) leaves, which arise at non-extreme cuts through the context history. Its ascent sketch needs a common optimal tree, which does not exist in general.

## 4. Evidence

Contexts come from `contexts(s,e,L,k)`. NE means every maximum is in [2,k−3]. Jobs marked (coord) are the coordinator's. Every job peaked at ≤ 676 MiB and ran for ≤ 29 minutes.

### 4.1 P on non-extreme contexts

| case | range | NE contexts | exact | +1 | +2 | −1 | −2 | job |
|---|---|---|---|---|---|---|---|---|
| (4,4,6),(4,5,6),(5,5,6) | s3e2L2 | 606 each | all | – | – | – | – | 140829-258402 (coord) |
| (4,5,6),(5,5,6) | s4e2L2 | 1167 each | all | – | – | – | – | 141019-ae52b7, e87842 (coord) |
| (4,5,7),(5,6,7) | s3e2L2 | 1292 each | all | – | – | – | – | 141020-8ffc93, 141019-5d8c2e (coord) |
| (4,4,7),(4,6,7),(5,5,7),(6,6,7) | s3e2L2 | 1292 each | all | – | – | – | – | 142129-b46ac3 |
| (4,5,6) | s3e3L3 | 15126 | 12706 | 2420 | – | – | – | 141020-dc2603 (coord), 143154-57e8d9 |
| (4,4,6) | s3e3L3 | 15126 | 11478 | 3648 | – | – | – | 57e8d9 |
| (5,5,6) | s3e3L3 | 15126 | 13542 | 1584 | – | – | – | 57e8d9 |
| (4,5,6) | s2e4L4 | 135209 | 96185 | 36792 | 2016 | 216 | – | 57e8d9 |
| (5,5,6) | s2e4L4 | 135209 | 105833 | 27920 | 1440 | 16 (thick) | – | 57e8d9 |
| (5,5,7) | s3e3L3 | 46832 | 44444 | 2388 (12 thick) | – | – | – | 143155-8e7199 |
| (5,5,7) | s2e4L2 | 10357 | 10293 | – | – | 64 | – | 150532-3b4db6 |
| (6,6,7) | s2e4L2 | 10357 | 10341 | – | – | – | 16 | 3b4db6 |
| (5,6,8),(6,7,8) | s3e2L2 | 2234 each | all | – | – | – | – | 3b4db6 |
| (6,6,8) | s3e2L2 | 2234 | 2230 | – | – | – | 4 | 3b4db6 |

Spot checks with the shared evaluator:
- `S1L2US` at (7,7,9), maxima (2,2): 85 vs 45+45 (defect −5);
- `1L2US1L2US` at (7,7,8), maxima (2,2): 45 vs 24+24 (defect −3).

### 4.2 Decomposition of the defect (`structure_probe.py`)

Tree-identity violations: 0 in every run. Extended-coupling gain: 0 in every run, including on 77,826 contexts of all classes (job 150532-6b9fe2: (4,5,6) and (5,5,6) at s2e3L3; (5,5,7) and (6,6,7) at s3e2L2).

| class | observation |
|---|---|
| thick NE, k=6, L3 | exact; 12/132/220 contexts only by compensation (N11 = noncommon = 1) |
| thin NE | every +1 or +2 is an uncompensated N11 gain; every −1 is noncommon |
| extreme contexts | full levels: +1 = N11 (the child is a single point); markers alone exact; thick mL,mU: −1 at (5,5,6), −2 at (6,6,7) |

### 4.3 The P-induction chain (`step_probe.py`, job 145811-674b04)

Scope: every partition, both orientations, d ∈ [2,k−3], NE σ. The link "additivity at k−1" never failed, and additivity itself was never violated.

| case | steps | descent fails on a part | ascent fails on σ |
|---|---|---|---|
| (5,5,6) s3e4L2 | 285,760 | 37,240 (13%) | 512 |
| (4,5,6) s3e3L3 | 281,920 | 106,732 (38%) | 0 |
| (5,5,7) s3e2L2 | 34,824 | 1,296 (3.7%) | 0 |
| (5,6,7) s3e2L2 | 34,824 | 1,296 (3.7%) | 0 |

The defective parts have bound 1–3.

### 4.4 Parts of extreme cuts (job 151058-378701)

Scope: distinct parts of d ∈ {1, k−2} cuts, s3e2L2.

| case | full-sibling parts | of which P-defect +1 | marker-sibling parts | of which P-defect +1 |
|---|---|---|---|---|
| (5,5,6) | 5440 | 954 | 5440 | 144 |
| (5,5,7) | 11608 | 1476 | 11608 | 144 |

A full-sibling part always has bound ≤ 1.

### 4.5 Boundaries

- **a = 3:** 60 failures at (3,4,5), 180 at (3,5,7), all +1. The cap world is then the one-point world.
- **u = k:** (4,5,5) 2 failures (+1); (5,5,5) 4 (+2); (4,7,7) 2 (+1); (5,7,7) 2 (+4). Lemma 1 needs u ≤ k−1, and at u = k no (k−1)-world parameter reproduces the chain term, so this is not a normalization issue.
- **Markers (maximum 1, image a ghost level):** exact, except the `S1L2US` sandwich: −1 (5,5,6), −2 (6,6,7), −2 (6,6,8), −3 (7,7,8), −5 (7,7,9).
- **Full levels:** +1 exactly on (1,1) points.

## 5. Failure families

All examples are well-formed and NE, and were confirmed with the shared evaluator.

### 5.1 Single-run isolated vertex (+1; needs 4 levels)

- (4,4,6) `2U1US3L4L` (2,2,2,2): run limits (1,1); bound 1 vs 0+0.
- (4,5,7) `2U1US3L4L` (2,2,2,4): 1 vs 0+0.
- (6,6,8) `1U2US3L4L` (2,5,2,5): 1 vs 0+0.

By Corollary 5 this is the only way a single run can fail.

### 5.2 Isolated vertices created by cuts (+1 or +2; three levels)

- (4,5,6) `1L2LS3US` (2,3,3): 1 vs 0+0.
- (4,5,6) `1L3US2US` (3,2,2): 2 vs 0+1.
- (4,5,6) `2L4US1L3US` (2,3,2,2): 2 vs 0+0.
- Thick: (5,5,7) `S2L1LS3US` (2,2,4): 4 vs 1+2.

### 5.3 Misalignment (−1 to −5; thick, NE, every k)

| family | case, maxima | bound_k vs cap + cup |
|---|---|---|
| `1L2US1L2US` | (5,5,6) (2,2) | 5 vs 3+3 |
| | (5,5,7) {2,3}² | 5 vs 3+3 |
| | (6,6,7) (2,2) | 16 vs 9+9 |
| | (6,6,8) {2,3}² | 16 vs 9+9 |
| | (7,7,8) (2,2) | 45 vs 24+24 |
| `S1L2US` | (6,6,8) (2,2) | 30 vs 16+16 |
| | (7,7,9) (2,2) | 85 vs 45+45 |

Mechanism:
- These contexts are mirror-symmetric (a = u), so the cap and cup worlds are mirror images, and so are their optimal trees.
- In `1L2US1L2US`, for example, the cap world's best cut puts block {5} lower, while the cup world's puts {2} lower or {5} upper.
- The k world has to choose one orientation.
- No failures of this kind at (4,5,6), (5,6,7), (5,6,8), (6,7,8) or (5,7,8).

## 6. Induction and residual

**The intended chain.** For a partition (K,o,d) of a NE σ with d ∈ [2,k−3]:

    bound A + bound B ≤ Σ images         (descent on A, B)
                      ≤ capRed.bound + cupRed.bound   (additivity at k−1; valid by Lemma 2)
                      ≤ bound σ          (ascent)

**What it does not certify:**
- **R1:** d ∈ {1, k−2}.
- **R2:** some maximum in {1, k−2}.
- **R3:** a or u ∈ {2, 3, k}.
- **R4:** NE σ where a part has an uncompensated isolated vertex. This is 13%, 38% and 3.7% of the steps above, occurs in thick σ, and appears at every k tested.
- **R5:** misaligned NE σ. These are generic thick contexts, and the defect grows with k.

R4 and R5 are bulk families, so the reduction to extreme cases is refuted.

**No weaker inequality helps.** Suppose G satisfies bound ≤ G on the parts, G ≤ bound on the parent, and G is additive by induction. Then G must equal bound. Theorem 4 is the only exact identity found, and it is a maximum of a two-world sum, not a function of the two bounds.

## 7. Proof status

- **Proved (paper):** Lemmas 1–3, Theorem 4, Corollaries 5 and 6.
- **Open:** E0. It implies `bound⁻_k ≤ cap + cup`.
- **Refuted:** P, P≤, P≥, P_thick and the P-induction. Both directions that the induction needs are false in the bulk.

## 8. Recommendation

1. Do not register P or the P-induction. Keep the §5 families as regression fixtures.
2. Theorem 4 transports cut trees exactly, so a proof that moves trees between worlds loses nothing. A proof that uses only values does lose something, because the two worlds' optimal trees differ. A mechanism that works for all k must therefore dominate in all Pascal worlds at once, at the level of leaf limits or labels. This is consistent with 0123 §7, where labels turned out to be global.
   - Concrete test for Track A: does its exchange rule dominate leaf by leaf in limits, with one interval tree working in the k world and both reduced worlds?
3. Optional formal assets, if something needs them:
   - Corollary 5 (exact for any maxima; could serve single-run bands);
   - Lemmas 1 and 2 (short transport lemmas);
   - Theorem 4 (needs a `CutTree` type);
   - E0 as a small conjecture.
4. Pascal descent in k does not help Codex's fixed-k route; it adds obstructions in the bulk.

## 9. Files

All under `runs/claude-uniform-mechanism-20260928/descent/`.
- **Library:** `pascal_lib.py`. It provides `make_F` with a coupling range and a configurable value for (1,1) leaves; it matches the shared evaluator on 4,468 contexts. It also has the reductions and the classifiers.
- **Probes:** `p_probe.py`, `structure_probe.py`, `aoc_probe.py` (output `aoc-small.*`, run interactively), `step_probe.py`, `extreme_parts_probe.py`, `tree_identity_check.py`.
- **Outputs:** `p7-s3e2l2.*`, `p8*`, `p7-s2e4l2-ne.json`, `struct6-ne*`, `struct7-ne*`, `struct-all*`, `step*`, `extreme-parts.txt`, `tree-identity-check.txt`.
- **Reused:** `contexts`, `child`, `limits_from_signature(lean=True)`, `T`.
- **New:** only the coupling-range variant of `make_F2`. Promote it to the shared library only if coupling-restricted recursions get reused.
