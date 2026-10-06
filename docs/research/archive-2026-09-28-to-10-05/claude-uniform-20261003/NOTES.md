# Uniform gate statement: band decomposition (claude-uniform-20261003)

Labels: **[P]** proved on paper here; **[C]** computed (pysat/CaDiCaL, no DRAT, not Lean); **[?]** conjectural.

## 1. The object

A zone profile is P = (zones, Cp[i][j], Cu[i][j]). N(P; α, β) is the largest decomposable X that obeys P, has
cup ≤ α and cap ≤ β, and has no strong k-set, i.e. satisfies the DS node condition cup A + cap B ≤ k−1 at every node.
Concretely, N(P; α, β) = V(P ∧ (α, β)), computed by the audited r26u1 profile SAT (`psat.py`).
- **Lean contexts** map to P through `decomposable.context-limits` (zones = runs).
- **KS block profiles** are P with Cp[i][i] = a−1−d_i; union deficiencies are the off-diagonal entries.
- **[P] Dominance.** In the DS recursion the 14 per-zone interleavings reduce to AB, BA, ABA, BAB, with no required
  counts (`dsv.cpp`). Pure recursion is still too slow at k = 7.

## 2. Values (Q1, Q2)

N(P; α, β) on the full (α, β) grid, in `data/band_*.txt`:
- the 47 DS-child profiles of the gap bound G(5,6,7) (exact child sums: max 21 = G);
- 2,250 context profiles at k = 6 (≤ 4 letters, ≤ 3 levels);
- 806 KS/union-deficiency block profiles at k = 6.

**Q1: no** [C]. N is not "window words − one kill family K(P)". For G(5,6,7) the kills |W(α,β)| − N are:
- 1 at (3,4);
- 0 at (4,3) and (5,3);
- 4 at (4,4) and (5,4).

No fixed family fits. In fact N(G; α, β) = T(β, α+1, k) + C(k−3, β−2): the gate's kill grows with the coupling.

What does hold on all 3,103 profiles:
- kill counts are monotone in (α, β);
- N ≤ Σ_j N(P; j+1, k−1−j), the sum of single-band values.

**Q2** [C]. N is *adjacent-band Markov* (N = Σ(adjacent two-band values) − Σ(interior single bands)):
- it holds on all 923 one-sided context profiles and all 47 gap-children;
- it fails only for two-sided (cap + cup) contexts, 130 of 1,293, and for multi-gate block profiles that are not
  contexts, 11 of 403 (e.g. four cup blocks).

So a union deficiency shows up as an interaction between non-adjacent bands.

## 3. Structure: the Band Decomposition Lemma

**BDL [?].** Let X be decomposable with no strong k-set, α = cup X, β = cap X, α + β ≥ k. Then X = ⊔ X_j over
k−1−β ≤ j ≤ α−1, with cup X_j ≤ j+1 and cap X_j ≤ k−1−j.

**[P] BDL ⇒ Theorem 8.** By classical ES, |X_j| ≤ C(k−2, j); summing gives T. No gates are needed. The labelling is
point ↦ (band j, classical ES path inside the band), i.e. a window word. The ES lower-bound construction is exactly a
chain of bands. For general signotopes BDL would imply the Erdős–Szekeres conjecture, so a proof must use
decomposability.

**Evidence [C]:**
- all decomposable colourings with n ≤ 8 and every admissible k: 442,930 (X, k) pairs, 0 failures;
- 1,090 random sets and 2,803 sets with forced nested splits at k = 6, 7: 0 failures;
- k = 8: 574 samples over (4,8,8), (5,7,8), (5,8,8), (4,7,8), (6,7,8): 0 failures. The 240 tight-nested
  absorptions are counted in §4.

The *peel* form (a hitting set of the max caps with cups ≤ k−β) is **false**, at 14 and 11 points in (5,5,6).

**Why (Q3).** At X = A << B, A's bands are < cup A and B's bands are ≥ k−1−cap B. These ranges are disjoint by the
node condition, so the children's partitions concatenate and the kill families add on disjoint bands. This is the
window identity made structural. The one exception is below.

## 4. Proof attempt and the missing step

**[P] DS induction for BDL.** Every root split closes except one:
- classic children go to a free band;
- a non-tight nested A is absorbed into B's bottom band k−1−β (caps ≤ cap X, cups ≤ cup A + 2 ≤ k−β);
- the exception is **case R**: cap B = cap X = β and cup A = k−1−β. This is the tight nested split, i.e. the
  Baek–Balko gap.

Case R closes outright when B is classic or one-band: F = first points of A's β-caps goes into band k−1−β together
with B, and A∖F into band k−β. When B is window, case R closes **if B's bottom band lies on one side of A**.

**Invariant P [?].** If the β-caps of B share an interior core (L*, R*), then B has a band partition with bottom band
in (−∞, L*], and also one with bottom band in [R*, ∞).

Evidence [C]:
- P held on all 1,571 sampled sets with a nonempty cap core;
- the mirror P′ held on all 3,292 with a nonempty cup core;
- tight-nested absorption held in 3,240/3,240 samples (k = 6, 7, 8);
- the bottom band can even be taken inside the first points (or the last points) of the max caps, in 4,140/4,140
  samples.

**[P] BDL + P ⇒ gap bound.** The bottom band sits on one side of the gap, where caps are ≤ a−2, giving C(k−3, a−3);
the other bands give T(a−1,u,k); total G.

**Missing.** Propagate P through root splits. In DS language, at a tight nested split we need
|B_{k−1−β}| + |A| ≤ C(k−2, k−1−β) with B's bottom band one-sided. The naive constructions fail in three cases:
- a lone classic A at the bottom band;
- non-tight absorption;
- case R itself.

In each, A enters X's bottom band and can straddle core(X). The likely uniform hypothesis is BDL in a context, with
the sibling's letters tagged by band.

## 5. Negative results

- The context-local Pascal identity fails on 608 of 6,856 contexts.
- The classic peel is not exact.
- The ES-type Pascal rules fail.
- The pointwise core rule is unavailable (cupcore + capcore reaches 8 > k).
- My first V-vs-Lean comparison was invalid (one letter per run); Q4 has gone to Sol.

## Evidence

Scripts:
- `bdl_test.py`, `bdl_adv.py`, `bdl_exh.py`, `bdl_abs.py`, `bdl_core*.py`, `bdl_F.py`;
- `band_test.py`, `markov*.py`, `killgrid.py`.

Data: `data/`.

Jobs:
- 20261003-095429-9608b8, -100059-05af34, -100607-fa7e1c, -100752-1fa091, -100843-9ddc4e, -101533-03d361,
  -101959-70d8a4, -103732-79cbcd;
- -095254-5f6a3f / -6bb0e7 / -101605-f5de76.
