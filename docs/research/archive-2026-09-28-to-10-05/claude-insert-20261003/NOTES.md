# Q11: induction on points for BDL (claude-insert-20261003)

Tags: **[P]** proved by hand; **[C]** computed (exhaustive Python or pysat/CaDiCaL; diagnostic, not Lean).

## Answer

**Negative.** No choice of x makes the repair local:
- A BDL partition π of X−x can be far from every BDL partition of X, even for the best x, and the distance
  grows with k.
- Repair along a single cup or cap through x fails.
- A point that can always be reinserted (a free point) usually does not exist.

## 0. Trivial facts [P]

- **Essential x** (x lies on every max cup or every max cap). Every π of X−x extends: put x alone into the
  freed extreme band.
- **Non-essential x.** J(X−x) = J(X), so σ|X−x is a partition of X−x and some π extends with no other point
  moving.
- So "every partition of X−x fails" **never** happens. All the content is in the worst π:
  D(x) = max_π min_σ #{y ≠ x : π(y) ≠ σ(y)}.

## 1. Repair distance [C]

**Exhaustive** (all decomposable colourings, every k with ≥ 2 bands, every non-essential x):

| n | max D(x) | (X,k,x) with a π that is not chain-repairable | (X,k) without essential point: min over x of D |
|---|---|---|---|
| ≤ 6 | 2 | 0 | 0: 5, 1: 7 |
| 7 | 3 | 5 | 0: 123, 1: 89, 2: 2 |
| 8 | 3 | 75 | 0: 1506, 1: 1203, 2: 18, 3: 1 |

**Tight samples.** "Free" means D(x) = 0. LB is a lower bound on D(x), from blocked and random π.

| set | samples with a free point | min over x of D |
|---|---|---|
| T(5,5,6), n=14 | 0/40 | LB ≥ 2 in 14/15; one set has **D(x) = 7 exactly for every x** |
| T(5,6,7), n=25 | 12/30 | LB: 0:3, 1:5, 2:3, 3:1 |
| T(6,6,7), n=30 | 2/15 | LB **8, 6, 5, 3**; for every x the farthest π is not chain-repairable |
| 2-band T(4,6,7), T(5,5,7), T(4,7,8) | 16/30, 29/30, 16/20 | LB ≤ 1 |

**Slack makes it worse.** Sets with slack 2–7 have a free point in only 4/30, 4/30 and 1/40 samples.

**D is not bounded by one chain.** In one n=25 set, 13 points have D = 11–14, while cup X = 5.

## 2. Which x [C]

At n=8 there are 2728 cases without an essential point. The best point of each role reaches D = 0/1/2/3 as
follows:

| role | D = 0 | D = 1 | D = 2 | D = 3 |
|---|---|---|---|---|
| first point of a max cap (best) | 1141 | 1551 | 35 | 1 |
| cherry leaf | 1197 | 1438 | 90 | 3 |
| leftmost point (worst) | 793 | 1561 | 364 | 10 |

The same ranking holds at k=7. No role is safe.

## 3. Strengthened statements: all false [C]

1. **"Every π repairs along one cup or cap through x."** It first fails at n=7. In the T(5,5,6) set, most
   partitions of X−x fail it, for every x: 263–911 per x.
2. **Monotone chain repair** (up along a cup, down along a cap). It fails at n=6.
3. **"Some x is free."** It fails in 40/40 sampled T(5,5,6) sets.
4. **"Bounded repair for the best x."** It fails: 7 in 13.

**Hall analogue.** The partitions of X−x that extend are exactly the restrictions of P(X). In that set these
are 36 of 383–1074. Characterising them means knowing P(X); there is no local criterion at x.

## 4. Why [C, with a proof attempt]

**Rigidity of tight sets.**
- Band sizes are forced: |X_j| = C(k−2, j).
- Extreme bands with chain limit 2 are single maximal chains, and they must cover the max chains left by the
  other bands.
- So P(X) is tiny: 36 or 53 partitions.
- Deleting x frees one unit of slack and removes all max chains through x. P(X−x) then grows 10–30×.
- The new partitions use extreme chains that X forbids. Example: a bottom 4-cap through point 3, which no
  partition of X uses.
- Returning means switching to another, possibly disjoint, maximal chain, and that cascades through the
  middle bands.

**DS anatomy** (n=25, `o_anatomy_sample1.txt`).
- The root split X = A << U is generic. A has cup 3 and cap 4, and lies in band 2 in all 53 partitions. U
  has cup 5 and cap 3, and lies in bands 3–4.
- The free points are exactly A.
- For x ∈ U, the worst π **mixes the children**: 6 A-points go up to band 3 and 6 U-points go down to band 2,
  giving D = 13.
- Lemma DS places nothing local in the way. A cap meeting U is a cap of U plus at most one A-point at each
  end; a cup meeting A is a cup of A plus at most one U-point at each end.
- With x present, only the strict concatenation survives.

**Where it bites.**
- The all-x counterexample is case R at the root ({7} << U), followed by a second nested marker {9}.
- Classical sets stay nearly local: every point of E(α,β) is free, and 2-band sets have best D ≤ 2.
- Non-locality appears with **≥ 3 bands**, i.e. exactly when the no-strong-k-set coupling is active.

**Consequence.** Point induction must restrict π to unmixed (concatenated) partitions, i.e. carry the tree.
That returns us to DS induction and case R: the same global coupling as Q7c (lookahead) and Q9 (global
freedom).

**Proof attempt [P].** With 2 bands, the canonical partition (bottom band B0 = first points of the β-caps)
inserts monotonically:
- F(X) = F(X−x) ∪ {first points of β-caps through x};
- only those points move, and all of them move down.

Q9 found no canonical multi-band rule, so this has no BDL analogue.

## Evidence

**Code:** `ins.py`, `combo.py`, `satrep.py`, `adv.py` (CEGAR worst π, blocked π, chain adversary), `free.py`,
`lb.py`, `exact1.py`, `certify556.py`.

**Jobs:**

| job | what |
|---|---|
| 20261003-130455-286e1d / -2c63f5 | n=8 |
| 20261003-133109-47be03, 20261003-134503-3300c9 | free points |
| 20261003-133608-ba496c | LB |
| 20261003-132507-27c91c | exact; sample 1 kept |

**Outputs:** `o_combo8_s*.txt`, `o_free*.txt`, `o_lb.txt`, `o_anatomy_sample1.txt`; data in `data_*.pkl`.

**All-x counterexample.** `o_exact_556_s0.txt`, re-checked without SAT by exhaustive DFS in
`o_certify556.txt`.
