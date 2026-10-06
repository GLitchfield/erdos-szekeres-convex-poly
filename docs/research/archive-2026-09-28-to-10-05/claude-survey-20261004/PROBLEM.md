# The problem, stated for a literature survey (2026-10-04)

Self-contained. All facts are from the project's runs; "[P]" means proved by hand (most are audited), "[C]" means
exhaustively or extensively computed but not proved.

## 1. Objects

**Colourings.** Points 1..n in x-order. Every triple i<j<k is coloured cup or cap, satisfying the signotope
(one-change) 4-point rule: for i<j<k<l, the sequence χ(ijk), χ(ijl), χ(ikl), χ(jkl) changes value at most once.
- A t-cup (t-cap) is x_1<…<x_t with every consecutive triple a cup (cap). In signotopes, every triple of it is then a
  cup (cap).
- A *strong t-set* (convex t-gon) is a set where for all i<j<k<l: χ(ijk) = χ(ijl) and χ(ikl) = χ(jkl). Equivalently,
  it is the union of a cup and a cap sharing both endpoints.
- Point sets in general position give signotopes: cup/cap is the orientation of the triple.

**Decomposable colourings** (Baek–Balko).
- Each point gets a binary label (its address in a binary tree).
- For a triple, take the first bit where its three labels differ. The triple is a cup iff its middle point (in
  x-order) has bit 0 there.
- Equivalently: X is a singleton, or X = L << U ("L deep below U") with both parts decomposable, where every triple
  meeting both parts is a cup iff its middle point lies in L.
- The x-order may INTERLEAVE L and U arbitrarily. The Erdős–Szekeres extremal construction is decomposable.

## 2. The theorem we want (Baek–Balko "Theorem 8")

A decomposable set with no a-cap, no u-cup and no strong k-set has at most T(a,u,k) points, where:
- T = C(a+u−4, a−2) if a+u <= k+3 (the classical cups–caps bound);
- T = Σ_{j=k−a}^{u−2} C(k−2, j) otherwise, i.e. the subsets of [k−2] with size in a window, or lattice paths of length
  k−2 in an (a−2)×(u−2) box.

This is tight. With a = u = k it gives 2^{k−2}, the Erdős–Szekeres conjecture bound, restricted to decomposable sets.

The published proof has a gap exactly at the case below.

## 3. What is known

- **Lemma DS [P, also in Lean].** For X = A << B: a cap of X meeting B is a cap D of B extended by at most one A-point
  before it and one after it; dually for cups.
  - strong(X) = max(strong A, strong B, cup A + cap B).
  - So "no strong k-set" is LOCAL: cup(A) + cap(B) <= k−1 at every tree node.
  - Lemma S [P]: strong(X) does not depend on the interleaving. Cup and cap depend only on where each part's extreme
    points fall among the other's points.
- **BDL, the Band Decomposition Lemma [C; exhaustive to n = 9, never failed for decomposable sets].** X with no strong
  k-set, cup α, cap β, α+β >= k, partitions into bands X_j (k−1−β <= j <= α−1) with cup X_j <= j+1 and
  cap X_j <= k−1−j.
  - [P, in Lean] BDL ⇒ Theorem 8: the classical bound gives |X_j| <= C(k−2, j), and the bands sum to T.
  - The bands mirror the blocks of the Erdős–Szekeres construction.
  - BDL is FALSE for general signotopes (a 14-point counterexample), so any proof must use decomposability.
  - BDL partitions are massively non-unique: 12 to more than 20,000 per tight set.
- **PSL, the Pascal split [C; never failed, even on general signotopes].** X = R ∪ Bl with cap R <= β−1,
  cup Bl <= α−1, and both with strong <= k−2. It gives Theorem 8 by induction on k.
- **Reduction [P, audited as conditional].** BDL ⟺ MIXED ROOT.

## 4. The single open step: MIXED ROOT (the "lock")

At a root split X = A << B (A lower), let s = k−1, β = cap X = cap B, p = cup A = s−β (tight). A sits strictly inside
the common core of B's maximum β-caps (every max cap of B starts before A and ends after A). A maximum β-cap of X uses
points of BOTH A and B ("mixed"): A-points extend B's (β−1)-caps.

Given a valid band partition of B, we must produce a valid band partition of X on the same band range. Points may
change bands.

What makes it hard:
- **No one-sided positioning.** "Put the bottom band of B on one side of A" is FALSE (n = 24 at p = 1; n = 40 at
  p = 2), yet BDL(X) still holds there.
- **Keep-or-lift.** Some A-points must stay in the bottom band and some must be lifted one band. Which ones depends on
  B's chain structure several tree levels down (lookahead).
- **Exact local conditions exist [P].** Lifting a point z to band p+1 is valid iff that band has no (β−1)-cap ending
  before z and none starting after z. Keeping a set K in band p is valid iff band p "straddles" no p-cup of K. These
  conditions are local; deciding WHICH points to lift is global.
- **The certificate is bounded but non-local [C].** At most about 4 tagged pieces of sibling information suffice at
  any node, but which pieces is fixed by the global partition.

## 5. Approaches that FAILED (with reasons), so the survey can skip them

- **Tree induction with any bounded context** (positional cuts, tower profiles, universal partitions, admissible
  contexts): the context regrows, or the choice needs lookahead. A proof always EXISTS inside a finite "two-sided
  tower" context language, but no local rule selects it.
- **Canonical, lookup or sweep rules** for bands or for PSL colourings: impossible by SAT (UNSAT cores). Tight sets
  have no forced choices.
- **Point insertion / augmenting repair:** the repair distance is unbounded. Realignment needs multi-band swap
  "stars", not chains.
- **Hall's condition:** insufficient (X14 satisfies it with no partition).
- **Matroid partition:** the band families are not matroids.
- **Greene–Kleitman shape:** none; the profile is not concave.
- **Polymorphisms (lattice/majority):** none. The 1-in-β relation appears.
- **Bounded width:** no; the width grows with n.
- **Lovász Local Lemma:** fails by a factor that grows with k. Strong sets are dense, about 250 per point at k = 6,
  n = 16.
- **Polyhedral:** the residual polytope is not integral; it has an odd cycle.
- **Rectification by local moves** (keep size, never increase cup/cap/strong, reach a non-interleaved set where the
  induction already works): monotone paths exist, but every potential function plateaus.
- **Context-bound recursion (an older route):** its bound function is not the true maximum.

## 6. Meta-insight

Statements that hold for general signotopes (PSL, and a related "CORE") would, if proved without decomposability,
prove the Erdős–Szekeres conjecture for signotopes. So a feasible proof must use the decomposable structure
ESSENTIALLY: the binary labels, the "deep-below" splits, Lemma DS. It cannot use only generic signotope facts.

## 7. What a useful tool would do

Any one of these would help:
- prove a global existence statement (a partition with prescribed band chain limits) where every local or
  inductive method fails, by exploiting the tree/label structure;
- give a bijective or algebraic model of decomposable sets, or of their cup/cap/strong structure, in which BDL or the
  window count T becomes structural (e.g. a lattice-path, Young-tableau or Boolean-lattice correspondence);
- or transform configurations (shifting/compression, symmetrization) toward a canonical form without increasing cup,
  cap or strong number, with a potential that provably decreases.
