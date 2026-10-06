# The gluing rule for halvings (k = 5 complete, k = 6 tested)

[C] = computed (diagnostic). [P] = hand proof at the end. Scripts and outputs are in this directory.

## Bottom line

- **Which pairs glue: all of them** [C].
  - k = 5: all 560 combinations (35 words × 16 half-types) occur.
  - k = 6: all 77 order types, and all 3,003 unordered pairs of them, occur as halves (198,514 halvings of 3,000
    samples).
- **How they glue.**
  - k = 5: exactly pairwise, by the pair rule (§2). This parametrizes every extremal 8-set completely.
  - k = 6: not pairwise.
- **The one global principle is an obstruction [P].** Points of one half that the other half cannot distinguish force
  a k-gon (twin lemma, §3). So the uniform gluing ES uses for *bands* (deep-below, cluster) never glues *halves*:
  the halves must twist through each other.

## 1. Gluing data [P]

- The cross triples are exactly: for each z ∈ Z, the extension Y + z (a cut of Y), and for each y ∈ Y, the cut
  Z + y. The cuts are coupled only by the one-change law on 2+2 quadruples.
- **x-separated halves.** A non-convex 4-set has exactly 7 views from the right [C]: the prefixes of its allowable
  sequence. So each z carries one slope label τ_z ∈ {0..6} (the number of Y-lines below z), each y carries σ_y, and
  (τ, σ) determines X.
- **At k = 6,** an extremal 8-set has 42–124 cuts from the right (199 sampled) [C]. These are not slopes.

## 2. The k = 5 rule

**Arc-separation lemma [P].** Let A be convex, and let A + z and A + z′ be convex with z, z′ in slots (edges) e and
e′. Then A ∪ {z, z′} is convex iff the line zz′ separates the vertices of A strictly between e and e′ from the rest.
- e = e′: there are no vertices between.
- e and e′ adjacent: the vertex between is the shared vertex.
- e and e′ not adjacent: the union is always convex.

**Pair rule (necessary and sufficient, any halving) [P].** X = Y ⊔ Z is pentagon-free iff there is no z ≠ z′ in one
half and no triangle T of the other half, with T + z and T + z′ both convex, such that:
- z and z′ use the same edge of T, and T lies on one side of the line zz′; or
- z and z′ use edges meeting at v, and the line zz′ cuts v off.

Checked: exact agreement with brute force on 303,358 halvings [C].

**x-separated form [P].** Take z < z′ to the right of Y, and let S^∓ be the Y-points below/above the line zz′.
There is a pentagon iff S⁻ contains one of:
- a 3-cup lma with z′ above the line ma;
- a 3-cap lma with z below the line ma;
- points l < a, a′ with z′ above la and z below la′;

or S⁺ contains the mirror of one of these. These are threshold conditions on (τ_z, τ_z′). This agrees with brute
force on all 384 configurations [C].

**Completeness [C].**
- Every extremal 8-set has 2–4 line-separable halvings.
- The 6,008 x-separated extremal signotopes realize all 77 order types.

So every extremal 8-set is, after a re-sweep, two triangles-with-interior-point side by side, glued by 8 slope
labels obeying the pair rule.

## 3. Why halves must twist [P]

**Twin lemma.** Let Y be extremal for k−1 and assume ES(k−1) (proved for k ≤ 7). If z, z′ ∈ Z lie in the same cell
of Y's line arrangement and the line zz′ misses conv(Y), then X has a k-gon.

**Corollary.** Deep-below or cluster gluing contains a (2k−4)-gon. At k = 5 all 32 deep-below and deep-above
gluings have a hexagon [C]. This explains why deep-below agreement tops out at 70–90%. At k = 6, all 3,983 twin
pairs seen have their line crossing the other half [C].

**Example [C].**
- Points: Y = (3,16), (7,18), (9,0), (13,32) and Z = (15,24), (20,20), (26,22), (38,25).
- X is pentagon-free. Labels: τ = (3,4,4,4) and σ = (4,3,6,0).
- The three twins with τ = 4 lie almost on one line, and that line passes through conv(Y).

## 4. The k = 5 gluing space has no simple shape [C]

- **Fraction.** 1.6–7.1% of completions are pentagon-free per (word, types); 2.9% overall.
- **Not a product.** There are 224–520 free x-gluings per type pair, but 448–5,333 tuples in the product of
  per-label allowed values.
- **Not a lattice.** Under the best of 128 orientations, at most 65% of pairs are closed under meet and join.
- **Not connected.** Under label steps the space has 2–12 components (the full space has 1). Under single flips it
  has 2–29.
- **Soft.** 53% of valid cross-flips of an extremal halving stay pentagon-free (64% at k = 6).

## 5. Bands and ES [C]

- **ES(5)** has 16 halvings. Its 9 Pascal halvings (T₀ with any 2 points of T₁ and any 1 of T₂) are not separable.
- **ES certificate.** Polygons cross bands as in ES: a cup in the first band, a cap in the last, at most 1 point in
  each band between. This forces k-gon-freeness, but it holds in some sweep for only **3 of 77** order types. Bands
  are a counting skeleton, not the gluing mechanism.
- **Canonical band split** (split each band by the cups–caps rule): it gives a halving for every k = 5 orbit, but
  for only 64 of 100 k = 6 samples (≤ 300 partitions searched).

## 6. k = 6 tests [C]

- **Separable halvings are rare.** Only 657 of 3,000 samples have one, although all 5 stored constructions do (for
  ES(6), the chord through T₁ and T₃).
- **Fixed-sweep x-gluing is selective.** Only 325 of 2,000 random pairs of extremal 8-signotopes glue with Y left
  of Z. None of the 251 pairs where both inner endpoints end/start a 4-cup and a 4-cap glued. This is a trend, not a
  law: its k = 5 analogue glues.
- **Not pairwise.** Of 7,392 hexagon-creating cross-flips, 767 create only (3,3)-hexagons. Example: sample #0 with
  Y = {0,1,2,3,5,6,7,9}; flipping (1,9,13) to a cup creates exactly {0,1,9 | 13,14,15}.
- **What survives** is the twin lemma and the (k−2, 2) arc separation, which gives the **corner rule [P]**: the
  Z-points extending a convex quadrilateral of Y use the edges at one vertex. This holds on all 103,206 cases checked.

## 7. Understanding

- **Mechanism.** Convex position is 4-local. A mixed k-gon is therefore a mutually extending pair (A ⊂ Y, B ⊂ Z):
  every point extends the other side, and every cross pair passes arc separation. At k = 5 the halves have no convex
  4-set, so only splits (3,2) and (2,3) occur, which makes the rule pairwise.
- **Obstacle.** Nothing compresses this local test further. Gluing is too flexible: every pair glues, about half of
  all flips survive, and the space is neither a product nor connected.
- **Open questions.**
  1. Is there a construction that glues *any* two given extremal (k−1)-sets? Test with SAT over the sweeps of two
     fixed order types.
  2. Is there a quantitative twist invariant, for example a minimum number of cells Z must occupy? Test by measuring
     it over the k = 6 halvings.
  3. Is there a triangle analogue of the corner rule? Test by slot analysis of the 767 (3,3)-only flips.

## Hand proofs

**Arc separation.**
- In Q = A ∪ {z, z′}, the only new turns are at the shared vertex v (adjacent slots) or at z and z′ (same slot).
  Every other turn already occurs in A, A + z or A + z′.
- Adjacent case: put v at the origin. The edge-region conditions place z and z′ on either side of the wedge at v.
  Then (z, v, z′) is a left turn iff the short arc from z′ to z contains the wedge, iff the line zz′ cuts v off.
  When the arc misses the wedge, no ray of the wedge meets the line zz′.
- Same-slot case: the two new turns are left iff A lies on one side of the line zz′.
- Inserting points into edge regions keeps the turning number at 1, so an all-left Q is convex.

**Pair rule.**
- A mixed pentagon is T ∪ {z, z′}, because the halves contain no convex 4-set.
- Any two edges of a triangle meet, so arc separation leaves exactly the two clauses.
- The x-form comes from the bridge decomposition. A strong set meeting both sides is a cup and a cap from l ∈ Y to
  r ∈ Z, each crossing the cut once, and each joint triple is a threshold test on τ.

**Twin lemma.**
- ES(k−1) gives a (k−1)-gon A + z in Y + z.
- A twin z′ has the same orientation with respect to every pair of Y, so A + z′ is convex with the same slot.
- The line zz′ misses A, so A ∪ {z, z′} is a k-gon.
- Deep-below gluing makes all of Z twins, with every line zz′ missing Y. By ES(k−1), Y plus the point at infinity
  contains a (k−2)-point right-open polygon, and Z has a matching left-open one. The bridge decomposition joins the
  two into a (2k−4)-gon.

**Corner rule.** Non-adjacent slots give a k-gon. In a polygon with at least 4 vertices, a set of pairwise adjacent
edges shares a vertex.

## Artifacts

- **Enumeration.** All 1,232,944 signotopes on 8 points: `all8.npy`. The 19,870 extremal ones: `free8.npy`
  (from `gen8.py`).
- **Order types:** `ordertypes5.json`.
- **k = 5 gluing:**
  - gluing space: `space8.json`;
  - (τ, σ) labels: `tausig5.json`;
  - pair-rule checks: `pairrule5.py`, `checks.py`;
  - order-structure tests: `lattice5.out`, `flipconn5.py`, `flip5.py`.
- **Separability and bands:** `sep_k5.jsonl`, `sep_k6.jsonl`, `escert_ot.json`, `bandhalf5.out`, `bandhalf6.out`.
- **k = 6 tests:** `halftypes6.jsonl`, `corner6.json`, `flip6.json`, `xglue6.jsonl`, `constr6.jsonl`.
- **Shared code:** `sig.py` (signotope utilities).
