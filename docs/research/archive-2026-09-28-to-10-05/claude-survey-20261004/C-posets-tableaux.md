# Area C: posets, chain partitions, tableaux, insertion (survey, 2026-10-04)

All computations below are diagnostic [C], not Lean. Scripts and outputs are in `C/`. Unrestricted BDL never failed in any of them. "cupend(v)" means the longest cup ending at v (left to right); "capend", "cupstart" and "capstart" are defined the same way.

## 1. Moshkovitz–Shapira / Fox–Pach–Sudakov–Suk labelling (the bijection behind C(a+u−4, a−2))

**Idea.** Give each edge uv the pair (c, d) = (longest cup ending with uv, longest cap ending with uv). Let D(v) be the down-closure of {(c(u,v), d(u,v)) : u < v}. For v < w, the triple uvw raises c or d, so (c(v,w), d(v,w)) lies in D(w) but not in D(v). Hence v ↦ D(v) is injective into the Young diagrams in a (u−2)×(a−2) box, of which there are C(a+u−4, a−2). The argument uses only consecutive triples, so it holds for every 2-colouring of triples (FPSS: N₃(2,n) = C(2n−4, n−2)+1; MS: the q-colour version, counted by (q−1)-dimensional partitions).

**Application.** The test confirmed the injectivity of D. On the ES sets `es_block(a,u)` (a, u ≤ 7) D is a **bijection** onto all diagrams in the box. The x-order is then a linear extension of inclusion (`ms_linext.out`), and the tree label is visibly the diagram's boundary word. For Theorem 8, T = #{(j, λ) : λ ⊆ j×(k−2−j)}. So BDL followed by MS inside each band is exactly a *graded* MS labelling, with the band j as the grade.
- On the ES Theorem-8 tight sets, the band equals cupend(v)−1, which also equals the Durfee size of D(v) when a ≥ u (`ms_labels.py`, `mirsky_bands.out`).

**Test.** The global labels do not see the strong bound. Over random sets with strong ≤ k−1, the diagrams realized number 16 at a = u = k = 5 (T = 8) and 42 at k = 6 (T = 16), so no fixed family of size T contains them (`ms_labels.out`).

**Verdict.** This answers the bijection question: yes, and it is a Seidenberg-type injection into lattice paths. It explains the count exactly, but it supplies no grading. Since it never uses decomposability, §6 implies it cannot prove Theorem 8 on its own. **Rank 1**, as the right target object; see the shortlist.

## 2. Dilworth (1950), Mirsky (1971): level-set partitions

**Idea.** The level sets of "longest chain ending at x" are antichains.

**Application.** Define the *Mirsky band* b(v) = cupend(v)−1, clipped to the BDL range. A (j+2)-cup inside band j would end at a point with cupend ≥ j+2, so **cups are automatically valid [P, trivial]**. Only caps can overflow. Dually, b(v) = k−1−capend(v) makes caps automatic.

**Tests** (`mirsky_bands.py`, `mirsky_lists*.py`, `mirsky_window_*.py`):
- The Mirsky-cup rule reproduces the ES blocks on all six tight constructions. It is valid in only 26–70% of random multi-band instances; all failures are cap overflows. The Durfee rule does worse.
- *Window* W(v) = [min, max] of {cupend−1, k−1−capend}:
  - It always admits a BDL partition, exhaustively for n ≤ 7 (21,796 instances at n = 7), even though it keeps only 7.3% of all BDL partitions there.
  - It also succeeded on 45,557 random instances and on 1,204 generated near-tight instances (n ≤ 32; 216 of them are tight with an interleaved root).
  - **It fails on 13 of the 1,116 configuration-H hard instances** (h_all[220, 325, 328, 348, 466, 467, 519, 534] with their reversals; smallest n = 21, k = 7). Each of these has a BDL partition.
  - The intersection with the right-to-left window fails in 16% of instances at n = 7.
  - The 4-value, reversal-symmetric span W4 survives all 1,116 hard instances, but it removes only 21% of (point, band) pairs. That is a weak restriction, not a mechanism.

**Verdict.** The cup half of BDL comes for free from a canonical rule, which makes the problem one-sided (cap repair only). Every window that is canonical and actually restrictive fails at larger n, the same pattern as BRL+ and S1. **Rank 2.**

## 3. Greene–Kleitman (1976), Greene (1974/76), Saks (1979), Gansner (1981), Frank (1980), Linial (1981)

**Idea.**
- Greene–Kleitman: chain partitions exist that are k-saturated, and even simultaneously k- and (k+1)-saturated.
- Greene: for a permutation, the RSK shape λ satisfies λ₁+…+λ_k = the largest union of k increasing subsequences.
- Proofs of these results:
  - Saks: take the product with a chain.
  - Gansner: the shape is the Jordan type of a generic nilpotent matrix on the poset or DAG.
  - Frank: min-cost flow, which gives orthogonal chain and antichain families.
- Linial carries the theorem to digraphs.

**Application.** As a "t-family", take the points of bands ≤ t. The analogue would ask for one BDL partition that is simultaneously saturated: |P_{≤t}| = G_t := max over BDL partitions, for every t.

**Test** (`gk_saturation.py`). This simultaneous partition fails in 6 of 168 sampled instances (bottom saturation) and 17 of 168 (top saturation). An exhaustively checked witness (`gk_example.out`): n = 8, k = 6, labels `0101 000 0010 0100 0011 1 0111 0110`, bands 1..4. Here G₁ = 4 and G₂ = 8, but no partition attains both.

**Verdict.** No. Every proof of these results needs the constraints to be chains of a transitive binary relation, so that the matrix is totally unimodular, a network, or a nilpotent matrix. Here the constraints are 3-uniform cups and caps, and the project has already found a non-integral polytope, non-matroid band families and a non-concave profile.

## 4. RSK / Schensted (1961), Knuth (1970), jeu de taquin, plactic monoid, Viennot (1977) shadows

**Idea.** Row insertion with bumping: the length of row 1 is the LIS (longest increasing subsequence), and Knuth moves preserve the shape. Viennot draws the same rows as shadow lines.

**Application.**
- Rows are bands. Points are inserted in x-order. A blocked point bumps one occupant into the next band: up after a cup violation, down after a cap violation.
- A plactic analogue does exist in one respect: by Lemma S, strong is invariant under re-interleaving, as shape is under Knuth moves. But cup and cap are not invariant, so no "shape" survives.

**Test** (`schensted_bands.py`). On random instances, Schensted bumping succeeds in 19/29, 326/394, 37/54 and 931/1015 cases (by size), against 17/29, 366/394, 33/54 and 998/1015 for first-fit greedy.

**Verdict.** No. This is single-path augmenting repair, which the project already found insufficient (repair needs multi-band "stars").

## 5. Fomin growth diagrams and dual graded graphs (1994, 1995); Krattenthaler (2006)

**Idea.** RSK as local rules on a 2-D grid of partitions. Krattenthaler applies this to 0–1 fillings of Ferrers shapes, where the longest NE-chain and SE-chain have a symmetric joint distribution.

**Application.** The MS labels behave like a growth process: appending a point on the right adds a new diagram D(w) and leaves the earlier diagrams unchanged.

**Verdict.** No. Local rules need a 2-relation on cells. The project's SAT result (no bounded lookup or sweep rule) excludes a bounded-state growth rule for bands.

## 6. Splitting permutations: Kézdy–Snevily–Wang (1996), Wärn (2021), Jelínek–Valtr (2015)

**Idea.**
- Partitioning a permutation into k increasing and l decreasing subsequences is obstructed by finitely many "critical" permutations. Wärn shows these can be long.
- Jelínek–Valtr call a class *splittable* when every member is a merge of members of two proper subclasses.

**Application.** BDL is a merge statement for the hereditary class of decomposable sets, with the bands as subclasses. Signotopes have an obstruction (X14); decomposable sets apparently have none.

**Verdict.** This is a reframing only. One could attempt "every minimal BDL obstruction contains a non-decomposable pattern", but KSW-type methods bound the size of obstructions and do not construct partitions. **Rank 3.**

## Ranked shortlist

1. **Graded MS labelling (§1).** Restate BDL as: X injects into the pairs (j, λ ⊆ j×(k−2−j)) with j = the band. This is a lattice-path (Young-diagram) model in which T is structural, which is exactly what PROBLEM §7 asks for. The missing piece is a grading taken from the tree.
   - Next test: on the configuration-H corpus, look for a BDL partition whose band-internal diagrams are the global D(v) truncated to the band box.
2. **Mirsky-cup start plus cap repair (§2).** Cups are free, so the problem becomes a single-family covering question. The W counterexamples (smallest n = 21) are the instances to study, because their repair must leave the window.
3. **Obstruction / splittability reframing (§6).** Low expected yield.

Refuted or unpromising: Greene–Kleitman simultaneous saturation (witness at n = 8), Schensted bumping, growth diagrams, and flow, LP or nilpotent-matrix proofs.

## References (verified via Crossref, arXiv or publisher pages)

- R. P. Dilworth, A decomposition theorem for partially ordered sets, Ann. of Math. 51 (1950) 161–166.
- L. Mirsky, A dual of Dilworth's decomposition theorem, Amer. Math. Monthly 78 (1971) 876–877.
- C. Schensted, Longest increasing and decreasing subsequences, Canad. J. Math. 13 (1961) 179–191.
- D. E. Knuth, Permutations, matrices, and generalized Young tableaux, Pacific J. Math. 34 (1970) 709–727.
- C. Greene, An extension of Schensted's theorem, Adv. Math. 14 (1974) 254–265.
- C. Greene, D. J. Kleitman, The structure of Sperner k-families, J. Combin. Theory Ser. A 20 (1976) 41–68.
- G. Viennot, Une forme géométrique de la correspondance de Robinson–Schensted, LNM 579 (1977) 29–58.
- M. Saks, A short proof of the existence of k-saturated partitions of partially ordered sets, Adv. Math. 33 (1979) 207–211.
- A. Frank, On chain and antichain families of a partially ordered set, J. Combin. Theory Ser. B 29 (1980) 176–184.
- E. R. Gansner, Acyclic digraphs, Young tableaux and nilpotent matrices, SIAM J. Algebraic Discrete Methods 2 (1981) 429–440.
- N. Linial, Extending the Greene–Kleitman theorem to directed graphs, J. Combin. Theory Ser. A 30 (1981) 331–334.
- S. Fomin, Duality of graded graphs, J. Algebraic Combin. 3 (1994) 357–404.
- S. Fomin, Schensted algorithms for dual graded graphs, J. Algebraic Combin. 4 (1995) 5–45.
- A. E. Kézdy, H. S. Snevily, C. Wang, Partitioning permutations into increasing and decreasing subsequences, J. Combin. Theory Ser. A 73 (1996) 353–359.
- C. Krattenthaler, Growth diagrams, and increasing and decreasing chains in fillings of Ferrers shapes, Adv. Appl. Math. 37 (2006) 404–431.
- J. Fox, J. Pach, B. Sudakov, A. Suk, Erdős–Szekeres-type theorems for monotone paths and convex bodies, Proc. London Math. Soc. 105 (2012) 953–982.
- G. Moshkovitz, A. Shapira, Ramsey theory, integer partitions and a new proof of the Erdős–Szekeres theorem, Adv. Math. 262 (2014) 1107–1129.
- V. Jelínek, P. Valtr, Splittings and Ramsey properties of permutation classes, Adv. Appl. Math. 63 (2015) 41–67.
- D. Wärn, Partitioning permutations into monotone subsequences, arXiv:2102.10328 (2021).
