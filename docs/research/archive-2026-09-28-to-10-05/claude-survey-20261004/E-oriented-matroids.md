# Area E: oriented matroids, order types, pseudoline arrangements (survey, 2026-10-04)

Every reference below was checked by web lookup (title, authors, venue, year). Statements marked
[derived] are my own short arguments. Statements marked [diag] come from small exhaustive Python
runs (each under a minute, not saved, not Lean-certified).

## E1. Higher Bruhat order B(n,2)

**Key idea.** A signotope on [n] is a consistent set I ⊆ C([n],3), namely its set of cap triples.
B(n,2) orders these sets by single-step inclusion (Manin–Schechtman 1989). Felsner–Weil (2000) showed
this is the same as plain inclusion. The order is graded by |I|, its minimum is the all-cup (cyclic)
arrangement, and B(6,2) is not a lattice (Ziegler 1993). Allowable sequences map onto B(n,2), and each
fibre is a distributive lattice (Felsner–Weil 2001, Thm 13).

**Application.**
- A t-cap is a t-set S with C(S,3) ⊆ I, and a t-cup is one with C(S,3) ∩ I = ∅. So cap number
  increases and cup number decreases going up B(n,2). A band constraint (cup ≤ j+1, cap ≤ k−1−j)
  therefore cuts an order-convex window out of B(X_j,2).
- **The deep-below split is a parabolic interval [derived].** Fix L, U and the x-interleaving w. Let
  M(w) be the mixed triples whose middle point lies in U. The signotopes with this split form the
  inclusion interval [M(w), M(w) ∪ C(L,3) ∪ C(U,3)]. This interval is isomorphic to
  B(|L|,2) × B(|U|,2). It is the exact analogue of a parabolic coset uW_J = [u, u·w0,J] ≅ W_J in the
  weak order. Decomposable signotopes are what you reach from singletons by iterating these product
  intervals. A strong set is a one-level instance of the same construction: a cup deep below a cap
  (Lemma DS).

**Test.** [diag] At n = 6, every one of the 62 splits has a fibre of size exactly |B(r,2)|·|B(6−r,2)|.

**Verdict.** This is the right algebraic home for the split, but it does not produce a band partition.
Moving monotonically inside the interval is rectification, which plateaus (§5). **Medium, as a
language.**

## E2. Allowable sequences, wiring diagrams, reduced words of w0, rhombic tilings

**Key idea.** Simple allowable sequences are reduced words of w0. Up to commutation they correspond
exactly to arrangements and signotopes (Goodman–Pollack 1980, 1984; Felsner–Weil 2001 Thm 2). They also
correspond to rhombic tilings of the 2n-gon (Elnitsky 1997).

**Application [derived].**
- (L,U) is a deep-below split iff the wiring diagram has two sweep positions with the following
  property: between them only L–L and U–U crossings occur, with the L wires and the U wires each in one
  contiguous block.
- Equivalently, w0 ≐ π·(w0(L) × w0(U))·π′, where π and π′ have only L–U inversions. Such shuffles avoid
  the pattern 321, so they are fully commutative (Stembridge 1996) and their part of the tiling is
  forced.
- The tiling is therefore two sub-zonogons Z(L) and Z(U) glued at one vertex, plus two rigid L–U rhombus
  grids bounded by the lattice path of w.
- In the multiscale realization (y-gaps M1 ≫ M2 ≫ …), the middle cut is the y-order and crossings nest
  by tree depth.
- So a decomposable set is a binary tree whose nodes carry lattice paths in |L|×|U| boxes. Cups and
  caps are sets of de Bruijn strips whose induced subtiling is the minimum or the maximum one.
- Lemma S reappears here: a node's grid sees only where the sibling's extreme strips enter it.

**Test.** None needed for the encoding itself. Its usefulness is tested by E6.

**Verdict.** A clean re-encoding of (tree, x-order) that adds no new invariant. **Medium-low on its
own.**

## E3. Knuth, *Axioms and Hulls* (LNCS 606, 1992)

**Key idea.** CC systems are defined by five axioms on triples (cyclic symmetry, antisymmetry,
nondegeneracy, interiority, transitivity). They are 2-to-1 with uniform acyclic rank-3 oriented
matroids. Up to polynomial factors they are as numerous as pseudoline arrangements and primitive sorting
networks. There are at most 3^C(n,2) of them, and convex hulls can be computed in O(n log n) time using
only the CC predicate.

**Application.** Hull algorithms recognise convex position, not bands. I could not verify any ES result
in the book, so I cite none. ES for CC systems is the Goodman–Pollack conjecture (E5).

**Test.** None.

**Verdict.** **Low.**

## E4. Flips, mutations, realization spaces

**Key idea.**
- Triangle flips connect all simple arrangements (Ringel 1956).
- Realizable uniform oriented matroids are connected by mutations (Roudneff–Sturmfels 1988).
- The flip graph is the graph of B(n,2), which is not polytopal in general (Felsner–Ziegler 2001).
- Realization spaces can be arbitrarily complicated (Mnëv 1988).
- The mutation graph is disconnected in rank 7 and higher (Gu–Knauer, arXiv 2609.15850, Sept 2026). It
  is still connected in rank 3.

**Application.** Decomposable sets are always realizable (multiscale coordinates), so Mnëv-type
pathology is irrelevant. Flips are just rectification moves.

**Test.** [diag] Decomposable signotopes induce a connected subgraph of the flip graph for n ≤ 8. Their
counts for n = 1..8 are 1, 1, 2, 8, 62, 718, 10596, 186888, against all signotopes (OEIS A006245)
1, 1, 2, 8, 62, 908, 24698, 1232944. The decomposable sequence is not in OEIS.

**Verdict.** **Low** (§5 already covers this).

## E5. Erdős–Szekeres for pseudoconfigurations, CC systems and signotopes

**Key idea.**
- ES for signotopes is the Goodman–Pollack conjecture (1981). The cups–caps bound carries over to that
  setting.
- Dobbins–Holmsen–Hubard (2014) proved it equivalent to the Bisztriczky–Fejes Tóth conjecture for convex
  bodies.
- Holmsen–Mojarrad–Pach–Tardos (2020) extended Suk's bound 2^{n+O(√(n log n))} to pseudoline convexity.
- Balko–Valtr (2017) refuted the Peters–Szekeres hypergraph conjecture.
- Baek–Balko (SoCG 2025): state Theorem 8 with the proof omitted; show that the abstract
  ordered-hypergraph ES fails (C_weak(7) > 33); and found no counterexample among signotopes.

**Application.** This confirms the §6 meta-insight. No source has a band lemma, and the only
decomposable-specific source is Baek–Balko.

**Test.** None.

**Verdict.** **Background only.**

## E6. Tree-like subclasses and lexicographic extensions

**Key idea.**
- Horton sets (Horton 1983; Valtr 1992) are decomposable with alternating interleaving at every node.
  Valtr's construction and the ES construction are decomposable too (Baek–Balko §4).
- The literature's substitution operations (Valtr's cluster substitution, Las Vergnas' lexicographic
  extensions) replace a point by a set that is an interval in both x and y. The deep-below union is an
  interval in y only. I found no theory of the class closed under it.

**Application [derived].** In oriented-matroid terms, B sees every A-point as an infinitesimal
perturbation of the same point at vertical infinity. A triple made of one A-point and two B-points
depends only on the A-point's gap in B. Two consequences:
- A-points in the same gap of B are indistinguishable to B, and they form an x-interval of X.
- By §4, given band p+1, a point z can be lifted iff z lies strictly inside the common core (latest
  start, earliest end) of that band's (β−1)-caps. That region is also an x-interval.

**Test (gap-monotone lifting).** On the n ≤ 9 data and on the n = 24 and n = 40 one-sidedness
counterexamples, check by SAT whether some valid partition lifts, within each gap-run of A, an x-prefix,
an x-suffix or an x-interval of the run. If so, the global choice reduces to one cut per gap: a lattice
path, the same object T counts.

**Verdict.** **Medium**: cheap and sharp.

## E7. Zonotopal tilings, separation and purity

**Key idea.**
- The vertex labels of a rhombic tiling are the semispaces of the configuration (Goodman–Pollack 1984).
  They are also the maximal strongly separated collections (Leclerc–Zelevinsky 1998).
- Galashin–Postnikov (Mem. AMS 2023) define M-separated collections for any oriented matroid M:
  - Thm 2.7: those of maximum size correspond to fine zonotopal tilings and have size |Ind(V)|;
  - purity (every inclusion-maximal collection has maximum size) holds only for special M (in rank 3,
    the positroids).

**Application.**
- *Numerology.* For a = k, T(k,u,k) = Σ_{j≤u−2} C(k−2,j) = |Ind(U_{u−2,k−2})|. That is the number of
  vertices of every fine tiling of a zonotope of k−2 generic vectors in R^{u−2}. The general window
  counts the subsets S ⊆ [k−2] with |S| ≤ u−2 and |S^c| ≤ a−2.
- Purity theorems are exactly global existence results proved where local arguments fail, which is the
  kind of tool §7 asks for.
- The analogue here is **PURITY(a,u,k)**: every decomposable set with no a-cap, no u-cup and no strong
  k-set that has no one-point decomposable extension has exactly T points. PURITY together with
  non-extendability of the one explicit set P(a,u,k) implies Theorem 8.

**Test.** [diag] PURITY holds exhaustively at the following triples:

| (a,u,k) | T | sets by size (m = 3..T) | what was checked |
|---|---|---|---|
| (5,5,5) | 8 | 2, 8, 54, 374, 1656, 2862 | every set with ≤ 7 points extends |
| (4,5,5) | 7 | 2, 7, 35, 129, 193 | none of size 8 |
| (4,4,5) | 6 | — | 20 tight sets, all smaller ones extend |

Plain cups–caps (4,4) also holds for general signotopes. The general-signotope runs at k = 5 were stopped
unfinished because they would have exceeded the one-minute limit for runs outside the job system.

Next test: random greedy saturation at k = 6 (T = 16) and at (5,6,6), in both the decomposable and the
general class. One stuck set below T refutes PURITY. If PURITY also holds for general signotopes, it
inherits the §6 hardness, so watch for a gap between the two classes.

**Verdict.** Speculative, and the binomial windows may be a coincidence. But refuting it is cheap, and
this is the only source in Area E of global-existence theorems with matching sizes.

## Ranked shortlist

1. **PURITY test (E7).** Cheap to refute, and if true it turns "a partition exists" into "a point exists"
   plus one explicit check.
2. **Gap-monotone lifting (E6).** It would turn the keep-or-lift lookahead into a lattice path per gap.
3. **The parabolic-interval / fully-commutative-grid encoding (E1 + E2)** as the working language for
   the MIXED ROOT, including the cup and cap monotonicity in B(·,2).

## References

- Baek, Balko. The Erdős–Szekeres conjecture revisited. SoCG 2025, LIPIcs 332, 13.
- Balko, Valtr. A SAT attack on the Erdős–Szekeres conjecture. European J. Combin. 66 (2017) 13–23.
- Björner, Las Vergnas, Sturmfels, White, Ziegler. Oriented Matroids. CUP 1993.
- Dobbins, Holmsen, Hubard. The Erdős–Szekeres problem for non-crossing convex sets. Mathematika 60
  (2014) 463–484.
- Elnitsky. Rhombic tilings of polygons and classes of reduced words in Coxeter groups. JCTA 77 (1997)
  193–221.
- Felsner, Weil. A theorem on higher Bruhat orders. DCG 23 (2000) 121–127.
- Felsner, Weil. Sweeps, arrangements and signotopes. DAM 109 (2001) 67–94.
- Felsner, Ziegler. Zonotopes associated with higher Bruhat orders. Discrete Math. 241 (2001) 301–312.
- Galashin, Postnikov. Purity and separation for oriented matroids. Mem. AMS 289 (2023), no. 1439.
- Goodman, Pollack. On the combinatorial classification of nondegenerate configurations in the plane.
  JCTA 29 (1980) 220–235.
- Goodman, Pollack. A combinatorial perspective on some problems in geometry. Congr. Numer. 32 (1981)
  383–394.
- Goodman, Pollack. Semispaces of configurations, cell complexes of arrangements. JCTA 37 (1984) 257–293.
- Gu, Knauer. Neither simpliciality nor mutation connectivity… arXiv:2609.15850 (2026).
- Holmsen, Mojarrad, Pach, Tardos. Two extensions of the Erdős–Szekeres problem. JEMS 22 (2020)
  3981–3995.
- Horton. Sets with no empty convex 7-gons. Canad. Math. Bull. 26 (1983).
- Knuth. Axioms and Hulls. LNCS 606, Springer 1992.
- Leclerc, Zelevinsky. Quasicommuting families of quantum Plücker coordinates. AMS Transl. (2) 181 (1998)
  85–108.
- Manin, Schechtman. Arrangements of hyperplanes, higher braid groups and higher Bruhat orders. Adv.
  Stud. Pure Math. 17 (1989) 289–308.
- Mnëv. The universality theorems… LNM 1346 (1988) 527–544.
- Ringel. Teilungen der Ebene durch Geraden oder topologische Geraden. Math. Z. 64 (1956) 79–102.
- Roudneff, Sturmfels. Simplicial cells in arrangements and mutations of oriented matroids. Geom.
  Dedicata 27 (1988) 153–170.
- Stembridge. On the fully commutative elements of Coxeter groups. J. Algebraic Combin. 5 (1996)
  353–385.
- Valtr. Convex independent sets and 7-holes in restricted planar point sets. DCG 7 (1992) 135–152.
- Ziegler. Higher Bruhat orders and cyclic hyperplane arrangements. Topology 32 (1993) 259–279.
