# Living bibliography and source ledger

Retrieved or rechecked 2026-08-01 unless noted. `Primary` means an original
research work or official formal source; `survey` means a synthesis. Preprints
are identified explicitly. URLs favor DOI, journal, arXiv, and official
repository records.

## Foundational problem and exact threshold

1. **P. Erdős and G. Szekeres**, “A combinatorial problem in geometry,”
   *Compositio Mathematica* 2 (1935), 463--470. Primary. Original existence,
   Ramsey proof, cup--cap proof, and conjecture.
   <https://www.numdam.org/item/CM_1935__2__463_0/>
2. **P. Erdős and G. Szekeres**, “On some extremum problems in elementary
   geometry,” *Annales Universitatis Scientiarum Budapestinensis de Rolando
   Eötvös Nominatae, Sectio Mathematica* 3--4 (1960/61), 53--62. Primary.
   All-`n` lower-bound construction.
3. **G. Szekeres and L. Peters**, “Computer solution to the 17-point
   Erdős--Szekeres problem,” *ANZIAM Journal* 48 (2006), 151--164. Primary.
   Exact `ES(6)=17`. <https://doi.org/10.1017/S144618110000300X>
4. **F. Marić**, “Fast formal proof of the Erdős--Szekeres conjecture for
   convex polygons with at most 6 points,” *Journal of Automated Reasoning* 62
   (2019), 301--329. Primary/formal, Isabelle/HOL.
   <https://doi.org/10.1007/s10817-017-9423-7>.  The official ARGO downloads
   page advertises the formalization archive as
   <https://argo.matf.bg.ac.rs/downloads/formalizations/HappyEnding.zip>.
   Retrieved and audited 2026-08-15: 42,349 bytes, SHA-256
   `505e855ae8b9b41fbfb705129ee1935d5b2413f1100484af22e883cf3f371b02`.
   It contains only `convex.thy`, `Combinatorics.thy`, and
   `generate-formula.cpp`; the checked theories stop at cases through five,
   while `6/17` appears only as dormant generator input.  No license, session
   root, generated formula, checked proof artifact, or final six-point theorem
   is included, so this archive is not an admitted formal proof of `ES(6)=17`.

## Upper bounds and proof methods

5. **F. R. K. Chung and R. L. Graham**, “Forced convex n-gons in the plane,”
   *Discrete & Computational Geometry* 19 (1998), 367--371. Primary.
   <https://doi.org/10.1007/PL00009353>
6. **D. Kleitman and L. Pachter**, “Finding convex sets among points in the
   plane,” *Discrete & Computational Geometry* 19 (1998), 405--410. Primary.
   <https://doi.org/10.1007/PL00009358>
7. **G. Tóth and P. Valtr**, “Note on the Erdős--Szekeres theorem,” *Discrete
   & Computational Geometry* 19 (1998), 457--459. Primary.
   <https://doi.org/10.1007/PL00009363>
8. **G. Tóth and P. Valtr**, “The Erdős--Szekeres theorem: upper bounds and
   related results,” in *Combinatorial and Computational Geometry*, MSRI
   Publications 52 (2005), 557--568. Survey with improvements.
   <https://library.slmath.org/books/Book52/files/30toth.pdf>
9. **G. Vlachos**, “On a conjecture of Erdős and Szekeres,” preprint (2015).
   Primary/preprint. <https://arxiv.org/abs/1505.07549>
10. **S. Norin and Y. Yuditsky**, “Erdős--Szekeres without induction,”
    *Discrete & Computational Geometry* 55 (2016), 963--971. Primary.
    <https://doi.org/10.1007/s00454-016-9778-2>
11. **H. N. Mojarrad and G. Vlachos**, “An improved upper bound for the
    Erdős--Szekeres conjecture,” *Discrete & Computational Geometry* 56
    (2016), 165--180. Primary.
    <https://doi.org/10.1007/s00454-016-9791-5>
12. **A. Suk**, “On the Erdős--Szekeres convex polygon problem,” *Journal of
    the American Mathematical Society* 30 (2017), 1047--1053. Primary;
    `2^(n+o(n))`. <https://doi.org/10.1090/jams/869>
13. **A. F. Holmsen, H. N. Mojarrad, J. Pach, and G. Tardos**, “Two
    extensions of the Erdős--Szekeres problem,” *Journal of the European
    Mathematical Society* 22 (2020), 3981--3995. Primary; best recorded error
    term and related extensions. ArXiv v3 and the EMS publication record were
    reauthenticated 2026-08-16. <https://arxiv.org/abs/1710.11415>
    <https://doi.org/10.4171/JEMS/1000>
14. **G. Moshkovitz and A. Shapira**, “Ramsey theory, integer partitions and a new proof of
    the Erdős--Szekeres theorem,” *Advances in Mathematics* 262 (2014),
    1107--1129. Primary/combinatorial reformulation.
    <https://doi.org/10.1016/j.aim.2014.06.008>

## Equivalent, strengthened, and structural formulations relevant to the target

15. **P. Erdős, Z. Tuza, and P. Valtr**, “Ramsey-remainder,” *European Journal
    of Combinatorics* 17 (1996), 519--532. Primary; strengthened conjecture and
    equivalence framework. <https://doi.org/10.1006/eujc.1996.0045>
16. **M. Balko and P. Valtr**, “A SAT attack on the Erdős--Szekeres
    conjecture,” *European Journal of Combinatorics* 66 (2017), 13--23.
    Primary; refutes a stronger abstract formulation.
    <https://doi.org/10.1016/j.ejc.2017.06.010>
17. **J. Baek**, “On the Erdős--Tuza--Valtr conjecture,” *European Journal of
    Combinatorics* 124 (2025), 104085. Primary; first new ETV case and Lean 4
    formalization. <https://doi.org/10.1016/j.ejc.2024.104085>
18. **J. Baek**, `jcpaik/erdos-tuza-valtr`, Apache-2.0 Lean 4 source.
    Primary/formal software. Read-only audit at commit
    `a5ad53efefb36f8654b9227ce4dba2bf04a7ec3f` found Lean `v4.13.0-rc3`;
    retrieved 2026-08-01. <https://github.com/jcpaik/erdos-tuza-valtr>
19. **J. Baek and M. Balko**, “The Erdős--Szekeres conjecture revisited,”
    *Journal of Combinatorial Theory, Series A* 222 (2026), 106195. Primary;
    split polygons, decomposable sets, and new extremal constructions.
    <https://doi.org/10.1016/j.jcta.2026.106195> The open-access SoCG 2025
    proceedings version was inspected on 2026-08-13:
    <https://doi.org/10.4230/LIPIcs.SoCG.2025.13>.
20. **N. Alon, E. Chiniforooshan, V. Chvátal, and F. Genest**, “Another
    abstraction of the Erdős--Szekeres happy end theorem,” *Electronic Journal
    of Combinatorics* 17 (2010), N11. Primary; useful for abstraction limits.
    <https://doi.org/10.37236/460>
21. **I. Pinelis**, “An order-refined and generalized version of the
    Erdős--Szekeres theorem on convex polygons,” preprint (2006). Primary;
    degeneracies and ordered polygons. <https://arxiv.org/abs/math/0611802>
22. **G. Damásdi, Z. Dong, M. Scheucher, and J. Zeng**, “Saturation results
    around the Erdős--Szekeres problem,” *European Journal of Combinatorics*
    131 (2026), 104236. Primary; includes saturation of the original lower-bound
    construction. <https://doi.org/10.1016/j.ejc.2025.104236>
23. **J.-P. Roudneff and B. Sturmfels**, “Simplicial cells in arrangements and
    mutations of oriented matroids,” *Geometriae Dedicata* 27 (1988),
    153--170. Primary; representability-preserving mutation connectivity for
    general-position arrangements. It does not address connectivity after
    restricting to target-free configurations. Rechecked 2026-08-10.
    <https://doi.org/10.1007/BF00151346>

## Computation and formal-verification methods

24. **M. Balko and P. Valtr**, item 16 above. Triple-orientation SAT model and
    decisive warning about over-strong abstractions.
25. **B. Subercaseaux, W. Nawrocki, J. Gallicchio, C. Codel, M. Carneiro, and
    M. J. H. Heule**, “Formal Verification of the Empty Hexagon Number,” ITP
    2024. Primary/formal Lean methodology; the empty-polygon result itself is
    not the project target. <https://doi.org/10.4230/LIPIcs.ITP.2024.35>
26. **M. J. H. Heule and M. Scheucher**, “Happy Ending: An Empty Hexagon in
    Every Set of 30 Points,” 2024. Primary/computational method.
    <https://arxiv.org/abs/2403.00737>
27. **B. Dumitru**, “Notes on the 33-point Erdős--Szekeres problem,” preprint (2025).
    Primary/preprint; SAT encoding for the first open exact case, not a settled
    proof. A complete local audit on 2026-08-30 found only the standard
    four-subset convexity proposition plus definitions and author-reported
    computations on non-exhaustive hull/anchor templates; the assigned source
    contained no independently checkable certificates.
    <https://arxiv.org/abs/2512.24061>
28. **V. Koshelev and A. Koshka**, “Combinatorial Geometry of Erdős--Szekeres
    Type Problems: SAT/ASP Modeling and Linear Subreduction,” preprint (2026).
    Primary/preprint; recent computational variants requiring independent review.
    <https://arxiv.org/abs/2604.20120>
29. **K. Fukuda, H. Miyata, and S. Moriyama**, “Complete enumeration of small
    realizable oriented matroids,” *Discrete & Computational Geometry* 49
    (2013), 359--381. Primary/computational. The authors' archived official
    OM(3,9) final-polynomial table supplies the exact 59-row certificate used
    for the Ringel-nine Lean theorem. Retrieved 2026-08-14 from the 2022-12-07
    Internet Archive snapshot of the official data endpoint; exact archive,
    member, and README hashes are recorded in the ignored run ledger.
    <https://doi.org/10.1007/s00454-012-9470-0>
30. **J. J. Carroll**, *Java Oriented Matroids*, version 0.3. Primary/software,
    GPLv3-or-later. The official `Examples.ringel()` crossing description was
    used only as a hashed read-only reference and was independently transported
    to the frozen 84-sign representative; no GPL source is incorporated into
    this MIT-licensed repository. Retrieved 2026-08-14.
    <https://sourceforge.net/projects/oriented/files/>

## Surveys and historical syntheses

31. **W. Morris and V. Soltan**, “The Erdős--Szekeres problem on points in
    convex position--a survey,” *Bulletin of the American Mathematical Society*
    37 (2000), 437--458. Survey; 89 references through 2000.
    <https://doi.org/10.1090/S0273-0979-00-00877-6>
32. **I. Bárány and G. Károlyi**, “Problems and results around the
    Erdős--Szekeres convex polygon theorem,” in *Discrete and Computational
    Geometry*, LNCS 2098 (2001), 91--105. Survey.
33. **A. Suk**, item 12, includes a compact modern history and the key
    transition to base two.
34. **Erdős Problems: Convex**, live problem index used only for discovery,
    never as a substitute for primary sources.
    <https://www.erdosproblems.com/tags/convex>

## Screened neighboring branches

These works are not alternative project destinations. They are retained for a
specific technique or caution.

35. **I. Bárány and P. Valtr**, “A positive fraction Erdős--Szekeres theorem,”
    *Discrete & Computational Geometry* 19 (1998), 335--342. Partition/same
    type machinery. <https://doi.org/10.1007/PL00009350>
36. **J. Fox, J. Pach, B. Sudakov, and A. Suk**, “Erdős--Szekeres-type
    theorems for monotone paths and convex bodies,” *Proceedings of the London
    Mathematical Society* 105 (2012), 953--982. Ordered monotone paths.
    <https://doi.org/10.1112/plms/pds018>
37. **A. Hubard, L. Montejano, E. Mora, and A. Suk**, “Order types of convex
    bodies,” preprint (2010). Order-type machinery.
    <https://arxiv.org/abs/1010.4613>
38. **M. G. Dobbins, A. Holmsen, and A. Hubard**, “The Erdős--Szekeres problem
    for non-crossing convex sets,” *Mathematika* 60 (2014), 463--484.
    Pseudoline/order-type connections.
    <https://doi.org/10.1112/S0025579314000072>
39. **O. Devillers, F. Hurtado, G. Károlyi, and C. Seara**, “Chromatic
    variants of the Erdős--Szekeres theorem on points in convex position,”
    *Computational Geometry* 26 (2003), 193--208. Colored screening.
    <https://doi.org/10.1016/S0925-7721(03)00013-0>
40. **T. Gerken**, “Empty Convex Hexagons in Planar Point Sets,” *Discrete &
    Computational Geometry* 39 (2008), 239--272. Empty-polygon screening.
    <https://doi.org/10.1007/s00454-007-9018-x>
41. **J. D. Horton**, “Sets with no empty convex 7-gons,” *Canadian
    Mathematical Bulletin* 26 (1983), 482--484. Shows why empty polygons are a
    genuinely different problem. <https://doi.org/10.4153/CMB-1983-077-8>
42. **G. Károlyi and P. Valtr**, “Point configurations in d-space without
    large subsets in convex position,” *Discrete & Computational Geometry* 30
    (2003), 277--286. Higher-dimensional screening.
    <https://doi.org/10.1007/s00454-003-0009-4>

## Oriented-matroid and signotope extension theory

43. **L. Finschi and K. Fukuda**, “Generation of Oriented Matroids—A Graph
    Theoretical Approach,” *Discrete & Computational Geometry* 27 (2002).
    Primary/computational. The paper records Las Vergnas's exact coline-cycle
    localization criterion for abstract one-element extensions; it does not
    establish stretchability of the extension. Retrieved 2026-08-13.
    <https://doi.org/10.1007/s00454-001-0056-5>
44. **B. Sturmfels and G. M. Ziegler**, “Extension Spaces of Oriented
    Matroids,” *Discrete & Computational Geometry* 10 (1993). Primary.
    Distinguishes fixed-realization adjoint extension spaces, their union over
    realization classes, and abstract extension-space topology. Retrieved
    2026-08-13. <https://doi.org/10.1007/BF02573961>
45. **H. Bergold, S. Felsner, and M. Scheucher**, “An Extension Theorem for
    Signotopes,” in *39th International Symposium on Computational Geometry
    (SoCG 2023)*, LIPIcs 258, article 17. Primary. Crossing-poset lower sets
    construct abstract signotope extensions; the theorem is not a
    straight-line realization criterion. Retrieved 2026-08-15 from the
    official Dagstuhl publication. <https://doi.org/10.4230/LIPIcs.SoCG.2023.17>
46. **A. Padrol and E. Philippe**, “Sweeps, Polytopes, Oriented Matroids, and
    Allowable Graphs of Permutations,” *Combinatorica* (2023). Primary.
    Separates sweep oriented matroids, their little oriented matroids, and
    pseudo-sweep/allowable structures. Retrieved 2026-08-13.
    <https://doi.org/10.1007/s00493-023-00062-3>
47. **H. Miyata**, “On Combinatorial Properties of Points and Polynomial
    Curves,” preprint (2017). Primary/preprint. Represents the relevant
    generalized sign systems by pseudoconfigurations; pseudocurve
    representability is not straight-line realizability. Retrieved 2026-08-13.
    <https://arxiv.org/abs/1703.04963>

## Additional authenticated quantitative input

48. **A. Pór and P. Valtr**, “The partitioned version of the
    Erdős--Szekeres theorem,” *Discrete & Computational Geometry* 28 (2002),
    625--637. Primary. Theorem 4 supplies the cyclic positive-fraction
    clustering cited by Suk. Its p. 629 construction selects
    `ceil (N / 2^(32*r)) - 1` interior points before adjoining the boundary
    anchor. Rechecked 2026-08-15.
    <https://doi.org/10.1007/s00454-002-2894-1>

## Weighted and geometric hypergraph machinery screened for Ticket 0039

49. **T. Kelly and L. Postle**, “Fractional coloring with local demands and
    applications to degree-sequence bounds on the independence number,”
    *Journal of Combinatorial Theory, Series B* 169 (2024), 298--337. Primary.
    The stable-set-polytope and weighted-independence equivalences validate the
    project's finite support-polytope language but do not produce a bound for
    predecessor hypergraphs. Retrieved 2026-08-19.
    <https://doi.org/10.1016/j.jctb.2024.07.002>
50. **G. Whittle**, “A geometric theory of hypergraph colouring,”
    *Aequationes Mathematicae* 43 (1992), 45--58. Primary. Its associated
    polymatroid and critical exponent encode hypergraph colorability; without
    an orientation-sensitive exponent bound this is target-equivalent rather
    than a producer. Retrieved 2026-08-19.
    <https://doi.org/10.1007/BF01840474>
51. **B. Keszegh and D. Pálvölgyi**, “Proper Coloring of Geometric
    Hypergraphs,” *Discrete & Computational Geometry* 62 (2019), 674--689.
    Primary. Its range hypergraphs arise from homothets or pseudo-disks; no
    theorem identifies strong predecessor edges with those traces at the
    required two-color threshold. Retrieved 2026-08-19.
    <https://doi.org/10.1007/s00454-019-00096-9>
52. **A. Biniaz, J.-L. De Carufel, A. Maheshwari, M. Smid, S. Smorodinsky,
    and M. Stojaković**, “Polychromatic Coloring of Tuples in Hypergraphs,”
    SoCG 2025, article 19. Primary. Its bounded-VC and geometric results color
    tuples or assume vertex-coloring bounds; they do not produce the required
    predecessor-free vertex support. Retrieved 2026-08-19.
    <https://doi.org/10.4230/LIPIcs.SoCG.2025.19>
53. **A. F. Holmsen and Z. Patáková**, “The fractional Helly number for
    separable convexity spaces,” arXiv:2412.01445v4 (2026). Primary/preprint.
    The theorem concerns intersecting subfamilies in separable convexity
    spaces with bounded Radon and dual VC parameters; a bridge to weighted
    predecessor independence is absent. Retrieved 2026-08-19.
    <https://arxiv.org/abs/2412.01445>

## Convex-geometry beta machinery screened for Ticket 0063

54. **P. H. Edelman, V. Reiner, and V. Welker**, “Convex, acyclic, and free
    sets of an oriented matroid,” *Discrete & Computational Geometry* 27
    (2002), 99--116. Primary. The application section expresses a beta
    invariant as an alternating sum over free sets and relates it to interior
    elements. The authors' TeX was retrieved 2026-08-21 from
    <https://www-users.cse.umn.edu/~reiner/Papers/pointed.tex>; the 65,749-byte
    file has SHA-256
    `680b2ac9d8787ab5af8401cc57d4bd0e9ddbeca1c2328c2eecf0664d7877e939`.
    Its displayed `(-1)^(rank-1)` interior formula conflicts with its preceding
    sphere dimension and with the exact rank-three four-point free-set sum,
    which has the opposite sign. Ticket 0063 therefore does not admit the
    frozen hereditary cone; a corrected convention requires a fresh audit.
    <https://doi.org/10.1007/s00454-001-0055-6>

## Structural sources authenticated for Batch 011

55. **M. Bouvel, V. Féray, X. Goaoc, and F. Koechlin**, “A Canonical Tree
    Decomposition for Order Types,” arXiv:2403.10311v2 (2024); official SoCG
    version titled “A Canonical Tree Decomposition for Chirotopes,” LIPIcs
    SoCG 2024, article 23. Primary. The source defines the bowtie product,
    proves its chirotope/realizability and extreme-element criteria for
    nontrivial factors with extreme marked proxies, and proves the unique
    canonical tree with no convex--convex edge. It does not state the
    project's proposed convex-capacity maximum formula or deep-split adapter.
    A project audit on 2026-08-30 derived the one-node maximum formula directly
    from the source sign rule at proposal level, including boundary
    restrictions; proxy-conditioned recursion and the ordered deep-split
    adapter remain unproved. Retrieved and cross-version audited 2026-08-22.
    <https://arxiv.org/abs/2403.10311>
    <https://doi.org/10.4230/LIPIcs.SoCG.2024.23>
56. **C. Huemer, F. Hurtado, M. Noy, J. Urrutia, and D. R. Wood**, “On the
    Number of Convex Polygons in Planar Point Sets,” *Discrete & Computational
    Geometry* 68 (2022), 448--476. Primary. The version of record defines the
    one-interior alternating edge charge, proves the pointwise/global
    identities and the `{-1,0,1}` local range, and characterizes charge `+1`
    by all remaining points lying in the interior of the opposite `p`-wedge.
    It supplies no canonical divider of that wedge, threshold-positive
    incidence theorem, or project deep-split adapter. ArXiv v1 and the version
    of record were retrieved and compared 2026-08-22.
    <https://arxiv.org/abs/1910.08736>
    <https://doi.org/10.1007/s00454-022-00395-8>

## Structural source authenticated for Batch 013

57. **V. Dotsenko and A. Khoroshkin**, “Gröbner bases for operads,” *Duke
    Mathematical Journal* 153(2) (2010), 363--396. Primary. The exact arXiv
    v2 source authenticates decorated tree monomials for free shuffle operads,
    admissible path-lex orders, divisibility and reductions, S-polynomials,
    the Diamond/Buchberger criterion, normal-monomial bases, and the
    symmetric-to-shuffle bridge. It does not supply the project's typed
    decomposition-tree operad, evaluation morphism, contextual congruence,
    relation producer, finite overlap bound, or normal-tree capacity theorem.
    Retrieved and source-audited 2026-08-23; arXiv archive SHA-256
    `da57684272b7b858b12cc8c832aa6b2019dbc954565f2c644766d66a3d3dad5f`,
    inspected `Grobner.tex` SHA-256
    `1337247274c720733231be814070445a37aa036f5ab341e56eb9b589b2fc9c41`.
    <https://arxiv.org/abs/0812.4069>
    <https://doi.org/10.1215/00127094-2010-026>

## Closure and graph-decomposition sources screened for continuous Batches 008--009

58. **P. H. Edelman**, “Meet-distributive lattices and the anti-exchange
    closure,” *Algebra Universalis* 10 (1980), 290--299. Primary. The
    accessible primary record authenticates the equivalence between finite
    anti-exchange closed-set lattices and meet-distributive lattices. It does
    not authenticate the project's binary rooted-circuit graph as a lattice
    join-dependency relation. Retrieved/rechecked 2026-08-25; full text was not
    obtained in the bounded audit. <https://doi.org/10.1007/BF02482912>
59. **R. M. McConnell and F. de Montgolfier**, “Linear-time modular
    decomposition of directed graphs,” *Discrete Applied Mathematics* 145
    (2005), 198--209. Primary. Defines directed modules, strong modules,
    quotient-node types, and the canonical decomposition of an independently
    specified digraph. It supplies no convex-closure-to-digraph correspondence
    or canonical geometric shore. Author manuscript inspected 2026-08-25.
    <https://doi.org/10.1016/j.dam.2004.02.017>
60. **A. L. Dulmage and N. S. Mendelsohn**, “Coverings of Bipartite Graphs,”
    *Canadian Journal of Mathematics* 10 (1958), 517--534. Primary. Sources
    finite simple bipartite relations, maximum disjoint edge sets, minimum
    covers, irreducible components, canonical decomposition, and the minimum-
    cover lattice. Publisher PDF retrieved 2026-08-25; SHA-256
    `40246997488a79622b5fb4d97f708cda28fd8c96c9d45a79c65aa9c83d678423`.
    <https://doi.org/10.4153/CJM-1958-052-0>
61. **N. Kita**, “The Dulmage-Mendelsohn Decomposition for b-Matchings,”
    arXiv:1606.08246v1 (2016). Primary/preprint. Its `b=1` specialization
    sources maximum matchings, elementary components, the canonical partial
    order and normalized ideals; later sections source one alternating-
    orientation algorithm and side-sensitive loose-vertex reachability. The
    exact classical chosen-matching implementation equivalence and explicit
    isolated/empty/perfect/multigraph conventions remain only partially
    covered. PDF retrieved 2026-08-25; SHA-256
    `57d5712a2bbd4da893eae3868e17e222f3c78f91614be5f58c0a8592c932336f`.
    <https://arxiv.org/abs/1606.08246>
62. **W. H. Cunningham**, “Decomposition of Directed Graphs,” *SIAM Journal on
    Algebraic and Discrete Methods* 3(2) (1982), 214--228. Primary. The
    accessible official abstract records a unique decomposition of digraphs
    under a general composition operation, but does not expose the precise
    arbitrary-undirected, disconnected, isolated-vertex graph-labelled-tree
    conventions required by the segment-crossing proposal. Retrieved
    2026-08-25; no source bytes retained.
    <https://doi.org/10.1137/0603021>
63. **E. Gioan and C. Paul**, “Split decomposition and graph-labelled trees:
    Characterizations and fully dynamic algorithms for totally decomposable
    graphs,” *Discrete Applied Mathematics* 160 (2012), 708--733. Primary.
    Definition 2.7, Lemma 2.8, Theorem 2.9, and Corollary 2.10 source connected-
    graph splits, marker vertices, reduced clique/star/prime graph-labelled
    trees, internal-edge leaf bipartitions, and uniqueness for connected
    graphs. They do not specify one canonical tree or forest for the proposed
    disconnected graph containing isolated segment vertices. Author manuscript
    retrieved 2026-08-25; 706,106-byte PDF SHA-256
    `862271e38564ca1c66d605bb81225fcb89042d79cf460f72b559acd7c3c7a529`.
    <https://doi.org/10.1016/j.dam.2011.05.007>
64. **M. Baker and O. Lorscheid**, “The moduli space of matroids,” *Advances in
    Mathematics* 390 (2021), article 107883. Primary. Theorems 5.9, 6.15, and
    7.25 together with Definition 7.27 and Corollary 7.28 source deletion and
    contraction on matroid moduli, the universal-idyll realization functor,
    and foundations as moduli for rescaling classes. They do not state the
    project's oriented, affine-rightmost marked-image theorem. Retrieved
    2026-08-25; 1,058,661-byte PDF SHA-256
    `6a76b0a1a6675ee8b2f1e137e6adf9eeba243016bb91522ed0c902d24a0e7359`.
    <https://arxiv.org/abs/1809.03542>
    <https://doi.org/10.1016/j.aim.2021.107883>
65. **M. Baker, O. Lorscheid, and T. Zhang**, “Foundations of matroids, Part 2:
    Further theory, examples, and computational methods,” arXiv:2310.19952v2
    (2023). Primary/preprint. Section 5.1 sources the generally noninjective
    foundation morphism `F_N -> F_M` induced by an embedded minor `N -> M`.
    By precomposition this supplies only the unmarked map from ambient-matroid
    to minor rescaling classes; it does not supply positive sign chambers,
    affine rightmost flags, a semialgebraic image theorem, or the project's
    union-fiber equivalence. Retrieved 2026-08-25; 737,732-byte PDF SHA-256
    `13d55a34b9010502b817ab68736137b178d7f607d9999391e20a55dc0ddd03c2`.
    <https://arxiv.org/abs/2310.19952>
66. **W.-L. Hsu and R. M. McConnell**, “PC Trees and Circular-Ones
    Arrangements,” *Theoretical Computer Science* 296 (2003), 99--116.
    Primary. Theorems 3.8 and 3.10 source the PC tree as a representation of
    all compatible circular orders for a matrix with the circular-ones
    property. The paper does not state that failed recognition returns a
    canonically normalized minimal Tucker submatrix of the original matrix.
    Author-hosted PDF retrieved 2026-08-25; SHA-256
    `466cb84242654aea514a089150bc0aa534a6fbb0f021ccf3667ec70fe70d5a1d`.
    <https://doi.org/10.1016/S0304-3975(02)00435-8>
67. **W. Hochstättler and M. Wilhelmi**, “Vertex-shellings of Euclidean
    Oriented Matroids,” arXiv:2306.07184v2 (2025 revision). Primary/preprint.
    Theorems 2.2 and 2.3 and Definition 2.5 source one-element-extension
    localizations, signed lexicographic extensions, their first-nonzero rule,
    reorientation to positive lexicographic extensions, and preservation of
    Euclideaness. Theorems 1.1 and 1.2 concern topological sweeps and
    vertex-shellings under Euclidean oriented-matroid-program hypotheses; they
    do not imply the project's minimum-support peeling, root-aligned point
    decomposition, or `D-DECOMP` bridge. PDF retrieved 2026-08-25; SHA-256
    `59963347040ed54882b802060c3c82884476025c77bc31648f6d1182edcd7e66`.
    <https://arxiv.org/abs/2306.07184>
68. **R. Bacher**, “The Orchard Morphism,” arXiv:math/0309071 (2003).
    Primary/preprint. Theorem 4.3 sources the natural complement-valued
    Orchard morphism, Section 5.2 its deletion-restriction vectors, and
    Propositions 6.1--6.2 the generic planar separating-hyperplane relation
    and flip covariance. A deletion vector has zero at the removed element;
    the paper does not define the project's total deleted-anchor pencil.
    Official-author PDF retrieved 2026-08-25; SHA-256
    `33aeac9f567a197d94b6c52551a576805b3333d28b3dc4cad7169c2845525db2`.
    <https://arxiv.org/abs/math/0309071>
69. **R. Bacher and D. Garber**, “Chromatic properties of generic planar
    configurations of points,” arXiv:math/0210051 (2002). Primary/preprint.
    Definition 1.1 and Theorem 1.2 give the planar Orchard equivalence via
    separating-line parity and at most two classes; Section 4 records that
    single-point deletion can change the relation substantially. It supplies
    no canonical deleted-anchor assignment or predecessor-bicoloring theorem.
    PDF retrieved 2026-08-25; SHA-256
    `461ae850528deb7294885f6b4f4b4e1aaaef96a21ed3560aa1aeb7b8747e88a8`.
    <https://arxiv.org/abs/math/0210051>

## Circular-ones and finite-algebra sources authenticated for continuous Batches 010--011

70. **M. D. Safe**, “Characterization and linear-time detection of minimal
    obstructions to concave-round graphs and the circular-ones property,”
    *Journal of Graph Theory* 93 (2020), 268--298. Primary. Theorem 6 gives
    the explicit minimal forbidden family `FcircR`; Lemma 10 maps a Tucker
    obstruction in a row-complement reduction back to the original matrix;
    Corollary 14 and Algorithm 1 return row/column maps selecting an `FcircR`
    member of the original negative instance in linear time. The returned
    occurrence is a replayable minimal-forbidden-submatrix certificate, but
    the source does not promise uniqueness, implementation-independent
    canonicality, or minimum cardinality among all occurrences. ArXiv PDF
    retrieved 2026-08-25; SHA-256
    `3a682ce5520676eccbd2be91bd4c2b8a21aed021716971424e89232ef928835d`.
    <https://arxiv.org/abs/1611.02216>
    <https://doi.org/10.1002/jgt.22486>
71. **L. Rónyai**, “Computing the structure of finite algebras,” *Journal of
    Symbolic Computation* 9(3) (1990), 355--373. Primary. The official record
    supports algorithms for radicals and simple summands of finite-dimensional
    associative algebras over finite fields under the paper's computational
    hypotheses. It does not define the project's proposed middle-link algebra
    or a canonical label-coordinate block. Official metadata/abstract checked
    2026-08-25; full text was not obtained in the bounded audit.
    <https://doi.org/10.1016/S0747-7171(08)80017-X>
72. **W. Eberly and M. Giesbrecht**, “Efficient Decomposition of Associative
    Algebras over Finite Fields,” *Journal of Symbolic Computation* 29(3)
    (2000), 441--458. Primary. The official record supports finite-field
    semisimple/Wedderburn decomposition and primitive-idempotent algorithms,
    not a canonical coordinate selector for an arbitrary route-specific
    commutant. Official metadata/abstract checked 2026-08-25; full text was
    not obtained. <https://doi.org/10.1006/jsco.1999.0308>
73. **A. Konovalov et al.**, *Wedderga: Chapter 9, The basic theory behind the
    functions*, GAP package manual. Official software documentation. It
    documents primitive central idempotents and Wedderburn components for
    semisimple group algebras and notes nonuniqueness of complete orthogonal
    primitive idempotents. Its domain is not an arbitrary generated matrix
    algebra. Checked 2026-08-25.
    <https://gap-packages.github.io/wedderga/doc/chap9.html>
74. **X. Zhu**, “Lifting Central Idempotents Modulo Jacobson Radicals and Ranks
    of K0 Groups,” *Communications in Algebra* 36 (2008), 2833--2848.
    Primary. The official record confirms that lifting central idempotents
    modulo a Jacobson radical is a hypotheses-sensitive separate problem; it
    supplies no automatic canonical lift for the proposed middle-link route.
    Official metadata/abstract checked 2026-08-25; full text was not obtained.
    <https://doi.org/10.1080/00927870802104352>

## Bracket and exact-certificate sources authenticated for continuous Batch 009

75. **S. J. Apel**, *The Geometry of Brackets and the Area Principle*,
    doctoral dissertation, Technical University of Munich (accepted 2014).
    Primary. Section 4.1, equations (4.2)--(4.3), and Definition 4.2 give the
    rank-three four-term and repeated-index three-term Grassmann--Plücker
    relations, alternating normalization, repeated-label zeros, and the
    rank-three bracket ring. Official TUM PDF retrieved 2026-08-25; 6,443,804
    bytes, SHA-256
    `17b67307e7df180c8580af17c1d191fddb8200f22e9a067a82659dda2a6f3cc7`.
    <https://mediatum.ub.tum.de/doc/1175107/104666.pdf>
76. **D. Speyer and B. Sturmfels**, “The Tropical Grassmannian,” *Advances in
    Geometry* 4 (2004), 389--411; arXiv:math/0304218v3. Primary. Section 3
    defines the Plücker ideal of generic minors over the integers and states
    quadratic generation/a quadratic Gröbner basis. At rank three this applies
    to original homogeneous vectors, not to an arbitrary abstract
    `TripleColoring`. PDF retrieved 2026-08-25; 248,684 bytes, SHA-256
    `335e576dd6370b6ffcd189426752b499ed253f26529824fdd4c99ea1419571c0`.
    <https://arxiv.org/abs/math/0304218>
77. **B. Natura**, *Exact Linear Programming: Circuits, Curvature, and
    Diameter*, PhD thesis, London School of Economics (2022). Primary.
    Theorem 7.1.1 and Definition 7.2.5 state exact matrix/subspace forms of
    Farkas alternatives and certificates for rational nonnegative systems.
    Official repository PDF retrieved 2026-08-25; 4,075,003 bytes, SHA-256
    `6e94bcb7c2b5b20823d3b62260c6d0d3c838743112201da73c501f07bb60f567`.
    <https://doi.org/10.21953/lse.00004448>
78. **K. K. H. Cheung, A. Gleixner, and D. E. Steffy**, “Verifying Integer
    Programming Results,” in *IPCO 2017*, LNCS 10328, 148--160. Primary.
    Section 2 and Remark 2 give signed linear-combination inference and the
    sufficiency of rational multipliers for rational infeasibility/optimality
    certificates and independent replay. Official Optimization Online PDF
    retrieved 2026-08-25; 350,860 bytes, SHA-256
    `f3c39ecda372d6873f7d92d84717d126592192a21218ad2730c869f6e4d3c17a`.
    <https://doi.org/10.1007/978-3-319-59250-3_13>

## Tope-graph sources authenticated for continuous Batch 011

79. **K. Knauer and T. Marc**, “On tope graphs of complexes of oriented
    matroids,” *Discrete & Computational Geometry* 63 (2020), 377--417.
    Primary. Theorem 1.1, Section 2, Theorem 4.9, and Corollary 7.2 source
    COM/OM tope graphs as antipodally gated partial cubes, theta-class
    halfspaces, gated-subgraph semantics, and the covector/antipodal-subgraph
    correspondence. They do not assert a proper gated-amalgam decomposition
    of every OM tope graph. Author manuscript retrieved 2026-08-25; SHA-256
    `30c4d31a3f80407ac4927e9ef99d86230bc03776305f7d48f6a7f1201f37122d`.
    <https://doi.org/10.1007/s00454-019-00111-z>
80. **V. Chepoi, K. Knauer, and T. Marc**, “Hypercellular graphs: partial
    cubes without $Q_3^-$ as partial cube minor,” *Discrete Mathematics* 343
    (2020), 111678; arXiv:1606.02154. Primary. Theorem B gives a successive
    gated-amalgam characterization for the special hypercellular partial-cube
    class. It does not state that arbitrary rank-three oriented-matroid tope
    graphs are hypercellular. Official arXiv record checked 2026-08-25; source
    bytes were not retained in the bounded audit.
    <https://arxiv.org/abs/1606.02154>

## Gammoid sources authenticated for continuous Batch 012

81. **J. H. Mason**, “On a Class of Matroids Arising From Paths in Graphs,”
    *Proceedings of the London Mathematical Society* s3-25 (1972), 55--74.
    Primary. Foundational finite path-matroid source; later literature records
    the resulting finite dimaze independence system as a matroid. Official
    metadata checked 2026-08-25; publisher text was not obtained.
    <https://doi.org/10.1112/plms/s3-25.1.55>
82. **A. W. Ingleton and M. J. Piff**, “Gammoids and transversal matroids,”
    *Journal of Combinatorial Theory, Series B* 15(1) (1973), 51--68.
    Primary. The official record supports strict-gammoid/transversal-matroid
    duality and the contraction characterization of general gammoids. It gives
    no project-specific Pascal-demand inequality. Checked 2026-08-25; full
    text was not obtained. <https://doi.org/10.1016/0095-8956(73)90031-2>
83. **H. Afzali, H.-F. Law, and M. Müller**, “Infinite strict gammoids,”
    arXiv:1310.6644v1 (2013). Primary/preprint. Definitions 1.2--1.3 define a
    dimaze, exits, mutually vertex-disjoint directed-path linkages, and the
    strict gammoid on the whole vertex set; the introduction records Mason's
    finite theorem. PDF retrieved 2026-08-25; 446,634 bytes, SHA-256
    `15af3d0ce1e9e68f77292b3960df94b4c2387f983ad9f96881d0741bf8d8b8f6`.
    <https://arxiv.org/abs/1310.6644>
84. **H. Perfect**, “Applications of Menger's graph theorem,” *Journal of
    Mathematical Analysis and Applications* 22 (1968), 96--111. Primary.
    Historical source for disjoint directed paths and gammoid independence;
    no exact statement located in the bounded audit relates linkability rank
    to the project's raw demand or ambient-cardinality bound. Official
    metadata checked 2026-08-25; full text was not obtained.
    <https://doi.org/10.1016/0022-247X(68)90163-7>

## Covector and matroid-connectivity sources authenticated for continuous Batch 012

85. **J. Oxley**, *Matroid Theory*, 2nd ed., Oxford University Press (2011).
    Primary monograph. The official book record and connectivity chapters
    source the standard represented-matroid and matroid-connectivity
    conventions used to make a binary incidence construction precise. They do
    not supply the project's covector incidence matrix, recursive selector, or
    point-cut consumer. Official record checked 2026-08-25; full book text was
    not retained. <https://doi.org/10.1093/acprof:oso/9780198566946.001.0001>
86. **S.-I. Oum**, “Rank connectivity and pivot-minors of graphs,” *European
    Journal of Combinatorics* 108 (2023), 103634; arXiv:2011.03205v4.
    Primary. The abstract explicitly defines graph cut-rank as the binary rank
    of the cross-shore adjacency submatrix. This corroborates a binary
    rank-connectivity convention only; it gives no oriented-matroid covector
    selector or bridge to the project's decomposition consumer. Official
    arXiv record checked 2026-08-25; source bytes were not retained.
    <https://doi.org/10.1016/j.ejc.2022.103634>

## Allowable-sequence, heap, and quasisymmetric sources audited for Batch 024

87. **J. E. Goodman and R. Pollack**, “On the Combinatorial Classification of
    Nondegenerate Configurations in the Plane,” *Journal of Combinatorial
    Theory, Series A* 29 (1980). Primary. Definition 2.1, Proposition 2.6, and
    Remark 2.7 source circular switch sequences, their restriction, and
    reflection for the paper's nondegenerate configurations. That hypothesis
    excludes parallel connecting pairs in addition to collinear triples, and
    the paper supplies no heap-factorization invariant or project deep-split
    consumer. Checked 2026-08-27; no paper bytes retained.
    <https://doi.org/10.1016/0097-3165(80)90011-4>
88. **G. X. Viennot**, “Heaps of Pieces, I: Basic Definitions and
    Combinatorial Lemmas,” *Annals of the New York Academy of Sciences* 576
    (1989). Primary. Definition 2.1 and Proposition 3.4 identify labeled heaps
    for a concurrency relation with the complementary commutation monoid. The
    specialization to pair-crossing supports is an inference; the source gives
    no geometric child operator or `HasDeepBelowSplit` theorem. Checked
    2026-08-27; no paper bytes retained.
    <https://doi.org/10.1111/j.1749-6632.1989.tb16436.x>
89. **S. Elnitsky**, “Rhombic Tilings of Polygons and Classes of Reduced Words
    in Coxeter Groups,” *Journal of Combinatorial Theory, Series A* 77 (1997).
    Primary. Theorem 2.2 distinguishes commutation classes of type-A reduced
    words from the other Coxeter moves. It does not prove braid invariance of a
    heap statistic. Checked 2026-08-27; no paper bytes retained.
    <https://doi.org/10.1006/jcta.1997.2723>
90. **U. Hoffmann and K. Merckx**, “A Universality Theorem for Allowable
    Sequences with Applications,” arXiv:1801.05992 (2018). Primary/preprint.
    The introduction, Lemma 1, and the universality results treat allowable
    sequences as refinements of order types and prevent an automatic inference
    of realization independence for a sequence statistic. They do not prove
    variation of the proposed Batch024 statistic on either frozen fixture.
    Checked 2026-08-27; no paper bytes retained.
    <https://arxiv.org/abs/1801.05992>
91. **R. I. Liu and M. Weselcouch**, “P-Partitions and Quasisymmetric Power
    Sums,” *International Mathematics Research Notices* (2021).
    Primary/preprint. Definitions 2.8--2.9, Theorem 2.12, and Sections
    2.3.2--2.3.3 source the labeled P-partition enumerator, its product, and the
    standard order-ideal coproduct retaining every parent-poset element. They
    define no support cut deleting cross-shore heap events. Checked 2026-08-27;
    no paper bytes retained. <https://doi.org/10.1093/imrn/rnz375>
92. **C. Malvenuto and C. Reutenauer**, “Duality between Quasi-Symmetric
    Functions and the Solomon Descent Algebra,” *Journal of Algebra* 177
    (1995). Primary. Theorem 3.2 distinguishes the relevant dual products and
    coproducts; the phrase “Solomon shuffle product” alone does not select the
    algebra, basis, grading, or normalization needed by the proposed residual.
    Checked 2026-08-27; no paper bytes retained.
    <https://doi.org/10.1006/jabr.1995.1336>
93. **R. I. Liu and M. Weselcouch**, “P-Partition Generating Function
    Equivalence of Naturally Labeled Posets,” *Journal of Combinatorial Theory,
    Series A* 170 (2020), 105136. Primary/preprint. The introduction and
    Section 5 give nonisomorphic naturally labeled posets with the same
    P-partition enumerator. This blocks a general inference from enumerator
    equality to heap structure but does not refute such a theorem on a newly
    characterized subclass. Checked 2026-08-27; no paper bytes retained.
    <https://doi.org/10.1016/j.jcta.2019.105136>

## Valuated delta-matroid source used for Batch 029 planning

94. **K. Murota**, “On Exchange Axioms for Valuated Matroids and Valuated
    Delta-Matroids,” *Combinatorica* 16 (1996), 591--596; full 1995 Bonn
    report OR95841. Primary. Section 1.2, axiom `(D1)`, fixes the maximization
    convention used in the bounded `FD029-VALUATED-SPLIT` plan: for
    `u` in `I symmetric_difference I'`, there is a distinct second exchange
    element such that the sum of the two original valuations is at most the
    sum after the paired symmetric exchanges. This sources only the exchange
    convention; it supplies no claim that the project's split-defect statistic
    is a valuated delta-matroid. Author-hosted report and publication metadata
    checked 2026-08-28; no paper bytes retained.
    <https://doi.org/10.1007/BF01271277>

## Nested-hull source audited in theorem-discovery Cycle 003

95. **K. Dehnhardt, H. Harborth, and Z. Lángi**, “A partial proof of the
    Erdős--Szekeres Conjecture for hexagons,” *Journal of Pure and Applied
    Mathematics: Advances and Applications* 2(1) (2009), 69--86. Primary.
    Theorem 1 proves the seventeen-point case when the outer hull is a
    pentagon.  Lemma 1 joins vertices from one edge bucket of an enclosing
    convex polygon to a nested convex core; Lemma 2 sums such capacities over a
    cyclic family of several cores.  These are conditional nested-hull tools,
    not a uniform half-support producer or a proof of the all-`n` formula.
    Author PDF and publication metadata authenticated 2026-08-30; PDF byte
    SHA-256
    `91417be27af9de23a9b4af52347e49d9c17435d31b389a8e20833a187967e736`.
    No paper bytes retained.
    <https://www.math.u-szeged.hu/~zlangi/publications/ErdosSzekeres.pdf>

## Coverage backlog

- Authenticate the 1960/61 lower-bound paper from a stable primary archive.
- Export and deduplicate citation graphs from zbMATH/OpenAlex/MathSciNet for
  the 1935 paper, Morris--Soltan survey, Suk paper, and Baek--Balko paper.
- Classify all 89 Morris--Soltan references as direct, method-relevant, or
  neighboring/out of scope.
- Check final publication metadata for items 27 and 28.
- Audit non-English and pre-digital literature, especially early exact-case
  proofs and Makai's `ES(5)=9` argument.
- Obtain legitimate full text and exact proposition locators for Dulmage--
  Mendelsohn's 1959 structure paper and 1963 SIAM algorithm paper, especially
  chosen-matching invariance and isolated/empty/perfect output conventions.
- Determine whether a useful implementation-level canonical selector for
  Safe's generally nonunique original-matrix `FcircR` certificates is needed;
  the primary obstruction and mapping theorems themselves are now sourced.
