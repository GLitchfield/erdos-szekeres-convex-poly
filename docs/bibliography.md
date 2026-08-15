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
    term and related extensions. <https://doi.org/10.4171/JEMS/1000>
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
    proof. <https://arxiv.org/abs/2512.24061>
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

## Coverage backlog

- Authenticate the 1960/61 lower-bound paper from a stable primary archive.
- Export and deduplicate citation graphs from zbMATH/OpenAlex/MathSciNet for
  the 1935 paper, Morris--Soltan survey, Suk paper, and Baek--Balko paper.
- Classify all 89 Morris--Soltan references as direct, method-relevant, or
  neighboring/out of scope.
- Check final publication metadata for items 27 and 28.
- Audit non-English and pre-digital literature, especially early exact-case
  proofs and Makai's `ES(5)=9` argument.
