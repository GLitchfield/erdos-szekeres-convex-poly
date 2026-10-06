# D. Global existence methods for the keep-or-lift step (survey, 2026-10-04)

All tests are exact Python or SAT computations. They are diagnostic, not Lean. Scripts `d_*.py` and outputs `o_*.txt`
are in this directory. The hard instances are configH's 25 S1 failures (`../claude-configH-20261004/o_walk2_final.pkl`,
n = 40, k = 8) and their case-R nodes X = A << B, with A a nested tight m-cap.

## 0. Two findings that drive every verdict

- **F1. The choice on A is cheap and is fixed by local rules; the existence content is re-partitioning B.**
  - On the hard nodes, the projected family of feasible keep/lift vectors (B free) depends only on how many A-points
    are kept:
    - "≤ 1 kept" at #5, m = 2, 3 (37 placements);
    - lift-all works at every keep-all failure sampled with m ≤ 4 (111 placements on #0 and #5);
    - "**exactly one kept**" at m = 5 (#0: 51 of 83 sampled placements, where neither keep-all nor lift-all works).
  - The last family is the 1-in-β relation, forced by cap(Lift) ≤ β−1 together with the straddle rule.
    (`d_keeplift.py`, `d_kola.py`)
  - On random small nodes some families fit no Schaefer class, even after renaming coordinates. An example is
    {0000, 0111, 1011, 1101, 1110} (6 of 600 nodes, `d_keeplift_rand.py`).
- **F2. Fractional existence is free and cannot see decomposability.** X14 (no partition) has a fractional partition
  in the conv-hull LP (`../claude-hypergraph-20261003/NOTES.md` §3).

## 1. Scarf's lemma, fractional kernels, hypergraphic stable matchings

- **Idea.** Scarf (1967) gives the following. For a nonnegative matrix whose rows carry preference orders, some vertex
  of {x ≥ 0 : Bx = b} is *dominating*. Aharoni–Holzman (1998) used it to show every clique-acyclic digraph has a
  fractional kernel. Aharoni–Fleiner (2003) used it to show every hypergraphic preference system has a fractional
  stable matching. Integral existence then comes from polytope integrality: Gale–Shapley (bipartite), and
  Boros–Gurvich (1996): perfect graphs are kernel-solvable.
- **Mapping.**
  - Rows: the points, plus one row per band.
  - Columns: pairs (S, j) with S ∈ F_j, where F_j is the family of sets with cup ≤ j+1 and cap ≤ k−1−j.
  - Preferences: points rank bands (for example bottom-first); a band ranks sets (for example by label order).
  - A Scarf vertex is a fractional, stable band partition.
- **Hypothesis needed.** An integral dominating vertex. That needs a perfection or balancedness property of the
  configuration matrix, plus an argument that a stable solution covers every point.
- **Test.** F2 shows the fractional object exists even with no integral one. The residual polytope has an odd cycle
  (PROBLEM §5). Computing a Scarf vertex is PPAD-complete (Kintali et al. 2013). That fits "no local rule", but gives
  no integrality.
- **Verdict.** Scarf supplies exactly the part we do not need. The template "fractional kernel + structure ⇒ integral"
  would need a new perfection property of decomposable sets. Shortlisted only as that template.

## 2. Kernels and Galvin's method

- **Idea.** Galvin (1995) lifts list colouring through two steps:
  - the kernel lemma: a kernel-perfect orientation with |L(v)| > outdeg(v) gives an L-colouring;
  - Gale–Shapley kernels in bipartite line graphs.
  Colour classes are peeled off one at a time as kernels, which are independent and absorbing sets.
- **Mapping.** Lists are band ranges. The absorbing step reads: one band absorbs every extremal chain.
  - TOP-PEEL: some T has cap T ≤ k−α and cup(X∖T) ≤ α−1.
  - BOTTOM-PEEL: some Bot has cup Bot ≤ k−β and cap(X∖Bot) ≤ β−1.
  - Applied recursively, either one gives BDL.
- **Test** (`d_peel.py`, `d_peel_hard.py`).
  - Small random sets: each peel fails in 1 of 200, and at least one holds in all 200.
  - Hard instances: BOTTOM-PEEL holds on all 25 B but **fails on every mixed-root X tested** (4 of 4); TOP-PEEL
    fails everywhere.
  - This matches configH's finding that no bottom band meets every β-cap. The minimal obstructions are chains of
    3 to k points, not edges. Richardson (1953) and Boros–Gurvich need pairwise conflicts.
- **Verdict.** Dead. No colour class at the lock is absorbing.

## 3. Gale–Shapley, Tarski, matching with contracts

- **Idea.** Tarski (1955): a monotone map on a complete lattice has a fixed point. Fleiner (2003) and Hatfield–Milgrom
  (2005) obtain stable outcomes as Tarski fixed points when choice functions are substitutable. Under the law of
  aggregate demand, every stable outcome leaves the same agents unmatched (the rural-hospitals property).
- **Mapping.**
  - Points propose to bands, bottom-first.
  - Band j keeps the greedy maximal F_j-subset in a priority order.
  - Lifting an A-point is a rejection from band p.
- **Test** (`d_substitutable.py`, `d_deferred*.py`, `d_da_insert.py`).
  - Greedy band choice is substitutable for 55 of 68 band families under x-order priority. In 1 family no order out
    of 23 tried is substitutable.
  - **Label-order DA (bottom-first) covers all 25 hard B (n = 40)**, where every one-sided rule fails.
  - It fails at the mixed root: X(16,16) of #5 leaves 10 points unmatched.
  - Inserting A's priority at any of the 41 positions improves this monotonically from 9 to 1 unmatched, never 0.
    Independent insertion of the two A-points never covers (0 of 441).
  - Small random sets: label-order DA fails in 3 of 200.
- **Verdict.** The best signal in this area, but the canonical fixed point stops exactly at the lock. With
  substitutable choices, rural hospitals means no stable outcome under these priorities covers X. So the priority
  must itself be part of the fixed point.

## 4. Sands–Sauer–Woodrow

- **Idea.** Sands–Sauer–Woodrow (1982): a 2-edge-coloured digraph has an independent set absorbing every vertex by
  monochromatic paths.
- **Mapping.** Take the digraph on pairs, with arc (x,y)→(y,z) coloured χ(xyz). Monochromatic paths are then
  cups and caps.
- **Verdict.** No. Absorption is by paths of unbounded length, while bands bound chain length.

## 5. Topological Hall and connectivity of independence complexes

- **Idea.** Topological Hall theorem (Aharoni–Haxell 2000; homological form, Meshulam 2001, 2003; Aharoni–Berger
  2006). Let V = ∪ V_v. If η(K[∪_{v∈I} V_v]) ≥ |I| for every I, then K has a colourful simplex.
- **Mapping.**
  - V_v = {(v, j)}, and K = the join over bands of F_j.
  - A colourful simplex is a band partition.
  - Since η is additive under joins, the condition becomes Σ_j η(F_j[I]) ≥ |I| for all I ⊆ X.
- **Test** (`d_tophall.py`, GF(2) homology).
  - The condition is false at n = 6: labels (001, 01, 0001, 0000, 10, 11), k = 6, bands {2, 3}, η = 3 + 2 < 6, yet
    the set has 31 partitions.
  - It fails in 7 of 40 instances (k = 6, n ≤ 10) and 9 of 20 (k = 5).
  - At n = 11–13 it fails in 10 of 12, with deficits down to −4, growing with n.
- **Verdict.** No in the global form; band complexes are far from matroidal. A root-local version is shortlisted.

## 6. Sperner, KKM, Hex, Tucker, Borsuk–Ulam, Lovász

- **Idea.** Parity or degree arguments give a fully labelled cell: Gale (1979) on Hex; Freund–Todd (1981) on Tucker;
  Matoušek (2003).
- **Mapping.** Label each core gap L or R by whether a left- or right-sided bottom exists (S2).
  - The labels are monotone by definition (configH `o_cr_test*.txt`).
  - KKM turns a covering into an intersection. Our missing step *is* the covering, which fails at #6, gaps 16–17.
- **Test** (`d_parity.py`).
  - The number of partitions is odd in 158 of 300 instances: no parity invariant.
  - The 2-band signed index Σ(−1)^{|X_p|} ranges over −7..10 and is 0 in 18 instances.
- **Lovász (1978) bounds** prove *non*-colourability. Borsuk–Ulam needs an equipartition-type target, which
  chain-length limits lack.
- **Verdict.** No natural invariant; not shortlisted.

## 7. Combinatorial Nullstellensatz, Alon–Tarsi

- **Idea.** Alon (1999); Alon–Tarsi (1992); Ramamurthi–West (2005) for hypergraphs. A nonzero top coefficient of a
  low-degree polynomial gives a nonvanishing point.
- **Mapping.** One variable per point over the band values; the polynomial vanishes on invalid band assignments.
- **Test** (`d_nullstellensatz.py`).
  - A product form needs degree at least the number of minimal forbidden chains. That is 1.3 to 8.8 times the
    allowed degree n(m−1).
  - The canonical certificate is Σ_valid Π_v w_{x_v} on the hyperplane Σw = 0. It vanishes in 22 of 91 two-band sets
    that have partitions. It is nonzero in all 209 sets with ≥ 3 bands, but there it only restates "the partition
    generating polynomial is nonzero" (its coefficients are nonnegative).
- **Verdict.** No.

## 8. Potentials, discharging; asymptotic tools

- **Potentials and discharging.** Rectification potentials plateau (PROBLEM §5). Discharging needs sparse local
  structure, but there are about 250 strong sets per point.
- **Shearer's lemma** (Chung–Graham–Frankl–Shearer 1986), **containers** (Balogh–Morris–Samotij 2015;
  Saxton–Thomason 2015) and **flag algebras** (Razborov 2007) give entropy, counting or density bounds with o(1)
  slack. None produces an exact partition or an exact T.

## 9. Ranked shortlist

1. **Fixed point with contracts on the tree order** (Fleiner; Hatfield–Milgrom).
   - Make A's priority, or a keep/lift contract per A-point, a lattice variable. The B-side outcome is then a monotone
     function of it.
   - Next test: on the hard nodes, check substitutability and the law of aggregate demand for label-order greedy
     choice. Check whether the single unmatched point is always a B-point displaced by a lifted A-point.
2. **Scarf + a decomposability "perfection"** (Aharoni–Holzman → Boros–Gurvich template).
   - Next test: compute Scarf vertices for label-order preferences at mixed roots, and test whether their support
     always contains an integral partition.
3. **Root-local topological Hall.**
   - K = partial keep/lift choices on A that extend to a partition of X minus the unassigned A-points. K is
     hereditary, and a colourful simplex is MIXED ROOT.
   - F1 says the A-families are symmetric cardinality constraints, so the connectivity needed would have to come
     from B's massive non-uniqueness.
   - Next test: GF(2) η of K on configH nodes.

**Proof idea for the target: none from this area.**
- **What was learned:**
  - the choice on A is a cardinality constraint forced by local rules;
  - fractional existence is blind to decomposability;
  - every canonical existence mechanism tested (DA, peeling, topological Hall) works on B and breaks exactly at the
    mixed root.
- **Common obstacle.** Each generic tool needs one of the following, and the band families have none of them:
  - lattice or product structure;
  - pairwise conflicts;
  - high connectivity.

## References (verified via Crossref or publisher pages)

Aharoni–Berger, Trans. AMS 358 (2006) 4895–4917 · Aharoni–Fleiner, JCTB 87 (2003) 72–80 · Aharoni–Haxell, J. Graph
Theory 35 (2000) 83–88 · Aharoni–Holzman, JCTB 73 (1998) 1–6 · Alon, CPC 8 (1999) 7–29 · Alon–Tarsi, Combinatorica
12 (1992) 125–134 · Balogh–Morris–Samotij, JAMS 28 (2015) 669–709 · Boros–Gurvich, Discrete Math. 159 (1996) 35–55
· Chung–Graham–Frankl–Shearer, JCTA 43 (1986) 23–37 · Fleiner, Math. Oper. Res. 28 (2003) 103–126 · Freund–Todd,
JCTA 30 (1981) 321–325 · Gale, Amer. Math. Monthly 86 (1979) 818–827 · Gale–Shapley, Amer. Math. Monthly 69 (1962)
9–15 · Galvin, JCTB 63 (1995) 153–158 · Hatfield–Milgrom, AER 95 (2005) 913–935 · Kintali–Poplawski–Rajaraman–
Sundaram–Teng, SIAM J. Comput. 42 (2013) 2063–2113 · Lovász, JCTA 25 (1978) 319–324 · Matoušek, *Using the
Borsuk–Ulam Theorem*, Springer 2003 · Meshulam, Combinatorica 21 (2001) 89–94; JCTA 102 (2003) 321–330 ·
Ramamurthi–West, Combinatorica 25 (2005) 355–366 · Razborov, J. Symbolic Logic 72 (2007) 1239–1282 · Richardson,
Ann. Math. 58 (1953) 573 · Sands–Sauer–Woodrow, JCTB 33 (1982) 271–275 · Saxton–Thomason, Invent. Math. 201
(2015) 925–992 · Scarf, Econometrica 35 (1967) 50–69 · Tarski, Pacific J. Math. 5 (1955) 285–309.
