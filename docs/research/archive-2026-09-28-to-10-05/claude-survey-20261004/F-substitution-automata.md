# Area F: substitution decomposition, tree automata and logic

Survey for MIXED ROOT / BDL, 2026-10-04. All tests are diagnostic Python (no Lean). Scripts are in this
directory (`F_t*.py`); each runs in under 25 s.

**A framing fact first.** A cup is a strong set, so with no strong k-set we have α, β <= k−1 and
n <= C(2k−4, k−2). For each fixed k the instance set is finite. "Finite-state for each k" and
Courcelle-style decidability are therefore automatic and say nothing. Area F can contribute in only two
ways: (i) explain *why* local rules fail, and (ii) give methods that are uniform in k.

## Test results (new)

| Test | Result |
|---|---|
| T1 `F_t1_splits.py`, `F_t1b_chain.py`: root-split family, all 11,386 colourings, n <= 7 | Lower parts L are **closed under ∪ and ∩** (no failures). They form a chain in 10,352/10,596 cases at n=7; otherwise the shape is a 3-element "diamond". |
| T1: minimum over **all labellings** of the largest number of L/U runs at any node | At n=7, 20 colourings need a node with **7 alternating runs**, including colourings with strong = 4. Interleaving is intrinsic to the colouring, not an artefact of the chosen labels. |
| T4 `F_t4_simples.py`: colourings with no x-interval module (a lower bound on inflation-simple colourings) | 0, 0, 2, 54, 1104 for n = 3..7. Inside the k=5 class: 2, 30, 186 for n = 5..7. |
| T2 `F_t2_types.py`: chain type τ = (F, G, strong), where F(i,j) and G(i,j) are the longest cup and cap on x-positions i..j | τ is a **congruence** for A <<_w B: 3,000 random compositions of distinct colourings with equal τ gave 0 mismatches (as Lemma DS predicts). At n=7 the 10,596 colourings have 414 distinct τ. |
| T3 `F_t3_automaton.py`: reachable τ-states, built bottom-up | k=5: 1,1,2,6,10,34,60,58,0 for n = 1..9. The state set is empty at n=9 (= 2^{k−2}+1), and all 58 states at n=8 are tight. k=6: 1,1,2,6,18,70,262,936,3504 for n <= 9, against 9,154 colourings at n=7 (35× compression). Theorem 8 holds on every state (k=5 all n; k=6 for n <= 9). |
| T2(b): witness states (subset construction for ∃ band partition: the set of pairs (band map, τ of each band)) at k=5 | **Injective**: 2, 8, 54, 374 states equal the number of colourings for n = 3..6, matching Q25. |

So the chain arithmetic forms a small automaton that does not depend on k. All of the complexity sits in
the existential second-order quantifier over the bands.

## 1. Separable permutations and substitution decomposition
Sources: Bose–Buss–Lubiw 1998; Möhring–Radermacher 1984; Albert–Atkinson 2005; Brignall–Huczynska–Vatter 2008.

1. **Key idea.** Every object is uniquely an inflation of a simple object. A class with finitely many
   simples has an algebraic generating function, a finite basis and partial well-order. Pin sequences
   show that long simples contain long simple substructures.
2. **Application.** Decomposable colourings are closed under inflation: substitute contiguous blocks by
   relabelling ℓ_i ↦ ℓ_i m_ij. The ES construction is an iterated inflation. If interleaved nodes reduced
   to boundedly many "simple interleavings", MIXED ROOT would reduce to finitely many cases per k.
3. **Test (T1, T4).** Simples grow about 20× per point, and full alternation cannot be removed by
   relabelling. The lock at lo = 1 (a single point z <<_g B) is not a substitution at all.
   Positive by-product: the root-split family is partitive-like, so a canonical decomposition tree
   (analogous to modular decomposition) apparently exists. The class counts 2, 8, 62, 718, 10596 are not
   in OEIS.
4. **Verdict.** No route to the lock. The canonical tree is bookkeeping only.

## 2. ES-type theorems in classes; extremal induction on substitution
Sources: Alon–Pach–Solymosi 2001 (the Erdős–Hajnal property is closed under substitution); Vatter 2016
(linear monotone subsequences unless the class contains all layered or all colayered permutations,
proved by grid slicing via Tardos, not by substitution); Fox–Pach–Sudakov–Suk 2012; Moshkovitz–Shapira 2014.

1. **Key idea.** Prove the bound for the prime pieces, then show it survives substitution.
2. **Application.** An APS-type "inflation lemma" (BDL for Q and for each Y_i gives BDL for Q[Y])
   disposes of contiguous blocks. But the hard residue is single-point insertion into the core of B's
   caps, which is untouched. Moshkovitz–Shapira prove ES by pigeonhole, injectively labelling points by
   partitions. Here the analogue is an injective map from points to words in {0,1}^{k−2} with weight in
   the window, which is exactly BDL plus the per-band classical bound.
3. **Test.** None run.
4. **Verdict.** APS: no. The Moshkovitz–Shapira labelling: worth passing to the bijective-model area.

## 3. Operads, species, dendriform
Sources: Bergeron–Labelle–Leroux 1998; Loday–Ronco 1998.

1. **Key idea.** Species equations and dendriform splittings of an associative shuffle product (split by
   which factor supplies the first letter).
2. **Application.** The species D = X + D·D, where the labelled product is the shuffle, counts
   (tree, interleaving) pairs, n!·Cat(n−1) of them. Colourings are a quotient of these. **<< is not
   associative**: with one point per part in x-order a<b<c, (A<<B)<<C is a cup but A<<(B<<C) is a cap. The cup rule
   splits by the *middle* point, so no dendriform or tridendriform identity is available.
3. **Test.** Checked by hand (3 points).
4. **Verdict.** No.

## 4. Tree automata, MSO, Courcelle
Sources: Thatcher–Wright 1968; Courcelle 1990; Courcelle–Engelfriet 2012; TATA.

1. **Key idea.** An MSO property gives a finite bottom-up automaton. ∃X_0..X_{k−2} φ is handled by the
   subset construction, and witnesses are extracted in two passes (bottom-up reachable states, then a
   top-down choice).
2. **Application.** If BDL is true, the language is universal, so its **minimal acceptor has one
   state**. Minimisation is useless; what a proof needs is an *inductive invariant*.
3. **Test (T2, T3).** τ is small, exact and k-free. The witness automaton is incompressible.
   "A proof exists in the tower language, but no local rule selects it" is the textbook situation in
   which witness choice needs the full bottom-up pass. The projection to tower signatures is
   near-injective (Q25), so that pass cannot be summarised.
4. **Verdict.** Diagnostic only, but it states the obstacle precisely. One spin-off:
   **Theorem 8 itself is a statement about τ**, since n, cup, cap and strong are all components of τ,
   whereas BDL is not.

## 5. Regular cost functions, counter automata
Sources: Colcombet 2013; Colcombet–Löding 2010.

1. **Key idea.** Quantitative MSO, decided only up to boundedness equivalence ≈.
2. **Application.** T(a,u,k) is exact; cost functions cannot tell T from 2T. The exact max-plus
   automaton is τ itself, which is already explicit.
3. **Test.** None needed.
4. **Verdict.** No.

## 6. Uniform in k: parameterised verification
Sources: invisible invariants (Pnueli–Ruah–Zuck 2001); regular model checking (Bouajjani–Jonsson–Nilsson–Touili
2000) with L*-learned invariants (Chen–Hong–Lin–Rümmer 2017); cutoffs (Emerson–Kahlon 2000);
orbit-finite automata (Bojańczyk–Klin–Lasota 2014).

1. **Key idea.** Compute the reachable states for small parameter values, generalise them to a
   parameterised assertion, and check that it is inductive for all parameters (small-model or cutoff
   theorems, or a learned regular invariant).
2. **Application.** The two-sided tower language is finite for each k. Its signatures depend only on the
   *order* of positions (orbit-finite) and on band indices with affine limits j+1 and k−1−j. Learn an
   invariant on **pairs (attained child signature, parent demand)**; Q25 shows that attained sets alone
   are not self-inductive. Seed it from k=5,6 and check it at k=7.
3. **Test.** Not cheap.
4. **Verdict.** This is the only Area F tool aimed at "for each k ⇒ for all k". The affine band
   arithmetic violates the bounded-data hypotheses of the small-model theorems, so the result would be a
   computer-found invariant to be proved by hand.

## 7. WQO, Kruskal, minimal counterexamples
Sources: Kruskal 1960; Atkinson–Murphy–Ruškuc 2002; Finkel–Schnoebelen 2001.

1. **Key idea.** Upward-closed sets have finitely many minimal elements, so a minimal bad configuration
   exists.
2. **Application.** BDL is not hereditary: a subset has a smaller α and β and hence a different band
   range. Simples are unbounded (T4), so partial well-order of the class is unlikely (not tested).
3. **Test.** None run.
4. **Verdict.** No.

## 8. Generating functions, kernel method
Source: Bousquet-Mélou–Jehanne 2006.

1. **Key idea.** Algebraicity of series with one catalytic variable.
2. **Application.** T satisfies Pascal's rule (rational). Extremal maxima over tree classes are tropical
   rather than generating-function quantities.
3. **Test.** None run.
4. **Verdict.** No.

## Ranked shortlist

1. **Parameterised invariant synthesis on the tower language** (§6). Use invisible invariants or
   L*-style learning on (child signature, demand) pairs from k=5,6, then check them at k=7. This is the
   most direct attack on uniformity in k. Its cost is engineering, and the result needs a hand proof.
2. **Prove Theorem 8 directly on the τ-algebra** (§4). τ is an exact, k-independent max-plus congruence
   with few states. Search by LP for a potential W(s(τ)), with s a coarse statistic, that is
   superadditive under every composition A <<_w B and satisfies W <= T. This would bypass BDL. Risk:
   the old context-bound route was one such s and failed, so the LP should search richer s
   (interval profiles near the extremes). Cheap side result: running T3 in compiled code to n = 16 at
   k=6 is a complete Theorem 8 check for k=6, estimated at 10^7 to 10^8 compositions.
3. **Canonical decomposition plus an inflation lemma** (§1, §2). This disposes of every contiguous-block
   case and isolates the lock as single-point insertion at interleaved nodes. It is low risk but
   narrows only; on its own it is bookkeeping.

## References (verified 2026-10-04)
- Bose, Buss, Lubiw, *Pattern matching for permutations*, Inf. Process. Lett. (1998).
- Möhring, Radermacher, *Substitution decomposition for discrete structures…*, Ann. Discrete Math. 19 (1984).
- Albert, Atkinson, *Simple permutations and pattern restricted permutations*, Discrete Math. 300 (2005) 1–15.
- Brignall, Huczynska, Vatter, *Decomposing simple permutations, with enumerative consequences*, Combinatorica 28 (2008) 385–400.
- Alon, Pach, Solymosi, *Ramsey-type theorems with forbidden subgraphs*, Combinatorica 21 (2001) 155–170.
- Vatter, *An Erdős–Hajnal analogue for permutation classes*, DMTCS 18(2) (2016).
- Fox, Pach, Sudakov, Suk, *Erdős–Szekeres-type theorems for monotone paths and convex bodies*, Proc. LMS (2012).
- Moshkovitz, Shapira, *Ramsey theory, integer partitions and a new proof of the Erdős–Szekeres theorem*, Adv. Math. (2014).
- Baek, Balko, *The Erdős–Szekeres Conjecture Revisited*, SoCG 2025, LIPIcs 332:13.
- Bergeron, Labelle, Leroux, *Combinatorial Species and Tree-like Structures*, CUP (1998).
- Loday, Ronco, *Hopf algebra of the planar binary trees*, Adv. Math. 139 (1998) 293–309.
- Thatcher, Wright, *Generalized finite automata theory…*, Math. Systems Theory 2 (1968) 57–81.
- Courcelle, *The monadic second-order logic of graphs I*, Inf. Comput. 85 (1990) 12–75; Courcelle, Engelfriet, *Graph Structure and MSO Logic*, CUP (2012).
- Comon et al., *Tree Automata Techniques and Applications* (TATA, online book).
- Colcombet, *Regular cost functions, Part I*, LMCS 9(3) (2013); Colcombet, Löding, *Regular cost functions over finite trees*, LICS 2010, 70–79.
- Bouajjani, Jonsson, Nilsson, Touili, *Regular model checking*, CAV 2000, 403–418.
- Chen, Hong, Lin, Rümmer, *Learning to prove safety over parameterised concurrent systems*, FMCAD 2017.
- Pnueli, Ruah, Zuck, *Automatic deductive verification with invisible invariants*, TACAS 2001, LNCS 2031, 82–97.
- Emerson, Kahlon, *Reducing model checking of the many to the few*, CADE 2000, LNAI 1831, 236–254.
- Bojańczyk, Klin, Lasota, *Automata theory in nominal sets*, LMCS 10(3) (2014).
- Kruskal, *Well-quasi-ordering, the tree theorem, and Vazsonyi's conjecture*, Trans. AMS 95 (1960) 210–225.
- Atkinson, Murphy, Ruškuc, *Partially well-ordered closed sets of permutations*, Order 19 (2002) 101–113.
- Finkel, Schnoebelen, *Well-structured transition systems everywhere!*, TCS 256 (2001) 63–92.
- Bousquet-Mélou, Jehanne, *Polynomial equations with one catalytic variable…*, JCTB 96 (2006) 623–672.
