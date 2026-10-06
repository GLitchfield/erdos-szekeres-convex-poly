# Q16: lattice or majority polymorphisms of BDL / PSL / FULL? (claude-lattice-20261003)

[P] proved by hand. [C] computed: own Python/C, exhaustive over all decomposable colourings unless marked "sample"; diagnostic, not Lean.

## 1. Closure: fails in every instance [C]

| object | instances | operations | fail |
|---|---|---|---|
| BDL, n<=7, every k with >=2 bands | 23,284 | integer meet, join, median; min under every total band order; Baker–Pixley 2-decomposability; all 727 non-projection idempotent binary ops (3 bands) | 100% |
| PSL, k=strong+1 and classical k=strong+2, n<=7 | 20,190 | AND, OR, majority, minority | 100% |
| FULL, n<=6 | 1,352 | letterwise AND/OR/majority; word-lex min/max; lattice-path meet/join | 100% |
| positional (height-function) lift, n=7 | 18,838 / 21,796 | PSL / BDL bottom band | 94% / 79% |

What these failures imply:
- By Post's lattice, every PSL solution set has only projections as polymorphisms (complement survives in 1,270 tight instances).
- The Baker–Pixley failure excludes every majority operation.

**Minimal witness [P].** Take a lone β-cap at k=β+1. Band 0 has cup<=1, so it holds at most one point; band 1 has cap<=β-1, so it cannot hold all β points. Hence the solutions are exactly "one point in band 0", the relation 1-in-β.
- PSL gives the same relation (exactly one Bl point). FULL gives the bijections onto the β words.
- 1-in-β has only projections as idempotent polymorphisms. So for every k>=4 the solution language has **no idempotent Taylor polymorphism**. With lists allowed, CSP theory therefore gives neither bounded width nor canonical extremes.

**Anatomy [C]** (`t3.py`, all pairs, n<=6).
- 90% of meet failures are a cup overflow in the bottom band; joins overflow caps in the top band. Every violating chain mixes points of both inputs.
- [P] Why: the bottom band is an independent transversal of the β-caps (it hits every β-cap and has cup<=k−β). A union of two such sets is not independent; an intersection is not a transversal.

## 2. Width (coordinator addition)

**Definition.** Each point gets a list of allowed values. (l,l+1)-consistency is the greatest restriction-closed family of valid partial assignments on <=l+1 points that has the forth property. The width is the maximum, over unsatisfiable list assignments, of the least refuting l. It is computed exactly over the minimal transversals of the solution hypergraph (MMCS, `width.c`, checked against the brute force `width_ref.py`). A denotes the largest constraint arity (A<=k−1).

**Results [C].**
- **PSL:** width <= A−1 in all 344,694 instances with n<=8. It is chain-local: with two colours, a list only pins points.
- **BDL:** maximum width at k=5 is 3, 3, 4, 4, 5 for n=4..8 (n=8 is a sample of 62). The excess over A−1 rises 0, 0, 1, 1, 2, up to the extremal n=2^(k−2).

The maximising list is always "delete one capacity-1 extreme band everywhere". That is a pigeonhole instance, so refuting it is a Theorem-8-type count. BDL therefore has no chain-scale width; only the trivial bound n−1 holds, exponential in k. This matches the absence of WNU polymorphisms.

## 3. Extreme solutions [C]

No lattice extreme exists, so I tested the lexicographic surrogates LEX-L and LEX-R (least band tuple read in x-order, or in reversed order). Data at n=7:
- **(a) Greedy:** LEX-L equals first-fit greedy whenever greedy succeeds [P]. Greedy dead-ends in 364 of 21,796 instances, so LEX-L needs lookahead.
- **(b) Composition:** fails. LEX(X) restricted to a child equals that child's own LEX for only 7,051 of 12,670 lower children and 2,461 of 12,670 upper children.
- **(c) BRL+:** BRL+ itself held in all 6,858 instances. LEX-L is left-sided in only 2,500 of them, and LEX-L or LEX-R is one-sided in 4,440. So the extremes do not give BRL+.

## 4. Restricted tests

- **BRL+ one-sided sub-families:** never closed under meet, join or median (6,858/6,858) [C].
- **Classical frame Bl ⊇ Fp** (Fp = first points of the β-caps):
  - AND is closed in every classical instance (8,232 at n=7), with least element Fp, the Erdős–Szekeres split [P+C]. Proof: R1∪R2 misses Fp, so it has no β-cap, and the conditions on Bl are hereditary.
  - At tight k, AND fails in 3,782 of 9,903 instances. **Every failure is a strong (k−1)-set inside R1∪R2** [C, `t8.py`].
- **BDL frame (bottom band ⊆ Fp):** not closed: 658 of 678 instances fail at n=6.
- **Move connectivity, n=7:**
  - Classical k: disconnected under 1-point moves in 8 of 8,242 instances, and under <=2-point moves in 2.
  - Tight k: disconnected under 1-point moves in 3,898 of 10,596 (BDL) and 3,112 (PSL); under <=2-point moves in 498 (BDL) and 554 (PSL).
  - Minimal rigid witness (n=5, k=5): X = A<<B with A the 3-cap {0,1,2} and B = {3,4}. The partition with A wholly in the low band is at Hamming distance 3 from all 9 others. This is case R in miniature.
  - BRL+ instances with n<=7 are all 1-move connected, but R25 §45 has an isolated partition at n=13.

## 5. Explanation and lift

**Why the choice is hard.** All three objects are exact covers: each class must be independent and must also cover the long chains. The core relation 1-in-β is already present in the classical case and admits no polymorphism. So polymorphisms are not how classical Erdős–Szekeres chooses canonically. It uses a **frame**: forcing Bl ⊇ Fp discharges the covering constraint, which leaves only hereditary constraints, giving an AND-semilattice with bottom element Fp.

The strong condition adds a second covering family, the strong (k−1)-sets, which no frame discharges. At n<=7 this family is the only source of non-closure inside the frame. It is what produces the rigidity (moves of at least 3 points), the lookahead (greedy dead ends) and the pigeonhole width.

**Proposed lift.** Add a second frame coordinate E: a transversal of the strong (k−1)-sets such that Fp∪E has no α-cup and no strong (k−1)-set. For fixed E, the family Bl ⊇ Fp∪E is AND-closed with least element Fp∪E [P]. Composition and BRL+ positioning then reduce to the behaviour of E.
- **Proof idea:** none yet. Everything reduces to choosing E, which is Q14's missing hitting set.
- **Obstacle:** E has no pointwise or sweep rule (Q14) and, by this run, no lattice structure.

## Evidence

- Code: `lat.py`, `t2.py`–`t8.py`, `width.c`, `width_ref.py`, `wsum.py`. Outputs: `o_*.txt`.
- Jobs (prefix 20261003-):
  - 162811-{e2b8f2, c31e00}
  - 163733-{a55943, 469127, 4e733b}
  - 165014-6e90bb, which reruns the cancelled 163907-1fdfdd
  - 170125-39b4ba
- Not run: closure tests at n=8, and the full BDL width at n=8 (only every 40th colouring, k=5).

## Q21: is PSL's chain-scale width robust?

PSL lists are pinnings and ref is monotone, so width is attained at minimal unsatisfiable pinnings (MUPs). `pslw3.c` samples them (random, near-miss, frame, core, pigeonhole, local search) and computes exact refs; it agrees with the pure-Python `verify21.py` on four MUPs.

**1. Robustness: the A−1 bound fails, and width grows with n [C].**
- k=5: n<=8 is every set (|X| <= 2^(k−2)), so the exhaustive bound width <= A−1 stands.
- k=6 (n<=16 is the whole range): 2,100 sets — random, near-extremal, nested case-R of depth 1–3; 418 tight, 1,018 within 2 of T.
- Maximum ref (k=6):

| n | <=11 | 12–13 | 14–15 | 16 |
|---|---|---|---|---|
| max ref | 4 = A−1 | 5 = A | 6 = A+1 | 5 |

- Python confirms the n=14 case: inst21_k6big id 55, α=5, β=4, pins R = {0,4,13}. It survives l<=5 and is refuted at l=6.
- k=7 (n=12–20, 300 sets): ref = A at n = 15 and 18–20.
- Exact width on an n=9 sample is still <= A−1, so the n<=8 signal was a small-size artifact.

**Mechanism.** The pins leave a residual covering problem whose infeasibility is a counting argument.
- *k=7:* with {6} R and {2,3} Bl, every 4-cap Q in {7..16} must be bichromatic (cap 6+Q needs Bl, gon 2,3+Q needs R); this 82-constraint core is non-2-colourable by a double pigeonhole.
- *k=6, n=12:* the forced "needs Bl" pairs form a graph none of whose independent sets hits all residual "needs R" sets.

**2. Structural explanations are refuted [C].**
- **Treewidth:** the primal graph is complete or nearly so, with treewidth about n−1.
- **Acyclicity:** the constraint hypergraph is never α-acyclic (2,399/2,400).
- **Chain-scale locality:** 38% of the 234,026 MUPs are not UP-refutable. Of those, 28% defeat both failed-literal probing and UP+2SAT. Their minimal cores mostly have >= 11 constraints and 6–11+ free points.

**What survives every test: W, "width <= α+β−3".**
- 0 violations, with exact refs up to α+β−2 for n<=16 (for the 26 sets with n>16, only up to level 6).
- Equality holds in 17 sets, so the bound is tight.
- Maximum ref by (α,β) at k=6:

| (α,β) | (3,4) | (3,5) | (4,3) | (4,4) | (4,5) | (5,3) | (5,4) | (5,5) |
|---|---|---|---|---|---|---|---|---|
| max ref | 3 | 4 | 3 | 5 | 5 | 4 | 6 | 5 |
| α+β−3 | 4 | 5 | 4 | 5 | 6 | 5 | 6 | 7 |

**3. Proof route.**
- **[P] The list-free check is trivial, and it holds up to α+β−3.** In the window α+β>=k+1, blocking a point needs α−1 Bl points and β−1 R points of the partial colouring, so at least α+β−2 points. Hence all valid partial colourings on <=α+β−2 points form a nonempty fixpoint. The list-free instance therefore survives every level l<=α+β−3 (>= A−1). No other local fact is needed.
- **So W ⇒ PSL [P].** The coordinator's A−1 version would also have sufficed, but it is false.
- **W is equivalent to a one-step lemma [P]:** if a pinning survives level α+β−3, then pinning any further point one of the two ways also survives. (Constraints have arity <= α+β−2, so a surviving full pinning is a solution.)
- **Proof idea for W: none.** The two child refutations must be merged without an extra pebble, and the residual problems are counting (hitting-set) problems. W contains PSL as the empty pinning, so it helps only if proved uniformly over pinnings.

**4. Frames.**
- [C] All 139 failures of the four Q14 frames are UP-refuted. Usually the cause is a monochromatic gon inside the frame set. Otherwise it is a depth-2 cascade: α−1 frame points complete α-cups that force a gon red.
- [C] There are 0 four-frame and 0 two-frame failures (plain-PSL versions).
- So each frame lemma splits in two:
  - a **local** part: the classes cannot all contain a forced gon — a finite exchange statement, plausibly provable;
  - a **global** part: a UP-consistent frame extends. This is Q18's hitting set E.
- Bounded width would make the global part local only through W. So width does not explain the frame lemmas; it moves them back to the same hitting-set step.

**Verdict.** Chain-scale width (A−1) is refuted at k=6 for n>=12 and at k=7. The refined W is tight, unrefuted on the sample, and implies PSL [P]. It is unproved and untested for k=7 at n=21–32.

**Evidence.**
- Code: `gen21.py`, `pslw.c`, `pslw2.c`, `pslw3.c`, `pslw4.c`, `verify21.py`, `sum21.py`.
- Instances: `inst21_*.txt`. Outputs: `o21_*.txt`, `o21w_*.txt`, `o21_verify_k6i55.txt`.
- Jobs (prefix 20261003-):
  - 172804-{eeeed8, 83ce76}
  - 173353-8923f0 (Python check)
  - 173951-5f929d, 173952-dd898f
  - 173650-7d33ef and 173708-62ff8f were cancelled for a local-search seed bug and rerun.

## Q23: the local part of the frame lemmas

Tags:
- **[P]** hand proof, in `q23/PROOFS.txt`. `q23/replay23.c` checks every step, with 0 violations on all 4.49M root splits of decomposable n = 9 and on SAT corpora.
- **[S]** exact SAT (CaDiCaL, decomposable labels).
- A gon is a strong s-set.

**1. Results [S].** The case s = 5 covers all decomposable sets (|X| ≤ 16).

| statement | decomposable, s = 5 | general |
|---|---|---|
| L4₀: Fp, Lp, Lu, Fu not all contain gons | holds | unrefuted, N ≤ 13 (α = β = 4) |
| L2₀: cored ⇒ F, L not both | holds | false, N = 12 |
| (a): Fp, Lu not both | false, N = 11 | false, N = 10 |
| U4: all four frames conflict at depth ≤ 2 | none, N ≤ 13 | |
| U2: both CORE frames conflict at depth ≤ 2 | none, N ≤ 14 | false, N = 12 |

- **Depth ≤ 2:** the points completing a forbidden chain or gon with the frame contain a gon. This covers both the frame's own gon and the cascade.
- **N = 16:** run restricted, using the §2 reductions, which lose nothing.
- **s = 6:** case (δ) is UNSAT for N ≤ 19, and L4₀ for N ≤ 15. Case (δ) would need cap A = cup B = 5, since a set with cup 3 and cap 6 never has gons in both Fp and Lp (exhaustive).

**2. Proved [P].** Root split X = A << B, with A low; a, p = cup, cap A and a′, p′ = cup, cap B.

- **Lemma D.** A gon inside A forces p ≥ p′+2 (from s+2 ≤ a+p and s ≥ a+p′). A gon inside B forces a′ ≥ a+2. So one A-type gon puts Fp and Lp inside A, and one B-type gon puts Fu and Lu inside B.
- **L4₀ cases.**
  - All four gons mixed: impossible by R′.
  - (β) Only A-type gons, with B nested in A's span.
  - (γ) The flip of (β).
  - (δ) Fp- and Lp-gons in A, Fu- and Lu-gons in B. This needs a, p′ ≥ 3, so s ≥ 6.
  - In (β), if all four gons are in A and α = a+1, then A is a smaller counterexample.
- **L2₀.**
  - No mixed gon lies in F or L.
  - An A-type gon makes A a smaller cored counterexample.
  - Two B-type gons make B ∪ {min A, max A} a smaller one when |A| ≥ 3.
  - |A| = 1 with β = p′+1 would put a in F ∩ L.

**3. Gaps.**
- **L2₀ residual.** Both gons lie in B, and either |A| = 2, or |A| = 1 with β = p′ and a closing (p′−1)-caps.
  - Every single F-gon at n ≤ 9 sits in such a configuration.
  - When β = p′+1, data (tight at n ≤ 9) give strong(F∩B) ≤ p′ once L∩B ≠ ∅. This bound would close that part.
- **L4₀.** Open: (β) with a mixed Fu- or Lu-gon; all gons in A with α = a (the cup-side twin of the L2₀ residual); (δ) for s ≥ 6.
  - (δ) needs a two-class bound such as "Fp, Lp gons ⇒ s ≤ α+2". SAT finds no counterexample to it for N ≤ 13.
- **Cascades.** No proof.

**Decomposability** enters every step through Lemmas S and R. L2₀ fails without it.

**Proof idea.** Induct on the decomposition. Lemma D fixes which child owns each class. Each configuration then either contradicts R′ or coredness, or shrinks.

**Learned.** A gon sits where its class lives. Mixed gons are excluded, and an inherited gon drags its whole class into one child.

**Obstacle.** A one- or two-point sibling turns near-maximal chains of the big child into maximal ones. The classes are then no smaller set's own classes, so the inductive statement needs anchors.

**Evidence.** Code and outputs in `q23/` (`viola3.py`, `viola4.py`, `replay23.c`, `rstar.c`, `o_*`); witnesses `cex23_dec.txt`, `cex_a_sig10.txt`, `cex_b_sig12.txt`, `w23_L3.txt`, `q23/w_U2_general12.txt`. Jobs: 20261003-182530, 183558, 200120, 201301, 202043, 202756, 204523, 205037, 210449.
