# Experiment 0115: the next predecessor-half falsifiers at k = 7

Date: 2026-09-05

Status: exact computations, every witness half re-verified by an independent
algorithm; no counterexample found; no Lean theorem is claimed.  Workstream E,
falsifiers 1 to 4 of `docs/plans/predecessor-half-conjecture.md` as the
5 September plan asked, all folded into the harness falsifier
`harness/falsifiers/predecessor_half_constructions.py` so that `es falsify`
re-runs bounded versions of them.

## Question

Does any heptagon-free set of 25 to 32 points that is not one of the known
extremal constructions, or one of their single-flip neighbours, fail to
contain a hexagon-free half?  Four searches, cheapest first.

## Predeclared gates

- A set counts as a test only if the chain enumerator of experiment 0111
  (geometric sets) or the four-vertex law (abstract colorings) reports no
  convex heptagon / strong 7-set.
- A witness half counts only if the independent cup/cap dynamic programme
  (`largest_convex_subset`) reports its largest convex subset below 6; for
  abstract colorings, the strong-6 atoms read off the SAT model are
  re-verified against the four-vertex law.
- The conjecture dies at `k = 7` on the first UNSAT half search of a
  realizable set; abstract (signotope-tier) witnesses are candidates only,
  pending a realizability check.

## 1. Longer flip walks from the 19 extremal sets

`scripts/predecessor_half_perturbation_search.py --mode flip --keep 80
--nearest 8 --seed 20260905` (experiment 0113 used 40 and 4).

| Bases | Flips tried | Heptagon-free | New order types | Halves found | Halves missing | Time |
|---|---|---|---|---|---|---|
| 19 | 3,816 | 1,680 | 1,520 | 1,520 | 0 | 750 s |

Output `data/derived/predecessor-half-k7-flip-search-long.json`.  With
the 760 types of experiment 0113 this makes 2,280 distinct heptagon-free
neighbours of the constructions, all with verified hexagon-free 16-point
halves.  About 44 % of flips across one of the eight nearest lines keep
heptagon-freeness.

## 2. Structured sets: Horton sets, double chains, deep-below unions

**Horton sets and double chains are not heptagon-free and have no large
heptagon-free subsets.**  The 32-point Horton set contains a convex 14-gon
(its longest caps and cups have 9 points), and for each of five vertical
scales (Horton's own order type and four "Horton-type" compressions) CaDiCaL
proves that no 25 of its points are heptagon-free (158,208 convex heptagons;
UNSAT at target 25 in under a second each; `scripts/predecessor_half_structured_sets.py`,
`data/derived/predecessor-half-k7-horton-pruning.json`).  The 64-point
Horton set has a convex 18-gon; its pruning did not finish inside the 8 GiB
cap and was not pursued.  A double chain with chains of `m` points contains
a convex `m`-gon (computed: 8 and 16 for `2×8` and `2×16`), so its
heptagon-free subsets have at most 12 points; the family cannot reach 25.

**Deep-below unions.**  A "Horton-type" set in the sense of an interleaved
lower part `A` and a far-above upper part `B` has the sweep coloring
determined by the two parts and the interleaving (a mixed triple turns left
exactly when its middle vertex is in `A`), which is `HasDeepBelowSplit`; the
union of two decomposable colorings is decomposable, hence sweep-realizable
(`IsDecomposable.isSweepRealizable`).  So these sets are tested abstractly
(`scripts/predecessor_half_interleaved_sets.py`): parts are the
Erdős–Szekeres sets `P(a,u)`, patterns are stacked, reversed, alternating and
random, unions with strong 7-sets are pruned by SAT to a strong-7-free
subset of at least 25 vertices when one exists, and the half search runs on
the strong-6 hypergraph.  Experiment 0116 proves that the interleaving of a
single split does not change the strong sets, and the run confirms it
(identical strong-set counts and half results for every pattern of a
two-part union); nested three-part unions do depend on the inner
interleaving (strong-7 counts 54,930 to 134,164 across patterns of
`P(6,4) ∪ P(5,4) ∪ P(4,5)`).

| Union | Points | Strong 7-sets | Tested (after pruning) | Strong 6-sets | Half | Largest strong-6-free subset |
|---|---|---|---|---|---|---|
| `P(6,4) ∪ P(4,6)` | 30 | 0 | 30 | 22,136 | yes (15) | 16 |
| `P(5,5) ∪ P(3,6)` | 25 | 0 | 25 | 7,126 | yes (13) | 15 |
| `P(7,4) ∪ P(4,5)` | 31 | 3,090 | 26 | 9,632 | yes (13) | 15 |
| `P(6,4) ∪ P(4,7)` | 36 | 3,090 | 31 | 22,342 | yes (16) | 16 |
| `P(6,4) ∪ P(5,4) ∪ P(4,5)`, 4 patterns | 35 | 54,930–134,164 | 25 | 6,022–7,126 | yes (13) | 15 |
| `P(5,5) ∪ P(4,5)`, `P(5,5) ∪ P(5,4)`, `P(4,7) ∪ P(5,4)`, `P(7,4) ∪ P(3,6)`, `P(5,5) ∪ P(5,5)` | 25–40 | 3,090–571,140 | no strong-7-free subset of 25 | – | – | – |

50 unions built, 25 tested, none without a half (`data/derived/predecessor-half-k7-interleaved-unions.json`,
688 s).  Every tested union is decomposable, so these are realizable tests,
but they are all inside the class where Baek–Balko's theorem applies and the
halves have two to three vertices of slack.

## 3. The signotope-tier instance at k = 7, counterexample-guided

`scripts/predecessor_half_k7_cegar.py`: an anchored one-change coloring on
`n = 25` vertices with no strong 7-set (Tseitin atoms for strong quads,
5-sets and 6-sets in both directions; 245,180 variables, 2.24 M clauses) in
which every 13-subset contains a strong 6-set.  The half constraint has
`C(25,13)` clauses and is learned instead: each satisfying coloring is
searched for up to eight distinct strong-6-free 13-subsets, and each such
subset `S` adds the clause "`S` contains a strong 6-set".  Incremental
CaDiCaL through python-sat.

| n | Anchored | Budget | Iterations | Learned half clauses | Mean solve | Largest strong-6-free subset seen (target 13) | Result |
|---|---|---|---|---|---|---|---|
| 25 | yes | 2,400 s | 331 | 2,648 | 7.2 s | 15 (55 iterations) or 16 (276 iterations); never below 15 | budget exhausted, no counterexample |

Output `data/derived/predecessor-half-k7-signotope-cegar-n25.json` (per
iteration: solve time, number of strong 6-sets, 1,068 to 7,560, and the
largest strong-6-free subset).

The learned clauses do not bite: the solver keeps finding colorings whose
largest strong-6-free subset has 15 or 16 vertices against the target 13,
i.e. three vertices of slack, the same slack the extremal constructions show
at 32 points (16-point hexagon-free halves in 32).  An UNSAT verdict at this
tier would have been the abstract theorem at `n = 25`; neither outcome is in
reach of this loop in an hour, and the honest reading is that the
signotope-tier search is a counterexample generator with no convergence
guarantee, useful only if a counterexample exists.

## 4. The harness falsifier

`harness/falsifiers/predecessor_half_constructions.py` now runs, in order:
the extremal constructions at `k = 6, 7` (experiment 0108), the deep-below
unions above with three random patterns, a flip walk of ten accepted moves
from each of the nineteen `k = 7` sets, and five minutes of the
counterexample-guided search at `n = 25` (the `cadical` file backend when
python-sat is not installed).  Exit 2 on any missing half of a realizable
set; an abstract witness is exit 3 (needs a realizability check).

`es falsify ErdosSzekeres.predecessorHalfSubsetAt_all`: pass, 528 s
(constructions: 5 sets at `k = 6, 7`; unions: 30 tested; flips: 187 new
heptagon-free order types from the 19 bases, all with halves; search: 12
iterations at `n = 25` in 316 s with the file backend, largest strong-6-free
subset 15).  Recorded in `harness/falsify/ErdosSzekeres.predecessorHalfSubsetAt_all.json`.

## Interpretation

Falsifiers 1, 2 and 4 of the conjecture note are done and negative: the
conjecture survives 2,280 flip neighbours, every structured heptagon-free
set the plan named that can reach 25 points (which, after the analysis of
experiment 0116, means deep-below unions; Horton sets and double chains
cannot), and a bounded abstract search.  Falsifier 3 (the abstract instance)
is implemented but does not decide anything at this budget.  The tests so
far all live near the constructions or inside the decomposable class; what
is missing is a source of heptagon-free 25- to 32-point sets that are
decomposable in no direction, which is what most extremal sets are
(experiment 0107).  A flip walk seeded from a non-decomposable extremal set
already explores that world (all nineteen bases include the sixteen Valtr
blow-ups), and longer walks remain the cheapest next step.

## Reproduction

```console
python3 scripts/predecessor_half_perturbation_search.py --input data/derived/baek-balko-constructions-k7.json --k 7 --mode flip --keep 80 --nearest 8 --seed 20260905 --cadical ~/.elan/toolchains/leanprover--lean4---v4.29.1/bin/cadical --output data/derived/predecessor-half-k7-flip-search-long.json --counterexample-dir data/derived/predecessor-half-k7-counterexamples
python3 scripts/predecessor_half_structured_sets.py --k 7 --families horton,double_chain --cadical ~/.elan/toolchains/leanprover--lean4---v4.29.1/bin/cadical --output data/derived/predecessor-half-k7-horton-pruning.json --counterexample-dir data/derived/predecessor-half-k7-counterexamples
python3 scripts/predecessor_half_interleaved_sets.py --random-patterns 2 --backend cadical --cadical ~/.elan/toolchains/leanprover--lean4---v4.29.1/bin/cadical --output data/derived/predecessor-half-k7-interleaved-unions.json --counterexample-dir data/derived/predecessor-half-k7-counterexamples
python3 scripts/predecessor_half_k7_cegar.py --n 25 --anchored --budget-seconds 2400 --output data/derived/predecessor-half-k7-signotope-cegar-n25.json --counterexample-dir data/derived/predecessor-half-k7-counterexamples
tools/es/bin/es falsify ErdosSzekeres.predecessorHalfSubsetAt_all
```

The CEGAR and union scripts use python-sat (`pip install python-sat`) when it
is importable and the CaDiCaL binary otherwise (slower: the growing instance
is re-solved from a file each iteration).
