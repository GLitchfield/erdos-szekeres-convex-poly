# Experiment 0112: Erdős–Tuza–Valtr numbers with cap parameter 5 at the signotope tier

Date: 2026-09-04

Status: exact SAT verdicts with independently checked satisfying colorings;
no Lean theorem is claimed.  Opening computation of Workstream C (research
plan step C.2).

## Question

The parameter-5 Erdős–Tuza–Valtr case asserts that
`decomposableThreshold 5 n n + 1` points in general position contain a 5-cap,
an `n`-cup, or a convex `n`-gon.  What is the exact number at the signotope
tier (one-change triple colorings) for the first open value `n = 6`, and does
the encoding reproduce the known cases?

## Predeclared gates

- The classical cup–cap number for (4,4) must come out as 7 (`C(4,2)+1`).
- ES(5) encoded as (5,5,5) must come out as 9.
- Baek's proved case (6,4,6) must come out as 12 (`decomposableThreshold 4 6 6 + 1`).
- Every satisfying coloring is re-checked against the definitions of
  one-change, cap, cup, and strong set by a checker separate from the clause
  generator.

## Inputs and provenance

- Git revision: `c74c737` (working tree).
- Generator and checker: `scripts/generate_etv_signotope_sat.py`
  (SHA-256 `3b5b2c5351d140e61d558ddd3a31c18c90079c4e5e1ca450b60a9372e0c65541`).
- Solver: CaDiCaL 2.1.2 (Lean toolchain).
- Outputs: `runs/experiments/20260903-week1/etv/gate-*.json` (gates) and
  `data/derived/etv-signotope-n6-a5-b6.json` (parameter 5, including the
  15-point extremal coloring as its list of left-turn triples).

## Method

Variables are the increasing triples of `N` ordered vertices (true = left
turn).  Clauses: the rank-three one-change law on every four vertices; for
every `a`-subset, not all triples right turns (no `a`-cap); for every
`b`-subset, not all triples left turns (no `b`-cup); for every `n`-subset,
none of the `2^(n-2)` strong colorings (no convex `n`-gon), the same clause
shape as the ES(5) and ES(6) certificates.  The least unsatisfiable `N` is the
signotope-tier number.

## Results

| Instance | N | Variables | Clauses | Verdict | Model check | CNF |
|---|---|---|---|---|---|---|
| cup–cap (4,4), no polygon bound | 6 | 20 | 150 | SAT | valid | `100a11da40d6122a…` |
| cup–cap (4,4), no polygon bound | 7 | 35 | 350 | UNSAT |  | `161ad244fd794f22…` |
| ES(5) as (5,5,5) | 8 | 56 | 1,120 | SAT | valid | `d94700518f61600b…` |
| ES(5) as (5,5,5) | 9 | 84 | 2,268 | UNSAT |  | `738e41ec9665be51…` |
| Baek (6,4,6) | 11 | 165 | 10,824 | SAT | valid | `8a301a2cc8c6f4eb…` |
| Baek (6,4,6) | 12 | 220 | 20,163 | UNSAT |  | `c8b69888f91a0da6…` |
| parameter 5: (6,5,6) | 15 | 455 | 99,008 | SAT | valid | `dfeabe223173dfde…` |
| parameter 5: (6,5,6) | 16 | 560 | 155,064 | UNSAT |  | `d79d91b2f10ddb63…` |

All three gates pass, and the parameter-5 case at `n = 6` gives exactly the
conjectured value: `N(6,5,6) = 16 = decomposableThreshold 5 6 6 + 1`.  Solver
time was seconds for every instance.

## Addendum: `n = 7` (4 September, afternoon)

With the hierarchical Tseitin encoding of `scripts/generate_etv_tseitin_sat.py`
(strong-quad, strong-5, strong-6 and cup-5, cup-6 atoms with both implication
directions; validated on the same three gates and on `(6,5,6) = 16`),
unanchored:

| N | Variables | Clauses | Verdict | Solver time | Model check |
|---|---|---|---|---|---|
| 26 | 609,570 | 5,962,060 | SAT | 75.7 s | valid |
| 27 | 773,955 | 7,654,140 | UNKNOWN | 10,800 s limit | – |

So `N(7,5,7) ≥ 27` at the signotope tier, consistent with the conjectured
value 27; whether 27 points force a 5-cap, a 7-cup, or a convex heptagon is
undecided at a three-hour CaDiCaL budget.  A sound next step is
cube-and-conquer on the triple variables of the first few vertices, which
parallelizes over the machine's cores without any normalization; anchoring
is not sound here (see the caution above).

## Interpretation

Because every sweep-realizable coloring satisfies the one-change law, the
16-point refutation implies the planar statement at `n = 6`: sixteen points
in general position contain a 5-cap, a 6-cup, or a convex hexagon.  The
15-point satisfying coloring lives at the signotope tier; planar sharpness
needs a realizable 15-point configuration, which the conjectured formula
predicts but this experiment does not produce.  The 155,064-clause instance
is small enough that the ES(6) pipeline (dependency core, checkpoint replay,
semantic clause lemmas) would turn the `n = 6` case into a kernel-checked
theorem in well under an hour of compiler time, should Workstream C want a
formal base case.  `n = 7` needs 27 points and a Tseitin encoding of strong
sets (the direct encoding has 28 million polygon clauses); it is the next
computation.  A caution learned on the way: the anchoring normalization is
not available for cap/cup constraints.  It preserves strong sets and the
one-change law, but re-indexing through a projective chart changes which
chains are caps or cups; an anchored 26-point instance returned UNSAT, which
would contradict the formula, and is simply meaningless.  All numbers in
this note are unanchored.

## Reproduction

```console
python3 scripts/generate_etv_signotope_sat.py --n 6 --a 5 --b 6 --points 15 16 --cadical ~/.elan/toolchains/leanprover--lean4---v4.29.1/bin/cadical --output data/derived/etv-signotope-n6-a5-b6.json
```
