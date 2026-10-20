# The predecessor-half conjecture: statement, consumer, falsifiers

Workstream E of `research-plan-2026-09-03.md`.  Written 4 September 2026.

## Statement

**Planar form.**  For every `k ≥ 4`: every set of `n` points in general
position with no `k` points in convex position contains `⌈n/2⌉` points with
no `k−1` points in convex position.

**Form in the project's model** (`StrongPredecessorBicoloring.lean`):

```lean
def PredecessorHalfSubsetAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ∃ support : Finset (Fin n),
      ¬ContainsStrongPolygonSet χ support (k - 1) ∧
      n ≤ 2 * support.card
```

The conjecture is `∀ k ≥ 4, PredecessorHalfSubsetAt k`.  The parameter is
`k`; `n` is free.  It is stated for sweep-realizable colorings, which is the
planar statement through the presentation bridge; nothing is claimed for
abstract one-change colorings, where the analogous statement is a different
conjecture.

## Why it matters: the consumer

`sweepExactUpperAt_of_predecessorHalfSubset` (same file): for `k ≥ 4`,
`SweepExactUpperAt (k−1)` and `PredecessorHalfSubsetAt k` give
`SweepExactUpperAt k`, where `SweepExactUpperAt k` says every realizable
coloring on more than `2^(k−2)` vertices contains a strong `k`-set.  With the
proved base cases, the conjecture for all `k` gives the exact Erdős–Szekeres
upper bound for all `k` by induction, and hence, with the classical lower
construction already in the tree, the conjecture itself.  A doubling
recurrence is the only known shape of argument that produces the exact
`2^(k−2)` without a case analysis growing with `k`, which is why this
statement, and not a weaker structural one, is the target.

## Status by parameter

| k | Status | Where |
|---|---|---|
| 4 | theorem | `predecessorHalfSubsetAt_four` |
| 5 | theorem | `predecessorHalfSubsetAt_five` |
| 6 | theorem, unconditional since 4 September 2026 | `predecessorHalfSubsetAt_six` (`PredecessorHalfSix.lean`): the theorem through fourteen vertices, the ES(6) ceiling, and the anchored Fin15 certificate |
| 7 | open; holds on every tested set | experiments 0108, 0113 |
| 8 | open; holds on every tested set | experiment 0111 |

## Evidence assembled so far

- Every known extremal set has the predicted half: the 5 sixteen-point sets
  at `k = 6`, the 19 thirty-two-point sets at `k = 7`, the 3 sixty-four-point
  sets at `k = 8` (Erdős–Szekeres, Valtr blow-ups, Baek–Balko Theorem 19),
  each half verified by an algorithm independent of the search
  (experiments 0108, 0111).
- Around the `k = 7` sets, 760 distinct heptagon-free order types reached by
  exact single-orientation flips all have hexagon-free 16-point halves
  (experiment 0113).
- At `k = 6` the statement is a theorem for all `n`, so the first size where
  a counterexample can live is `k = 7`, `n ≤ 32` (a heptagon-free set with
  `n > 32` points does not exist by ES(7) ≤ 33, if that holds, and in any
  case the extremal sets are the natural place to look).

## Falsifiers, cheapest first

1. **Flip neighbourhoods at `k = 7`** (done, negative): 2,349 single flips,
   760 new types, no failure.  Extend at negligible cost: longer walks
   (`--keep`), moves across lines that are not the nearest (`--nearest`),
   and walks seeded from every accepted state rather than from the base set.
2. **Structured heptagon-free sets that are not blow-ups**: Horton-type
   sets and double chains of 25 to 32 points, as the research plan asks.
   Build them, verify heptagon-freeness by the chain enumerator, run the
   half search.  Any set the enumerator reports as heptagon-free is a valid
   test regardless of how it was built.
3. **The signotope-tier instance at `k = 7`**: a one-change coloring on
   `n` vertices with no strong 7-set and no strong-6-free `⌈n/2⌉`-subset,
   for `n = 25, …, 32`, encoded as the Fin15 endpoint was (strong-quad,
   strong-five and strong-six atoms; "every `⌈n/2⌉`-set has a strong six").
   A SAT answer must then be checked for realizability, since only
   realizable counterexamples count; an UNSAT answer at all `n ≤ 32` would be
   the abstract-tier theorem at `k = 7`, which is stronger than needed and
   would deserve a kernel certificate through the existing pipeline.
   Anchoring is sound here (the constraints are strong sets and the
   one-change law), unlike for cap and cup constraints.
4. **Random heptagon-free sets far from the constructions**: rejection
   sampling is hopeless at 32 points, but the flip walk started from
   Horton-type or random-then-repaired sets explores other components of
   the flip graph.

## What a result looks like

- A counterexample at `k = 7`: a realizable 32-point (or smaller)
  heptagon-free set with no hexagon-free 16-point subset, its coordinates,
  the UNSAT certificate of the half search, and the realizability check.
  That ends the route cleanly and is a publishable observation on its own.
- Survival on falsifiers 1 to 3 earns the conjecture the one Workstream F
  slot: a candidate uniform mechanism for the half, stated with its
  parameter, tested first against the hostile worlds of Workstream D.

## Non-claims

No claim is made beyond `k ≤ 6`.  The evidence at `k = 7, 8` is a finite
sample of heptagon-free and octagon-free sets, all built from the known
constructions or near them.  The abstract signotope version is a separate
statement and may fail where the planar one holds.
