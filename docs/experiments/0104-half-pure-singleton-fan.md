# Experiment 0104: half-pure singleton-fan boundaries

Date: 2026-08-11

Status: generic consumer and the Fin9 target theorem compile; the first
nonvacuous Fin10 producer gate has complete computational support

## Question

Can the half-pure deep-split boundary be strengthened to a singleton on one
side and used as a noncircular producer for the predecessor half-subset
recurrence?

## Compiling consumer

`HalfPureSingletonFan.lean` defines
`HalfPureSingletonFanProducerAboveAt k`. Above the elementary
`2*k-3` range it asks for a side of at least half the ambient cardinality and
one exterior pivot. The side and singleton form a deep split, and every strong
`(k-1)`-subset of the side is pure in the color that the opposite singleton
extends to a strong `k`-set.

Lean proves
`predecessorHalfSubsetAt_of_halfPureSingletonFanProducerAbove`. Small ambient
sets use the existing elementary predecessor bicoloring; large sets use the
fan and target avoidance to show that the half-sized side is predecessor-free.
The theorem assumes neither the same-`k` exact upper bound nor the desired
half-subset conclusion.

## The `k=5,n=9` boundary is vacuous

The exhaustive fan-negation formula is UNSAT, but removing all fan clauses is
also UNSAT. The reason is now a compiling theorem rather than an experimental
inference:

```lean
containsStrongFiveFinNine_of_oneChange
```

reuses the existing nine-point ES5 certificate to show that every OneChange
coloring on `Fin 9` already contains a strong five-set. The corresponding fan
corollary compiles but is explicitly ex falso, so it supplies no structural
producer evidence.

## The first nonvacuous gate: `k=6,n=10`

The exact negation quantifies over 2,560 eligible side/pivot pairs and 5,120
oriented branches. Only ten pairs cover the other nine vertices; all 2,550
noncovering pairs are included. The primary encoding has 1,086 variables and
17,930 clauses; an independently generated encoding has 834 variables and
16,754 clauses.

Both full formulas are UNSAT, while both formulas with the 5,120 fan-negation
clauses removed are SAT. Thus target-free OneChange colorings exist and the
fan conclusion is genuinely doing work. The primary LRAT replay checks 6,502
additions and 4,730 deletions and derives the empty clause; a corrupted proof
control is rejected. This is complete bounded computational evidence, not a
Lean theorem.

## Disposition

`GO_BOUNDED_PROMOTION`.

The exact next finite theorem is
`halfPureSingletonFanAtSixFinTen_of_oneChange`. Its proof should promote the
compact propositional certificate through an independently audited semantic
bridge. Success would establish a second, nonvacuous boundary for the producer
but would still not prove `HalfPureSingletonFanProducerAboveAt 6`, the
all-parameter predecessor half-subset theorem, or the happy-ending conjecture.
