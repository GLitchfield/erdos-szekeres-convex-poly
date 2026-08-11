# Experiment 0101: fractional predecessor covers

Date: 2026-08-11

Status: Generic exact-doubling consumer compiles; main-route promotion deferred

## Question

Can the predecessor bicoloring route be weakened from an integral partition
into two target-free classes to a fractional cover of total rational weight at
most two?

## Compiling contract and consumer

`StrongPredecessorBicoloring.lean` defines
`FractionalPredecessorCoverAt k`. For every sweep-realizable coloring avoiding
a strong `k`-polygon, it asks for nonnegative rational weights on vertex
subsets such that:

- every positive-weight subset avoids a strong `(k-1)`-polygon;
- every vertex receives total incident weight at least one; and
- the total weight is at most two.

The definition contains no cardinal conclusion, decomposition, or bicoloring.
Lean proves

```lean
sweepExactUpperAt_of_fractionalPredecessorCover
    (hk : 4 ≤ k)
    (hprev : SweepExactUpperAt (k - 1))
    (hfrac : FractionalPredecessorCoverAt k) :
    SweepExactUpperAt k
```

Every positive-weight support has cardinality at most `2^(k-3)` by restriction
and the predecessor theorem. Finite rational double counting bounds total
vertex incidence by this cardinality times total weight, giving
`n ≤ 2 * 2^(k-3) = 2^(k-2)`.

This is a completed Lean implication. It does not prove
`FractionalPredecessorCoverAt k`.

## Separation and bounded gate

The fractional contract is fractional Property B for the hypergraph whose
edges are predecessor strong polygons. Integral predecessor bicoloring implies
it, but the converse fails for relaxed uniform hypergraphs:

- a checked three-uniform separator first occurs on six vertices; and
- a checked four-uniform separator occurs on eight vertices.

The producer and structurally independent checker verify the rational covers,
reject every two-coloring, and reject five corrupted outputs. These relaxed
hypergraphs are not signotopes or planar configurations.

At the project-relevant `k=5`, `Fin 8` abstract-signotope gate, fractional
cover gives no new distinction: deterministic CNF DPLL and an independent
direct CSP both find that every strong-five-free instance already has an
integral balanced predecessor bicoloring. This is bounded computational
evidence, not a Lean theorem.

## Disposition

`MODIFY`.

The exact recurrence consumer is reusable and now formalized. The fractional
existence route should not be promoted over integral Property B until a frozen
`k=6` or later exact-model search exhibits a fractional/integral separation.
The canonical audit result has SHA-256
`67e35ac22cb03984a48d2b3898e04ffc3df81e53cfbf6fd248f22bc19135d36a`.
