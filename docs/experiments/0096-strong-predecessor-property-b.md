# Experiment 0096: strong-predecessor property B

Date: 2026-08-10

Status: Exact recurrence interface compiles; bounded `k = 5` gate passes

## Question

Can every realizable coloring with no strong `k`-polygon be partitioned into
two vertex classes that both avoid a strong `(k-1)`-polygon? Such a partition
would give the exact doubling recurrence without first constructing a
decomposition tree.

## Compiling recurrence

`StrongPredecessorBicoloring.lean` defines the exact hypothesis
`StrongPredecessorBicoloringAt k`. Lean proves the base case

```lean
sweepExactUpperAt_three : SweepExactUpperAt 3
```

and the load-bearing consumer

```lean
sweepExactUpperAt_of_predecessorBicoloring
    (hprev : SweepExactUpperAt (k - 1))
    (hbicolor : StrongPredecessorBicoloringAt k) :
    SweepExactUpperAt k
```

for `4 ≤ k`. The proof restricts the swept coloring to each class, transports
any predecessor polygon back to the ambient support, and bounds both classes
by `2^(k-3)`. Their disjoint union therefore has at most
`2 · 2^(k-3) = 2^(k-2)` vertices.

This implication is a completed Lean theorem. It does not prove the
bicoloring hypothesis.

## Bounded first gate

A deterministic CNF producer and an independent non-CNF, eight-valued
quadruple CSP checker both found the following search UNSAT:

- ground sizes `n = 7` and `n = 8`;
- the rank-three signotope law;
- no strong five-set;
- no red/blue partition whose two classes both avoid a strong four-set.

The stronger balanced gate also passes: every strong-five-free rank-three
signotope on eight vertices in the bounded audit has a `4+4` partition with
neither block strong four.

These are computational results without a checkable UNSAT certificate. Since
the abstract signotope search found no witness, no rational-realization step
was needed. The result supports the realizable contract because the abstract
model is a superset, but it does not prove the unbounded statement.

## Route disposition

`GO_AT_K5_BOUNDED_GATE`.

This route is structurally independent of state 578 and of Layer-F mutation
normalization. It explains the exact exponent directly through a binary
recurrence, rather than merely transporting an already proved decomposable
bound.

The next formal target is a generated certificate theorem

```lean
strongFiveFreeSignotopeFinEight_balancedBicoloring
```

After that promotion, the mathematical question is whether the balanced
partition has a structural construction that extends to arbitrary `k`, or
whether the next bounded instance supplies a counterexample.

## Evidence and resources

- `ErdosSzekeres/StrongPredecessorBicoloring.lean`
- `runs/agents/20260810-property-b-audit/audit-report.json`
  (SHA-256
  `e7fa7c95dc95c07f8d40ef788ebf84f9ff1f4043ec53af7f36ca5f86a6329992`)
- longest bounded search: 5.48 seconds
- peak RSS: 20,368 KiB
- output: 76 KiB
- targeted Lean build: 3,326 jobs
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
