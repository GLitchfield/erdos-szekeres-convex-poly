---
title: Consume the state-578 crossing residual row
type: research
mode: AFK
status: closed
claim: codex-state-578-crossing-row-2026-08-09
blocked_by: none
---

## Question

Can the residual four-cup which crosses the selected six-cap support and
evades the unused three-boundary be consumed at the full matrix's common
minimum, using cap localization and the at-most-eight child theorem, to close
the tight one-spine branch of the color-dual `(7,5,8)` singleton-root gate?

## Decision criteria

- Work only from the compiling full residual-family matrix, its common
  minimum, the exact `24+8` six-cap package, and the kernel-checked
  at-most-eight three-boundary theorem.
- First port the sampled cap-localization classification to the full matrix.
  Retain the actual child containments, minimum-address column, and
  distinguished-row plateau rather than replacing them by address counts.
- In a localized branch, prove the complementary child has at most eight
  vertices and transfer decomposability and five-cup avoidance before using
  the local boundary theorem.
- Before investing in a base-address consumer, test the relaxed model in
  which the missed crossing row remains at the common minimum in all six
  columns.  Treat satisfiability as computational evidence only.
- Any surviving global consumer must use all six disjoint cap blocks or the
  exact unused eight vertices essentially.  A statement which decomposes into
  six independent pair classifications does not close the documented gap.
- A completed positive result is a compiling Lean theorem without `sorry`,
  `admit`, or an unverified oracle.  A negative result must give the smallest
  exact obstruction available and precisely state which additional
  hypothesis remains unused.
- Obtain read-only innovation and contrarian audits of the frozen contract.
  Use bounded Sol/Fable review before selecting, changing, or expiring the
  route.

## Candidate outcomes

1. The crossing row and child-capacity bridge construct the exchange boundary
   and close the tight one-spine state-578 branch.
2. Lean proves the child-capacity bridge but reduces the route to an exact
   minimum-address endpoint or incidence obstruction.
3. A bounded countermodel refutes the address-only bridge, expiring it and
   selecting a stronger six-cap endpoint/incidence invariant.

## Resolution

Closed with **Outcome 3**.  The full-family cap localization and exact
complementary-child boundary compile.  A residual row in a localized branch
is wholly inside the large child or stays at the minimum in all six columns.
A kernel-checked relaxed 32-vertex model proves that crossing the global
selected/unused partition does not force the row to meet the small
decomposition child.  Address-only closure is therefore expired.

The reviewed replacement, a 24-row cap-vertex-deletion ledger, now exists in
Lean at the exact 32-vertex gate.  In each cap column it supplies a row
disjoint from that cap or four distinct rows, and base cells retain exact
endpoint shapes.  Two kernel-checked obstructions show why this still does
not close the state: a relaxed 32-vertex ledger may have 24 distinct,
pairwise-intersecting rows all at the base address, and an eight-vertex
decomposable, sweep-realizable, target-free coloring realizes four distinct
deletion rows with one common three-vertex core and the same endpoint shape.

The global density hypothesis does yield new reusable structure.  After
blocking one four-cap, every transversal of the remaining four-cups has at
least six vertices.  Covering the sweep-middle pairs with two vertices would
contradict this bound, so Lean extracts two residual cups with disjoint
middle pairs.  A cardinality-minimal ten-vertex decomposable,
sweep-realizable, target-free Lean model realizes exactly that conclusion,
with both middle pairs in the lower child and two shared upper endpoints.
Thus one-column deletion, address, endpoint-shape, and two-middle-pair
consumers are all insufficient.

The strongest surviving theorem is an upper-bracket invariant: under
five-cup avoidance, every lower set strictly between two upper vertices is
cap-colored; if seven-caps are also absent, that bracket contains at most six
lower vertices.  No current theorem forces such a bracket from the six cap
blocks.  Ticket 0004 therefore makes that genuinely cross-column implication
the next falsification gate.

## Evidence

- `ErdosSzekeres/StructuralChargingNextState578EightVertex.lean` proves the
  at-most-eight three-boundary theorem and the exact crossing-residual-cup
  package.
- `ErdosSzekeres/StructuralChargingNextState578CarrierMatrix.lean` defines the
  full residual matrix, proves its global common minimum, and establishes the
  one-sided-or-distinguished-row-plateau classification.
- `docs/experiments/0073-state-578-eight-vertex-plateau.md` records the latest
  kernel checks, the bounded provider review, and the exact limitation.
- `docs/experiments/0074-state-578-crossing-row-consumer.md` records the
  full-family localization, child boundary, strict-row repair, and relaxed
  negative control.
- `docs/experiments/0075-state-578-deletion-middle-bracket.md` records the
  deletion ledger, exact endpoint and middle-pair counterexamples, surviving
  bracket theorem, bounded review, and route expiry.
