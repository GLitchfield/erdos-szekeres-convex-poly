# Experiment 0057: higher-index cone predecessor

## Question

Can the index-three pivot cone be generalized without falling back to the
classical cup--cap bound, which is too large for the selected published core?

The first higher gate is the parent state `(5,8,8)`.  Coning alone makes the
pivot seed avoid a four-cap, but ordinary no-four-cap/no-eight-cup counting
permits 28 pivots while the selected index-four core has only 23 vertices.

## Result

Yes, conditionally on the strictly smaller off-diagonal E3 state required by
the intended well-founded induction.

For every `a`, a nonempty lower child and no parent `(a+1)`-cap imply that the
complete hidden-lower entering-pivot seed contains no `a`-cap.  No
decomposability, one-change, sweep-realizability, cardinality, or recurrence
hypothesis is used in this geometric statement.  The color-dual theorem uses
the maximum upper vertex to exclude a `u`-cup on the hidden-upper pivot seed
from the absence of a parent `(u+1)`-cup.

If the opposite child is decomposable and `DecomposableStateUpper a u k` is
available as a predecessor hypothesis, the seed has cardinality at most
`decomposableThreshold a u k`: a larger seed would contain an `a`-cap, a
`u`-cup, or a strong `k`-set, and all three alternatives contradict parent
avoidance.  When the published child index is `a` (or color-dually `u`), Lean
constructs one actual published slice whose core retains every canonical
pivot simultaneously.

## First higher scalar gate

Lean verifies

```text
choose 8 2 = 28
decomposableThreshold 4 8 8 = 22
decomposableThreshold 4 8 8 + 1 = 23
not (28 <= 23).
```

Thus one-change or ordinary realizable cup--cap counting cannot pay the core.
The inherited predecessor state supplies exactly the missing refinement: 22
pivots fit in a 23-vertex retained core.

## Lean evidence

`ErdosSzekeres/StructuralChargingHigherCone.lean` proves:

- the all-parameter hidden-lower cap-avoidance cone;
- the color-dual hidden-upper cup-avoidance cone;
- sharp source-cardinality bounds from `DecomposableStateUpper a u k`;
- actual selected upper and lower published slices retaining every pivot; and
- the exact `(5,8,8)` arithmetic regression above.

The file compiles without `sorry`, `admit`, unsafe axioms, or an external
oracle.  Its declarations use only `propext`, `Classical.choice`, and
`Quot.sound`.  An independent read-only review accepted the statements and
their selected-index substitutions.

## Limitation and next gate

This result does **not** prove `DecomposableStateUpper a u k`, the selected
index equality, or the all-parameter E3 recurrence.  Those remain explicit
hypotheses.  The next main theorem-design target is to place this bridge inside
a well-founded three-parameter induction and prove that every saturated branch
supplies the required strictly smaller predecessor state and exact selected
index.  Callers must also derive the local no-`(a+1)`-cap or no-`(u+1)`-cup
hypothesis from their outer state.
