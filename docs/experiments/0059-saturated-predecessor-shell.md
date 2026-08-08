# Experiment 0059: saturated-predecessor shell

## Question

Does the unique saturated published branch expose exactly the strictly smaller
E3 state and local avoidance hypotheses required by the higher-index pivot
cone, without assuming the outer state being proved?

## Result

Yes, conditionally on the intended strong-induction hypothesis over the sum of
the cap and cup parameters.

For an upper saturated branch, `PublishedSaturatedBranch.Valid` states that
the selected cap index plus one is the outer cap parameter. Lean derives both
strict cap-parameter descent and strict decrease of `a + u`, rewrites absence
of the outer cap into the exact successor-cap avoidance used by the higher
cone, and selects a published upper core containing every canonical
hidden-lower entering pivot. The lower branch is the exact color dual.

The combined dispatcher first applies the existing unique-saturated-branch
theorem. It then consumes a single predecessor family

```text
forall a' u', a' + u' < a + u -> DecomposableStateUpper a' u' k
```

and returns the pivot-containing published slice on whichever branch is
valid. The outer state itself is never requested.

## Lean evidence

`ErdosSzekeres/StructuralChargingSaturatedPredecessor.lean` proves:

- strict selected-index descent on both saturated branches;
- strict decrease of the joint measure `a + u`;
- upper and lower pivot-slice constructors from only strict predecessor
  states; and
- one branch-dispatch theorem using the unique saturated-branch arithmetic.

The file compiles without `sorry`, `admit`, unsafe declarations, or custom
axioms. The four arithmetic lemmas use no axioms. The three slice theorems use
only `propext`, `Classical.choice`, and `Quot.sound` through mathlib.

An independent frozen-diff review checked the equality directions, avoidance
rewrites, predecessor uses, deterministic selected indices, compilation, and
axiom profile and accepted the result as a conditional saturated-predecessor
shell.

## Limitation and next gate

This theorem does **not** prove the outer `DecomposableStateUpper a u k`.
It may reselect a core with the same deterministic published index and
cardinality, so it does not preserve the identity of an earlier chosen core.
Most importantly, local pivot injectivity and leaf-owner nonreuse are still
separate facts: no theorem yet shows that selected pivot-containing cores pay
all parent hidden-gap obligations across a decomposition tree without global
reuse.

The next main target is therefore a tree-global pivot-payment compatibility
law. It must connect immutable conserved gap tokens or their leaf owners to
the active entering pivots retained by the selected cores, prove the required
nonreuse/counting statement across ancestor and descendant nodes, and then
feed that count into the outer structural-charging transition.
