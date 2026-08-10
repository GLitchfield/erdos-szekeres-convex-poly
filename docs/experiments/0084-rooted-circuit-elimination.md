# Experiment 0084: rooted-triangle circuit elimination

Date: 2026-08-10

Status: strong two-anchor route refuted in Lean; branch stopped

## Question

Can planar circuit elimination preserve enough signed support to shorten a
minimal deletion-obstruction chain outside the recursively decomposable
model?

## Bounded audit

Ordinary convex-hull substitution followed by planar Carathéodory preserves
at most one designated support point in the useful local formulation. That
weak statement has no identified recurrence consumer. The first potentially
useful strengthening asks to preserve both untouched anchors of a rooted
triangle when its third support point is itself replaced by a rooted triangle.

## Kernel-checked counterexample

`RootedTriangleCircuitCounterexample.lean` gives seven explicit rational
points in general position. It proves that `p` is rooted in triangle `abc`
and `a` is rooted in triangle `def`, but no point of `{d,e,f}` makes `p` rooted
in the triangle formed with both anchors `b,c`.

The exact rational orientation calculations, all general-position cases, and
all three failed replacements are checked by Lean. The packaged theorem
`two_anchor_strong_elimination_counterexample` has only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`.

## Outcome

STOP. Two-anchor signed circuit elimination is false. One-anchor elimination
remains plausible but is strategically inert without a bounded-fiber or
chain-shortening consumer, so it is not promoted as a competing proof route.
The counterexample remains reusable as a regression test for future Layer-F
proposals.

## Evidence

- `ErdosSzekeres/RootedTriangleCircuitCounterexample.lean`
- `ErdosSzekeres/Convexity.lean`
