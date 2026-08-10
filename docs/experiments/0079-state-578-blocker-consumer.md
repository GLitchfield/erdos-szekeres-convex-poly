# Experiment 0079: state-578 blocker consumer and load-bearing audit

Date: 2026-08-10

Status: Outcome 2 -- mixed directions compile away; state `(5,7,8)` remains
open and is route-local rather than a universal prerequisite

## Question

Can the exact color and decomposition laws consume the mixed rectangle in the
complete blocker-avoiding cup/six-cap matrix? How much of the route to the
general exact formula would proving the resulting state actually complete?

## Frozen review

The bounded Sol/Fable route review froze revision
`dbb36b58ff2b9d09a042f114e8260bc5da46e301`. Its evidence packet has SHA-256
`ae587e8cc5df8b1b74c3fc6fa53dff68000b8e97241fcef9924bead76ab7e2d8`.
Both reviewers classified state `(5,7,8)` as a genuine but conditional
fixed-`k=8` milestone, not a universally necessary theorem. Their route
recommendations differed, so no new main route is selected from model
agreement. Provider output is advisory rather than mathematical evidence.

## Compiling mixed-direction consumer

`StructuralChargingNextState578BlockerConsumer.lean` proves that a
blocker-family matrix cannot have both a false-strict and a true-strict cell
above one common minimum when the support has no strong eight-set. The first
cell localizes a genuine four-cup in the minimum node's lower child; the
second localizes a genuine four-cap in its upper child. The existing
deep-split cup/cap theorem glues them into a strong eight-set and transports
the witness back into the support.

The resulting classification has exactly three alternatives:

1. all six saturated caps lie in the lower child, of cardinality at least 24;
2. all six saturated caps lie in the upper child, of cardinality at least 24;
3. every blocker-avoiding cup has one cap-column cell at the common-minimum
   address.

This is a color-sensitive theorem and is not inherited by the relaxed
incidence/address certificate.

## Surviving obstructions

A read-only adversarial audit constructed deterministic target-free
decomposable models at proposal/computational-evidence level:

- a 24-vertex six-cap partition in which every matrix cell is at the root and
  blocker middle-pair transversal numbers are `6,6,6,9,9,9`;
- a 25-vertex extension with genuine false-strict rows, two-blocker deletion
  escape, and no two-cover of any complete blocker middle-pair family; and
- a 26-vertex extension containing enough cap/cup witnesses to show that bare
  strict descent does not inherit any useful strict predecessor avoidance.

These models were exhaustively checked in memory but are not Lean artifacts.
They omit parts of the full 32-vertex private-star/density package, so they
refute projected consumers, not the exact state.

The strongest surviving strict-descent statement is a same-state child window:
the localized child is decomposable, inherits target avoidance, contains the
24-vertex cap support, has cardinality between 24 and 31, and has a nonempty
opposite sibling of cardinality at most eight. That is not yet a strict
parameter predecessor.

## Route-level audit

State `(5,7,8)` has threshold 41. On the current structural-charging route it
is needed before the `(5,8,8)` higher-cone consumer, but even its two singleton
gates plus all strict predecessors would prove only this one hereditary state.
The active ticket-0007 work addressed the color-dual `41+1` tail; the original
singleton-lower tail is a separate obligation.

After `(5,7,8)`, seven symmetry-unique active states at fixed `k=8` remain
untouched before the diagonal theorem: `(6,6,8)`, `(5,8,8)`, `(6,7,8)`,
`(6,8,8)`, `(7,7,8)`, `(7,8,8)`, and `(8,8,8)`, with thresholds respectively
`50,42,56,57,62,63,64`. More generally, the current active fixed-`k` state
lattice has `(k-3)(k-2)/2` ordered entries before color duality, so serial
state closure does not itself supply the missing all-`k` invariant.

Even a uniform proof of every decomposable state would establish only Layer
E3. Layer E4 would then reduce any minimal exact counterexample to the
indecomposable class, and Layer F still requires a new theorem controlling
that class. State 578 is therefore several structural layers away from the
general formula.

## Generic route infrastructure

`DecomposableStateDuality.lean` now proves in Lean that the truncated binomial
window and full threshold are symmetric under `(a,u) <-> (u,a)`. It transports
the hereditary state, root-local transition, and exact critical-root
obstruction across this symmetry. This removes duplicated off-diagonal proof
obligations but does not solve any new state by itself.

The best bounded route-level experiment is specification-first rather than a
route change: freeze an endpoint-indexed predecessor-fiber shelling and test
whether target-free decomposable colorings admit injective Boolean labels of
size `2^(k-2)`. This would bypass state 578 if true, but it must first survive
the existing through-eight colorings and every committed rank/downset
collision. It is currently a proposal and risks restating the desired bound;
no theorem is claimed.

## Outcome

Ticket 0007 obtains Outcome 2. The mixed rectangle is eliminated by a
compiling theorem, while the one-sided and minimum-column branches move to
ticket 0008. `DecomposableStateUpper 5 7 8` remains open: it is neither proved
nor refuted.

## Evidence

- `ErdosSzekeres/StructuralChargingNextState578BlockerConsumer.lean`
- `ErdosSzekeres/DecomposableStateDuality.lean`
- `docs/wayfinder/tickets/0007-consume-state-578-blocker-matrix.md`
- `docs/wayfinder/tickets/0008-consume-state-578-localized-cap-or-minimum-column.md`
- `runs/reviews/20260810-e3-route-load-bearing/run1/REPORT.md`
  (ignored advisory output)
