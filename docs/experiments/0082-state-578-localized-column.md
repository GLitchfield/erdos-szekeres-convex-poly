# Experiment 0082: full state-578 localization and column consumers

Date: 2026-08-10

Status: Outcome 2 -- full trichotomy sharpened; four exact obstructions remain

## Question

Can the full 32-vertex private-star, deletion-ledger, and density package
consume the localized-cap or universal-minimum-column branches left by
Experiment 0079?

## Compiling full-matrix reduction

`StructuralChargingNextState578LocalizedColumn.lean` lifts the
no-opposite-extensions argument from the blocker-filtered family to the full
residual-cup/six-cap matrix.  A false extension localizes a four-cup in the
lower child and a true extension localizes a four-cap in the upper child, so
the existing deep-split gluing theorem produces a forbidden strong eight-set.

Consequently the distinguished-spine plateau disappears.  The exact matrix
has only three alternatives:

1. the 24-vertex cap support lies in the lower child;
2. it lies in the upper child; or
3. one complete cap column remains at the common-minimum address.

## Full density consumers

Both localized branches now carry symmetric, compiling witness packages: a
three-vertex boundary in the complementary at-most-eight child and a residual
cup missed by that boundary.  The escaping cup is either local to the large
child or its complete six-cell row remains on the minimum address.

The universal-column branch also receives an exact deletion-ledger consumer.
Either a residual cup is disjoint from the column cap, or that four-cap is a
genuine four-owner private residual star.  In the latter case the four
deletion witnesses are injectively distinct and each intersects the cap in
exactly its own source singleton.

Thus the complete remaining obstruction is a four-way split: lower localized
escape, upper localized escape, a disjoint cup at a universal column, or a
four-owner minimum-column private star.

## Limitations and outcome

No branch yet yields a forbidden target or a strict parameter predecessor.
The exact 24--26 vertex projected countermodels from Experiment 0079 do not
retain the full density package, so they do not refute these new witness
packages.  Ticket 0008 obtains Outcome 2 and closes; the four-way consumer is
the next bounded state-578 question.  `DecomposableStateUpper 5 7 8` remains
open.

## Evidence

- `ErdosSzekeres/StructuralChargingNextState578LocalizedColumn.lean`
- `ErdosSzekeres/StructuralChargingNextState578ExteriorDensity.lean`
- `ErdosSzekeres/StructuralChargingNextState578DeletionLedger.lean`
- `docs/wayfinder/tickets/0008-consume-state-578-localized-cap-or-minimum-column.md`
- `runs/reviews/20260810-three-thread-preflight/run1/REPORT.md`
  (ignored advisory output)
