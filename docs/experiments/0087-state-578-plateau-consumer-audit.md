# Experiment 0087: state-578 plateau consumer audit

Date: 2026-08-10

Status: No ticket outcome; tested local consumer expired

## Question

Does the plateau four-cup, its singleton source-cap intersection, and two
foreign disjoint cap blocks force a `(5,7,8)` target at their first common
decomposition split?

## Audit result

A read-only structural audit derived a three-profile first-split
classification: depending on whether the plateau cup is lower, crossing, or
upper, each foreign cap is crossing with the appropriate endpoint shape or is
safe reverse-separated. This is a proof proposal assembled from existing
compiled localization lemmas; the combined statement was not kernel-checked
in this run.

The proposed local consumer is false at the exact-small computational level.
A 15-vertex recursively decomposable signotope was reported with one plateau
cup, one singleton-intersecting source cap, and two foreign disjoint caps, all
allocated at the root, while its maximum cup, cap, and strong-polygon sizes
are `(4,6,7)`. Further reported controls realize all three plateau placement
profiles. These computations were deterministic but were not promoted to a
certificate, independently checked script, or Lean theorem, so they remain
proposal-level evidence.

## Consequence

None of ticket 0010's three outcomes was reached. In particular, the models
omit the full six-column/32-point density package and do not refute state 578.
They do expire any next consumer that uses only the local plateau cup and two
foreign caps. A positive theorem must use genuinely global data absent from
the controls: all six cap columns, the 24-entry deletion ledger, the full
residual family/density, or a collective private-star law.

The upstream `hone` split is still unresolved. The multi-spine branch already
has compiling constructors, but no consumer for its expanding carrier. The
one-spine plateau theorem must therefore remain explicitly conditional.

## Evidence levels

- Existing plateau and localization declarations: prior kernel-checked Lean.
- Combined classification: mathematical proposal, not compiled here.
- Fifteen-vertex models: deterministic computational proposal, neither
  independently certified nor kernel-checked.
- Sol/Fable review: advisory planning evidence only.

## Evidence

- `ErdosSzekeres/StructuralChargingNextState578PlateauForeignCaps.lean`
- `ErdosSzekeres/StructuralChargingNextState578LocalizedColumn.lean`
- `docs/wayfinder/tickets/0010-consume-state-578-plateau-or-localized-escape.md`
- ignored provider report
  `runs/reviews/20260810-next-three-streams/run1/REPORT.md`
