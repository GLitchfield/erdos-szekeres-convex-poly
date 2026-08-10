# Experiment 0085: state-578 private-star plateau

Date: 2026-08-10

Status: Outcome 2 -- private-star branch sharpened in Lean

## Question

Can all four singleton-owned deletion rows and all six saturated cap columns
sharpen the universal-column private-star obstruction from Experiment 0082?

## Compiling result

`StructuralChargingNextState578PlateauForeignCaps.lean` uses strong-eight
avoidance to make every strict matrix extension one-sided. If all four
source-indexed deletion rows extended strictly, their private source vertices
would put the complete universal-column cap in that child. The source-column
cell nevertheless stays at the common minimum, contradicting its exact
lowest-separating-node condition.

Therefore one deletion row is a full plateau across all six cap columns.
That row is a four-cup, so the six disjoint four-cap blocks also provide two
distinct foreign columns disjoint from it. The theorem
`MinimumColumnPrivateResidualStar578.exists_plateauTwoForeignCaps_of_noStrongEight`
packages the plateau row, its exact singleton source intersection, and both
foreign caps.

## Limitations and outcome

This is ticket Outcome 2, not state-578 closure. The raw private-star branch
is replaced by a color-sensitive plateau/two-foreign-cap obstruction. Relaxed
all-base incidence models show that the next consumer must use decomposition
or triple-color laws rather than address and cardinal data alone. The two
localized escape branches and the disjoint universal-column cup branch also
remain open.

This branch is conditional on the already displayed private-star package.
The upstream 32-point constructors still carry the unique-full-cup-spine
hypothesis `hone`; this theorem neither discharges that hypothesis nor handles
the multi-spine branch. A frozen pre-implementation Sol/Fable review flagged
that qualification and rejected injectivity-only counting. The compiling
plateau proof avoids that invalid count, but does not repair the upstream
qualification.

The theorem compiles and its axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`.

## Evidence

- `ErdosSzekeres/StructuralChargingNextState578PlateauForeignCaps.lean`
- `ErdosSzekeres/StructuralChargingNextState578LocalizedColumn.lean`
- `docs/wayfinder/tickets/0009-consume-state-578-localized-escape-or-private-star.md`
- `runs/reviews/20260810-three-route-deep-block/run1/REPORT.md`
  (ignored advisory output)
