# Experiment 0103: state-567 carrier-only rectangles

Date: 2026-08-11

Status: structural reductions and the exact area-profile dichotomy compile;
the tempting local color terminal is realizably refuted

## Question

Can the exact ten-point residual probe family turn the remaining state-567
carrier occupancies into a finite omission-rectangle system strong enough to
force a target?

## Compiling reductions

Lean first strengthens the 30-probe incidence dichotomy to
`exists_sameOccupancyCollision_or_carrierOnlyWitness567`. In the second branch
the strong six has no residual vertices, so it lies in the two original
carriers and has an explicit overlap profile from `1+5` through `5+1`.

For a light witness, `light_replacement_data` proves exact one-for-one or
two-for-two replacement of a nonstrong residual six. Its color corollary
records the corresponding middle-extension or middle-pair-extension failure.
For a light same-occupancy collision,
`lightSameOccupancyCollision567_has_four_repair_network` either finds a heavy
witness or constructs four pairwise-distinct light witnesses with triangular
residual avoidance. It makes no unsupported block-distinctness claim.

These are reductions. None proves the packed internal leaf or
`TwoCapFreeSidesBound567`.

Lean also proves
`exists_carrierOnlyOmissionRectangleSystem567_of_noCollision`: in the absence
of a same-occupancy collision, all carrier-only witness sets form a finite
normalized family whose omission rectangles cover every anchor pair and are
pairwise edge-disjoint for distinct witness sets. The disjointness proof
reuses the original incident bad blocks at a shared omitted anchor; it does
not rely on the computational gate below.

The system's remaining set-theoretic content is now exact. Lean defines the
omission-area counts and proves that every normalized system has one of two
profiles:

- four disjoint `3×3` rectangles; or
- four area-5 rectangles and two area-8 rectangles.

The intermediate arithmetic profile with two area-5, one area-8, and two
area-9 rectangles is excluded by a color-free row/column packing argument.
In the balanced profile Lean also extracts four pairwise-disjoint `3×3`
blocks. These statements are in
`StructuralChargingCarrierOnlyRectangleProfiles567.lean` and use no external
solver result.

## Relaxed rectangle gate

A frozen Fin12 model retains two disjoint six-carriers, all 36 anchor pairs,
carrier-only omission rectangles, exact-one anchor coverage, OneChange, and
the local target exclusions. Three possible area profiles were checked, and a
semantically different unrestricted encoding was generated as a control.

The unrestricted instance has 56,582 variables and 1,073,724 clauses and is
UNSAT. Its LRAT is approximately 624 MB and was internally checked by CaDiCaL,
but it has not been kernel-checked. The relaxed model omits the full 22-point
packing, exact residual, and internal-side hypotheses.

## Exact failure of the grid-only color consumer

A proposed next lemma said that four disjoint three-point blocks whose six
pair-unions are strong sixes must force a cap five, cup six, or strong seven
under the one-change law. Consecutive blocks passed a bounded Fin12 UNSAT gate,
but arbitrary block placement is false.

The independently replayed counterexample uses

```text
F0 = {0,1,6}      F1 = {5,7,8}
S0 = {4,10,11}    S1 = {2,3,9}.
```

It satisfies all 495 one-change quadruples, makes all six pair-unions strong,
and has no cap five, cup six, or strong seven. Moreover it is realized by the
integer planar points

```text
(0,-120), (5,-144), (194,2), (230,-154),
(406,167), (447,-179), (642,77), (667,752),
(858,397), (879,-152), (1071,-329), (1100,-318).
```

Exact rational determinant replay checks all 220 orientation signs, with
minimum absolute determinant 233. Two full subset dynamic programs agree that
the coloring is not recursively decomposable. Thus sweep realizability does
not repair the local lemma, while decomposability or the original
packed-22/ten-residual provenance may still do so.

## Disposition

`GO_FULL_CONTEXT_ONLY`.

The universal omission-rectangle coverage, edge-disjointness, area-profile
dichotomy, and balanced-grid extraction are formalized. The grid-only color
route is expired, even in the realizable subclass. The recommended repair is
to retain `PackedInternalPairFourResidualEscape` together with the balanced
grid: the counterexample has no ten-point residual and therefore does not
inherit this premise. The smallest next formal landing is a mechanical package
combining the grid with the existing two carrier-touching residual escapes.
The actual color contradiction remains open and must use that full context
essentially.
