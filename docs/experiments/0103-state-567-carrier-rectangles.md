# Experiment 0103: state-567 carrier-only rectangles

Date: 2026-08-11

Status: structural reductions compile; relaxed terminal is computationally
UNSAT

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

## Relaxed rectangle gate

A frozen Fin12 model retains two disjoint six-carriers, all 36 anchor pairs,
carrier-only omission rectangles, exact-one anchor coverage, OneChange, and
the local target exclusions. Three possible area profiles were checked, and a
semantically different unrestricted encoding was generated as a control.

The unrestricted instance has 56,582 variables and 1,073,724 clauses and is
UNSAT. Its LRAT is approximately 624 MB and was internally checked by CaDiCaL,
but it has not been kernel-checked. The relaxed model omits the full 22-point
packing, exact residual, and internal-side hypotheses.

## Disposition

`GO_INTERFACE_ONLY`.

The universal omission-rectangle coverage and edge-disjointness interface is
now formalized. The computation does not justify importing the external UNSAT
result or claiming the carrier-only branch closed. The next terminal must use
exact coloring and the full packed context, or the route is reduced only to
another finite certificate problem.
