# Finite middle-failure classes

Date: 2026-08-05

## Objective

Replace the raw endpoint and shared-middle roles in the mutually obstructed
crossing pair by explicit, indexed color constraints that can participate in
a later gluing or counting argument.

## Compiling Lean results

`StructuralChargingMiddleSplits.lean` now proves that every one of the twelve
directed failures has a five-way anomaly/fan normalization. Depending on the
probe side, the alternatives are:

1. an internal left-endpoint anomaly;
2. a first-boundary or internal left fan;
3. a fresh-middle fan;
4. an internal right-endpoint anomaly; or
5. an internal right fan or final-boundary fan.

The packing theorem lands directly in a state containing proper crossing
splits and weight-one-or-two middle words for both polygons, together with
these normalized failures.

`StructuralChargingMiddleSplitClasses.lean` indexes every internal position
by `Fin 4` and packages the alternatives as the literal 19-element type
`NormalizedCutFailureClass`. An anomaly with an arbitrary polygon endpoint
either propagates to the canonical first or final endpoint, or produces a fan
variation at the same index. Thus the finite anomaly classes use common
polygon endpoints.

The same file begins the compatibility layer. Under `OneChangeOn`:

- an interleaving canonical anomaly forces two bridge triples to equal the
  polygon's reference middle color;
- a first-boundary fan has the order-dual transition of the existing
  final-boundary fan theorem;
- an internal left or right fan variation forces two bridge triples to share
  a specified fan color; and
- a fresh-middle fan contains a one-sided fan, whose two bridge triples again
  share a specified color.

All statements compile without `sorry`, an external oracle, or a new axiom.

## Checked countermodel replay

`scripts/analyze_middle_split_failure_classes.py` replays the independently
validated model from experiment 0019. It checks the canonical bridge
equalities and reports every class and internal index realized by all twelve
directed probes.

The model refutes a capacity-one interpretation of the indexed classes. Two
probes can share the same internal fan class and index, and two probes can
share the same canonical right-anomaly index. It also shows that fresh-middle
and internal fan branches are essential rather than exceptional. The replay
is falsification evidence, not a Lean proof of a universal claim.

## Next theorem

This target is completed in [experiment 0021](0021-middle-bridge-certificates.md).
All 19 classes now supply one common bridge certificate, and the surviving
two-probe agreement is proved in Lean. Exhaustive checking rejects any
stronger bare-certificate conclusion involving a triple through both probes.
