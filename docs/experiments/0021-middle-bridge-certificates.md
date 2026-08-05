# Common middle-failure bridge certificates

Date: 2026-08-05

## Objective

Replace the 19-way normalized failure disjunction by one common object that
can be compared across probes, then determine exactly what two probes on one
three-vertex polygon frame force.

## Compiling Lean results

`StructuralChargingMiddleSplitBridges.lean` defines a bridge certificate as
four ordered vertices consisting of one probe and three vertices of the
reference polygon. In the induced tetrahedron color sequence, either the
first three or the last three colors agree.

Lean proves:

1. every one of the 19 normalized failure classes supplies such a certificate
   under `OneChangeOn`;
2. all twelve directed failures in a properly crossing mutually obstructed
   pair therefore supply bridge certificates;
3. deletion packing lands directly in a disjoint partner with those twelve
   certificates, without needing cap-five or cup-six avoidance;
4. every fresh-middle fan supplies an interior certificate;
5. an interior certificate is anchored to the color of its three polygon
   vertices; and
6. two probes anchored on the same ordered polygon frame have equal
   outer-pair colors.

All theorems compile without `sorry`, an external oracle, or a new axiom.

## Bounded two-probe audit

`scripts/analyze_two_probe_bridge_compatibility.py` exhausts all `2^10`
colorings of five ordered vertices. It checks all four common probe gaps and
all four head/tail certificate pairs, for 16 scenarios total. Every scenario
has between 14 and 22 one-change colorings. No scenario forces a strong five,
and no forced equality in any scenario touches a triple containing both
probes. Thus a bare shared-frame certificate cannot by itself glue the probes
into a larger strong polygon.

`scripts/analyze_middle_split_failure_classes.py` also replays the independently
validated `3+3` model. Across its twelve directed probes it finds 194 bridge
certificates. Six probes have interior anchored frames, and six probe pairs
share at least one such frame. Every shared-frame outer-pair agreement checks.

These computations are falsification and route-selection evidence, not Lean
proofs. The positive shared-frame agreement is separately proved in Lean.

## Next theorem

The raw two-probe bridge route is exhausted. The next bounded question is
whether the class, split, and weight-one-or-two constraints force three probes
on one side to contain a shared anchored frame. This incidence claim should be
SAT-falsified before formalization. If it fails, the bridge certificate must
retain an additional class-specific endpoint or middle index rather than only
its three-vertex frame.
