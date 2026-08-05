# Packing and realizability route gates

Date: 2026-08-05

## Decision question

After the local middle-bridge route failed, does either global deletion
packing or straight-line realizability supply a theorem-sized replacement?

A bounded blind Sol/Fable review at revision `73a7c6255b232c8806896dc9056cd6fdabeb4aad`
had evidence-packet SHA-256
`8cd2198abf2250f4dcf279984d99f3dde0b6809427dd954e9055b4b0c1f2d999`.
Both reviewers preferred global packing, with geometry as fallback. Fable
correctly warned that a full 22-point SAT gate is vacuous because the parent
hypotheses are already computationally UNSAT. The review is advisory.

## Sharp-model packing census

`scripts/analyze_packed_escape_sharp_models.py` and the independent
`scripts/verify_packed_escape_sharp_census.py` replay the three validated
sharp 21-point models. All three already satisfy the full condition that every
six-deletion leaves a disjoint strong six, but they do not satisfy extreme
packing:

| Cut | Strong sixes | Deletions with a middle but no extreme witness |
| --- | ---: | ---: |
| `6+15` | 602 | 5,106 |
| `10+11` | 1,158 | 2,399 |
| `11+10` | 720 | 5,800 |

Thus the broad claim that global packing extremizes every deletion is false.
Each sampled model contains an internal strong six, so this does not refute a
contract restricted to the no-internal branch.

## Exact no-internal packing gate

`scripts/check_packed_middle_escape.py` gives every six-set an exact strongness
variable, imposes the full deletion quantifier, and uses the middle-disagreement
characterization to block strong sevens. An independent checker directly
replays any SAT result.

The eager `8+8` base instance and its route-negation instance reached 300- and
600-second limits. A lazy fixed-deletion run showed genuine refinement:

| Packing clauses | Result time | Uncovered deletions |
| ---: | ---: | ---: |
| 0 | 0.638 s | 6,292 |
| 256 | 2.979 s | 3,777 |
| 512 | 163.629 s | 1,456 |
| 768 | 599.887 s limit | unknown |

The first nondegenerate near-balanced base state, `7+8`, is UNSAT in 91.907
seconds. Its 138,121-clause CNF has SHA-256
`4413e3502bb818a64d88e7711827b113b47e77be4225ff004163d38038714197`.
This suggests the stronger statement that full packing forces an internal
strong six, but it does not prove that statement at arbitrary size.

CaDiCaL emitted a text LRAT trace. A streaming backwards dependency analysis
found 1,084 of the 5,005 packing clauses in the first proof. Re-solving only
the 80,439 referenced original clauses and tracing the new proof reduced the
packing dependency to 704 deletions, still spread across every split as
`4,32,75,198,286,103,6`. The reduced LRAT SHA-256 is
`c444de2956ba5900fae4ad51768fab64ed8f752aa6dc863e0644b22a73c2fdbf`.
This is a proof-planning dependency core, not an independently checked or
Lean-imported certificate.

The proposed modest multi-deletion route therefore fails its stop condition:
the surviving contradiction is still a broad finite packing argument rather
than a theorem-sized stable deletion pattern. The full-packing-forces-internal
statement remains a possible large finite certificate route, not the selected
conceptual route.

## Realizability fallback

The review's suggested four-index consistency law is already exactly the
`TurnSequenceAllowed`/`OneChangeOn` law imposed by the countermodel, so it
cannot separate geometry from the abstract model.

`scripts/search_middle_bridge_realization.py` instead fixes increasing integer
abscissae and solves the resulting linear orientation inequalities for the
ordinates. It found rational coordinates for the decisive no-extreme model on
trial 129. `scripts/verify_middle_bridge_realization.py` independently checks
all 220 determinants with exact rational arithmetic; the minimum signed
determinant is `3545127 / 125000000 > 0`. The input model SHA-256 is
`c0fa45ce413d17fa0c5023e8dd13192e7056fa6c5723aa48023187c8f7b3dc21`.

The coordinates and the exact 89-left-triple coloring are promoted in
`StructuralChargingMiddleSplitRealization.lean`. The compiling theorem
`middleSplitRealizationColor_isSweepRealizable` proves that coloring is induced
by a rational swept configuration in general position. Its axiom audit is only
`propext`, `Classical.choice`, and `Quot.sound`.

The remaining SAT-side avoidance and no-extreme properties are independently
checked computational evidence, not Lean theorems. Nevertheless the compiling
realizability theorem closes the only abstraction gap in that countermodel:
straight-line geometry cannot be invoked merely to reject its triple coloring.

## Disposition

Neither reviewed replacement produced a small positive lemma. Local bridge
refinement, modest multi-deletion extremization, and realizability as a local
repair are retired. Under the review's predeclared fallback rule, the next
strategic task returns to the E3 invariant and must first freeze a new uniform
state with a bounded transition falsification gate; no previous failed scalar,
rank, downset, or turn-language quotient should be reproposed.
