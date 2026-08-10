# Experiment 0090: state-578 global carrier cover

Date: 2026-08-10

Status: Compiling global reduction; no ticket outcome

## Question

Can the six cap columns, 24 deletion rows, full residual density, and the
expanding full-spine carrier be coupled on one state-578 witness to close the
remaining singleton gate?

## Compiling results

`StructuralChargingNextState578Global.lean` now provides four exact pieces.

First, the tight six-column/deletion-density package and the expanding
full-spine carrier can be selected on the same private-star witness after the
fourth-disjoint-cup alternative is excluded. This repairs a potentially
unrelated-existential packaging gap, but does not itself consume either
package.

Second, an expanding carrier never contains the old seven-vertex carrier.
The old carrier has cardinality seven, the replacement has cardinality at
most seven, and the escaping residual cup contributes a vertex outside the
old carrier. Consequently iteration is replacement rather than monotone
inclusion growth.

Third, `FullSpineSevenCarrierCover578` isolates a terminal global consumer. If
one carrier of size at most seven can be assigned to each full spine and those
carriers cover every residual four-cup, local three-boundaries combine to a
`3r` residual boundary. The exact 32-point density theorem then yields
`False`.

Fourth, `exists_escape_from_any_residualSeed_at_32` proves the matching local
limitation. In the one-spine branch, every chosen residual seed produces a
carrier of size at most seven with a local boundary of size at most three,
but density supplies another residual cup disjoint from that boundary and not
contained in the carrier. No single deletion row, deficit row, or selected
fan row is therefore an absorbing cover.

## Falsification audit

An independently replayed relaxed 32-vertex incidence/address model retains
the same-witness packages, all six columns, all 24 deletion rows, fan-density
data, and a two-cycle of replacement carriers. Exact-small decomposable
15-vertex controls also contain two-cycles with local boundaries. These
models do not satisfy the full exact 32-point state and therefore do not
refute state 578; they show why cardinality, address data, or local target
avoidance cannot supply carrier acyclicity.

## Route disposition

The exact outcome remains **578-NO-OUTCOME**. None of ticket 0010's Outcomes
1--3 was reached. The new cover is a valid terminal consumer, but none of the
four current tight branches constructs it. A successful successor must
quantify over the complete residual family and prove a genuinely color-
sensitive global coverage or acyclicity law; selecting a better individual
seed is insufficient.

## Evidence

- `ErdosSzekeres/StructuralChargingNextState578Global.lean`
- `ErdosSzekeres/StructuralChargingNextState578DeficitDensity.lean`
- `docs/wayfinder/tickets/0010-consume-state-578-plateau-or-localized-escape.md`
- ignored relaxed and exact-small checkers under `/tmp/state578-next-block/`
