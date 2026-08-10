# Experiment 0078: state-578 deficit/full-family synchronization

Date: 2026-08-09

Status: Outcome 2 — full-family addresses and strengthened total reduction
compile; the missing universal-intersection anchor is the next obstruction

## Question

Can the five deletion rows avoiding one saturated cap be synchronized with
every four-cup avoiding that blocker strongly enough to close state `(5,7,8)`,
or at least remove the raw source-disjoint and lower-local escape forms?

## Frozen route review

The bounded Sol/Fable review froze revision
`8e3f5cc5cf9c783e893a7f526f1122c178da587a` and the eight ticket-0006 input
files. Its evidence-packet SHA-256 is
`77c0abcee5af03a671555277af4dfa1ce5117d876ca10ef3701dad9ce9fbed50`.
Both providers returned `MODIFY`: the complete blocker-avoiding matrix is a
sound and useful extension, but it has no row analogous to the residual
spine which is known to intersect every other row. Consequently its mixed
opposite-direction rectangle cannot be collapsed to a distinguished-row
plateau. Provider output is advisory rather than proof evidence.

## Compiling full-family synchronization

`StructuralChargingNextState578DeficitDensity.lean` defines the type of every
ambient four-cup avoiding one selected cap block and pairs all of those cups
with all six saturated caps. Lean proves row and column prefix comparability,
a global common minimum, strict-child localization, and the exhaustive
one-sided/minimum-column/mixed-rectangle classification for an arbitrary
finite row type.

Canonical lowest-separating paths prove that a residual-matrix cell and a
blocker-family cell have equal paths whenever they represent the same cup/cap
pair. Thus selected deletion rows and arbitrary density cups now inhabit one
address system. What is not proved is an intersection anchor between those
rows.

## Distinct selected rows

The positive deletion-fan outcome now retains the previously discarded
`all_base` and `all_meet` proofs. The latter puts every indexed source in its
deletion cup. Sources are injective across the six disjoint cap columns, and a
one-upper four-cup contains at most three of them. Therefore five deficit
entries represent at least two genuinely distinct cups. The bounded
autoprove workflow was run on the exact composition leaf: `aesop`, state
search, and premise search did not solve it; the multi-attempt pass found the
stable explicit two-line proof.

Every counted deficit cup is proved to be a member of the complete
blocker-avoiding family. This is the strongest synchronization inherited from
the current incidence data.

## Strengthened total reduction

The two raw deletion escapes are replaced by exact payloads:

- a source-disjoint four-cup also avoids a second, distinct cap column; and
- a lower-local deletion cup has all six cup/cap cells strictly below the
  common minimum in the false direction.

The positive branch retains five deficit entries, at least two distinct
selected cups, and two independent blocker-avoiding density cups with
disjoint sweep-middle pairs. The exact theorem
`twoBlocker_or_strictLower_or_fanDensity_at_32` packages these three outcomes.
`exists_fourthDisjointCup_or_twoFullSpines_or_tightDeficitDensityReduction_at_32`
reconnects the package to the exact 32-vertex color-dual gate, including the
fourth-cup, two-spine, and cap-support-not-lower alternatives.

No theorem in this experiment proves state `(5,7,8)`, E3, or the general
Erdős--Szekeres formula.

## Strengthened relaxed obstruction

The 32-vertex relaxed certificate and independent checker now construct the
complete blocker-avoiding cup/six-cap matrix for every blocker. Their exact
restricted transversal numbers are `9,9,9,9,10,10`; in particular the matrix
interface alone cannot force a boundary of cardinality at most five. The
checker also replays all 24 deletion rows, the nine-source fan, five-entry
deficit concentration, multiplicity at most three, and at least two distinct
deficit cups.

This certificate is an ordered finite-hypergraph/address model, not a
`TripleColoring`, recursively decomposable coloring, signotope, sweep
realization, or planar configuration. It refutes only consumers inherited by
the retained incidence and two-level address data. A genuinely color-sensitive
theorem remains possible.

## Outcome and next obstruction

Ticket 0006 obtains Outcome 2. The old raw escapes are now strict reusable
states, and the selected and arbitrary blocker-avoiding cups share one
compiled address matrix. The terminal route still fails because the full
blocker family lacks a universal-intersection anchor.

Ticket 0007 asks for a color-sensitive consumer of the exact mixed rectangle
or strict lower descent. A viable theorem must either construct a two-vertex
cover for the complete crossing blocker-avoiding middle-pair family (which a
local three-boundary would turn into a forbidden five-boundary), or extract a
strictly smaller named predecessor state from the lower descent. Incidence,
address, selected-row, or endpoint counting alone is expired by the relaxed
certificate.

## Formal and reproducible evidence

- `ErdosSzekeres/StructuralChargingNextState578DeficitDensity.lean`
- `data/derived/state578-exterior-density-relaxed-countermodel.json`
- `scripts/check_state578_exterior_density_relaxed_countermodel.py`
- `runs/reviews/20260809-state578-deficit-density-sync/run1/REPORT.md`
  (ignored, advisory provider output)
