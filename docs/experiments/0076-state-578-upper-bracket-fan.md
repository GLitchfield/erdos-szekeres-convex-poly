# Experiment 0076: state-578 upper bracket and exterior fan

Date: 2026-08-09

Status: Outcome 2 — exact exterior fan compiled; local bracket closure refuted

## Question

Does the six-cap deletion matrix force two upper vertices which strictly
bracket seven lower cap vertices? If not, what collective consequence of all
24 cap sources survives the one-upper-endpoint branch?

## Bounded route review

The Sol/Fable review used revision `d4dda65` and the frozen deletion-ledger,
middle-pair, bracket, carrier-matrix, and ticket inputs under
`runs/reviews/20260809-state578-upper-bracket/run1/`. The evidence-packet
SHA-256 is
`a98c80b868d4beb3dde17f042601f334a39ec75b3a35c5b9bbf40ce90152b567`.
All four provider passes rejected the proposed seven-vertex common bracket:
the current hypotheses permit a residual cup with exactly one upper sweep
endpoint. Provider output is advisory and is not proof evidence.

Read-only innovation and contrarian audits independently reached the same
one-upper obstruction. Their proposed examples and repairs were treated as
untrusted until promoted through Lean or bounded replay.

## Exact endpoint split

`StructuralChargingNextState578UpperBracket.lean` defines the actual lower
bracket between two ordered upper endpoints and separates four-cups into
one-upper and two-upper endpoint shapes. Lean proves that every lower vertex
of a two-upper cup lies in that bracket. The existing no-five-cup/no-seven-cap
theorem then bounds every such bracket by six.

`StructuralChargingNextState578UpperBracketLedger.lean` applies this split to
all 24 cap-vertex-deletion rows at a common-minimum node. Each row either has
exactly one upper endpoint or pays its indexed cap source into a genuine lower
bracket. This is simultaneous over all six cap columns, but it does not force
the two-upper alternative.

## Cardinality-minimal local obstruction

`StructuralChargingNextState578UpperBracketCounterexample.lean` gives a
nine-vertex recursively decomposable coloring. Two disjoint lower four-caps
have eight source-indexed residual cups, every row meets its source cap only
at that source, all pairs have the root as their genuine first joint split,
and every row has exactly one upper endpoint. Lean proves that the coloring is
sweep-realizable and has no five-cup, seven-cap, or strong eight-set.

Nine vertices are cardinality-minimal for this local configuration: two
disjoint four-sets in one child require eight vertices and a nonempty opposite
child requires one more. This refutes any two-column or endpoint-incidence-only
proof of the common bracket.

## Compiling `24 → 18 → 9` reduction

At the global common-minimum node, the minimum and maximum upper vertices
strictly bracket at most six of the 24 saturated cap vertices. At least 18 cap
vertices therefore lie outside the upper span, so at least nine lie on one
common exterior side. Every deletion row indexed by one of those exterior
sources must have exactly one upper endpoint.

Lean packages this as `NineOneSidedDeletionFan578` and proves
`exists_nineOneSidedDeletionFan`. It also proves that nine distinct sources
cannot fit inside only two four-cap columns, so the fan necessarily uses at
least three columns. The bounded autoprove workflow exposed the required
cardinality premises; the final proof uses the two cap-cardinality facts,
`Finset.card_le_card`, `Finset.card_union_le`, and `omega`.

## Exact three-column obstruction

A deterministic bounded search found a 13-vertex decomposable coloring with
three disjoint lower four-caps and twelve indexed one-upper deletion rows.
Nine cap sources lie on one side of the unique upper vertex. The explicit
model was promoted in
`StructuralChargingNextState578UpperBracketFanCounterexample.lean`.

Lean proves decomposability, sweep realizability, all source/cap intersection
and root-address claims, and absence of a five-cup, seven-cap, and strong
eight-set. The target-avoidance checks use kernel-reduced lists of exactly the
five-, seven-, and eight-subsets; they use neither `native_decide` nor an
external oracle.

This model does not contain six cap blocks, 32 vertices, or the global
`32/23` residual-cup density. It therefore refutes a fan-only consumer, not
the full exact state-578 implication.

## Outcome and next obstruction

Ticket 0004 obtains **Outcome 2**. A compiling synchronized carrier exists:
the nine-source one-sided deletion fan. The hoped-for seven-vertex bracket is
not forced by the available endpoint data, and an exact three-column model
shows that the fan alone still does not yield a target.

The full state-578 branch remains open. Ticket 0005 requires the next consumer
to use the six-column/32-vertex residual-density package essentially, for
example by constructing a forbidden four-cup transversal of size at most nine
or an equivalent global collision. No proof of the general Erdős--Szekeres
formula follows from this experiment.

## Formal evidence

- `ErdosSzekeres/StructuralChargingNextState578UpperBracket.lean`
- `ErdosSzekeres/StructuralChargingNextState578UpperBracketLedger.lean`
- `ErdosSzekeres/StructuralChargingNextState578UpperBracketCounterexample.lean`
- `ErdosSzekeres/StructuralChargingNextState578UpperBracketFanCounterexample.lean`
