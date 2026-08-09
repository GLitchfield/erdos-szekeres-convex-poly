# Experiment 0075: state-578 deletion ledger and bracket invariant

Date: 2026-08-09

Status: Outcome 3 — one-column deletion closure refuted; bracket invariant retained

## Question

Can cap-vertex deletion turn the crossing residual-cup row into a collective
endpoint or incidence contradiction at the common-minimum split?  If not,
what is the smallest color-sensitive statement which survives exact
falsification?

## Bounded route review

The Sol/Fable review used the committed crossing-row inputs at revision
`f39d92f` under
`runs/reviews/20260809-state-578-crossing-row-route/`.  The evidence packet
SHA-256 is
`023585cd799ed7585c1403b78531df4075f37f27cc5335fc7d15ea7e58388071`;
the report SHA-256 is
`98bcb6a2fb3c2ff00e04a236b5fab8d7487f5662294e2a77da3c33957e19089d`.
Both providers returned `partially_supported`.  They rejected address-only
and small-child-boundary consumers and selected a cap-vertex-deletion ledger
only after adding exact endpoint information.  Provider output is advisory,
not proof evidence.

Read-only innovation and contrarian audits independently tested the proposed
contracts.  Their suggestions were treated as untrusted proposals and only
the declarations listed below were promoted through Lean.

## Compiling deletion ledger

`StructuralChargingNextState578DeletionLedger.lean` defines a 24-row ledger:
one residual four-cup for every vertex of every one of the six disjoint
four-caps.  The existing `32/23` density theorem supplies each row after the
other three vertices in its cap column are deleted.

Lean proves that each column has one of two exact forms:

1. some selected row is disjoint from the complete cap block; or
2. its four vertex-indexed rows are distinct.

At a common-minimum cell which is not disjoint, the first-joint-split endpoint
classifier gives a cap-upper shape or a cup-lower endpoint shape.  This is a
genuine color-sensitive strengthening of the previous address matrix, but it
does not impose cross-column nonreuse.

## Exact counterexamples to one-column closure

`StructuralChargingNextState578DeletionLedgerCounterexample.lean` gives a
relaxed `Fin 32` model with six disjoint cap blocks and 24 distinct deletion
rows.  Every row consists of its indexed cap vertex plus the same
three-vertex core; all addresses are the root.  Thus distinctness, avoidance,
pairwise intersection, and an all-base matrix are simultaneously possible at
the finite-set/address level.

`StructuralChargingNextState578DeletionEndpointCounterexample.lean` upgrades
the obstruction to an exact decomposable triple coloring on eight vertices.
It is sweep-realizable, has one four-cap and four distinct deletion cups, and
all four cups share one three-vertex core.  Their cap intersections are their
designated source vertices, every pair has the same root first joint split,
and every pair realizes the same lower-endpoint shape.  Lean proves absence of
a five-cup, seven-cap, and strong eight-set.  Hence adding decomposability,
realizability, target avoidance, and the local endpoint classifier still does
not make one cap column close.

## Density consequence and its sharp obstruction

`StructuralChargingNextState578RestrictedMiddlePairs.lean` proves a reusable
restricted-transversal inequality.  If a four-vertex blocker is removed from
the residual four-cup family, every transversal of the remaining cups has at
least six vertices.  The union of an upper boundary and a cover of all sweep
middle pairs is such a transversal.  Consequently, in the no-two-cover
branch, two restricted residual cups have disjoint sweep-middle pairs.

This conclusion is set-theoretic and does **not** localize arbitrary density
witnesses to the large child.  The distinction is essential.
`StructuralChargingNextState578RestrictedMiddlePairsCounterexample.lean`
provides the cardinality-minimal ten-vertex exact obstruction.  It is
decomposable and sweep-realizable, contains a lower four-cap and two residual
four-cups disjoint from it, and the cups share precisely two upper endpoints
while their disjoint middle pairs lie in the lower child.  Lean proves that it
has no five-cup, seven-cap, or strong eight-set.  Therefore two disjoint lower
middle pairs do not by themselves force the target.

An ignored deterministic search sampled 200,000 ten-vertex decomposition
trees before this exact model was found.  It is advisory process evidence
only; the explicit Lean counterexample is the completed negative result.

## Surviving bracket theorem

`StructuralChargingNextState578Bracket.lean` proves the exact geometric
repair.  In any deep split, if a lower set lies strictly between two upper
vertices, five-cup avoidance forces every triple in that lower set to be
cap-colored.  If seven-caps are also absent, at most six lower vertices can
share the bracket.

The proof is conceptual.  A hypothetical cup triple in the bracket, together
with the two upper endpoints, forms a five-cup: internal triples use the
hypothesis, while crossing triples are cup-colored by the deep-split law.
The cardinal corollary then extracts seven vertices and contradicts
seven-cap avoidance.

The bounded autoprove workflow was run on the cardinal corollary.  `aesop` made
no progress, `omega` only exposed the cardinal threshold, and state search and
hammer premise selection returned irrelevant declarations.  The explicit
proof using the bracket theorem, `Finset.exists_subset_card_eq`, and cap
monotonicity compiles.  Automation therefore assists only after the geometric
bridge has been supplied.

## Outcome and next obstruction

This is **Outcome 3** for ticket 0003.  Address-only localization,
one-column deletion, common endpoint shapes, and two-middle-pair extraction
are formally insufficient.  The ledger, restricted-transversal bound, exact
counterexamples, and bracket theorem remain reusable compiling results.

The exact state-578 branch is not closed.  Ticket 0004 asks for a genuinely
cross-column theorem using the six cap blocks and global density to force two
upper vertices bracketing at least seven lower vertices.  No current theorem
supplies that synchronization, and no claim of the full formula follows from
this experiment.

## Formal evidence

- `ErdosSzekeres/StructuralChargingNextState578DeletionLedger.lean`
- `ErdosSzekeres/StructuralChargingNextState578DeletionLedgerCounterexample.lean`
- `ErdosSzekeres/StructuralChargingNextState578DeletionEndpointCounterexample.lean`
- `ErdosSzekeres/StructuralChargingNextState578RestrictedMiddlePairs.lean`
- `ErdosSzekeres/StructuralChargingNextState578RestrictedMiddlePairsCounterexample.lean`
- `ErdosSzekeres/StructuralChargingNextState578Bracket.lean`
