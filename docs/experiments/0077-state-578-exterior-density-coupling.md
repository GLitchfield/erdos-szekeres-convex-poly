# Experiment 0077: state-578 exterior-fan/density coupling

Date: 2026-08-09

Status: Outcome 2 — six-column deficit and exact density coupling compile;
the selected-row/density-witness synchronization remains open

## Question

Does the full six-cap, 32-vertex, `32/23` residual-density package turn the
nine-source one-sided deletion fan into a target outcome or an explicit
four-cup transversal of cardinality at most nine?

## Frozen route review

The bounded Sol/Fable review used revision
`9fb45d4cc7bcf5b2158cf1e3c91f3957591dd5b6` and the ticket, experiment 0076,
upper-bracket ledger, full carrier matrix, boundary exchange, eight-vertex
consumer, seven-witness saturation, and restricted-middle-pair files frozen by
SHA-256.  The evidence-packet SHA-256 is
`d5370bc6daf8bcab74d90358d169be214edd76239150dd0f6041cc817c00e693`.
The provider passes agreed that a three-boundary for the full residual family
is not an intermediate consequence: exact density supplies a residual cup
escaping every such boundary.  Provider output is advisory, not proof
evidence.

Read-only innovation and adversarial audits independently isolated the same
escape and proposed two checks: retain the exact lower-local/row-plateau
dichotomy, and use all six disjoint cap columns to count row/column deficits.
Their proposals were treated as untrusted until compiled or independently
replayed.

## Independently checked relaxed obstruction

`state578-exterior-density-relaxed-countermodel.json` is a compact 32-vertex
ordered finite-hypergraph certificate.  Its six disjoint four-cap columns
occupy 24 vertices.  The ambient four-edge family has transversal number ten
and every 23-set contains an edge.  It carries all 24 source-indexed deletion
rows, a nine-source one-upper fan spanning all six columns, and genuine
two-level common-minimum addresses.

The residual family nevertheless has transversal number exactly four: the
four protected spine vertices hit it, and four explicit pairwise-disjoint
residual edges prove the matching lower bound.  The independent checker
replays 28,641 ambient edges, 7,631 residual edges, all deletion rows, and the
address/order data.

This is not a `TripleColoring`, decomposable coloring, signotope, sweep
realization, or planar realization.  It refutes only a proof inherited by the
listed incidence/order/address consequences.  In particular it does not
refute an exact color-sensitive state-578 theorem.

## Compiling six-column deficit

`StructuralChargingNextState578ExteriorDensity.lean` proves that distinct
indexed cap blocks are disjoint and defines the cap columns met and missed by
a finite set.  Meeting `r` columns consumes at least `r` distinct vertices in
the 24-vertex cap support.  Hence every four-set misses at least two columns.

A one-upper exterior row has only three vertices in the lower child.  Since
all six cap blocks are lower-local, such a row meets at most three columns and
misses at least three.  Double-counting at least `9 * 3 = 27` deficits over six
columns gives the compiling theorem
`NineOneSidedDeletionFan578.exists_fiveDeficitColumn`: one cap column is
missed by at least five source-indexed fan entries.  This arithmetic uses six
columns essentially and is unavailable in the exact three-column model from
experiment 0076.

## Corrected density consumer

Lean proves
`exists_upperBoundary_and_escapeRow_of_capSupport_subset_lower_at_32`.
The at-most-eight upper child has a local three-boundary.  Exact `32/23`
density supplies a residual cup disjoint from it.  Full-matrix localization
then gives the sharp alternative:

- the escaping cup is wholly local to the 24-point lower child; or
- all six of its cup/cap cells stay on the common-minimum row plateau.

The theorem does not claim that the local boundary hits the full residual
family.

The restricted-density theorem independently supplies two four-cups avoiding
the five-deficit blocker, neither wholly in the upper child, with disjoint
sweep-middle pairs.  The bounded autoprove cycle was run on the exact
composition leaf.  `aesop` exhausted 200 rule applications, while state search
and premise search returned irrelevant library declarations.  A stable
three-line composition proof closed
`exists_fiveDeficitColumn_and_two_disjoint_restrictedCupMiddlePairs`.

## Total deletion-branch reconnect

The compiling theorem
`deletionEscape_or_fiveDeficitDensityCoupling_at_32` reconnects the result to
the exact 32-vertex deletion ledger.  It returns one of three explicit
outcomes:

1. a deletion row is disjoint from its own source cap;
2. a deletion row retreats wholly into the 24-vertex lower child; or
3. a nine-source fan exists, one column has five deficit entries, and density
   supplies two blocker-avoiding cups with disjoint middle pairs.

Thus the previously implicit `hbase` and `hmeet` premises of the fan
constructor are no longer hidden: their failures are first-class branches.

## Exact local synchronization obstruction

The existing 13-vertex recursively decomposable and sweep-realizable coloring
contains a lower four-cap blocker and five distinct exterior source-private
one-upper cups which all avoid that blocker.  Each cup/blocker pair has the
root as its genuine first joint split.  Lean proves that their five ordered
sweep-middle pairs have no two-vertex cover, while the coloring avoids every
five-cup, seven-cap, and strong eight-set.

This new theorem is compiled in
`StructuralChargingNextState578ExteriorDensityCounterexample.lean`.  It
refutes the proposed post-concentration *local* bridge.  The example has only
three cap columns and no 32/23 density, so it leaves open a theorem which
continues to use the other five cap columns or quantifies over the full
residual family after the deficit column is selected.

## Outcome and next obstruction

Ticket 0005 obtains **Outcome 2**.  The project now has a genuinely
six-column invariant and an exact density-coupled total branch theorem, but no
target or nine-vertex transversal.  The unresolved synchronization is precise:
the five selected fan rows and the two arbitrary restricted-density cups are
not known to share witnesses, endpoints, or a covering pair.

Ticket 0006 continues only with a full-family/cross-column invariant which
eliminates the source-disjoint and lower-local escape branches or couples the
five deficit entries to every blocker-avoiding residual cup.  Any candidate
that discards the other five columns after selecting the blocker is already
refuted by the exact 13-vertex Lean model.  No proof of state `(5,7,8)`, E3,
or the general Erdős--Szekeres formula follows from this experiment.

## Formal and reproducible evidence

- `ErdosSzekeres/StructuralChargingNextState578ExteriorDensity.lean`
- `ErdosSzekeres/StructuralChargingNextState578ExteriorDensityCounterexample.lean`
- `data/derived/state578-exterior-density-relaxed-countermodel.json`
- `scripts/check_state578_exterior_density_relaxed_countermodel.py`
- `runs/reviews/20260809-state578-exterior-density/run1/REPORT.md` (ignored,
  advisory provider output)
