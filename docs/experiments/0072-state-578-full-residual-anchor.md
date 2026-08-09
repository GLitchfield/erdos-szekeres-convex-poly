# Experiment 0072: state-578 full-residual anchor plateau

## Question

Can the tight one-spine branch be closed by combining four owner incidences,
the six disjoint cap blocks, and the residual-cup address matrix?  If not, what
is the smallest exact obstruction which the next theorem must eliminate?

## Outcome

**Outcome 2: the route survives in a stronger form, but the exact singleton
tail is not closed.**  Four sampled residual cups do not supply enough global
coupling.  The compiling replacement indexes *every* residual four-cup, proves
that the resulting residual-cup/six-cap matrix has a global prefix minimum,
and reduces mixed strict directions to one precise obstruction: every cell of
the distinguished four-owner spine row remains at the common minimum address.
This is the full-residual **anchor plateau**.

The next theorem must break that plateau using decomposability and the exact
32-vertex capacity, or produce the global three-vertex boundary exchange.  It
cannot be a collection of independent cup--cap classifications.

## Review and bounded falsification

The bounded Sol/Fable review is stored under the ignored directory
`runs/reviews/20260809-state578-carrier-matrix-coupling/`.  The evidence packet
SHA-256 is
`7d55a8e61ad398c3f9aa5f168d1bd1c050124109263c8b890278f4620b4c1d61`;
the report SHA-256 is
`6dc1165c3baa1cbd86a28d0376e274bc4d7b1ca0faf395fb41f39b07a327f88f`.
All provider verdicts were `partially_supported`.  Provider output is advisory,
not proof.

The review exposed a defect in the old sampled classification: its final
cross-corner disjunct allowed all four indices to equal the minimum, so it did
not retain strict mixed witnesses.  The replacement theorem
`fourBySix_oneSided_or_oppositeExtensions` keeps explicit false and true
extensions and the two forced cross-minimum cells.

A deterministic quotient enumeration checked all 59,049 normalized `4 × 6`
direction profiles.  It found 65 all-left profiles, 65 all-right profiles,
30,100 mixed profiles, and 28,819 profiles with a full minimum column.  A
separate owner-map census checked 81 fixed-point-free maps and 15 set
partitions.  These computations motivated the contracts but are not Lean
results.

## Compiling Lean results

`StructuralChargingNextState578CarrierMatrix.lean` proves:

- every owner-indexed residual cup contains a different spine owner;
- the chosen owner map is either injective or at most three spine owners hit
  all four sampled residual cups;
- each residual-cup/target-private-cup carrier has at most seven vertices and
  therefore a local three-boundary when five-cups are excluded;
- the repaired sampled `4 × 6` address classification retains its strict
  witnesses and localizes all six caps in a child or on a minimum column;
- intersecting cup rows cannot strictly leave a common address in opposite
  directions;
- every residual four-cup can be paired with all six caps, all rows and
  columns are prefix chains, and the full matrix has a global minimum;
- in the one-spine branch, opposite strict directions force the entire
  distinguished spine row to equal the minimum; consequently the complete
  matrix is one-sided or has the spine anchor plateau;
- the full matrix and its minimum reconnect to the exact 32-vertex gate.

The same file isolates the local eight-vertex obstruction.  On exactly eight
vertices, a three-vertex four-cup transversal exists iff some five-subset has
no four-cup.  It also proves the first decomposable case: when a root's lower
child is a singleton, every four-cup lies in the at-most-seven-vertex upper
child, so the existing seven-vertex theorem supplies a boundary or a five-cup.

## Eight-vertex plateau search and autoprove

Two independent bounded enumerators checked all 186,888 recursively
decomposable triple colorings on eight labeled vertices.  Among the 121,577
five-cup-free colorings, every four-cup family has a three-vertex transversal.
This is computational evidence for the remaining local theorem, not a formal
result.

Decomposability is essential.  A contrarian semantic coloring on eight
vertices, with non-cup triples
`027, 036, 045, 126, 135, 147, 234, 567`, has no five-cup and has four-cup
transversal number four.  That coloring was checked computationally but is
not a Lean certificate and was not shown decomposable.

The bounded autoprove workflow was run on the exact hard leaf
`eightVertex_decomposable_denseFourCups_force_cupFive`.  `aesop` made no
progress; state search and hammer premise selection returned no relevant
decomposition or cup lemmas.  The theorem is therefore not promoted.  Only
the compiling hypergraph equivalence and singleton-lower split case are
claimed.

## Next exact target

Prove a decomposition-sensitive anchor-plateau breaker.  The smallest local
version says that an eight-vertex decomposable carrier whose every five-subset
contains a four-cup must contain a five-cup.  A successful theorem would turn
every at-most-eight owner-escape carrier into a three-boundary.  The global
version may instead use all six cap columns and the 24+8 capacity to show that
the spine plateau cannot persist.  Failure of both versions expires this
matrix route as the main state-578 closure mechanism.

## Reproduction

```text
python3 scripts/adversarial_review.py run
python3 runs/state578-carrier-matrix-coupling/enumerate_owner_matrix_profiles.py \
  runs/state578-carrier-matrix-coupling/owner-matrix-profiles.json
python3 runs/state578-carrier-matrix-coupling/check_owner_matrix_profiles.py \
  runs/state578-carrier-matrix-coupling/owner-matrix-profiles.json
python3 runs/state578-carrier-matrix-coupling/search_eight_owner_escape.py \
  runs/state578-carrier-matrix-coupling/eight-owner-escape.json
python3 runs/state578-carrier-matrix-coupling/check_eight_owner_escape.py \
  runs/state578-carrier-matrix-coupling/eight-owner-escape.json
lake build ErdosSzekeres.StructuralChargingNextState578CarrierMatrix
make test
```

## Files

- [Lean carrier and full-residual matrix](../../ErdosSzekeres/StructuralChargingNextState578CarrierMatrix.lean)
- [Previous boundary-exchange wave](0071-state-578-boundary-exchange-wave.md)
- [Wayfinder ticket](../wayfinder/tickets/0002-test-e3-and-select-repair.md)
