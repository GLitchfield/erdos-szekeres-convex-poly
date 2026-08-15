# Experiment 0105: finite sweep realizability through six

## Question

For four, five, and six sweep-ordered vertices, does the complete one-change
law already capture every restriction imposed by straight-line planar
realizability?  Separately, is the set of possible rightmost extensions
determined by one coordinate representative of a parent triple coloring?

## Method

The formal layer proves the general necessary implication and handles the
complete four-point converse with all eight exact integer configurations.

The finite layer starts from the independently reconstructed labeled catalogs
of 8, 62, and 908 one-change colorings.  It emits an explicit recursive
deep-below decomposition tree for every decomposable state.  Exact integer
coordinates are searched only for the 190 remaining six-point states.  A
separately implemented checker exhausts the Boolean coloring cube, validates
every tree and determinant, checks exact union coverage, and runs corruption
controls.

For the representative-cell question, two deterministic exact realizations of
each five-point parent are selected.  Every one of the `2^10` signs of a new
rightmost point against the ten old pair lines is decided by exact rational
strict-half-plane elimination.  The checker independently reconstructs the
complete cell sets and validates an explicit rational witness for every
accepted cell.

## Results

- `IsSweepRealizable.oneChangeOn_univ` compiles.
- `oneChangeRealizabilityCompleteAt_four` compiles with all eight coordinate
  witnesses and standard project axioms only.
- All 62 five-point states have checked decomposition trees.
- At six points, 718 states have checked decomposition trees and the other 190
  have checked exact integer-coordinate realizations.  The coverage union is
  exactly all 908 catalog states; 3,800 coordinate determinants are nonzero and
  have the prescribed signs.
- Across two exact realizations of each five-point parent, rightmost extension
  sets differ for 43 of 62 parents.  The checker validates 1,550 total cells.

The deterministic certificate SHA-256 values are:

- four-point coordinates: `5265340b8e8ea28fa7847b85f3c2f8cc07d8afa223f03618bd5770fa9a8899cf`;
- five/six coverage: `3f73e654ffbb6d76ad0243957fe75a7ebb84a4fbceb481f537551e2c1e4d170c`;
- fixed-extension cells: `c25567d03867db78ab6e8eb7af0c4d733a72f2a7d5d836e47facd4f2a72df600`.

The scripts are
[`generate_local_realizability.py`](../../scripts/generate_local_realizability.py),
[`check_local_realizability.py`](../../scripts/check_local_realizability.py),
[`generate_local_realizability_56.py`](../../scripts/generate_local_realizability_56.py),
[`check_local_realizability_56.py`](../../scripts/check_local_realizability_56.py),
[`analyze_fixed_realization_extensions.py`](../../scripts/analyze_fixed_realization_extensions.py),
and
[`check_fixed_realization_extensions.py`](../../scripts/check_fixed_realization_extensions.py).

## Interpretation and limitations

The five/six statement is computational evidence, not a compiling universal
Lean theorem.  A failed coordinate search would not have shown
nonrealizability; here the positive exact witnesses do establish full checked
coverage.

This result does not move a load-bearing proof edge.  It rules out an extra
forbidden-pattern repair supported only on at most six labels, but it neither
proves the nine-point Ringel exclusion needed by `FP-02.F` nor supplies the
global 17-point argument needed by `FP-16`.  The fixed-extension result concerns
particular realization spaces and warns against representative-based
recurrences; it is not a new universal order-type constraint.

Bulk five/six Lean certificate promotion is withheld under the project's
consumer gate.  The next local geometric boundary requires a new ticket: either
seven/eight equality with a named consumer, or the formal nine-point
nonstretchability bridge.
