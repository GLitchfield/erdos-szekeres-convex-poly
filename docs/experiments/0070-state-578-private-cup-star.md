# Experiment 0070: state-578 private-cup star and address matrix

## Question

Can the 10--12-owner private-cup ledger from Experiment 0069 be compressed
into a collective structure that couples to the six disjoint cap blocks and
produces the forbidden nine-vertex four-cup transversal?

The tested route had three layers: extract a selected four-cup wholly inside
the owner transversal, use its four owners as a private-cup star, and analyze
the resulting `4 × 6` private-cup/cap first-joint-split matrix.

## Review boundary

The route was frozen at revision
`258000a8051e25a2f584c6240752945532dbd5e8`. The one-round Sol/Fable packet
has SHA-256
`d09e40be09a1f4ce7c958e9d1db0ebef8eb8ee69b0a561f96da391c6e6dd2a5d`.
Both providers retained the mixed `4 × 6` address matrix and the global
at-most-nine transversal as the primary route. They rejected any consequence
based only on repeated addresses, private-tail multiplicity, or independent
pair classifications. Two read-only specialist audits independently reached
the same restriction and supplied small semantic countermodels. Review and
computation are advisory; the positive results below are checked by Lean.

## Compiling structural results

`StructuralChargingNextState578PrivateCupStar.lean` proves the following.

- Three disjoint selected four-cups have twelve vertices. If their union
  contains a four-cup transversal of cardinality at least ten, then one of the
  three selected cups lies wholly in the transversal. This bound is tight at
  the finite-set level: `4+3+3` need not contain two full selected cups.
- The four vertices of that contained cup index four distinct private cups.
  Each private cup meets the owner spine exactly at its owner; deleting the
  owner leaves a three-vertex tail in the reservoir outside the transversal,
  with at least one vertex outside the original twelve selected cup vertices.
- The private star and six-cap saturation package coexist in one exact state.
  Unless the prior fourth-disjoint-cup branch occurs, the 32-vertex gate
  supplies this joint state and an explicit decomposition tree.
- Every one of the 24 private-cup/cap pairs has a first joint split. In each of
  the four rows, all six paths are prefixes of one private-cup path; in each of
  the six columns, all four paths are prefixes of one cap path. Hence every
  row and every column is prefix-comparable. This is genuine collective tree
  structure, but it does not yet control orientations across different rows
  and columns.
- On an arbitrary seven-vertex carrier, either the four-cup family has a
  transversal of at most three vertices or the coloring contains a five-cup.
  This supplies the exact local replacement size required by the intended
  exchange argument.

The same module freezes the remaining consumer as
`PrivateCupBoundaryExchange578`. If `r` protected four-owner blocks occupy
`4r` vertices, the current transversal has size at most `9+r`, and at most
`3r` boundary vertices hit every cup missed by the unprotected part, then
Lean constructs

```text
(transversal \ protected) ∪ boundary
```

as a four-cup transversal of size at most nine. Under the exact `32/23`
density hypotheses this is impossible, because every four-cup transversal
has size at least ten. Thus constructing the boundary exchange is now an
exact, compiling terminal interface rather than an informal aspiration.

## Certified limit of star-only arguments

`StructuralChargingNextState578PrivateCupStarCounterexample.lean` gives an
explicit seven-vertex recursively decomposable coloring with a four-vertex
cup spine and four private spokes which all share the same three-vertex tail.
Lean proves the coloring sweep-realizable and proves that it contains no
five-cup, seven-cap, or strong eight-set. The spine/spoke intersections and
identical erased tails are also kernel-checked.

This formally rules out tail disjointness, tail multiplicity, and pairwise
nonreuse as consequences of the private-star axioms. Small semantic examples
also realize common safe reverse-separated addresses; these are bounded
computational evidence, not Lean theorems. The exact 32-vertex gate has six
caps and global density absent from the seven-vertex counterexample, so the
mixed matrix route is not refuted.

## Outcome and next gate

**Outcome 2: reusable structural advance, not closure.** The private-star
extraction, exact star/six-cap state, full `4 × 6` address matrix, row/column
prefix chains, local three-vertex transversal theorem, and conditional
boundary-exchange contradiction all compile. Star-only and pairwise address
consumers are formally or computationally expired.

The next theorem must construct `PrivateCupBoundaryExchange578` from the
mixed matrix and exact state-578 hypotheses. Concretely, it must select enough
four-owner blocks and tree boundary sets so that each selected block can be
replaced by at most three vertices while every reservoir four-cup remains hit.
Any proposal which analyzes the 24 cells independently, assumes distinct
tails, or concludes only repeated addresses should be rejected: it cannot
discharge the compiled collective `hits` field.

## Reproduction

```console
lake build ErdosSzekeres.StructuralChargingNextState578PrivateCupStar
lake build ErdosSzekeres.StructuralChargingNextState578PrivateCupStarCounterexample
make test
```

## Evidence

- [Lean private-star and mixed-matrix machinery](../../ErdosSzekeres/StructuralChargingNextState578PrivateCupStar.lean)
- [Lean common-tail counterexample](../../ErdosSzekeres/StructuralChargingNextState578PrivateCupStarCounterexample.lean)
- [Previous seven-witness saturation](0069-state-578-seven-witness-saturation.md)
