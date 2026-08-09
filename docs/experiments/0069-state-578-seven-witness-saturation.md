# Experiment 0069: state-578 seven-witness saturation

## Question

Can the full seven-witness package left by Experiment 0068, rather than its
12-vertex local restriction, force a strict reduction at the exact
32-vertex color-dual `(7,5,8)` gate?

The tested consumers were six-cap saturation, a shared-middle cup/cap role,
the protected missed cup in the `2+2+0` branch, and the global `32/23`
four-cup density.

## Review boundary

The route question was frozen at revision
`d4f59d39c16871ab9366c3fef089dbbcb81557a8`. Both read-only specialist
audits verified the revision and all eight input hashes. Their common
recommendation was to retain six-cap saturation and the density-derived
minimum-transversal route, while rejecting unsupported multiplicity,
common-address, weak-ordering, and shared-middle assumptions. The one-round
Sol/Fable evidence packet has SHA-256
`1273470fc844f18e9fbbf6ca14d183be0fdad768d3ae89b94357a6d8871a128c`.
Both providers selected six-cap saturation as primary and shared-role descent
as reserve; after critique they agreed that the protected `2+2+0` consequence
uses only one further cap, not two. Provider review is advisory; every
positive mathematical result below is separately checked by Lean.

## Compiling structural results

`StructuralChargingNextState578SevenWitness.lean` proves the following.

- The regenerated cap and three external caps occupy 16 vertices. Two uses of
  the strict `(4,5,8)` predecessor on residual supports of sizes 16 and 12
  produce six pairwise-disjoint four-caps. Their support has cardinality 24,
  leaving exactly eight of the 32 reservoir vertices.
- At one containing deep split, a vertex cannot be a sweep-middle vertex of
  both a local four-cup and four-cap unless the cup is wholly upper or the cap
  is wholly lower. The resulting four-way role profile compiles, as does the
  honest lower-child demand bound: absent a wholly lower cap, the six caps
  contribute at most twelve lower incidences.
- Deleting any one of the 24 cap-support vertices leaves a decomposable
  23-set and therefore a four-cup. The resulting deletion ledger supplies
  avoidance, but no multiplicity statement.
- In the `2+2+0` branch, the missed selected cup is disjoint from the four
  existing caps. Protecting those 20 vertices leaves a 12-set, so one further
  predecessor cap gives a mutually disjoint one-cup/five-cap packing on 24
  vertices, again with an eight-vertex remainder.
- The exact gate now returns either that protected package or an explicit
  all-hit `2+1+1` seven-witness state.
- Every transversal of all reservoir four-cups has at least ten vertices.
  Applying this to the original 12 cup vertices gives a sharper dichotomy:
  either a fourth four-cup is disjoint from the three selected cups, or a
  minimum subtransversal has 10--12 owners with injectively chosen private
  four-cups. Every private cup meets the transversal only at its owner and has
  a vertex outside the original cup support.

The last item is the surviving strict reduction. It replaces 24 unrelated
deletion choices by at least ten distinct global cup probes.

## Certified and checked limits

The existing 12-vertex Lean counterexample now additionally certifies a
shared vertex which is a sweep-middle vertex of both the `2+1+1` cap and the
third cup. The cup is wholly in the root upper child, so the new shared-middle
theorem is true but nonclosing. Thus shared-middle conflict alone does not
resolve the all-hit branch.

The independent checker
`scripts/verify_state578_private_cup_incidence_model.py` validates the compact
certificate
`data/derived/state578-private-cup-incidence-countermodel.json`. Its relaxed
32-vertex incidence system simultaneously has six disjoint caps, a `24+8`
split, `32/23` cup density, transversal number exactly ten, ten distinct
private cups with exterior vertices, the `2+1+1` selected-cup profile, and a
raw deletion ledger using only two distinct cups. Every cup meets every cap
in at most two vertices.

This certificate is not a coloring, signotope, decomposable configuration, or
Lean counterexample. It rules out closure from cardinalities and incidence
alone; it does not refute a decomposition-tree or orientation-sensitive
consumer.

## Outcome and next gate

**Outcome 2: reusable structural advance, not closure.** Six-cap saturation,
the protected `2+2+0` package, the ten-vertex transversal bound, and the
private-cup ledger compile. No theorem closes the exact singleton tail, and
no target-free 32-vertex coloring refutes the full route.

The active consumer is now precise: use decomposition-tree addresses and
orientation to couple the at least ten distinct private cups to the six cap
blocks and eight remainder vertices. A valid continuation must prove
cross-owner nonreuse or construct a four-cup transversal of at most nine
vertices; the latter contradicts the compiled density theorem immediately.
Expire any proposal that assumes more than two distinct raw deletion cups,
common lowest addresses, weak ordering of the caps, or a shared nonendpoint
without proving it.

## Reproduction

```console
lake build ErdosSzekeres.StructuralChargingNextState578SevenWitness
lake build ErdosSzekeres.StructuralChargingNextState578RegenerationCounterexample
python3 scripts/verify_state578_private_cup_incidence_model.py \
  data/derived/state578-private-cup-incidence-countermodel.json
make test
```

## Evidence

- [Lean seven-witness saturation](../../ErdosSzekeres/StructuralChargingNextState578SevenWitness.lean)
- [Lean local counterexample](../../ErdosSzekeres/StructuralChargingNextState578RegenerationCounterexample.lean)
- [Relaxed incidence certificate](../../data/derived/state578-private-cup-incidence-countermodel.json)
- [Independent certificate checker](../../scripts/verify_state578_private_cup_incidence_model.py)
- [Previous regeneration experiment](0068-state-578-three-cup-regeneration.md)
