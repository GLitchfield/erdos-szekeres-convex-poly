# Experiment 0068: state-578 three-cup regeneration

## Question

Does recursive decomposability force a five-cup, seven-cap, or strong
eight-set whenever three disjoint four-cups partition a 12-vertex support and
a four-cap is regenerated inside that support?

## Frozen review

The route-selection packet was frozen at revision
`602a5dc97f17acee0b467b19a8ec69a88fa5be43`. Its Sol/Fable evidence packet
has SHA-256
`514044d4b8a527ff4078b73faf95bd4c252a3d32ad267524d16e2f0d9cd31170`.
After one critique round both providers judged the proposed local theorem
false and requested an explicit Lean certificate. Their agreement is
advisory; the certificate below is the mathematical evidence.

## Compiling structural results

`ThreeCupRegenerationConfiguration578` packages the three cups, regenerated
cap, pairwise disjointness, and support equality. Lean proves:

- the support has exactly 12 vertices;
- every regenerated cap has one of the exhaustive incidence profiles
  `2+2+0` or `2+1+1` against the three cups; and
- at every containing deep split, all three cups and the cap obey their exact
  asymmetric endpoint/cardinality root profiles.

The file also preserves the global information that the local reduction had
discarded. A `ThreeDisjointCupCapFourPacking578` occupies exactly 24 vertices
of the 32-vertex reservoir and leaves exactly eight unused vertices. The
new `SevenWitnessRegenerationPacking578` retains the regenerated cap together
with the three external caps. Those four caps are pairwise disjoint. The exact
singleton-root gate now returns this full package directly.

## Structural model and native-checked counterexample

Use `(A < B)` for a decomposition node with lower child `A` and upper child
`B`. Lean checks the explicit tree

```text
((((1 < 3) < (0 < 11)) < ((8 < 9) < (2 < 10)))
  < ((5 < 6) < (4 < 7))).
```

The following three sets are pairwise-disjoint four-cups partitioning
`Fin 12`:

```text
C1 = {0,1,3,11}
C2 = {2,8,9,10}
C3 = {4,5,6,7}.
```

The same coloring contains both kinds of regenerated cap:

```text
K220 = {0,2,8,11}, with profile (2,2,0)
K211 = {0,4,5,8},  with profile (1,1,2).
```

Native finite evaluation reports that the coloring has no five-cap, no
five-cup, no seven-cap, and no strong eight-set. The explicit decomposition
tree and both incidence profiles are kernel-checked, and the general
realization theorem applies to the structural coloring. The target-avoidance
endpoints, however, use `native_decide` and depend on its generated axiom.
They are checked computational evidence rather than completed kernel-only
theorems, and the module is excluded from the root library import surface.

An ignored independent checker reconstructs the same tree coloring directly
and obtains zero five-cups, zero seven-caps, and zero strong eight-sets. This
is independent computational corroboration, not formal proof movement.

## Outcome and route decision

**Outcome 3: checked counterexample and route expiry as search information.** Recursive
decomposability, sweep realizability, target avoidance, the complete local
root profiles, and either incidence branch do not close regeneration on the
12 selected cup vertices. Any continuation using only that local
configuration is expired.

This does not refute the exact 32-vertex singleton-root gate. The certified
model lacks the three external disjoint caps, the remaining eight vertices,
and global `32/23` density. The active repair must use at least one of those
features essentially. The strongest currently compiled interface is the
seven-witness package: three disjoint cups, four pairwise-disjoint caps (one
regenerated inside the cups), a 24-vertex selected support, and an eight-vertex
remainder. A next consumer that reduces again to four independent local cap
arguments is ruled out for planning purposes by this experiment. This is a
search-information decision, not a completed kernel-only refutation.

## Reproduction

```console
lake build ErdosSzekeres.StructuralChargingNextState578Regeneration
lake build ErdosSzekeres.StructuralChargingNextState578RegenerationCounterexample
python3 runs/agents/20260808-state-578-regeneration/verify_counterexample.py
make test
```

## Evidence

- [Lean regeneration machinery](../../ErdosSzekeres/StructuralChargingNextState578Regeneration.lean)
- [Lean minimal counterexample](../../ErdosSzekeres/StructuralChargingNextState578RegenerationCounterexample.lean)
- [Preceding dual packing](0067-state-578-dual-packing.md)
