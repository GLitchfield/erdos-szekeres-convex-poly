# Experiment 0102: the Fin8 half-pure deep-split boundary

Date: 2026-08-11

Status: exact bounded theorem proved in Lean; uniform producer open

## Question

Does every eight-vertex rank-three one-change coloring with no strong
five-polygon admit a deep split whose half-sized side has all strong
four-polygons of one pure color?

## Bounded evidence

Two complete enumerations first checked the unchanged contract on every
strong-five-free rank-three signotope on eight vertices. They independently
found 19,870 such signotopes, and every one admitted a witness among all 2,998
eligible ordered disjoint side pairs. This included noncovering pairs and was
stronger than the earlier decomposable-only census.

The exact negation was then encoded using 266 propositional variables and
5,084 clauses. An independent checker reconstructed the semantic CNF and
replayed a compact UNSAT core with 483 semantic leaves and 261 RUP additions.
Corrupted clause and proof controls were rejected.

## Lean promotion

`HalfPureDeepSplitFin8.lean` now proves

```lean
halfPureDeepSplitAtFiveFinEight_of_oneChange
    (chi : TripleColoring 8)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : not ContainsStrongPolygonSet chi Finset.univ 5) :
    exists lower upper,
      HasDeepBelowSplit chi lower upper and
      -- one side is nonempty, has doubled size at least eight,
      -- and every strong four-set on the other side is color-pure
      ...
```

The generated semantic bridge is split across 21 modules. The theorem and its
LRAT replay compile with only `propext`, `Classical.choice`, and `Quot.sound`.
This is a completed Lean result at the eight-vertex boundary.

## Disposition

`GO_STRUCTURAL`.

The result validates `HalfPureDeepSplitAt` at its first complete boundary and
promotes the main predecessor route beyond computational evidence. It does not
prove the arbitrary-size producer or the exact Erdős--Szekeres formula. The
next work should mine the completed clause bridge for a structural split
argument; larger raw enumeration is deferred.
