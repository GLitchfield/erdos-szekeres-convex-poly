# Experiment 0067: state-578 dual packing

## Question

Can the exact `41+1` color-dual singleton-lower gate be converted from
four-cup density in every 23-vertex restriction into a global cross-color
packing whose decomposition-tree profiles force a forbidden seven-cap,
five-cup, or strong eight-set?

## Frozen review

The route-selection packet was frozen at revision
`d8bbe6bbe920f489127e8d92dd83e053e672f639`.  Its Sol/Fable evidence packet
has SHA-256
`e20635284cdffe5317f2814298c152aea42edaf877dbf3fe878554663edae938`.
Both reviewers rated the proposed extraction `partially_supported`: they
accepted the conditional `3+3` packing and rejected any claim that the nine
pair addresses already synchronize.  The review is advisory, not evidence.

## Compiling positive results

Assume the strictly smaller predecessor `DecomposableStateUpper 4 5 8`.
The exact 32-vertex reservoir supplies three pairwise-disjoint four-cups:
the `32/23` density is spent on residual sizes `32`, `28`, and `24`.
After deleting those 12 vertices, the predecessor is spent on decomposable
residuals of sizes `20`, `16`, and `12`, producing three four-caps.  All six
four-sets are pairwise disjoint across colors.  This is packaged by
`ThreeDisjointCupCapFourPacking578` and
`exists_threeDisjointCupCapFourPacking_of_colorDualLower_at_32`.

For every disjoint cup--cap pair, Lean now selects its canonical lowest joint
decomposition-tree split.  At that split:

- the cup cannot be wholly lower while the cap is wholly upper in a
  strong-eight-free support;
- any cup not wholly upper and any cap not wholly lower obey the exact
  two-endpoint crossing laws; and
- the reverse separated orientation, cup upper and cap lower, remains a real
  alternative.

At a single common split containing all six witnesses, target avoidance does
give one global defense ledger: either all three cups have a vertex outside
the lower child, or all three caps have a vertex outside the upper child.
This uses all six witnesses, but it does not yet make those three defense
vertices distinct across different tree levels.

Finally, applying the `(4,5,8)` predecessor inside the 12-vertex union of the
three cups regenerates a four-cap.  Lean proves the exact alternative: the new
cap is disjoint from one selected cup, or its three intersection sizes are
`2,1,1` in some order.  The theorem
`exists_dualPackingRegeneration_of_colorDualLower_at_32` reconnects this
alternative to the exact singleton-root gate.  This is the strongest positive
result of the experiment.

## Certified obstruction

The recursively decomposable eight-vertex tree

```text
[[[0,3],[1,2]], [[5,6],[4,7]]]
```

has a four-cap wholly in its lower root child and a disjoint four-cup wholly
in its upper root child.  Lean checks decomposability, the two witnesses, and
absence of a seven-cap, five-cup, and strong eight-set.  Thus the reverse
orientation is genuinely safe; repeating the pairwise first-split theorem
nine times cannot close the gate.

## Bounded falsification

Ignored deterministic scripts under the experiment task packet tested the
next stronger ideas within 60 seconds and 1 GiB:

- A six-token quotient admits all three caps below and all three cups above
  one common root.  All nine addresses agree, yet every pair has the safe
  reverse orientation.  This is a relaxed address model only.
- A rank-three signotope on 12 vertices has three interleaved four-cups and a
  target-free regenerated `2+1+1` four-cap.  An independent recursive-split
  recognizer rejects that particular model as decomposable.  It refutes a
  signotope-only continuation, not the exact decomposable theorem.
- A deterministic sample of 50,000 recursively decomposable 12-vertex trees
  found no target-free `2+1+1` regeneration witness.  This is bounded negative
  evidence only, not an UNSAT certificate or theorem.

The initially observed UNSAT result for three consecutive cup blocks was not
promoted: arbitrary sweep interleavings invalidate that normalization.

## Outcome and route decision

**Outcome 2: reusable structural advance.**  The global disjoint `3+3`
packing, common-split defense, first-joint-split classifier, and exact
regeneration alternative all compile without `sorry`.  They do not prove the
32-vertex gate.

The address-equality-only route is expired by the certified reverse pair and
the relaxed common-root model.  The surviving next theorem must use recursive
decomposability essentially to control the regenerated cap across the three
interleaved cups.  It must eliminate both the disjoint-cup branch and the
`2+1+1` branch, or turn one branch into a named child-capacity violation.
Signotope laws, pairwise address repetition, and independent pair classifiers
are insufficient hypotheses.

Follow-up Experiment 0068 kernel-checks a decomposable, sweep-realizable
12-vertex model realizing both regeneration branches target-free. It therefore
expires this local continuation while retaining the full external `3+3`
packing as the next global interface.

## Evidence

- [Lean dual packing](../../ErdosSzekeres/StructuralChargingNextState578DualPacking.lean)
- [Lean reverse-orientation counterexample](../../ErdosSzekeres/StructuralChargingNextState578DualPackingCounterexample.lean)
- [Preceding color-dual gate](../../ErdosSzekeres/StructuralChargingNextState578Dual.lean)
- [Preceding private-cap trace experiment](0066-state-578-private-cap-traces.md)
