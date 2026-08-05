# Packed crossing strong-six splits

Date: 2026-08-05

## Question

How does the sharp-boundary strong-six deletion packing produce enough
strong-five residues to activate the proved three-residue overlap theorem?

The preceding bounded Sol/Fable review identified the strong-six packing as
the missing global coupling source. This work implements that vetted route;
it does not claim that the middle crossing splits have yet been eliminated.

## Compiling Lean results

`StructuralChargingPackingResidues.lean` proves the following without
`sorry`, an external oracle, or a new axiom.

1. A six-set contained in two disjoint sides is the disjoint union of its two
   side intersections.
2. Under deletion packing and absence of an internal strong six in either
   side, every packed witness has exactly one of the five proper crossing
   splits `1+5`, `2+4`, `3+3`, `4+2`, or `5+1`.
3. A `1+5` crossing strong six is equivalent to a left vertex carrying a
   strong-five residue on the right. The mirror equivalence holds for `5+1`.
4. If the three middle split types are absent, there are at least seven total
   strong-residue carriers. Otherwise six carriers could be placed in the
   prescribed deletion, while packing would return a fresh extreme carrier
   outside it.
5. Seven carriers force at least four on one side of the balanced cut.
6. Any three carriers into an eleven-set admit three ordered strong-five
   residue bases, two of which overlap in at least two vertices. Consequently
   the no-middle-split packing hypothesis activates the existing overlap
   theorem on one side.

These are conditional structural theorems. They do not prove that a balanced
counterexample lacks middle crossing strong sixes.

## Mathematical interpretation

The hoped-for conclusion of “at least three strong residues” does not follow
from deletion packing by a bare set-system argument: a packing family could
consist entirely of `3+3` sets. The coloring structure must rule out or
transform the middle splits. Once it does, the deletion quantifier is much
stronger than an ordinary pigeonhole argument and yields seven carriers.

## Next theorem

For an ordered `11+11` cut with cap-four-free sides and ambient avoidance of a
cap five, cup six, and strong seven, prove that every crossing strong six of
split `2+4`, `3+3`, or `4+2` either:

- already forces one of the three target outcomes; or
- can be replaced by an extreme `1+5` or `5+1` crossing strong six while
  preserving avoidance of a prescribed six-set.

The three split types should be analyzed separately before proposing a single
combined theorem. The `3+3` case is the symmetric first target.
