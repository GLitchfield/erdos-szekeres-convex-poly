# Two-lane adjacent uncrossing gate

## Question

The full reflected candidate family is the union of two endpoint lattice
intervals in one untagged ideal lattice. The remaining proposal is to use those
lanes only inside the proof and exchange two adjacent representatives by their
lattice meet and join. This gate asks which local exchange rule is even true on
the frozen root before defining an augmenting algorithm or Lean theorem.

## Two exact local rules

For adjacent frontier spans with representatives `I` and `J`, the rigid rule is

    I meet J remains with the earlier span,
    I join J remains with the later span.

The flexible rule allows either that assignment or its reversal, but only when
both resulting untagged ideals belong to the corresponding full two-lane
candidate unions. The choice is checked from the two ideals and two local
families; it does not consult a completed matching.

## Frozen result

The rigid rule is false. In the cap/rank-three frontier, adjacent spans
`(4,6)` and `(5,7)` admit only the full and empty ideals respectively for the
tested pair. Their meet is empty and their join is full, so only the reversed
assignment preserves membership.

The flexible rule passes every one of the 738 ordered ideal pairs across every
adjacent pair in all four frozen color/rank frontiers. Some pairs admit only the
forward assignment, some only the reverse assignment, and some both. Thus a
proof cannot fix one global meet/join orientation, but the local two-choice
exchange survives this first falsifier.

The producer uses cell-mask ideals and bitwise meet/join. The checker
reconstructs nonincreasing row-height ideals and uses coordinatewise minimum
and maximum. Both reconstruct all reflected candidate families and every
adjacent check. The compact manifest SHA-256 is
`98a1a794d3d955f79be0e0fd92234ebbf5323133a2f2fab3a5dd5e13fd2a35df`.

## Lean obstruction to a pairwise proof

`StructuralChargingTransitionHallUncrossing.lean` defines the abstract
flexible meet/join predicate, two-family expansion, and existence of distinct
representatives. It constructs three candidate families over the two-element
lattice, all equal to the same two-element transition interval. Both
proof-side lanes may be that identical interval. The compiling theorem

    flexibleMeetJoin_pairExpansion_not_sufficient

proves simultaneously that every pair flexibly uncrosses, every two distinct
families expands to at least two ideals, and no injective representative exists
for all three. Its axiom audit uses only `propext`, `Classical.choice`, and
`Quot.sound`.

This is not a counterexample to the actual reflected frontier, whose full
frozen families pass Hall. It is a kernel-checked counterexample to the
abstract implication from local flexible uncrossing plus pair expansion to an
SDR.

## Claim boundary and next obstruction

The 738-pair pass is bounded computational evidence, not a Lean theorem. The
insufficiency of its abstract premise is kernel-checked. The next mathematical
target is an exact well-founded hole-moving invariant. A state leaves one span
unmatched and injectively represents the others. If the hole cannot be filled
directly, a certified lane switch or adjacent meet/join move must strictly
decrease a fixed measure derived from local endpoint/lane data. A measure
computed from distance to a known matching would be circular. Lane labels must
remain proof-side only; representatives and capacity remain the original
untagged ideals.

## Reproduction

    python3 scripts/check_two_lane_adjacent_uncrossing.py \
      --output data/derived/e3-two-lane-adjacent-uncrossing-frozen-n12-k7.json
    python3 scripts/replay_two_lane_adjacent_uncrossing.py \
      data/derived/e3-two-lane-adjacent-uncrossing-frozen-n12-k7.json
