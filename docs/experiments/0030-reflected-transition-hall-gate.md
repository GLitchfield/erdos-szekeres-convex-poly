# Orientation-reflected transition-Hall gate

## Question

The unreflected endpoint-transition Hall condition is formally false.  In the
kernel-checked `n = 12`, `k = 7`, rank-three collision, the two retained spans
`(4,6)` and `(5,7)` cross the allocated root in opposite orientations but have
the same rigid full `2 x 3` ideal.  The bounded Sol/Fable review proposed one
capacity-preserving repair: rotate-complement all candidate ideals for exactly
one crossing orientation.

This gate asks whether that repair:

1. is genuinely a permutation of the existing Pascal slots;
2. repairs the entire frozen root frontier, not only the known pair; and
3. preserves full Hall on all 631,474 documented `k = 6` frontier groups.

It also searches explicitly for same-orientation rigid pairs,
reflection-fixed opposite pairs, and triple-rigid collisions.  Any failure
stops the repair.  A pass is bounded evidence for attempting a structural
proof, not the structural proof itself.

## Fixed convention

For a lower ideal `I` in an `r x c` rectangle, define

    RC(I) = {(i,j) | (r-1-i,c-1-j) is not in I}.

This rotate-complement is again a lower ideal and is involutive.  A retained
span keeps its original two-endpoint interval candidates when its left
endpoint lies in the lower child.  When its left endpoint lies in the upper
child, every candidate is replaced by its rotate-complement.  Both cases use
the same untagged ideal lattice and the same `AllocatedPascalSlot rank k`;
there is no orientation coproduct.

## Lean result

`StructuralChargingTransitionHallReflection.lean` proves, without `sorry`,
that rotate-complement is an involution and that its boundary path is obtained
by reversing the original boundary slot.  After transport to the adjacent
Pascal layer, the compiling theorem

    rankIdealSlotEmbedding_reflectedComplement

states that ideal reflection is exactly `allocatedPascalSlotReversal`, an
equivalence of the unchanged slot carrier.  The file defines the reflected
Hall condition and proves

    allocatedExactRankFrontier_card_le_spanPascalDemand_of_reflectedHall.

Thus any future proof of reflected Hall yields the original local Pascal
coefficient, not a doubled bound.

`StructuralChargingTransitionHallReflectionCollision.lean` separately proves
that the two frozen spans have reflected candidate sets `{fullIdeal}` and
`{emptyIdeal}` and consequently expand to two candidates.  The axiom audit of
the involution, slot identity, Hall-to-capacity reduction, and frozen pair uses
only `propext`, `Classical.choice`, and `Quot.sound`.

## Bounded result

The frozen root coloring has support mask `fff`, lower-child mask `596`, and
coloring mask

    c9f7fdfe93f000dfe107f9e80053009e8005300efeff083fd37ffff.

All four of its color/rank frontier groups satisfy reflected Hall.  In the
known cap/rank-three group, span `(4,6)` keeps the singleton full ideal `3f`,
while span `(5,7)` receives the singleton empty ideal `0`.

The complete `k = 6` census then reproduced the earlier context coverage:

| context class | count |
| --- | ---: |
| compatible roots | 376,764 |
| open | 267,898 |
| terminal strong-six | 108,866 |
| exact-rank frontier groups | 631,474 |

No reflected Hall failure was found.  No group contained a same-orientation
rigid collision, a reflection-fixed opposite rigid collision, or three rigid
spans sharing one reflected candidate.  The checked-group digest is

    ec2589569ad25402540813c5b2739dc1f495756a86a5b56a74d6f33ceb3492f8.

## Independent replay

The producer represents ideals by cell bitmasks and uses augmenting paths for
the representative matching.  The checker imports no reflected-gate producer
code: it reconstructs the colorings with the independent recursive replay,
represents ideals by nonincreasing row heights, implements reflection as
`(h_0,...,h_{r-1}) -> (c-h_{r-1},...,c-h_0)`, and uses backtracking matching.

The checker reproduced the frozen coloring and four root groups, the exact
full-versus-empty separation, all context counts, all 631,474 Hall outcomes,
the targeted-obstruction results, and the checked-group digest.  The compact
manifest SHA-256 is

    f65c400c9b99f944eb755f5ea3d38e47adf94f9a25737e56401fec1af263c267.

## Interpretation and next theorem

This is positive computational evidence for the first candidate construction
that survives both the frozen `k = 7` obstruction and the complete existing
`k = 6` universe while retaining the exact Pascal capacity.  It does not prove
reflected Hall for arbitrary `k` or support size, and reflection by itself
does not reconstruct the witness incidence forgotten by endpoint ideals.

The next structural theorem must connect the orientation choice to actual
child rays at the span's unique lowest separating node.  Concretely, it should
derive membership in the unreflected or reflected candidate family from the
appropriate predecessor/successor ray occurrence, with no ability to choose
the orientation merely to avoid a collision.  Only after that bridge is
proved should the route attempt consecutive-block expansion, arbitrary Hall,
and the global injection into `decomposableBinomialWindow`.

If that structural bridge fails, the Innovation Scout's reviewed fallback is
a skew-Bollobás set-pair encoding of actual child-ray events, not another
finite quotient of endpoint profiles.

## Reproduction

    python3 scripts/enumerate_reflected_transition_hall.py \
      --maximum-n 8 \
      --output data/derived/e3-reflected-transition-hall-k6-n8.json
    python3 scripts/check_reflected_transition_hall.py \
      data/derived/e3-reflected-transition-hall-k6-n8.json
