# Rank-two gap promotion gate

## Question

Can the excess exact-rank-two transitions from Experiment 0051 be moved into
higher Pascal layers using actual deep-below geometry, rather than bounded in
the false rank-two layer?

For the sweep-ordered lower/upper membership word at one root, write the word
as alternating nonempty runs. Every boundary between runs is a rank-two
frontier span. Leave the first boundary unmatched. Each later boundary enters
a run whose first vertex and the last vertex of the preceding run of the same
child form a child-internal gap hidden by the intervening opposite-child run.
This gives the elementary identity

    crossing transitions = hidden child gaps + 1.

The color is forced by `HasDeepBelowSplit`: a hidden lower gap with an upper
middle vertex is a cap triple, while a hidden upper gap with a lower middle
vertex is a cup triple.

The gate treats each color separately. A cap transition is promoted only when
its matched hidden gap lies in the lower child; a cup transition is promoted
only for a hidden upper gap. The promoted object is placed at its exact
ambient endpoint-span rank. All unpromoted transitions remain at rank two. At
rank at least three, the promoted noncrossing gaps are combined with the
existing crossing exact-rank frontier.

This is a new ambient-support carrier. A promoted gap is noncrossing at the
parent and therefore is not an `allocatedExactRankFrontier` member there.

## Complete bounded result

Two independent implementations checked every recursively decomposable
`k = 7` root through support size eight. The producer uses alternating runs
and cell-mask ideals. The checker instead finds consecutive vertices directly
inside each child, reconstructs the entering transition from the intervening
opposite-child vertices, computes ranks by subset enumeration, and represents
ideals by row heights.

| Quantity | Count |
| --- | ---: |
| Compatible root contexts | 376,764 |
| Open contexts | 366,086 |
| Promotion records | 392,562 |
| Adjusted color/rank groups | 1,913,894 |
| Direct Pascal-capacity failures | 0 |
| Endpoint-ideal candidate failures | 0 |

The maximum adjusted sizes were:

| Exact rank | Maximum | `choose(5, rank - 1)` |
| ---: | ---: | ---: |
| 2 | 4 | 5 |
| 3 | 8 | 10 |
| 4 | 5 | 10 |
| 5 | 3 | 5 |
| 6 | 1 | 1 |

The same maxima occur for cups and caps. In particular, the alternating
seven-vertex root that formerly had six rank-two spans no longer violates its
rank-two layer: color-compatible hidden gaps are moved to actual higher-rank
spans. The complete checked-prefix digest is
`39f6694e56fb7af5a7d852269b1783eb54a795cd0a4f4d21e997a1033231ad9b`.
The manifest SHA-256 is
`2f352e1c06600ba6f7d778299379cd587dc178327b7c161c91ac525dcc627f43`.

## Lean promotion

`StructuralChargingRankTwoGenealogy.lean` now compiles the following pieces:

- `binaryCrossingGapCount_eq_hiddenChildGapCount_add_one` proves the numerical
  run-word identity when both run colors occur;
- `IsHiddenLowerGap.hasCapSpanRankAtLeast_three` turns an explicitly hidden
  lower adjacency into a cap endpoint span of rank at least three in the
  parent support;
- `IsHiddenUpperGap.hasCupSpanRankAtLeast_three` proves the color-dual cup
  result;
- `AmbientPromotedGap` is the explicit color-compatible, noncrossing source
  carrier with an exact rank in the parent support, and
  `exists_ambientPromotedGap_of_mem` constructs it from every source gap;
- its generalized endpoint-rank candidates and encoded Pascal-slot candidates
  are well typed and nonempty without a crossing, Hall, or capacity premise;
- `allHiddenGapSourceSumUnitEquivParentCrossingGap` constructs the exact
  equivalence between all explicit hidden sources plus one unit and all parent
  crossing gaps;
- `rankTwoResidual_card_eq_complementHidden_card_add_one` proves the
  fixed-color residual identity used by the producer; and
- `AdjustedHigherRankDemand` combines the crossing frontier with fixed-rank
  promoted sources. Exact promoted spans force the same-color corner into both
  incident endpoint profiles, and adjusted Hall is proved sufficient for the
  published Pascal-layer capacity.

## Bounded route review

The frozen review packet has SHA-256
`71f017be9d5fe2d54b029f939f78a19bd96d4001666048a76e421a5f75820860`.
Sol returned `partially_supported` with medium confidence: it regards this as
the strongest surviving direction in the packet, while identifying the
noncrossing candidate semantics and two-color recurrence composition as the
remaining blockers. Fable returned zero tokens with a provider usage-limit
error, so no Fable judgment or Sol/Fable consensus is claimed.

## Claim boundary and next obstruction

The census is independently reproduced bounded computation. The listed Lean
results are kernel-checked. This does not prove arbitrary-`k` capacity,
Hall expansion, a valid slotting, the published recurrence, or the exact
Erdős--Szekeres formula.

In particular, the existing endpoint-ideal candidate formula was evaluated
on promoted noncrossing spans only as a falsification gate. Its ray bridge was
proved for crossing allocated spans and does not automatically apply here.
The ambient promoted carrier, exact canonical matching, fixed-color residual
arithmetic, fixed-rank adjusted carrier, and first noncrossing incidence facts
are now compiled. The exact next formal contract is adjusted Hall expansion
for the combined crossing/promoted family, without assuming Hall or capacity.
A separate uniform bound on the rank-two residual and a two-color composition
theorem must then connect these local layers to the published recurrence; the
bounded pass alone does not supply either theorem.

## Reproduction

    python3 scripts/enumerate_rank_two_gap_promotion_k7.py \
      --maximum-n 8 \
      --output data/derived/e3-rank-two-gap-promotion-k7-n8.json
    python3 scripts/check_rank_two_gap_promotion_k7.py \
      data/derived/e3-rank-two-gap-promotion-k7-n8.json
