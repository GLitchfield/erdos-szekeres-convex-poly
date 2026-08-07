# Forced endpoint-extreme counterexample

## Question

Experiment 0044 finds that every nonvacuous `k = 6` hole through eight
vertices has a normalized endpoint extreme that belongs to no compatible
block-small owner. Does that singleton strengthening survive the frozen
`n = 12`, `k = 7` root from experiment 0042?

The four roles are the past and future ideals at the hole's left and right
endpoints, after applying the same orientation reflection as the candidate
family.

## Frozen result

No. Of the 29 nonvacuous frozen holes, 25 force all four endpoint extremes,
but four cup/rank-three holes force none of them.

The first counterexample is the full seven-span cup block with hole span
`(2,5)` at index 2. Its normalized endpoint roles are:

| Role | Ideal | Compatible block-small owners |
| --- | ---: | --- |
| left past | `9` | indices 3, 4, 5 |
| left future | `3f` | index 5 |
| right past | `1b` | indices 3, 5 |
| right future | `1b` | indices 3, 5 |

Thus no endpoint extreme alone forces a block-large owner. The broader
small-owner deficiency survives: the two-ideal anchor `{f,1f}` has only owner
index 5 in its block-small neighborhood, so its deficiency is `2 - 1 = 1`.

Across all 29 nonvacuous holes, 26 have a singleton minimum deficient anchor
and three require two ideals. Every minimum deficiency is exactly one.
Cell-mask production and an independent row-height/boundary-slot replay agree.
The manifest SHA-256 is
`7ef7234ea4be594ed4260ea5e2d4fa03051d30bea2dea3315224c676a44b610c`.

## Claim boundary and route consequence

This refutes both a fixed left-future rule and the existential claim that some
endpoint extreme always forces a block-large owner. It does not refute the
block-large reached-owner profile or the small-owner deficiency formulation.
The counterexample explains why injectivity matters at `k = 7`: two hole
ideals can compete for one block-small owner even though neither ideal is
individually excluded from all small owners.

The active bridge must therefore produce a deficient anchor set, not
necessarily a singleton endpoint label. The compiled forced-ideal and forced-
extreme implications remain valid sufficient lemmas, but this experiment
retires them as the arbitrary geometry target.

## Reproduction

    python3 scripts/check_forced_endpoint_extreme.py \
      --output data/derived/e3-forced-endpoint-extreme-frozen-n12-k7.json
    python3 scripts/replay_forced_endpoint_extreme.py \
      data/derived/e3-forced-endpoint-extreme-frozen-n12-k7.json
