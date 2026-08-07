# All-root block-large reached-owner gate

## Question

Does the block-large reached-owner profile from experiment 0042 survive every
recursively decomposable `k = 6` root through eight vertices, every reflected
exact-rank frontier group, every nonempty consecutive block, and every hole?

Enumerating all feasible owner maps is unnecessary. For a fixed block and
hole, restrict the possible owners to spans whose candidate family has size at
most a threshold. The least threshold admitting a matching of the entire hole
family is exactly the minimum, over feasible owner maps, of the maximum family
size reached by that map. The active profile fails precisely when this
bottleneck is smaller than the block.

Lean independently formalizes the logical reduction as
`finiteCandidateFeasibleOwnerHasBlockLargeFamily_iff_no_smallOwnerObstruction`.
The computation uses small bipartite matching only to test bounded instances
of the obstruction.

## Bounded result

The complete gate passes.

| Quantity | Count |
| --- | ---: |
| Compatible root contexts | 376,764 |
| Exact-rank frontier groups | 631,474 |
| Consecutive blocks | 1,126,134 |
| Block/hole checks | 1,438,464 |
| Nonvacuous holes | 3,792 |
| Zero-feasible-map holes | 1,434,672 |
| Profile failures | 0 |

All holes through support size six are vacuous. At support size seven, all 448
nonvacuous holes have bottleneck slack `+3`. At support size eight, the 3,344
nonvacuous holes have the following exact minimum-slack distribution:

| Slack | Holes |
| ---: | ---: |
| `+1` | 424 |
| `+2` | 2,132 |
| `+3` | 788 |

The cell-mask producer and an independent row-height implementation agree on
all aggregate counts, bottleneck histograms, deterministic owner witnesses,
and the checked-prefix digest
`54a95152cdafcee575f0779f4b22bad1a1cfae4a7ebc248d2c641efec08e029b`.
The manifest SHA-256 is
`7cd47914f9f6596d67b2dc89d0a2a1afdebf48ffecdcb4386f390b38dad8a4a1`.

The same replay mines the least small-owner neighborhood deficiency. Every one
of the 3,792 nonvacuous holes has a one-ideal deficient anchor with deficiency
one. More strongly, every hole has such a singleton among its four normalized
past/future endpoint extremes: that ideal belongs to no compatible block-small
non-hole span. This is the exact strengthened contract now exposed in Lean as
`AllocatedReflectedEndpointRankTransitionHasBlockLargeForcedExtreme`.
This is a `k = 6` pattern, not a general theorem: experiment 0046 subsequently
refutes the forced-extreme strengthening on the frozen `k = 7` cup frontier.

## Claim boundary and consequence

This is substantially broader evidence for the active invariant than the
single frozen `n = 12`, `k = 7` root, but it is still finite evidence for
`k = 6` through eight vertices. It does not prove the arbitrary genuine
profile, construct one-hole states, prove Hall, or imply the exact
Erdős--Szekeres formula.

The useful structural consequence is negative as well as positive: the
invariant survives every existing all-root frontier census. The singleton
endpoint witness is a useful equality clue at `k = 6`, but experiment 0046
shows that the arbitrary proof must permit larger deficient anchor sets.
Generic interval convexity and reflection remain insufficient.

## Reproduction

    python3 scripts/enumerate_block_large_reached_owner_all_roots.py \
      --maximum-n 8 \
      --output data/derived/e3-block-large-reached-owner-all-roots-k6-n8.json
    python3 scripts/check_block_large_reached_owner_all_roots.py \
      data/derived/e3-block-large-reached-owner-all-roots-k6-n8.json
