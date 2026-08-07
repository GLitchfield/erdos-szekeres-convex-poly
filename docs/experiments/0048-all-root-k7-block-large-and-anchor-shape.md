# All-root `k = 7` block-large and anchor-shape gate

## Question

Does the block-large reached-owner profile survive every decomposable `k = 7`
root through eight vertices? When endpoint singletons fail, does the
deterministically first minimum deficient anchor remain a complete chain
interval inside one normalized endpoint lane?

The matching-threshold reduction from experiment 0044 avoids owner-map
enumeration. The producer uses cell-mask ideals; the independent checker uses
row heights and separately reconstructs local ranks, reflection, matchings,
and anchor shapes.

## Bounded result

The complete gate passes.

| Quantity | Count |
| --- | ---: |
| Compatible root contexts | 376,764 |
| Exact-rank frontier groups | 947,452 |
| Consecutive blocks | 1,830,286 |
| Block/hole checks | 2,422,116 |
| Nonvacuous holes | 3,056 |
| Zero-feasible-map holes | 2,419,060 |
| Profile failures | 0 |

All holes through support size six are vacuous. Support size seven contributes
224 nonvacuous holes; support size eight contributes 2,832. The exact minimum
bottleneck-slack histogram is:

| Slack | Holes |
| ---: | ---: |
| `+2` | 248 |
| `+3` | 624 |
| `+4` | 104 |
| `+5` | 160 |
| `+6` | 1,884 |
| `+7` | 36 |

Endpoint-singleton deficiency survives in 1,876 holes and fails in 1,180.
Exactly those 1,180 holes have a first minimum deficient anchor of size two;
all other minima have size one. Every selected anchor has deficiency one and
is independently verified to be a chain, a saturated lattice interval, and
contained in one normalized endpoint lane. Thus every selected pair is a
one-cell cover pair.

The checked-prefix digest is
`ac7c3acf82b3a2e4d62191f803153c29c47a8cad433f2b6df85fff6f093423b3`.
The manifest SHA-256 is
`50c4d1adebc9ca883cfda58aebfcbad1bc85bfb1a19e1ced5a4bfa9e4732f262`.

## Claim boundary and consequence

This is bounded evidence for `k = 7` through support size eight, not a Lean
proof of the arbitrary profile. The shape statistic concerns the canonical
first minimum anchor; it does not claim every minimum anchor has the shape.

The result materially strengthens the route: multi-anchor deficiency occurs
in 1,180 genuine cases, yet every selected pair is a one-lane cover interval.
Lean now exposes normalized lanes, lattice chain intervals, and the exact
`AllocatedReflectedEndpointRankTransitionLaneChainMinimalDeficiency` contract,
and proves that contract implies the active small-owner deficiency. Constructing
the shaped anchor from exact-rank geometry remains the open theorem.

## Reproduction

    python3 scripts/enumerate_block_large_reached_owner_all_roots_k7.py \
      --maximum-n 8 \
      --output data/derived/e3-block-large-reached-owner-all-roots-k7-n8.json
    python3 scripts/check_block_large_reached_owner_all_roots_k7.py \
      data/derived/e3-block-large-reached-owner-all-roots-k7-n8.json
