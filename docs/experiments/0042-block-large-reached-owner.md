# Block-large reached-owner gate

## Question

Experiment 0041 proves only a bounded owner-star union inequality. A stronger
profile could be easier to derive geometrically: for every hole and every
injective membership-feasible map from the hole ideals to distinct non-hole
spans, does at least one mapped owner have a candidate family at least as large
as the entire block?

This profile is strictly stronger than owner-star expansion. Different mapped
owners can collectively make a large star even when no individual family is
block-large. Its value is that a block-large mapped family is visibly contained
in the owner star, so the implication to the existing target is elementary and
now proved in Lean.

## Frozen result

The gate passes all 247 feasible owner maps on all 62 nonempty consecutive
blocks. The minimum maximum-owner-family slack is `+1`.

| Group | Feasible maps | Minimum slack |
| --- | ---: | ---: |
| cap, rank 3 | 30 | `+1` |
| cap, rank 4 | 0 | vacuous |
| cup, rank 3 | 217 | `+1` |
| cup, rank 4 | 0 | vacuous |

The global slack histogram is:

| Slack | Maps |
| ---: | ---: |
| `+1` | 5 |
| `+2` | 14 |
| `+3` | 181 |
| `+4` | 23 |
| `+5` | 15 |
| `+6` | 6 |
| `+7` | 3 |

The cap minimum is the full six-span block. Its singleton hole `{3f}` maps to
span `(2,5)`, whose seven candidates give slack `+1`. The cup minimum is the
full seven-span block. The map from `{0,1,9}` reaches `(8,11)` through ideal
`1`; that owner has eight candidates, again giving slack `+1`.

The certificate retains each selected owner's unreflected left and right
transition intervals, the four past/future endpoint ideals, their boundary-slot
coordinates, and the orientation reflection bit. This is important because
generic lattice intervals with abstract reflection do not satisfy the profile.
Cell-mask production and an independent row-height replay agree exactly.

The manifest SHA-256 is
`b3f75fb27142b11023db09ab8ed28ba9bed67ab4b23da10fca3d169f5a644ac9`.

## Formal implication and claim boundary

Lean defines `FiniteCandidateFeasibleOwnerHasBlockLargeFamily` and proves
`finiteCandidateFeasibleOwnerStarExpansion_of_blockLargeFamily`. The proof
only includes the selected owner family into the owner-star union. It does not
prove that genuine reflected frontier systems satisfy the stronger premise.

The experiment is bounded evidence at one frozen `n = 12`, `k = 7` root. Two
color/rank groups are vacuous. It does not establish the profile for arbitrary
frontiers or `k`, construct one-hole states, prove Hall, give the global Pascal
injection, or prove the Erdős--Szekeres formula. A structural proof must use
actual endpoint-rank incidence; generic interval convexity, consecutive order,
and reflection are insufficient.

## Reproduction

    python3 scripts/check_block_large_reached_owner.py \
      --output data/derived/e3-block-large-reached-owner-frozen-n12-k7.json
    python3 scripts/replay_block_large_reached_owner.py \
      data/derived/e3-block-large-reached-owner-frozen-n12-k7.json
