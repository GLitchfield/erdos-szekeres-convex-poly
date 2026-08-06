# Stable-ownership cup/rank-three cycle gate

## Question

The singleton-or-block-large profile fails only on the frozen seven-span
cup/rank-three group. The reviewed fallback is a targeted one-hole census on
that group: can the unchanged boundary-priority ownership rule terminate by
multiple transfers even though the one-step cardinality theorem no longer
applies?

The state and move are exactly those of experiment 0036. A state has one hole
and injective untagged representatives for the other six spans. A fillable
state stops. Otherwise the hole takes its first candidate in ascending
row-boundary order and transfers the hole to that candidate's unique owner.

## Frozen result

The result is negative. Among 78,236 one-hole states, 74,944 fill directly and
3,292 are blocked. Of the blocked states, 3,220 fill after one transfer. The
remaining 72 states flow into 36 directed cycles, all of length two.

The first canonical cycle is

    hole 3: [1, 3, 9, -, 0, b, 1b]
    hole 4: [1, 3, 9, 0, -, b, 1b]

for frontier spans

    (0,2), (1,3), (2,5), (3,7), (6,8), (7,9), (8,11).

The hole alternates between `(3,7)` and `(6,8)`: both select ideal `0` first
and steal it back from the other span. Every state in the cycle is unfillable.
The transfer remains a valid one-hole state, so the failure is termination,
not membership or injectivity.

The cell-mask producer and row-height checker reconstruct the candidate
families, enumerate all 78,236 states, and independently reproduce the 36
cycles and first witness. The manifest SHA-256 is
`4a593c7ebf8c4d679f92a2f6818a48632d466a98ef1841402936eacfb2de6429`.

## Claim boundary and next obstruction

This refutes only the unchanged ascending boundary-priority rule. It does not
refute other local ownership priorities, collision-free meet/join escapes, or
reflected Hall itself. The first cycle exposes the next exact obstruction: a
valid rule must avoid immediately stealing the same ideal back. For example,
at hole `(6,8)`, ideal `1` is also occupied and is owned by the ten-candidate
span `(0,2)`, which would give a cardinality exit; choosing ideal `0` instead
creates the cycle. Before promotion, any cycle-breaking priority must be
frozen from local family/endpoint data and checked against all 36 cycles and
all remaining blocked states.

## Reproduction

    python3 scripts/check_stable_ownership_cup_rank3_cycle.py \
      --output data/derived/e3-stable-ownership-cup-rank3-cycle-frozen-n12-k7.json
    python3 scripts/replay_stable_ownership_cup_rank3_cycle.py \
      data/derived/e3-stable-ownership-cup-rank3-cycle-frozen-n12-k7.json
