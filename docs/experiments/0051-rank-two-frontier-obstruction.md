# Rank-two frontier obstruction

## Question

Do the reflected endpoint Hall and lane-path mechanisms from Experiments
0029--0050 also cover exact rank two, and does every rank-two frontier fit the
proposed Pascal demand `choose (k - 2) 1`?

The earlier all-root scripts used a shared group generator containing the
explicit guard `rank >= 3`. Their reported group and hole totals therefore
contained no rank-two case. This experiment enumerates rank two separately.

## Bounded results

The stronger lane-path target already fails at support size five. With
`support = 0x1f`, `lower = 0x15`, and coloring `0xc8`, the cap frontier is

`(0,1), (1,2), (2,3), (3,4)`.

For the hole `(1,2)`, neither reflected endpoint lane admits the required
owner-labelled path. Independent cell-mask production and row-height replay
agree on the first failure after checking 465 exact-rank-two groups and 1,312
holes through that stopped prefix.

The full rank-two reflected-Hall census through support size eight is more
decisive:

| Quantity | Count |
| --- | ---: |
| Compatible root contexts | 376,764 |
| Open contexts | 366,086 |
| Exact-rank-two group checks | 732,172 |
| Reflected Hall failures | 20,254 |
| Direct Pascal-capacity violations | 2,896 |
| Maximum frontier size | 7 |

At support size six, a five-span family already violates reflected Hall. At
support size seven, the first direct capacity obstruction has the alternating
split `lower = 0x55` and frontier

`(0,1), (1,2), (2,3), (3,4), (4,5), (5,6)`.

It has six rank-two spans but `publishedSpanPascalDemand 7 2 = 5`. The two
independent implementations agree on checked-prefix digest
`9f2e8cb050840894fceade6dacc70d876b1a44d63acf5160a40b6cb261865ba0`.
The complete manifest SHA-256 is
`03ebf81794ba2195dfabd74ddc91d185cf7909b46f346a5c1681e032d45e0085`.

## Lean result and interpretation

`StructuralChargingSpanFrontier.lean` proves two exact structural facts:

- an exact rank-two crossing span has no interior vertex in the active child
  (lower for cups and upper for caps); and
- the retained rank-two frontier consists exactly of adjacent crossings in
  the sweep-ordered split-membership word.

`StructuralChargingRankTwoCounterexample.lean` then defines an explicit
well-formed seven-leaf decomposition tree. Lean proves that its root split is
deep-below, its full support is recursively decomposable, and it contains no
strong seven-set. It proves that all six alternating adjacent spans lie in the
cap/rank-two frontier, that the frontier exceeds its five-slot Pascal demand,
and that the corresponding `AllocatedExactRankSlotting` type is empty.

Thus the per-rank individual-frontier allocation target is false, not merely
unsupported, even in an open decomposable context. The reflected Hall,
block-large owner, deficiency, and lane-path chain are all downstream of that
false capacity target at rank two and cannot repair it there. This does not
refute the rank-at-least-three subroute, nor any grouped or globally coupled
accounting of rank-two transitions.

## First replacement and its refutation

A bounded route review proposed charging every node-local rank-two adjacency
to its unique lowest separating node and bounding the total by the number of
globally adjacent pairs, `support.card - 1`. Sol rated that proposal only
partially supported; Fable returned zero tokens because its provider quota was
exhausted, so no Sol/Fable consensus is claimed. The frozen evidence packet
has SHA-256
`188ea81cb2d630c59eea64d343bf6f02a071a8ed383112d88a8890735c64a4cd`.

The proposed linear bound is false on the smallest possible nontrivial tree.
Let the root split `{0, 2}` from `{1}`, and let the first child split `{0}`
from `{2}`. The root has local rank-two adjacencies `(0,1)` and `(1,2)`, while
the child has the local adjacency `(0,2)`. These are three distinct endpoint
pairs with distinct valid lowest-node ownership, but the whole support has
only two globally adjacent gaps. The theorem
`two_node_rank_two_mass_exceeds_global_adjacent_count` kernel-checks this
counterexample in `StructuralChargingRankTwoCounterexample.lean`.

Thus unique ownership eliminates duplicate endpoint pairs but does not turn
node-local adjacency into global adjacency. The surviving generic bound by
all unordered endpoint pairs is quadratic and cannot supply the needed
Pascal coefficient. Moreover, all six spans in the seven-vertex alternating
root obstruction are already globally adjacent, so restricting to global
gaps still gives `6 > 5`. A viable replacement must quotient or jointly pay
for rank-two transitions inside the recurrence itself; it cannot be obtained
from lowest-node bookkeeping alone.

## Claim boundary

The all-root counts are bounded reproduced computation. The explicit
seven-vertex obstruction, the three-vertex global-count obstruction, and the
rank-two normal forms are kernel-checked Lean theorems. Neither establishes a
replacement arbitrary-`k` recurrence or the exact Erdős--Szekeres formula.

## Reproduction

    python3 scripts/enumerate_rank_two_lane_path_certificates_all_roots_k7.py \
      --maximum-n 5 \
      --output data/derived/e3-rank-two-lane-path-counterexample-k7-n5.json
    python3 scripts/check_rank_two_lane_path_certificates_all_roots_k7.py \
      data/derived/e3-rank-two-lane-path-counterexample-k7-n5.json
    python3 scripts/enumerate_rank_two_reflected_endpoint_hall_all_roots_k7.py \
      --maximum-n 8 --no-stop-on-failure \
      --output data/derived/e3-rank-two-reflected-endpoint-hall-k7-n8.json
    python3 scripts/check_rank_two_reflected_endpoint_hall_all_roots_k7.py \
      data/derived/e3-rank-two-reflected-endpoint-hall-k7-n8.json
