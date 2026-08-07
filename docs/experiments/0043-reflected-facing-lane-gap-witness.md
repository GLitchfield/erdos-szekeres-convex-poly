# Reflected facing-lane gap-witness gate

## Question

Can the owner-star inequality be proved by a deterministic gap charge? For a
feasible owner map, order unmapped block positions from left to right, charge
each to its nearest mapped owner, use the endpoint lane facing the gap, and
select the first normalized boundary-slot ideal outside the hole family and
all prior charges.

This tests the concrete reflected frontier-gap mechanism selected by the
bounded Sol review as a falsification target. It tests the mechanism itself,
not merely the already known owner-star cardinality.

## Frozen result

The rule fails on the first tight cap witness, so the broader 247-map scan is
not run.

The full six-span cap/rank-three block has singleton hole `{3f}` at index 2,
mapped to owner span `(2,5)` at index 1. The unmapped positions begin
`0,2,3,4,5`.

1. Gap 0 faces the owner's left lane. After excluding `{3f}`, the rule selects
   normalized boundary-slot ideal `1f`.
2. Gap 2 faces the same owner's right lane. That lane is exactly `{3f}`, so it
   has no ideal outside the hole family. The second charge cannot be made.

Cell-mask production and an independent row-height replay agree on the block,
owner map, normalized lanes, first selection, and failure. The manifest
SHA-256 is
`cd376724314ee6ea44849e86922f12c4ea003fcfa102a6cbad16dc978c9441d6`.

## Claim boundary and route consequence

This refutes only the nearest-owner, facing-lane, greedy boundary-slot rule. It
does not refute arbitrary gap-witness injections, owner-star expansion, or the
block-large reached-owner profile. In fact, the same owner has a seven-element
two-lane candidate family and supplies the successful experiment 0042 witness;
the failure is caused by forcing a charge into its rigid right lane.

The route therefore returns to the pre-vetted block-large reached-owner
fallback. Any future gap rule must allow cross-lane capacity or a different
owner assignment and must be independently falsified before Lean work.

## Reproduction

    python3 scripts/check_reflected_facing_lane_gap_witness.py \
      --output data/derived/e3-reflected-facing-lane-gap-witness-frozen-n12-k7.json
    python3 scripts/replay_reflected_facing_lane_gap_witness.py \
      data/derived/e3-reflected-facing-lane-gap-witness-frozen-n12-k7.json
