# Maximum single-lane spread counterexample

## Question

Can the active block-large reached-owner profile be strengthened by requiring
one reached owner's left or right endpoint interval to have cell spread at
least `block.card - 1`? Here lane spread is the number of cells in the
symmetric difference of the lane's past and future Pascal-grid ideals.

Such a theorem would combine with a lattice-interval cardinality bound to make
one individual lane pay for the whole block.

## Frozen counterexample

The proposal already fails on the tight cap witness from experiment 0042.
The full block has six spans and singleton hole family `{3f}`. Its only mapped
ideal is owned by span `(2,5)`, whose complete two-lane candidate family has
seven ideals and is therefore block-large.

The left lane runs from ideal `3` to ideal `3f`. Its cell symmetric difference
has size four, while the right lane is the singleton interval at `3f` and has
spread zero. Thus

```text
maximum lane spread + 1 = 4 + 1 = 5 < 6 = block size.
```

Cell-mask production and an independent boundary-slot calculation agree. The
counterexample manifest SHA-256 is
`2d20a99bbad28611676dacde1a34b032deef154d2d4e8958d29548d57e7b9278`.

## Claim boundary and consequence

This refutes only the proposed maximum-single-lane-spread owner bridge. It does
not refute the block-large reached-owner profile: the same owner has seven
distinct candidates because the interval lattice branches, even though every
maximal chain between the lane endpoints has only five states. A successful
bridge must therefore retain interval branching, combine both lanes, or use a
small-owner incidence deficiency. Chain length in one endpoint interval is
not enough.

## Reproduction

    python3 scripts/check_max_lane_spread_owner.py \
      --output data/derived/e3-max-lane-spread-owner-counterexample-frozen-n12-k7.json
    python3 scripts/replay_max_lane_spread_owner.py \
      data/derived/e3-max-lane-spread-owner-counterexample-frozen-n12-k7.json
