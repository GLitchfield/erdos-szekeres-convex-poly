# Frozen small-owner anchor structure

## Question

After experiment 0046 refutes singleton endpoint witnesses, can every frozen
nonvacuous hole still choose a minimum-cardinality deficient anchor that is a
complete lattice chain interval contained in one normalized endpoint lane?

The producer enumerates every minimum-cardinality deficient anchor, rather
than retaining only the first. It records both existential and universal
shape summaries. The checker independently reconstructs the root with
row-height ideals.

## Bounded result

The existential classification passes all 29 nonvacuous holes. Twenty-six
holes have singleton minima and three require two ideals. In every hole, some
minimum anchor is a one-lane saturated lattice interval. The three
non-singleton holes have the following structured choices:

- `{f,1f}` inside one lane for spans `(2,5)` and `(7,9)`;
- `{0,1}` inside both lanes for span `(6,8)`.

All are cover pairs differing by one grid cell. The first and third holes also
admit the skipped pair `{f,3f}` as an alternative minimum anchor. Consequently
all minimum anchors are chains and lane-local, but only 27 of the 29 holes
have every minimum anchor saturated and lattice-convex.

Every minimum anchor has deficiency one. Lean now proves this is an abstract
consequence of inclusion minimality, not additional geometric evidence. It
also proves that deleting any member preserves the small-owner neighborhood
and classifies the singleton and two-anchor cases exactly.

The cell-mask and row-height implementations agree. The manifest SHA-256 is
`1ae7e59414d61dc5dfc02f42bb3d43a6d44dfa40f8da4f418c56da9e511d6c83`.

## Claim boundary

This is a complete classification only for the frozen `n = 12`, `k = 7`
root. It does not prove that a deficient anchor exists for arbitrary genuine
frontiers. The shape is meaningful only as a candidate mechanism; generic
unions of two lattice intervals admit cross-lane, nonconvex deficient anchors.

## Reproduction

    python3 scripts/analyze_frozen_small_owner_anchor_structure.py \
      --output data/derived/e3-frozen-small-owner-anchor-structure-n12-k7.json
    python3 scripts/replay_frozen_small_owner_anchor_structure.py \
      data/derived/e3-frozen-small-owner-anchor-structure-n12-k7.json
