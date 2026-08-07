# All-root `k = 8` block-large and anchor-shape gate

## Question

Does the block-large reached-owner profile survive the first new parameter
`k = 8` through eight vertices? Does every nonvacuous hole still admit the
singleton-or-cover-pair construction that the new Lean lemmas turn into a
one-lane chain-minimal deficient anchor?

The producer uses cell-mask ideals and the independent checker uses row
heights. Both reconstruct recursively decomposable roots, discard contexts
already containing a strong eight-set, and separately compute ranks,
reflection, matching bottlenecks, and minimum deficient anchors.

## Bounded result

The complete gate passes.

| Quantity | Count |
| --- | ---: |
| Compatible root contexts | 376,764 |
| Exact-rank frontier groups | 992,028 |
| Consecutive blocks | 1,953,566 |
| Block/hole checks | 2,606,420 |
| Nonvacuous holes | 2,096 |
| Zero-feasible-map holes | 2,604,324 |
| Profile failures | 0 |

Every nonvacuous hole has a singleton minimum deficient anchor. Thus all
2,096 selected anchors are automatically saturated lattice intervals in one
normalized endpoint lane. The minimum bottleneck slack is `+3`; the complete
histogram is `+3:128`, `+4:72`, `+5:80`, `+6:1800`, `+7:8`, and `+8:8`.

The producer and independent checker agree on checked-prefix digest
`b7b724e1fb238f9a05d4490ad1ba42ae15edfac1514518b24fb8f0c69ca94db7`.
The manifest SHA-256 is
`9970f6619e89bdddc3045c4a76127b99f4309e8fa88ef3bb8316dd46feaf15b1`.

## Claim boundary and consequence

This is bounded evidence for `k = 8` through support size eight, not an
arbitrary theorem. Because every surviving anchor is a singleton, this gate
does not test a path of positive length and supplies no evidence that longer
owner-labelled lane paths exist for larger supports or parameters.

Lean now proves the scalable statement separately: an explicit path of
`m + 1` strictly ordered lane anchors with `m` distinct adjacent-gap owners,
exhausting all block-small neighbors, is an inclusion-minimal deficient
anchor. Constructing that path from decomposable deep-split geometry remains
the open bridge.

## Reproduction

    python3 scripts/enumerate_block_large_reached_owner_all_roots_k8.py \
      --maximum-n 8 \
      --output data/derived/e3-block-large-reached-owner-all-roots-k8-n8.json
    python3 scripts/check_block_large_reached_owner_all_roots_k8.py \
      data/derived/e3-block-large-reached-owner-all-roots-k8-n8.json
