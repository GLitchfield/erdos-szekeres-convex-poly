# Experiment 0106: geometric right-extension fibers through six

## Question

For a fixed sweep-ordered point realization, can the complete set of colors
created by a new point to its right be reconstructed from the old pair-line
arrangement?  How does that fixed fiber compare with the abstract
`LastExtensionCompatible` fiber of the parent coloring?

The experiment concerns child sizes four, five, and six.  It makes no
seven-point claim and does not treat finitely many coordinate realizations as
the full union over a parent's realization space.

## Frozen representation

For every old pair, bit one means positive orientation, equivalently that the
new point lies above the labeled pair-line.  The wiring consists of:

- canonical pair labels in lexicographic pair-bit order;
- the bottom-to-top line order immediately right of the largest old
  abscissa;
- all later crossing abscissas in strict order; and
- at one common abscissa, the disjoint concurrent blocks in bottom-to-top
  order.

All blocks at one crossing slice reverse simultaneously.  Prefixes are sampled
only before or after the complete slice, so the replay does not invent phantom
cells between simultaneous crossings.

## Method

The producer independently enumerates every abstract compatible pair link and
every full-dimensional cell of the right-half-plane line arrangement for the
frozen exact-rational realization cohorts.  It records a rational witness,
cell sign mask, Hamming-one adjacency, and the frozen wiring.

The checker uses exact vertical-slab probes and separately rebuilds the wiring
replay.  It first reconstructs the 1,550 cells in the earlier fixed-extension
certificate before admitting new atlas outcomes.  Its corruption suite changes
a coordinate, line label, sign mask, cell, adjacency edge, and wiring slice.

## Results

| Child size | Parents | Abstract edges | Realizations | Cells | Sensitive parents |
| --- | ---: | ---: | ---: | ---: | ---: |
| 4 | 2 | 8 | 91 | 364 | 0 |
| 5 | 8 | 62 | 112 | 825 | 4 |
| 6 | 62 | 908 | 124 | 1,550 | 43 |

All 327 adjacency graphs are connected.  Every wiring collision class has one
fixed-fiber hash, and wiring replay equals direct cell enumeration for all
2,739 cells.  Every abstract compatible link is a permutation inversion set;
that is an abstract OneChange sanity check rather than an additional geometric
restriction.

The sampled-union abstract gaps are zero for child sizes four and five.  At
child size six, the gap histogram over 62 parents is
`0:18, 1:24, 2:9, 3:9, 4:1, 5:1`, for 78 missing abstract links in aggregate.
These are sample gaps, not proofs that the links are geometrically impossible.

The producer used 8.73 seconds and 33,472 KiB RSS; the checker used 1.94
seconds and 40,060 KiB RSS.  A fresh run was byte-identical.  The certificate
SHA-256 is
`f58ce6173b1051455fe245561e5e63b90523e83991cd55fae2e803564d0b569d`;
the check report SHA-256 is
`6090dffccf11c4880de5656511d95fec7dcfee79c93ba38d192e126c81b876a1`.

The deterministic tracked scripts are
[`analyze_geometric_extension_fibers.py`](../../scripts/analyze_geometric_extension_fibers.py)
and
[`check_geometric_extension_fibers.py`](../../scripts/check_geometric_extension_fibers.py).

## Interpretation

The enriched wiring is exact fixed-coordinate infrastructure, not a compressed
parent invariant and not a characterization of `GeometricRightExtensionFiber`.
The experiment changes no load-bearing proof edge.  Its useful search
information is negative: a future recurrence must retain simultaneous crossing
structure, must not use one representative for an order type, and must supply
a consumer-defined compression before extending this census to seven.
