# Stable-ownership one-hole descent gate

## Question

Flexible adjacent meet/join uncrossing is locally true on the frozen reflected
candidate families but is formally insufficient to produce distinct
representatives. The next gate asks whether an exact hole-moving rule can
repair a partial representative system without consulting a known matching.

The initially proposed discrete-convex boundary energy was rejected before
execution. Its hole proxy and lane envelope were undefined; linear ideal-size
energy is invariant under meet/join, ordinary convex size energy increases on
incomparable ideals, and a meet/join replacement can collide with a third
representative.

## Frozen ownership rule

A state chooses one hole in the six-span cap/rank-three frontier and assigns
distinct untagged ideals to the other five spans from their full reflected
two-endpoint candidate families. The ideals are ordered by their weakly
decreasing row-boundary tuple, lexicographically from the empty boundary
upward, with the cell mask as a deterministic tie-break.

If a candidate of the hole is unused, the state is fillable and the process
stops. Otherwise the hole takes its first candidate. That ideal has a unique
current owner; the owner becomes the new hole. This transfer preserves
candidate membership and injectivity by construction. It uses only the
current partial assignment and the frozen boundary priority, not a completed
matching, Hall expansion, or graph distance.

## Frozen result

There are exactly 5,208 membership-filtered one-hole states, with counts

    252, 336, 2100, 2016, 252, 252

by hole position. Of these, 3,612 are directly fillable and 1,596 are blocked.
Every blocked state has hole index 2 or 3, the two singleton candidate
families `{full}` and `{empty}`. After one ownership transfer the new hole is
at index 0, 1, 4, or 5, whose candidate family has respectively 10, 7, 9, or
10 ideals. Because only five ideals are occupied, the new hole is immediately
fillable. Thus every state terminates after at most one transfer; the complete
functional graph has no directed cycle.

The producer reconstructs lower ideals as cell masks. The independent checker
reconstructs them as weakly decreasing row-height tuples. Both enumerate all
5,208 states, apply the boundary priority and ownership transfer independently,
and agree on every aggregate and the absence of cycles. The manifest SHA-256
is `40f347c89e3cc13eec38def2d8ea4164a09172b86120d2782bd7f5275cad6acd`.

## Lean promotion and claim boundary

`StructuralChargingTransitionHallHoleDescent.lean` proves the reusable
mathematics behind this gate:

- an unused candidate completes a one-hole state to an SDR;
- more hole candidates than occupied representatives force an unused one;
- transferring an owned candidate to the hole preserves membership and
  injectivity;
- a transfer into a sufficiently large family is immediately fillable; and
- any well-founded strict progress relation from every unfillable state yields
  an SDR and the corresponding Hall inequality.

Those generic theorems compile without `sorry`. The exact frozen candidate
family cardinalities and the 5,208-state classification remain independently
replayed computational evidence, not a Lean proof of the frozen Hall instance
and not a theorem for arbitrary frontiers. The next proof-design question is
whether actual reflected frontier geometry always forces an analogous
small-to-large ownership transfer, possibly after a locally certified
uncrossing step.

## Reproduction

    python3 scripts/check_stable_ownership_hole_descent.py \
      --output data/derived/e3-stable-ownership-hole-descent-frozen-n12-k7.json
    python3 scripts/replay_stable_ownership_hole_descent.py \
      data/derived/e3-stable-ownership-hole-descent-frozen-n12-k7.json
