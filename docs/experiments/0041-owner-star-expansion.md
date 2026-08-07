# Feasible owner-star expansion gate

## Question

The two-step gate can forget most of a one-hole state.  If a state is blocked,
each ideal in the hole family has a unique current owner, and these owners are
distinct.  Does the stronger following property hold on every frozen
consecutive block?

For every hole and every injective membership-feasible map from its candidate
ideals to distinct non-hole spans, take the union of the hole family and all
mapped-owner families.  Is that owner-star union at least as large as the
block?

This quantifies over maps that may not extend to a partial representative
system.  It is therefore a stronger falsification gate than experiment 0040,
not a restatement of its successful states.  The empty map is included when a
hole family is empty.

## Frozen result

The gate passes.  Across all 62 nonempty consecutive blocks, only 247
injective membership-feasible owner maps exist.  Every owner-star union has at
least the block cardinality.  The minimum slack is `+1`.

| Group | Feasible owner maps | Minimum slack |
| --- | ---: | ---: |
| cap, rank 3 | 30 | `+1` |
| cap, rank 4 | 0 | vacuous |
| cup, rank 3 | 217 | `+2` |
| cup, rank 4 | 0 | vacuous |

The first minimum cap witness is the full six-span block with the singleton
hole at local index 2.  Its sole ideal `3f` maps to owner index 1, whose family
makes the star union have seven ideals.  The first minimum cup witness is the
full seven-span block with hole family `{0,1,9}` at local index 4; mapping these
ideals to owners 3, 6, and 2 gives a nine-ideal star.

The cell-mask producer and independent row-height replay agree on every
block, hole, feasible map, star union, slack histogram, and witness.  The
manifest SHA-256 is
`ac49dbc95b02951a3bc3482963473c412d1a3684a421fe3f1abed720422a4fe0`.

## Formal implication and claim boundary

Lean now defines the canonical `reachedOwners` of an actual state and its
`ownerStar`.  It proves that a blocked state satisfying owner-star expansion
has a two-step augmenting exit.  The proof is a cardinality contradiction: if
the actual owner-star were closed, it would lie in the used set of exactly
`block.card - 1` ideals.

The Lean theorem must use actual current owners.  Mere membership-feasible
ownership does not imply a two-step exit for an individual state.  The finite
gate may quantify over every feasible map because that stronger domain
contains every map induced by a blocked state.

This result remains bounded computational evidence at one frozen root.  It
does not prove owner-star expansion for arbitrary genuine reflected blocks,
Hall for arbitrary subfamilies, the global transition injection, or the exact
Erdős--Szekeres formula.  The next structural target is to derive the star
inequality from reflected boundary-slot intervals and consecutive endpoint
order.  A proof that imports Hall or a completed SDR is circular.

## Reproduction

    python3 scripts/check_owner_star_expansion.py \
      --output data/derived/e3-owner-star-expansion-frozen-n12-k7.json
    python3 scripts/replay_owner_star_expansion.py \
      data/derived/e3-owner-star-expansion-frozen-n12-k7.json
