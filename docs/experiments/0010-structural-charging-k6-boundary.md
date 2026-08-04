# Structural charging at the first `k = 6` boundary

## Status

The first consequence compiles in Lean. It identifies a seven-vertex deficit,
not a new upper bound for the exact conjecture.

## Extracted charge

The reusable output of the singleton-anchor argument is endpoint avoidance.
If no `a`-cap in the upper child has the external anchor `q` as a sweep
endpoint, then neither of the two sweep-gap sides of `q` contains an `a`-cap.
`StructuralChargingBoundary.lean` proves this for arbitrary `a`, without a
certificate or realizability hypothesis.

At `(5,6,6)`, an endpoint four-cap would extend across the singleton root to a
parent five-cap. Thus an open parent makes both gap sides four-cap-free. The
already proved decomposable `(4,6,6)` theorem bounds each side separately by
11, yielding only

```text
1 + 11 + 11 = 23.
```

Lean proves this coarse singleton-root bound as
`HasDeepBelowSplit.singleton_root_card_le_twenty_three_at_six`.

## Interpretation

The diagonal threshold at `k = 6` is 16, so endpoint avoidance plus two
independent side bounds misses by seven vertices. This is the first exact
structural obstruction after the successful `k = 5` cup-block proof. At
`k = 5`, avoidance of endpoint three-caps makes both sides cups, and a direct
two-block lemma couples them. At `k = 6`, avoidance of endpoint four-caps only
makes the sides four-cap-free; treating them independently loses all
cross-gap correlation.

The next bounded gate must therefore formulate and test a coupled two-side
charge for four-cap-free decomposable blocks. Merely strengthening the unary
side cardinal estimate cannot close the seven-vertex deficit unless it uses
information from the opposite side.

## Stop rule

Do not propose a uniform recurrence until a coupled invariant both:

1. has a certificate-free witness interpretation and a Lean statement, and
2. reduces the singleton-root `k = 6` bound from 23 to at most 16.

A finite counterexample to a proposed coupling rejects that coupling; it does
not refute the Erdős--Szekeres conjecture.
