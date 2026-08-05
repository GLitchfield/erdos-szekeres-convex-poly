# Endpoint-span rank footprint gate

Date: 2026-08-05

## Question and evidence boundary

The singleton residual oracle showed that an anchored all-gap maximum loses
correlation between the two endpoints of a near-threshold chain.  The bounded
Sol/Fable review therefore requested a precise critical-cut carrier, retained
endpoint incidence, and a singleton self-composition test before route
selection.

This experiment asks a deliberately narrower question:

> If an open coloring records the maximum cup and cap length having each exact
> ordered endpoint pair, does that record determine both the complete
> property-relative singleton observation and its record after adjoining one
> deep-below singleton root?

The answer is yes for every recursively decomposable coloring at the exact
`k = 6`, `8 -> 9` gate.  This is independently replayed bounded computation,
not a uniform transition theorem, a `k`-only state bound, or a proof of the
Erdős--Szekeres conjecture.

## Corrected critical-cut semantics

For a fixed nonempty chain, the singleton positions at which the chain can be
extended form the union of a left ray and a right ray.  The union need not be
order-convex.  `ErdosSzekeres/RootedChainFootprint.lean` makes the missing
endpoint side explicit and proves:

- the left-endpoint state is downward closed;
- the right-endpoint state is upward closed;
- the states are disjoint for an external singleton; and
- forgetting the side recovers the existing exact cup/cap singleton-extension
  iff.

It also gives the concrete set `{1, 3}` in `Fin 5`: positions `0` and `4` are
sweep endpoints, while position `2` is not.  Thus the review's proposed
unsplit interval-convexity lemma is false; the correct carrier is a pair of
side-labelled rays.

## Span-rank record

For every ordered pair `a < b`, an open record stores two values clipped below
the target `k`:

- the largest cup whose first vertex is `a` and last vertex is `b`; and
- the largest cap with those exact endpoints.

A coloring already containing a strong `k`-set is represented by one terminal
symbol.  At child size eight the open record has 28 endpoint-pair bytes plus a
status byte; at parent size nine it has 36 pair bytes plus a status byte.  The
record retains the two-gap endpoint correlation missing from the earlier
consecutive pair-rank matrix, while forgetting all internal witness vertices.

The ordinary all-gap observation is a direct readout: a gap sees a chain to
its left, to its right, or straddling it solely from the chain's two retained
endpoints.  The producer and checker nevertheless evaluate that readout
against a direct subset definition for every child and every parent.

## Exact result

The producer enumerates all 186,888 decomposable eight-vertex colorings and
all 18 singleton contexts (nine insertion positions and both root roles), for
3,363,984 parent transitions.  It finds:

- 46,699 child span-rank footprints;
- 24,041 nontrivial footprint classes;
- 22,658 singleton footprint classes;
- one terminal class of size 63,982;
- zero child observation-readout mismatches;
- zero parent observation-readout mismatches; and
- zero singleton transition collisions.

The footprint separates both committed regressions: the all-gap collision and
the complete consecutive pair-rank collision have unequal child footprints.
Parent footprint counts range from 18,365 at the middle insertion gap to
29,144 at an extreme gap, with the expected reversal/color symmetry.

`scripts/enumerate_span_rank_footprints.py` uses precomputed bit masks and the
existing bottom-up coloring enumerator.  The independent
`scripts/check_span_rank_footprints.py` imports neither producer, regenerates
the coloring family recursively, tests every chain and strong set directly,
reconstructs every singleton parent independently, and agrees on every source
hash, context digest, collision count, class statistic, and regression.

## Interpretation

This is the first structured endpoint-incidence state in the new-invariant
fallback that passes both required singleton gates.  It explains the previous
failures: an insertion response depends on the total span of a chain, not only
on a consecutive terminal pair or on maxima after forgetting which two gaps
bound the witness.

It does **not** yet solve the counting problem.  The raw carrier has one entry
per ambient endpoint pair, so its representation grows quadratically with the
number of vertices.  Its 46,699 observed classes also exceed the 7,159-class
one-step residual oracle.  It is valuable because it has a local mathematical
meaning and apparent composition law, not because the raw record is already a
small quotient.

The next gates are therefore:

1. prove the singleton span-rank transition from the side-labelled endpoint
   extension iff in Lean;
2. test the record under the pre-vetted two-vertex interleaved-root contexts;
3. define and falsify a dominance quotient that removes ambient endpoint
   identities while preserving the transition; and
4. only then seek a `k`-only weight bounded by `2^(k-2)`.

No uniform route is selected until the interleaved-root and `k`-only gates
survive.

## Reproduction

```console
python3 scripts/enumerate_span_rank_footprints.py \
  --child-size 8 --strong-size 6 --workers 8 \
  --run-directory runs/e3-span-rank-footprint-k6-n9 \
  --output data/derived/e3-span-rank-footprint-k6-n9.json
python3 scripts/check_span_rank_footprints.py \
  data/derived/e3-span-rank-footprint-k6-n9.json --workers 8
```

The compact manifest SHA-256 is
`74a0d2bb8de0419d51921d2c2edcb4a30532e1fde4d8a210743b7a86c414d12a`.

Large parent tables remain under ignored `runs/`; the checker does not read
them.

## Subsequent status

Experiment 0026 completes the uniform singleton transition bundle in Lean and
independently replays all 762,912 parents in the smallest feasible two-vertex
root gate, including 720,528 interleaved transitions. It finds zero footprint
collisions. The pending obstruction is therefore the ambient-free dominance
quotient and its `k`-only weight, not another undefined singleton refinement.
