# Uniform singleton transition and two-root span-footprint gate

Date: 2026-08-05

## Question and evidence boundary

Experiment 0025 established that exact endpoint-span ranks reconstruct every
property-relative observation and evolve without collision under all
`k = 6`, `8 -> 9` singleton roots. The bounded route review warned that a
singleton pass is not sufficient for arbitrary interleaved deep-below roots.
Its next required falsifier was the smallest feasible two-vertex interleaved
root census.

This package answers two separate questions:

1. What is the exact uniform mathematical transition behind the singleton
   computation?
2. Do equal child span footprints still produce equal parent footprints after
   adjoining a two-vertex root in every sweep placement and either root role?

The first answer is a compiling Lean theorem bundle. The second answer is yes
at the exact `k = 6`, `7 + 2 -> 9` boundary, independently replayed. The
finite census is evidence, not a Lean proof of congruence for all root sizes or
an all-`k` counting theorem.

## Uniform Lean transition

`ErdosSzekeres/RootedChainFootprint.lean` now defines:

- `HasSweepSpan chain a b`, saying that `a < b` are the exact retained sweep
  endpoints of a chain;
- `HasCupSpanRankAtLeast` and `HasCapSpanRankAtLeast`, the propositional
  threshold semantics of the computational footprint.

The file proves without a fixed cardinality or target parameter that:

- the left/right extension predicates are exactly the comparisons `q <= a`
  and `b <= q` once the total endpoints are retained;
- inserting a strict new left or right endpoint updates only that endpoint;
- an upper singleton raises a lower cup span rank, and a lower singleton
  raises an upper cap span rank;
- erasing the singleton gives an iff between a parent active-color chain and
  a child chain carrying the appropriate endpoint side;
- the opposite-color mixed contribution has cardinality at most three; and
- a parent strong `k`-set is either inherited from the child or is created by
  adjoining the root to a child `(k-1)`-cup or `(k-1)`-cap.

The last two clauses are necessary. A root of the “wrong” color can sit in the
middle of a three-vertex chain, and terminal strong closure is not captured by
the active endpoint-extension iff alone.

These theorems contain no `sorry`, project axiom, external certificate, or
fixed-`k` truth table. They supply the semantic singleton transition that the
review required, but they do not yet quotient away ambient endpoints.

## Two-vertex-root gate

The producer enumerates all 10,596 recursively decomposable colorings on seven
ordered vertices. For each coloring it adjoins a two-vertex root at every pair
of the nine parent positions and in both roles:

- the root is the lower child and the seven-vertex coloring is upper; or
- the root is upper and the seven-vertex coloring is lower.

There are 72 contexts and 762,912 parent transitions. A context is classified
as interleaved unless the two root vertices are the adjacent leftmost or
adjacent rightmost pair. Thus 68 contexts and 720,528 transitions are
interleaved; all are retained rather than symmetry-reduced.

Input equality means byte-identical child endpoint-span footprints, including
the terminal strong-six symbol. Failure means that equal inputs yield unequal
parent footprints under one fixed root placement and role. The parent record
is recomputed directly from all subsets; it is not obtained by iterating the
Lean singleton transition.

## Exact result

The child colorings realize:

- 4,737 span-footprint classes;
- 1,957 nontrivial classes;
- 2,780 singleton classes; and
- one largest class of size 1,442.

Across all parent transitions, the result is:

- zero observation-readout mismatches;
- zero footprint-transition collisions; and
- zero collisions on the 720,528 interleaved transitions specifically.

Parent footprint counts range from 270 to 707 across the 72 fixed contexts.

`scripts/enumerate_two_root_span_footprints.py` uses the optimized producer
semantics from experiment 0025. The independent
`scripts/check_two_root_span_footprints.py` imports neither producer. It uses
the prior independent checker semantics, regenerates the coloring family,
embeds the child by a separate routine, reconstructs every crossing color,
and agrees on every source hash, context digest, collision count, and summary
statistic. The 28 MiB parent tables remain under ignored `runs/`; the checker
does not read them.

## Interpretation and stop rule

The endpoint-span footprint has now passed:

1. direct property-observation readout;
2. every singleton root at the first `k = 6`, eight-vertex child boundary;
3. a uniform singleton transition theorem in Lean; and
4. every two-vertex root at the smallest feasible independently replayed
   interleaved boundary.

This is materially stronger evidence that retaining both total endpoints
captures the missing chain correlation. It still does not select the raw
footprint as the uniform E3 invariant. The record has one rank pair for every
ambient endpoint pair, and its carrier therefore grows with `n`.

The first dominance subobligation now compiles in
`ErdosSzekeres/SpanDominance.lean`: at a fixed far endpoint, a no-smaller rank
with a near endpoint farther toward the singleton supplies every extension of
the dominated span. This proves directional Pareto pruning sound for cups and
caps. It does not forget the far endpoint or prove a `k`-only bound.

The next task remains the previously required dominance quotient: forget
endpoint identities only after preserving the incidence needed by the
transition, then test quotient congruence on both committed collisions and
these singleton and two-root tables. A quotient is rejected immediately if
its carrier or weight still depends on ambient cardinality, if it merges
either committed regression, or if it produces a transition collision. Only
a surviving quotient with a proved `k`-only bound can promote this direction
to a selected uniform route.

The larger `k = 6`, `8 + 2 -> 10` census would contain 16,819,920 direct
parent transitions and is not claimed by this artifact. It should be run only
against a concrete quotient candidate, where it can provide a decisive gate
rather than unstructured depth.

## Reproduction

```console
python3 scripts/enumerate_two_root_span_footprints.py \
  --child-size 7 --strong-size 6 --workers 8 \
  --run-directory runs/e3-two-root-span-k6-n9 \
  --output data/derived/e3-two-root-span-k6-n9.json
python3 scripts/check_two_root_span_footprints.py \
  data/derived/e3-two-root-span-k6-n9.json --workers 8
```

The compact manifest SHA-256 is
`70d5f08c0bce7fb0ae7ef0748c59a19e81f0c1d002e077aa727877f4794b8a33`.
