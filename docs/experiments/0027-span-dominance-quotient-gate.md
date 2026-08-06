# Span-dominance incidence quotient gate

## Question

Can the ambient endpoint identities in the exact span-rank footprint be
forgotten by retaining only a finite, `k`-dependent incidence type, while
preserving the singleton and two-root transitions already checked at `k = 6`?

The candidate was frozen only after Lean proved the four directional
dominance rules in `SpanDominance.lean`. It retains:

1. the histogram of exact cup/cap rank labels, with every multiplicity clipped
   at `k`;
2. for every endpoint pair, the sidewise Pareto-frontier tags licensed by the
   Lean dominance theorems;
3. the local type of every endpoint, recording whether each incident retained
   span is cup-active and/or cap-active at rank three and the frontier tags on
   that span; and
4. the multiset of endpoint-local types, again with multiplicity clipped at
   `k`.

Exact endpoint identities and the assignment of exact ranks above three to
individual spans are forgotten. Exact rank multiplicities survive only in the
global clipped histogram.

## Why the carrier is `k`-only

There are `4(k-3)` possible directional color/rank frontier tags. Hence there
are at most `3 * 2^(4(k-3))` active coarse span labels: one of cup-only,
cap-only, or both, together with a tag subset. An endpoint type is a subset of
two endpoint roles times this finite label set. The state is a clipped count
for every such endpoint type plus a clipped exact-rank histogram. This gives
a finite carrier depending on `k`, although the resulting elementary bound is
far too large to imply the desired Erdős--Szekeres formula.

The checked Python encoding uses one-byte rank labels and therefore materializes
256 histogram bins. That is an implementation choice for the bounded `k = 6`
gate, not the proposed abstract Lean carrier.

## Small gates

The producer reuses the prior raw machine tables only after verifying every
table digest. The independent checker imports neither the producer nor its
quotient encoder and reconstructs every parent directly from coloring bits.

At the eight-vertex singleton boundary:

- 186,888 decomposable colorings;
- 46,699 raw footprint classes;
- 46,619 quotient classes;
- 80 quotient fibers merge distinct raw footprints;
- both committed all-gap and pair-rank regressions remain separated; and
- all 3,363,984 singleton transitions have zero quotient collisions.

At the prior seven-vertex two-root boundary, the quotient is still injective
on the 4,737 raw classes. All 762,912 transitions, including all 720,528
interleaved transitions, have zero quotient collisions. The independent
checker agrees on every context, class statistic, source hash, and digest.

## Larger raw gate

The reserved `8+2 -> 10` raw census is now complete. It covers all 186,888
children, 90 two-root contexts, and 16,819,920 parents, of which 16,072,368
are interleaved. The raw endpoint-span footprint has:

- zero observation-readout mismatches;
- zero transition collisions; and
- 46,699 child footprint classes.

The independent checker regenerates all children and parents without reading
the producer's 774 MiB ignored machine tables and agrees exactly with the
compact manifest.

## Quotient refutation

The quotient has 80 nontrivial fibers, each containing two raw footprint
classes. Raw congruence handles all colorings within a raw class, so the
quotient-specific large gate needs only two representative parents per fiber
and context: 14,400 direct evaluations rather than another 16.8 million.

This gate finds **320 quotient transition collisions**. The first collision
has child colorings

```text
329ff2bd0ffa3d
329ff7fd057a11
```

and lower roots at positions `[1,2]`. The child raw footprints differ only by
swapping codes `34` and `33` between endpoint pairs `(0,7)` and `(1,7)`. Their
global exact-rank histograms and coarse endpoint-incidence quotient agree.
After adjoining the roots, the parent footprints differ at `(3,9)`, so their
exact-rank histograms and quotient states differ. The independent compact
checker reproduces all 320 collisions and the representative-parent digest.

All failing contexts use the first or last internal child gap. Exploratory
repairs that retain exact boundary incidence reduce the collision count, but
clipped exact-rank counts strong enough to remove the remaining failures make
the quotient injective on all 46,699 observed raw classes. Those repair probes
are diagnostic calculations, not promoted certificates.

## Disposition

The coarse incidence quotient is rejected. It supplies a genuine `k`-only
carrier and passes the smaller gates, but it is not a transition congruence.
The obvious boundary repair restores essentially the ambient endpoint data at
this first nontrivial level and therefore does not solve the uniform-state
problem.

The raw footprint itself has stronger positive evidence after the complete
`8+2 -> 10` gate. What remains missing is a nonvacuous uniform quotient or a
different use of the raw footprint inside a structural counting argument. A
bounded Sol/Fable review must select the next precise theorem or falsifier
before this route changes again.

## Reproduction

```console
python3 scripts/enumerate_span_dominance_quotients.py \
  --singleton-run-directory runs/e3-span-rank-footprint-k6-n9 \
  --two-root-run-directory runs/e3-two-root-span-k6-n9 \
  --output data/derived/e3-span-dominance-quotient-k6-n9.json
python3 scripts/check_span_dominance_quotients.py \
  data/derived/e3-span-dominance-quotient-k6-n9.json --workers 8

python3 scripts/enumerate_two_root_span_footprints.py \
  --child-size 8 --strong-size 6 --workers 8 \
  --run-directory runs/e3-two-root-span-k6-n10 \
  --output data/derived/e3-two-root-span-k6-n10.json
python3 scripts/check_two_root_span_footprints.py \
  data/derived/e3-two-root-span-k6-n10.json --workers 8

python3 scripts/enumerate_large_span_dominance_quotient.py \
  --output data/derived/e3-span-dominance-quotient-k6-n10.json
python3 scripts/check_large_span_dominance_quotient.py \
  data/derived/e3-span-dominance-quotient-k6-n10.json
```
