---
title: Test E3 and select a repair strategy
type: research
mode: AFK
status: open
claim: codex-e3-adversarial-2026-08-01
blocked_by: none
---

## Question

Is `DecomposableExactUpperAt k` true for the repository's abstract recursive
deep-below model for every `k ≥ 3`, and, if so, which strengthened invariant
has the best bounded evidence for repairing the failed published induction?
If it is false, what is the smallest counterexample, and is that counterexample
sweep-realizable by an actual planar point configuration?

## Decision criteria

- Treat the truth and falsity directions symmetrically.  A search that only
  reproduces expected extremal examples cannot select the proof route.
- Use the exact repository definitions of `HasDeepBelowSplit`,
  `IsDecomposableOn`, cup, cap, and strong polygon.  Record separately whether
  a generated abstract coloring satisfies the signotope law and whether it is
  known to be realizable by straight-line planar points.
- First perform an exact exhaustive enumeration at the largest feasible small
  size, deduplicating colorings rather than merely sampling decomposition
  trees.  The producer and independent checker must not import one another.
- The default computation budget is 30 minutes, 8 CPU cores, 16 GiB RAM, and
  5 GiB under `runs/`.  Deterministic shards, seeds, conventions, and coverage
  counts are required.
- A counterexample branch advances only with a compact coloring/decomposition
  certificate independently checked against every defining predicate.  It
  refutes the repository's E3 statement only if sweep realizability is also
  certified; otherwise it redirects the abstraction boundary.
- A proof branch advances only when a candidate invariant survives exhaustive
  small cases, explains the `(4,5,5,1,3)` boundary regression, has an explicit
  inductive transition, and yields a nontrivial compiling Lean lemma.  Pattern
  agreement or reviewer consensus is not enough.
- Classify an inconclusive search by its exact coverage bound.  Do not infer
  the all-`k` theorem from a finite negative search.
- Before selecting the route, obtain a bounded blind and reciprocal Sol/Fable
  review of the evidence packet, then independently dispose of every material
  objection.

## Candidate strategies under review

1. **Endpoint-profile injection.** Refine the scalar cup/cap maxima by left and
   right endpoint-extension states, and inject vertices or recursive blocks
   into the `2^(k-2)` binary profiles.
2. **Rank-downset compression.** Start from the classical injective map from a
   sweep vertex to its cup/cap predecessor downset.  Search for the additional
   pairwise restriction imposed by recursive deep-below structure and absence
   of a strong `k`-gon.
3. **Context-carrying induction.** Repair the three-parameter recurrence by
   carrying an external cup/cap supplied by ancestor blocks.  A saturated
   off-diagonal child must pay for the binomial term that currently overflows.
4. **Minimal-counterexample descent.** Assume a smallest E3 counterexample,
   choose its root split, and use the exact crossing characterization plus
   saturation/straddling lemmas to contradict minimality or expose a smaller
   rooted counterexample.
5. **Falsification.** Enumerate recursive colorings and optimize/SAT-search for
   more than `2^(k-2)` vertices with no strong `k`-gon, then separately test
   signotope and straight-line realizability constraints.

## Resolution

Open.  The published scalar induction cannot be used: Lean checks a boundary
instance where the claimed two contributions are eight and the outer threshold
is seven.  Local endpoint transitions compile, but no global profile count has
yet been proved.  This ticket deliberately reopens the theorem's truth value
instead of assuming that an endpoint repair must exist.

The first falsification round is complete through eight leaves.  Independent
implementations agree on 186,888 distinct eight-leaf colorings, none of which
contradicts the proposed five-vertex base lemma.  All recursively decomposable
colorings are now proved in Lean to satisfy the signotope law, and the existing
nine-point LRAT certificate consequently proves
`decomposableExactUpperAt_five`.  The all-`k` statement remains open; the
reciprocal Sol/Fable route review and the general anchor-context transition are
still pending.

## Evidence

- [`ErdosSzekeres.Decomposable`](../../../ErdosSzekeres/Decomposable.lean)
- [Formalization plan](../../formalization_plan.md)
- [Literature review](../../literature_review.md)
- [Profile-search prototype](../../../scripts/decomposable_profile_search.py)
- [Exact coloring producer](../../../scripts/enumerate_decomposable_colorings.py)
- [Independent enumeration checker](../../../scripts/check_decomposable_enumeration.py)
- [Exact enumeration design and results](../../experiments/0002-e3-adversarial-design.md)
