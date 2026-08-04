# Exact Erdős--Szekeres formula decision map

## Destination

Produce a compiling Lean 4 proof that, for every `n ≥ 3`, the least number of
planar points in general position that forces `n` points in convex position is
`2^(n-2) + 1`. The proof must include both the universal upper bound and a
sharpness construction of size `2^(n-2)`.

## Notes

- Domain: extremal combinatorial geometry, order types, and finite Ramsey
  theory, formalized in Lean 4 with mathlib.
- Evidence standard: see `docs/reproducibility.md`.
- The map may carry bounded execution when a ticket predeclares its inputs,
  resource limit, outcome branches, and independent certificate.
- Strategic selection, redirection, closure, and frontier promotion receive a
  bounded Sol/Fable review under `docs/adversarial-review.md`.

## Decisions so far

<!-- One linked, one-line gist per closed ticket. Detail stays in the ticket. -->

None. The destination was fixed by the user on 2026-08-01.

## Open frontier

- [Choose the canonical formal model](tickets/0001-choose-formal-model.md)
  before committing the proof architecture to Euclidean geometry, ordered
  configurations, or a verified two-layer representation.
- [Test E3 and select a repair strategy](tickets/0002-test-e3-and-select-repair.md)
  by kernel-checking the bounded pair-rank non-congruence witness, then
  designing a higher-order predecessor-correlation invariant or a precise
  realizability-sensitive transition. The scalar recurrence, maxima-only
  contexts, deterministic downset words, complete child pair-rank matrices,
  and pairwise raw-downset counting shortcut are now refuted routes; abstract
  decomposability and planar realizability are both kernel-checked for the
  complete pair-rank collision. In fact every abstract recursively
  decomposable coloring is now proved sweep-realizable, so realizability
  supplies no further restriction anywhere inside this class and cannot
  repair the transition. The first higher-order repair, the endpoint-forgetting
  pair turn-language spectrum, is now also refuted by a kernel-checked open
  seven-vertex collision. Lean proves its chain semantics and predecessor
  recurrence; the collision isolates terminal-endpoint incidence as the lost
  datum. The incoming-star spectrum now passes an independently replayed
  `(k,d)=(6,4)` prefix-control and parent-transition census through eight
  vertices. Lean proves its cut causality and depth restriction, as well as a
  nearby open depth-three prefix collision showing that parameter-free prefix
  recovery is false. The clean conditional transition is now refuted by a
  kernel-checked nine-vertex collision, even with both parents recursively
  decomposable: equal child spectra and every relevant prefix can yield
  unequal parent spectra. Both witnesses contain a strong six-set, so an
  open-only implication remains logically possible, but it no longer
  separates transition sufficiency from the target property. The
  deterministic quotient-refinement route is stopped. The next bounded route
  decision selects structural charging. The normalized ordered `3+4`
  seven-vertex cup-block core now compiles by a seven-branch symbolic proof,
  and order-embedding transport plus reversal closes both arbitrary `3+4` and
  `4+3` blocks. The certificate-free upper-child gap trichotomy and resulting
  singleton-root cardinal bound seven now compile. The next obstruction is to
  extract its gap-side charge and test that invariant at the first `k=6`
  boundary before proposing a uniform recurrence. The endpoint-avoidance
  charge now compiles in arbitrary cardinality. Applied independently to the
  two sides with the `(4,6,6)` theorem, it yields only 23 against the diagonal
  threshold 16. The next bounded target must retain cross-gap correlation and
  close this seven-vertex deficit.

## Not yet specified

- A kernel-checked formal reproduction of the classical lower-bound
  construction for all `n`.
- A geometric/combinatorial equivalence layer for convex position, cups, caps,
  strong polygons, and realizable orientation configurations.
- Formal reproduction of the known exact cases `n ≤ 6` and extraction of the
  structural obstruction that first appears at `n = 7`.
- Formal use of the Erdős--Tuza--Valtr equivalence and the 2026 decomposable-set
  theorem to constrain a minimal counterexample.
- A new structural recurrence or decomposition theorem strong enough to close
  the gap between the lower construction and the best general upper bound.

## Out of scope

- Empty-polygon (hole), colored, higher-dimensional, convex-body, game, and
  projective variants are not independent destinations. They enter only when a
  precise lemma or formal technique advances the exact planar formula.
- Numerical evidence, SAT satisfiability/unsatisfiability, or an informal proof
  without a Lean kernel check cannot close the destination.
