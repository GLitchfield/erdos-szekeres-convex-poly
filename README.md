# Erdős--Szekeres convex-polygon formal research

This project attacks the exact Erdős--Szekeres happy-ending conjecture. Its
standard of completion is intentionally strict: a mathematical result counts
as complete only when the exact statement has a compiling Lean 4 proof.

For every `n ≥ 3`, let `ES(n)` be the least number such that every set of
`ES(n)` planar points in general position contains `n` points in convex
position. The target is

```text
ES(n) = 2^(n - 2) + 1.
```

The repository does not assume this conjecture. Stronger, relaxed, and abstract
variants are supporting material only when they advance this exact target. The
first strategic task is to choose the canonical formal model and the first
attack milestone without losing the connection to realizable planar point
sets.

## Current state

- Lean 4 and mathlib are pinned at `v4.29.1`.
- `ErdosSzekeres/Basic.lean` defines orientation, planar general position,
  convex position via convex hull, the forcing predicate, and the classical
  conjecture as an unproved proposition.
- `ErdosSzekeres/Sweep.lean` formalizes the sweep ordering, ordered triple
  coloring, increasing restrictions, cups/caps, and the bridge from left/right
  turns to slope changes.
- `ErdosSzekeres/Chains.lean` proves that, for sweep-realizable colorings,
  checking consecutive triples is equivalent to the all-triples cup/cap
  definition.
- `ErdosSzekeres/Presentation.lean` constructs a generic determinant-one shear
  and sorted sweep presentation for every finite general-position point set.
- `ErdosSzekeres/Convexity.lean` proves the orientation-sign triangle test, a
  purely sign-based convexity certificate for four points, and the
  local-to-global theorem reducing finite convex position to four-point
  subsets.
- `ErdosSzekeres/StrongPolygon.lean` defines the four-index strong-polygon law
  and proves it equivalent to convex position for swept configurations and
  for their original finite point sets, including selected convex subsets.
- `ErdosSzekeres/ES5Certificate.lean` proves the exact result `ES(5) = 9`.
  Its finite upper-bound certificate is checked from a committed LRAT trace,
  with a compiling Lean bridge from all 2,016 clauses to the sweep axioms.
- `ErdosSzekeres/E3State466Certificate.lean` and
  `ErdosSzekeres/E3State566Certificate.lean` kernel-check the two finite E3
  states needed at six vertices. Every twelve-vertex one-change coloring has a
  four-cap, a six-cup, or a strong six-set, and every sixteen-vertex
  one-change coloring has a five-cap, a six-cup, or a strong six-set.
  `E3FiniteReduction.lean` lifts these certificates to hereditary bounds and
  proves `decomposableExactUpperAt_six : DecomposableExactUpperAt 6`.
  The 155,064-clause state-566 bridge is split into bounded Lean modules and
  replayed structurally by an independent whole-data checker.
  This is the exact upper formula for the abstract recursively decomposable
  class at `n = 6`; it is not a proof of the unrestricted planar case or of
  the uniform all-`n` decomposable theorem.
- `ErdosSzekeres/E3State455Certificate.lean` kernel-checks the eight-vertex
  boundary state exposed by the failed published induction.
  `decomposableStateUpper_455` and its color dual prove the hereditary
  `(4,5,5)` and `(5,4,5)` bounds without a realizability assumption. This
  confirms that the `8 > 7` regression is a proof-method defect, but does not
  yet supply a uniform inductive transition.
- The exact all-root context census independently replays every decomposable
  coloring through eight leaves and every compatible root.  It refutes local
  and cross-anchor maxima summaries as composition states.  A compact
  `k = 6`, `n = 9` singleton-root certificate then refutes even the complete
  all-gap maxima word: equal open child profiles can produce unequal parent
  profiles.  This is a bounded, independently checked redirect toward a
  correlation-preserving rank/downset state, not yet a Lean theorem or an
  all-`n` proof. The next exact singleton-root gate now also refutes both the
  ordered vertex-downset word and the complete child pair-rank matrix as
  deterministic parent states. Raw downsets stay vertex-injective in all
  85,797 covered open parents, but their observed compatibility graph has a
  27-clique, so pairwise incompatibility alone cannot yield the required
  16-state bound. `RankProfileCollision.lean` now kernel-checks the complete
  pair-rank collision and proves both witnesses are induced by explicit
  rational planar configurations. Straight-line sweep realizability therefore
  does not repair this deterministic child-state transition.
- `ErdosSzekeres/DecomposableRealization.lean` closes the abstraction boundary
  for the entire recursive class. Its fixed-abscissa merge theorem vertically
  shifts arbitrarily interleaved deep-below children while retaining both
  internal colorings, and `IsDecomposable.isSweepRealizable` constructs a
  genuine planar configuration in general position for every abstract
  decomposable coloring. This strengthens the negative diagnosis: no extra
  realizability restriction inside this class can repair the pair-rank state.
  It realizes the induced coloring; it does not assert that the same tree
  satisfies the stronger coordinate-level `IsGeometricallyDeepBelow`
  predicate, nor supply the missing uniform `2^(n-2)` counting argument.
- `ErdosSzekeres/ContextProfile.lean` defines fixed-ambient sweep gaps and the
  three directional chain relations.  Its compiling monotonicity lemmas prove
  that a directional cup or cap witness survives enlargement without any
  hidden relabeling or gap transport.  The explicit profile-collision pair is
  not yet kernel-checked in Lean.
- `ErdosSzekeres/RankProfile.lean` gives a specification-first interface for
  consecutive pair ranks and clipped vertex downsets. Its compiling lemmas
  prove ambient-set monotonicity, threshold antitonicity, the rank-one base,
  and lower-rectangle closure for arbitrary triple colorings. Its executable
  recurrence is proved equivalent to the original `CupCap.IsTurnChain`
  pair-rank specification.
  `RankProfileCollision.lean` proves the bounded realizable non-congruence,
  including decomposability, openness, and exact rational realizations.
- `ErdosSzekeres/TurnLanguage.lean` defines complete bounded consecutive-turn
  languages at ordered endpoint pairs. Its executable predecessor recurrence
  is proved equivalent to increasing-chain semantics, and its constant-turn
  corollary identifies the incoming endpoint star needed when a new pair is
  formed. It now also defines incoming-star and prefix spectra and proves their
  cut causality and depth-truncation laws. `TurnLanguageCollision.lean`
  kernel-checks an open decomposable
  seven-vertex collision: the two lower endpoint-forgetting spectra agree
  through depth four, but the parent spectra differ by the word
  `right,right,left` at `(5,6)`. Grouping languages by terminal endpoints
  separates this witness. An independently replayed `(k,d)=(6,4)` gate has no
  incoming-star prefix or parent-transition collision through eight vertices.
  `IncomingStarPositive.lean` supplies a nontrivial positive regression, while
  `IncomingStarPrefixCollision.lean` proves that generic depth-three prefix
  recovery is false. `IncomingStarTransition.lean` proves the uniform
  crossing-pair transition and its congruence consequence; same-child pairs
  in the enlarged parent ambient set are a genuine obstruction.
  `IncomingStarTransitionCollision.lean` proves that equal child spectra and
  every root-relevant prefix can yield unequal parent spectra, including when
  both parents are recursively decomposable. Both witnesses contain a strong
  six-set. The deterministic incoming-star quotient route is therefore
  stopped; no uniform incoming-star spectrum transition is claimed.
- `ErdosSzekeres/StructuralCharging.lean` begins the selected replacement
  route without introducing another state carrier. It proves an asymmetric
  saturation incompatibility and reduces the reviewed seven-vertex
  upper-child gap trichotomy to one explicit `3+4` consecutive-cup-block
  lemma under the rank-three one-change law. It also proves that the
  trichotomy yields the certificate-free singleton-root `(4,5,5)` cardinal
  bound. `StructuralChargingCore.lean` proves the normalized ordered `3+4`
  core by seven symbolic turn branches and reusable one-change propagation;
  it imports no generated certificate and does not enumerate coloring space.
  Transport from normalized `Fin 7` coordinates to arbitrary blocks, including
  the mirrored `4+3` order, is the remaining obstruction to closing the stated
  cup-block theorem.
- `ErdosSzekeres/Extremal.lean` constructs the classical `2^(n-2)`-point
  lower-bound examples for every `n ≥ 3`.
- `docs/formalization_plan.md` records the intermediary lemma ladder from the
  sweep model to the exact conjecture.
- `docs/literature_review.md` records the initial research synthesis.
- `docs/bibliography.md` is the living source ledger.
- `docs/wayfinder/tickets/0001-choose-formal-model.md` is the first open
  strategic decision.

## Build

```console
make update
lake build
make test
python3 scripts/wayfinder_status.py
```

`make update` supplies a repository-local `unzip` compatibility command needed
by LeanHammer's ATP setup on machines without the system utility. See
[`docs/automation.md`](docs/automation.md) for the proof-search workflow and
trust policy.

No theorem containing `sorry` or `admit` is accepted by the test gate.
The `ES(5)` CNF and its generated Lean bridge can be reproduced with

```console
python3 scripts/generate_es5_sat.py certificates/es5-signotope.cnf \
  --lean ErdosSzekeres/ES5CNFGenerated.lean
```

Regenerating the LRAT trace additionally requires a solver capable of emitting
LRAT; the committed trace itself is checked during `lake build`.

## Layout

```text
ErdosSzekeres/              Lean source
docs/formalization_plan.md intermediary lemma ladder and proof boundaries
docs/literature_review.md  research synthesis and candidate directions
docs/bibliography.md       primary-source ledger
docs/wayfinder/            durable strategic map and tickets
docs/experiments/          designed computational experiments
data/reference/            metadata for authenticated external inputs
data/derived/              compact certificates and verified results
runs/                      ignored machine-local work
```

This repository was initialized from `open-math-research-template` and is MIT
licensed; see `LICENSE` and `NOTICE`.
