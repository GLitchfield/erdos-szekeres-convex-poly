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
- The singleton-context residual oracle exhausts all 186,888 eight-vertex
  decomposable colorings and all 18 one-vertex root contexts at `k = 6`. An
  independent implementation agrees that 5,917 immediate open profiles
  refine to 7,159 residual classes. The oracle separates the known all-gap
  collision but not the complete pair-rank collision. This identifies
  interior near-threshold chain extension as the missing profile datum while
  rejecting the full truth table as a uniform invariant. The next design gate
  is a finite rooted-chain-footprint state with a `k`-only count and an
  all-root transition; no such theorem is claimed yet. A bounded Sol/Fable
  review agrees that this object should be specified and falsified next, but
  rejects selecting it until interval convexity, domination, endpoint
  incidence, and the `k`-only bound are made precise.
- `ErdosSzekeres/RootedChainFootprint.lean` corrects the first footprint
  premise: successful singleton cuts are generally two rays rather than one
  interval. It proves downward/upward closure after labelling the active
  endpoint side, disjointness for an external singleton, the exact cup/cap
  extension iff, and a concrete counterexample to unsplit convexity. The
  independently replayed endpoint-span rank gate then covers all 3,363,984
  `k = 6`, `8 -> 9` singleton extensions with zero observation-readout
  mismatches and zero transition collisions, separating both earlier profile
  regressions. The raw state is still ambient-quadratic (46,699 observed child
  classes), so the next obligations are a Lean transition theorem, the
  two-vertex interleaved-root gate, and a dominance quotient with a `k`-only
  bound; no uniform route is selected yet.
- The same Lean file now supplies the complete uniform singleton transition
  semantics for exact span ranks: active-color rank updates, erase/recover
  iff laws, the rank-three opposite-color exception, and terminal strong-set
  creation. An independent `k = 6`, `7+2 -> 9` census then checks all 762,912
  two-vertex-root parents, including 720,528 interleaved transitions, with
  zero observation mismatches and zero footprint collisions. This closes the
  smallest pre-vetted interleaved-root gate. The ambient-quadratic endpoint
  identities remain the active obstruction; the next candidate must be a
  transition-preserving dominance quotient with a proved `k`-only bound.
- `ErdosSzekeres/SpanDominance.lean` proves the first safe quotient operation.
  For either active chain color and either extension direction, a no-smaller
  span rank at a more favorable near endpoint dominates every singleton
  response of the weaker state, while rank thresholds may be lowered without
  losing the witness. This licenses directional Pareto pruning at each fixed
  far endpoint. It also proves a sharp obstruction to using this order alone:
  equal-rank diagonal two-sided ports form arbitrarily large antichains, so an
  ordered crossing frontier need not have a `k`-only cardinal bound.
- The first finite dominance quotient retains clipped exact-rank histograms,
  directional frontier tags, and coarse endpoint-incidence types. It merges 80
  raw classes and passes all singleton and small two-root gates, but the
  independently checked `8+2 -> 10` gate refutes it with 320 collisions. The
  raw span footprint itself remains collision-free across all 16,819,920 large
  parents. Exact boundary-rank repairs tested so far remove the collisions
  only by becoming injective on the observed raw states, so no uniform route
  is selected from this candidate.
- The reviewed rooted-interface repair is also retired. A recursive state with
  exact side footprints and crossing ports at capped cut-relative depth three
  merges 1,710 fibers at the middle eight-vertex cut, but an independently
  checked `8+2 -> 10` witness gives unequal rooted parent states. Depth four
  becomes injective on all 46,699 raw classes at that cut. The pre-vetted route
  now returns the raw footprint to structural counting; the next contract is
  an allocated Pascal-demand inequality at lowest separating tree nodes, not
  another global finite quotient.
- `ErdosSzekeres/StructuralChargingPascalDemand.lean` now proves the
  arithmetic half of that redirect: the adjacent coefficient
  `choose (k-2) (rank-1)` bounds either color's one-step published threshold
  increase. It also packages the unique lowest-node allocation of distinct
  span endpoints and proves that the allocated node separates them between
  its two children. An independently replayed all-root census through eight
  vertices at `k=6` checks 631,474 open exact-rank frontiers with no Pascal
  capacity violation. `StructuralChargingSpanFrontier.lean` formalizes exact
  ranks, the allocated antichain, exact child-ray normal forms, and the
  complementary crossing-rank bound. It reduces the local capacity theorem to
  an explicit `AllocatedExactRankSlotting` injection. The same exhaustive gate
  refutes constructing it by cup--cap on either raw endpoint projection, so
  the next target uses ray incidence. That construction and the global
  injection into the outer binomial window remain open Lean targets.
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
  `StructuralChargingTransport.lean` maps witnesses through sorted
  restrictions, proves the mirrored `4+3` case by order reversal, closes
  `CupBlocks34Force455`, and therefore proves the reviewed gap trichotomy and
  certificate-free singleton-root cardinal bound seven.
- `ErdosSzekeres/StructuralChargingBoundary.lean` extracts the general
  endpoint-avoidance charge and tests its direct `k = 6` consequence. Combined
  separately with the existing `(4,6,6)` state on the two gap sides, it proves
  only the coarse singleton-root bound 23 versus the diagonal threshold 16.
  This localizes the next obstruction to a coupled cross-gap charge.
- `ErdosSzekeres/StructuralChargingIntervals.lean` proves finite interval
  Helly for cap-witness spans, extracts weakly separated witnesses, and tracks
  the sharp one-boundary-vertex overlap. Two separated four-caps reserve seven
  vertices. The exact remaining target is an eight-vertex exterior charge;
  Lean proves that target would recover the diagonal cardinal bound 16.
- `ErdosSzekeres/StructuralChargingCupBlocks45.lean` proves the normalized
  nine-vertex `4+5` cup-block gate by eight symbolic turn tests and nine fixed
  witnesses, proves the reversed `5+4` case, and transports both orientations
  to arbitrary ordered blocks. The resulting unconditional charge bounds two
  outcome-free cup blocks by eight vertices in total.
- `ErdosSzekeres/StructuralChargingSingletonRoot.lean` freezes the exact
  certificate-free cross-gap target at `k = 6` and proves something stronger:
  two weakly separated upper four-caps at a singleton deep-below root force a
  parent five-cap. Thus the separated-witness branch is impossible in an open
  `(5,6,6)` parent, and the conditional cardinal consequence reaches 16
  without the state-566 certificate. The remaining structural obstruction is
  the common-cut branch. A parameterized Lean theorem now proves that, for
  every positive `a`, absence of a parent `(a+1)`-cap makes the singleton root
  a common sweep cut for every upper `a`-cap. Its arbitrary-lower-child form
  proves that each upper `a`-cap interval covers every lower vertex. At the
  first saturated `(4,6,6,3,2)` boundary, the classical `(3,6)` theorem
  supplies such a covering upper three-cap without a finite certificate.
- `ErdosSzekeres/StructuralChargingFirstSplit.lean` proves that every
  two-or-more-vertex witness set inside a decomposable set is separated by
  some recursive deep-below split contained in the original set. It does not
  claim a canonical or minimal-depth split; those notions would require an
  explicit decomposition-tree occurrence relation.
- `scripts/check_crossing_separated_caps.py` exhaustively refutes the proposed
  next force-outcome gate through the complete eight-vertex range. Two weakly
  separated four-caps can both cross the same open decomposable root, even
  when the caps are disjoint. The smallest witnesses occur at seven vertices
  with a shared lower boundary and at eight vertices in the disjoint case.
  This is checked computational evidence, not a Lean theorem; it redirects the
  route from immediate outcomes to quantitative endpoint-port charging.
- `ErdosSzekeres/StructuralChargingPortCapacity.lean` proves that an ordered
  family of crossing caps uses any lower-child vertex at most twice, with the
  two possible uses forced into right-then-left endpoint directions. Its
  summation corollary bounds total lower incidence by twice the lower-child
  cardinality. This is the local amortized invariant replacing the refuted
  immediate-outcome gate.
- `ErdosSzekeres/StructuralChargingTreeAllocation.lean` reifies a
  proposition-level decomposition as an explicit tree, addresses internal
  nodes by Boolean paths, and proves existence and uniqueness of the lowest
  node separating any witness of cardinality at least two. This supplies the
  node identity needed to sum local charges without choosing the same
  occurrence twice. Allocated ordered four-cap families are now coupled to
  local port capacity, giving at most two caps per lower-child vertex. This is
  deliberately stated as a witness-count bound, not as a Pascal contribution.
- `ErdosSzekeres/PublishedInductionSemantics.lean` formalizes the actual
  maximal child-index and retained-subset construction used in the published
  induction. The retained contribution is a concrete subset of vertices, and
  its complement satisfies the exact next-threshold inequality. Uniformly,
  auxiliary index one forces the whole nonempty child to be a singleton. The
  `(4,5,5,1,3)` branch therefore reduces to the existing certificate-free
  singleton-root theorem and now compiles with the sharp bound seven. It also
  isolates the first remaining boundary `(4,6,6,3,2)`: Lean checks its exact
  arithmetic and its only child-cardinality pairs `(2,10)` and `(3,9)`.
- `docs/experiments/0012-published-offwindow-classification.md` records an
  independently replayed census through `k = 20`. Every feasible non-index-one
  scalar failure in that range has one saturated auxiliary parameter. Lean now
  proves that saturation classification for all admissible parameters using
  disjoint prefix/suffix allocations of the outer Pascal window; the bounded
  census remains an independent regression and identifies the first gate.
- `ErdosSzekeres/StructuralChargingSaturatedResource.lean` closes that first
  gate without a finite certificate. Any open `(4,6,6)` split with nonempty
  lower child and decomposable upper child has at most eight upper vertices,
  excluding both `(2,10)` and `(3,9)`; its color-dual theorem excludes
  `(10,2)` and `(9,3)`. It also proves the uniform gap-side kernel: absence of
  a parent `(r+1)`-cap makes both upper gap sides around every lower vertex
  `r`-cap-free.
- `ErdosSzekeres/Duality.lean` isolates the certificate-free symmetry that
  exchanges cups with caps and reverses a deep-below split.
- `ErdosSzekeres/StructuralChargingCupBlocks56.lean` advances to the first
  `k = 7` cup-block boundary. The first `(3,2)` auxiliary state and its dual
  are closed in Lean. Both residual leaves at the `(3,3)` state now compile,
  so the normalized `5+6` theorem, reversal/transport, cardinal payoff, and
  actual `(4,7,7,3,3)` application close upper sizes 11--13 and all color-dual
  child pairs without a finite certificate.
- `ErdosSzekeres/StructuralChargingCapFreeSides.lean` freezes the next exact
  open dependency, `TwoCapFreeSidesBound567`, and proves the ordinary
  cup--cap reduction: each side has at most 15 vertices, so a counterexample
  must have both side sizes in `[7,15]`. It now also proves generalized
  one-vertex failure certificates, consecutive localization of cap failure,
  and forced nested bridge colors from a five-cup. `Decomposable.lean` proves
  that the strong-polygon law is exactly middle determinacy of triple colors.
- `ErdosSzekeres/StructuralChargingWitnessBranches.lean` retires the false
  sharp nine-signature selector and closes the complete no-strong-six branch
  from the checked 16-vertex `(5,6,6)` state. It reduces the remaining work to
  an endpoint-obstructed internal-strong-six branch and the exact `11+11`
  split. `StructuralChargingStrongSixSignature.lean` proves that the internal
  strong six has exactly one right-colored middle position and normalizes
  opposite-side failures into four internal anomalies or one final-fan class.
  These are now a literal five-element Lean type. Sharp models refute a useful
  repetition bound on the five labels alone. The `11+11` exception is further
  reduced to exact three- or five-vertex residues on the opposite side whose
  reinsertion with the designated vertex gives a cap four or strong six.
  `StructuralChargingResidueTransitions.lean` proves the first coupling laws:
  shared cap residues give one of four monotone pair words, while shared
  strong residues either vary across the external pair or disagree only at
  their first base middle. It also proves that three strong five-residues in
  an eleven-set force two residues to share a pair.
  `StructuralChargingPackingResidues.lean` classifies every packed crossing
  strong six into its five possible side splits. The two extreme splits are
  exactly strong-five residue carriers. If the three middle splits are
  excluded, deletion packing forces at least seven carriers, hence three
  residues on one side with a pair overlap.
  `StructuralChargingMiddleSplits.lean` proves that ambient cap-five and
  cup-six avoidance restrict every strong-six middle word to weight one or
  two. Deleting a middle-split witness now produces a disjoint mutually
  obstructed partner with one of five splits and a bounded middle word. All
  twelve directed failures also have a side-aware three-state form: an
  interleaving endpoint or middle role, or an extreme role whose comparison
  core is forced entirely onto the vertex's side of the cut.
  `StructuralChargingMiddleSplitClasses.lean` eliminates the remaining raw
  roles, indexes the resulting anomaly/fan states by a literal 19-element
  type, canonicalizes anomaly endpoints, and proves one-change bridge
  equalities for canonical, internal-fan, and fresh-middle-fan branches.
  `StructuralChargingMiddleSplitBridges.lean` packages all 19 classes into one
  four-vertex bridge certificate and lifts it through deletion packing. Two
  probes anchored on the same three-polygon frame provably agree with the
  frame color, while exhaustive five-vertex checking rules out stronger bare
  gluing conclusions.
  `StructuralChargingMiddleSplitRealization.lean` now gives explicit rational
  coordinates for the decisive no-extreme coloring and proves in Lean that it
  is sweep-realizable. Bounded packing gates also found no small replacement:
  a reduced `7+8` proof core still uses 704 deletion obligations. Thus local
  bridge refinement, modest packing extremization, and realizability as a
  local repair are retired; the next strategic fallback is a new uniform E3
  invariant with an all-root transition gate.
- `ErdosSzekeres/StructuralChargingSaturatedResource.lean` proves that the gate
  would bound the large child by 21 and eliminate the `(5,6,7,4,2)` child
  pairs `(2,24)`, `(3,23)`, `(4,22)` and their color duals. A sharp 21-point
  SAT control and middle-determinacy UNSAT runs for every 22-point cut are
  evidence only; the local bound is not yet proved in Lean.
- `ErdosSzekeres/Extremal.lean` constructs the classical `2^(n-2)`-point
  lower-bound examples for every `n ≥ 3`.
- `docs/formalization_plan.md` records the intermediary lemma ladder from the
  sweep model to the exact conjecture.
- `docs/literature_review.md` records the initial research synthesis.
- `docs/bibliography.md` is the living source ledger.
- `docs/agents/README.md` defines the repository's bounded multi-agent
  orchestration protocol, durable specialist profiles, and task/result
  evidence contracts. The Wayfinder remains the sole strategic tracker.
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
docs/agents/               agent profiles and orchestration contracts
docs/wayfinder/            durable strategic map and tickets
docs/experiments/          designed computational experiments
data/reference/            metadata for authenticated external inputs
data/derived/              compact certificates and verified results
runs/                      ignored machine-local work
```

This repository was initialized from `open-math-research-template` and is MIT
licensed; see `LICENSE` and `NOTICE`.
