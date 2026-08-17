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
- `ErdosSzekeres/TripleColoringExtension.lean` proves the exact rightmost-point
  recurrence for the four-index one-change law: an extension is valid exactly
  when its old restriction is valid and every old triple is compatible with
  the three new incident-pair colors.  Independent exhaustive scripts recover
  8, 62, and 908 labeled one-change colorings on four, five, and six vertices.
  The first frozen smaller summary failed to compress beyond color reflection
  and order reversal, so this is local combinatorial infrastructure rather
  than a recurrence for the Erdős--Szekeres numbers or a realizability result.
- `ErdosSzekeres/TripleColoringGeometricExtension.lean` proves the exact
  geometric analogue without quotienting the realization space: a coloring on
  `n+1` vertices is sweep-realizable exactly when some particular swept
  `n`-point realization admits a general-position point strictly to its right
  with all prescribed incident colors.  This correct interface retains the
  parent coordinates and supplies no smaller load-bearing cell summary.
- `ErdosSzekeres/TripleColoringExtensionFiber.lean` separates compatible
  abstract children, children of one fixed coordinate realization, and the
  union of geometric children over all realizations of one parent coloring.
  It records the incident colors as a labeled old-pair link and proves the
  exact union-over-realizations membership theorem.  This is representation
  infrastructure: it neither characterizes straight-line realizability from
  the abstract link nor closes a destination dependency.
- `ErdosSzekeres/TripleColoringExtensionTransition.lean` proves that every
  compatible incident-pair link is a permutation tournament and that two
  consecutive extensions share connector-color intervals, obey the exact
  four-word law, and allow only one direction of change inside a connector
  block.  Through-six computation confirms these laws but also shows that the
  first link and connector blocks do not determine the second link, so no
  predictive recurrence or destination implication is claimed.
- `ErdosSzekeres/TripleColoringRealizability.lean` proves that every realizable
  coloring satisfies `OneChangeOn` and proves the exact converse at four
  points using all eight integer-coordinate witnesses.  Independent finite
  certificates cover all 62 five-point and 908 six-point states, but those
  universal Lean theorems are intentionally not claimed.  Two realizations of
  one five-point type can have different rightmost extension cells, so one
  coordinate representative cannot stand in for its entire realization space.
- `ErdosSzekeres/RankThreeBracket.lean`, `ErdosSzekeres/RingelNine.lean`, and
  `ErdosSzekeres/RingelNineNonrealizable.lean` formalize homogeneous
  rank-three bracket realizability and prove that the exact Ringel nine-element
  sign pattern is nonrealizable.  Sweep-realizable and decomposable
  restrictions therefore cannot realize that pattern.  This is a local
  nonstretchability theorem.  A convention-correct replay finds 67 Ringel
  restrictions in one admitted family-layer state-567 model, but no current
  theorem forces one from the stronger full context or improves the global
  upper bound.
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
- `ErdosSzekeres/TothValtrUpper.lean` proves the unconditional published bound
  `ES(n) <= choose(2*n-5,n-2)+2` for every `n >= 3`.  Its dependency chain
  constructs an explicit projective normalization, proves orientation-sign and
  finite-subset convexity preservation, extends transformed caps through an
  anchor, and proves a strict improvement over the classical binomial bound for
  `n >= 4`.  This closes supporting milestone `Q-UPPER`; it does not close or
  reduce the exact universal upper-bound edge.
- The `Suk*.lean` and `PorValtr*.lean` modules now formalize a larger finite
  segment of Suk's quantitative route.  Besides the finite height--width
  theorem, support-region order, full one-region geometry, and adjacent
  convex-union consumer, Lean now proves the exact adjacent-pool recurrence,
  its indexed chain-rich iteration, the path dichotomy between separated
  antichain-rich pools and a consecutive chain-rich run, marked cyclic-edge
  selection, strict-cap support-cell contraction, and a source-shaped bridge
  to raw consecutive support pools without cardinality loss.  The global
  theorem `SukConsecutiveRawPools.chainRun_or_antichainPacking` then produces
  actual chain or antichain witnesses from those raw pools.  Both branches now
  have compiling consumers, and
  `SukConsecutiveRawPools.containsConvexSubset_of_globalParameters` eliminates
  their disjunction under explicit finite cardinal parameters.  A separate
  theorem constructs a clockwise periodic strict-cap enumeration of any
  supplied finite general-position convex set on its original carrier, while
  the arithmetic layer repairs the one-point loss in the authenticated
  Pór--Valtr count for `k >= 13` under an explicit large-`N` hypothesis.  The
  source construction is now complete as a separate formal layer:
  `exists_porValtrSupportProductData` proves the exact cyclic support-product
  inequality on the original carrier, `porValtr_exists_rich_half` extracts the
  corrected ceiling-minus-one rich cells, and
  `exists_porValtrCyclicSupportData` packages every required marked pool with
  `carrier = P`.  The remaining positive-fraction layers now compile as well.
  `sukPositiveFraction_forces_threshold` instantiates every natural parameter
  and composes the source with both global branch consumers, while
  `suk_explicit_upper` proves for every `n >= 65` the concrete bound
  `2^(n + 64*(sukCubeScale n)^2*Nat.clog 2 (3*n) + 128)`.  This completes the
  project's conservative formalization of Suk's
  `2^(n+O(n^(2/3) log n))` route; it neither reproduces the optimized published
  constant nor changes the open exact Erdős--Szekeres upper-bound edge.
- The first finite layer of the sharper Holmsen--Mojarrad--Pach--Tardos
  point-set route now compiles.  `HMPTSpikeOrderGeometry.lean` derives the
  literal triangle-containment and crossed-closed-segment partial orders, plus
  exact exclusive comparability, from one `SukRegionGeometry` pool.
  `HMPTSpikeOrderConsumer.lean` constructs actual maximum chains and proves
  `|P_i| <= v_i*h_i` by finite Dilworth.  The next raw geometric bridge now
  compiles too: `HMPTAdjacentPairTransport.lean` proves that a vertically
  ordered pair in either of two adjacent spike pools sees the appropriate
  distinct outer anchor and every point of the opposite pool with the same
  strict orientation sign.  This closes the signed-pair input to adjacent
  gluing, but not the mixed-four-subset consumer or H2 itself.  H1 is still the
  only complete layer of the six-layer route to the published
  `2^(n+O(sqrt(n log n)))` bound; H2's official open-layer count remains five,
  and no exact-conjecture dependency changes.
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
  does not repair this deterministic child-state transition.  The
  literature-informed `FP-01.B` child consequently tested a full-ambient
  generated down-set and endpoint-repair alternative; it explicitly did not
  revive a recurrence through the clipped child state.  The local endpoint
  dichotomy and its recurrence consumer now compile, and the exact rational
  Fin9 witness now kernel-checks a refutation of the stronger single-cell
  half-support producer.  An adaptive two-cell Boolean support survives the
  stored witness and all 3,270 target-free models in two bounded rational
  domains, but no uniform geometric selector is proved.  The full classifier
  cube and conditional local-exchange consumer now compile, while exact replay
  finds 535 radius-one and 265 radius-two positive-defect local minima in the
  stored Fin9 model.  Any revival must use a genuinely nonlocal collective
  selection rather than merely search or locally improve its 4,096 classifiers.
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
  refutes constructing it by cup--cap on either raw endpoint projection. A
  refined two-endpoint transition-ideal candidate survives all 631,474 groups,
  while one-endpoint and fixed-label negative controls fail.
  `StructuralChargingTransitionHall.lean` proves the rectangular-ideal
  boundary encoding into the adjacent Pascal layer and the Hall-to-slotting
  reduction. The unreflected Hall premise is nevertheless formally false: an
  `n=12`, `k=7` decomposable coloring has two opposite-orientation rigid spans
  with the same full ideal. `StructuralChargingTransitionHallReflection.lean`
  repairs this candidate by rotate-complementing exactly one orientation and
  proves that this merely reverses the same untagged Pascal slots. The full
  frozen root frontier and all 631,474 `k=6` groups pass independent reflected
  Hall replays, and Lean proves the former pair is separated as full versus
  empty ideals. `StructuralChargingTransitionHallRayBridge.lean` now proves
  the structural child-ray bridge: at the unique lowest separating node, the
  exact parent span exposes the forced predecessor/successor child ray, and
  its incident endpoint profile belongs to the orientation-reflected candidate
  family. `StructuralChargingTransitionHallBlocks.lean` now proves the exact
  ordered-block API and equivalence with intrinsic consecutive subfamilies.
  Two independently replayed controls retire the most direct proofs: on a
  five-span `k=6` block the single active profiles are `0,f,0,f,0`, and on the
  frozen `n=12`, `k=7` root the adjacent spans `(2,5)` and `(4,6)` both have
  singleton active interval `{3f}`. The latter defect is kernel-checked in
  `StructuralChargingTransitionHallReflectionCollision.lean`, whose theorem
  `activeBlockExpansion_fails` formally refutes active single-endpoint interval
  block expansion. The full reflected two-endpoint family remains unrefuted.
  The first skew-Bollobas redirect is also boundedly refuted: when an actual
  event records direction, its complete child chain, and a marked chain
  vertex, four disjoint earlier present sets must fit into an absent set of
  size three at the fifth frozen span. The proposed
  direction/role/complementary-depth quotient is independently refuted too:
  `(2,5)` and `(4,6)` have identical coarse incidence keys, so fiberwise
  absence cannot cross-hit them. A bounded Sol audit then selected exact
  reflected endpoint-incidence rank as the sharpest falsifier; Fable returned
  no judgment because of a provider connection error. The exact `0/1/2`
  matrices are already refuted on the frozen root by rank defects `5 < 6` and
  `3 < 4`. The remaining two-lane route has passed its first local gate: a
  fixed meet/join orientation is false, but allowing either locally valid
  assignment preserves both candidate families for all 738 frozen adjacent
  ideal pairs. `StructuralChargingTransitionHallUncrossing.lean` then proves
  that this flexible rule plus every two-family expansion test still does not
  imply distinct representatives: three identical two-element transition
  intervals are a kernel-checked obstruction. The first exact hole-moving gate
  now succeeds. On all 5,208 one-hole states of the frozen cap/rank-three
  frontier, every blocked state lies at one of the two singleton families; one
  ownership transfer moves the hole to a family of size at least seven, so it
  is immediately fillable with only five occupied ideals. Independent
  cell-mask and row-height implementations agree. The generic completion,
  ownership-transfer, cardinality-exit, and well-founded-descent implications
  now compile in `StructuralChargingTransitionHallHoleDescent.lean`, together
  with a reviewed singleton-or-block-large one-transfer theorem. That profile
  is not uniform: the frozen seven-span cup/rank-three group has intermediate
  family sizes `6,6,3,6`. On its 78,236 one-hole states, the unchanged
  boundary priority has 36 terminal-free two-cycles. The first repeatedly
  steals ideal `0` between spans `(3,7)` and `(6,8)`. A priority-free
  length-two augmentation bypasses every cycle: all 4,888 blocked states in
  the four full frozen groups, and all 5,977 blocked states across their 62
  consecutive subblocks, have an occupied hole candidate whose owner has a
  fresh candidate. Independent representations agree, and Lean proves that
  this certificate completes the SDR and implies block Hall. Lean now also
  gives the reviewed overlap-to-slack statement an exact normal form: a closed
  saturated owner star is equivalent to being blocked with no two-step exit.
  The canonical star follows the actual owners in the partial injection, and
  a state-free feasible-owner-star expansion profile implies that this actual
  star is block-large, hence supplies the exit and an SDR. Together with a
  separately supplied one-hole state for each nonempty block, the profile
  implies reflected consecutive-block expansion. Reflection preserves
  nonemptiness of every genuine candidate family. Experiment 0041 checks the
  stronger state-free profile for all 247 feasible owner maps on the 62 frozen
  blocks, with minimum slack `+1`; this is bounded evidence, not the arbitrary
  theorem. Rotate-complement is now formally antitone, swaps meet and join, and
  transports whole transition intervals to their reflected intervals. A
  stronger fallback also compiles: if every feasible owner map reaches one
  owner family at least as large as the block, then owner-star expansion and,
  with the separate one-hole premise, block expansion follow. Experiment 0042
  checks this block-large-owner profile for the same 247 maps with minimum
  slack `+1`, retaining raw endpoint lanes and reflection data. A bounded Sol
  review selected a deterministic facing-lane gap charge as the next
  falsifier; Fable hit its usage limit, so no consensus is claimed. Experiment
  0043 refutes that rule on the tight cap witness when the second charge faces
  the rigid singleton lane `{3f}`. Experiment 0044 then passes the block-large
  reached-owner profile on every decomposable `k = 6` root through eight
  vertices: 631,474 frontier groups, 1,126,134 consecutive blocks, and
  1,438,464 holes, with all 3,792 nonvacuous holes having bottleneck slack at
  least `+1`. Every nonvacuous hole has a normalized endpoint-extreme ideal
  with no compatible block-small owner. Lean proves the exact reduction to
  excluding an injective map into only block-small owners, formalizes this
  forced-extreme strengthening, and proves it implies the active profile.
  Experiment 0045 refutes the first proposed
  geometric strengthening: maximum single-lane cell spread plus one is only
  `5 < 6` on the tight cap witness even though the reached owner family has
  seven candidates. Experiment 0046 then refutes the forced-extreme
  strengthening on four frozen `k = 7` cup holes. The first needs the two-ideal
  anchor `{f,1f}`, which has only one compatible block-small owner. The active
  exact target remains the pre-vetted fallback, now in its compiled small-owner
  deficiency form: every hole needs some anchor set with too few compatible
  block-small owners. Experiment 0047 classifies every minimum deficient
  anchor in the frozen root and finds a one-lane saturated chain interval for
  each hole. Experiment 0048 extends the existential shape to every
  decomposable `k = 7` root through eight vertices: all 3,056 nonvacuous holes
  have a selected minimum anchor of size one or two that is a complete
  one-lane lattice interval. Endpoint singletons fail in 1,180 cases, so the
  pair alternative is essential. Experiment 0049 passes the first `k = 8`
  all-root gate through eight vertices: all 2,096 nonvacuous holes have
  singleton minima and bottleneck slack at least `+3`, so that support range
  does not yet exercise longer anchors. Experiment 0050 audits the exact path
  contract over 2,422,116 bounded `k = 7` holes, including 2,419,060 cases
  omitted from the prior shape statistics because they have no feasible owner
  map. Every included hole has a path and an exact singleton-trace certificate;
  514 require two gaps. A post-audit found that the shared generator included
  only ranks at least three, however, so this was never evidence for rank two.
  Lean proves the general minimal-deficiency calculus, a scalable
  owner-labelled lane-path theorem, local-neighborhood and exact-trace
  constructors, and the vacuity of rank one. The reflected path contract
  implies the lane-chain contract and hence active small-owner deficiency.
  Experiment 0051 tests rank two directly and refutes the route: lane paths
  fail at five vertices, reflected Hall at six, and an alternating
  seven-vertex split has six exact-rank-two frontier spans against five Pascal
  slots. Lean proves both the adjacent-crossing normal form and an explicit
  open decomposable counterexample, including emptiness of the proposed
  slotting type. The rank-at-least-three trace route remains unrefuted, but a
  replacement recurrence must group rank-two alternations or couple their
  cost to other ranks before general Hall or the global outer-window injection
  can be pursued. The first suggested repair—charge every local adjacency at
  its unique lowest separating node and use the global `support.card - 1`
  gap count—also fails. A three-vertex interleaved decomposition has three
  distinct local rank-two spans but only two global gaps; Lean checks this
  second obstruction. Unique lowest-node ownership is sound bookkeeping, not
  the missing linear bound. Experiment 0052 tests the first cross-rank repair:
  later merge transitions are paired with color-compatible hidden child gaps
  and promoted to those gaps' exact ambient ranks. Independent implementations
  find no capacity or endpoint-candidate failure in 1,913,894 adjusted groups
  over every open decomposable `k = 7` root through eight vertices. Lean proves
  the binary run-count identity and that hidden lower/upper gaps give genuine
  rank-three cap/cup spans. This is a surviving direction, not a proof: the
  promoted spans are noncrossing, so their ambient carrier, rank-ideal bridge,
  and connection to the published recurrence must be treated separately from
  the old crossing frontier. The ambient carrier now compiles: every hidden
  source gap receives an exact parent-support rank and nonempty endpoint-ideal
  and Pascal-slot candidate families. Lean now also proves the exact canonical
  equivalence between all hidden child gaps plus one initial crossing and all
  parent crossing transitions. For either fixed color, removing its compatible
  image leaves exactly the opposite-color hidden sources plus one at rank two,
  by cardinality. The fixed-rank adjusted carrier combines the old crossing
  frontier with the promoted noncrossing sources; its endpoint incidence is
  nontrivial, and adjusted Hall expansion would imply the published
  Pascal-layer capacity. Experiment 0053 now refutes that target at the first
  tested alternating ten-point root. Lean proves seven crossing plus four
  promoted cap/rank-three demands against ten slots, then derives failure of
  adjusted Hall and emptiness of the slotting type. Raw aggregation is also
  too large: both colors and all ranks total 36 obligations against the 31
  nonempty slots of one untagged Pascal window. The compiled genealogy remains
  valid. The first exclusive-choice repair also fails: after pairing every
  hidden source with its complementary residual transition, the 27-charge
  graph has maximum matching 20 and an explicit 20-demand/13-neighbor Hall
  witness. Experiment 0054 tests the most promising reviewed repair: merge the
  seven cap/cup rank-three requests with identical endpoint spans. Their
  intersected candidate families do admit a perfect 20/20 matching, but Lean
  proves the semantic repair false. Cup and cap rays live in disjoint retained
  child cores, and the proposed one-coefficient threshold bound is `32 <= 22`.
  Common endpoints alone are therefore retired. Progress now requires a
  genuinely conserved branch-indexed tree charge, with an actual retained
  owner and a proved nonreuse law, rather than additive per-rank accounting.
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
- The rank-two replacement now has a compiling conservation carrier.
  `StructuralChargingGapTokenConservation.lean` identifies adjacency gaps plus
  one sentinel with actual support vertices and merges child carriers into the
  parent without changing owners. `StructuralChargingTreeTokenConservation.lean`
  folds this across explicit decomposition trees with leaf-address nonreuse,
  and exact three- and ten-point regressions compile. The unique saturated
  published branch does not necessarily contain the conserved endpoint owner;
  `StructuralChargingSelectedBranchOwnerCounterexample.lean` refutes that
  premise at `(4,6,6,3,2)`. The corrected actual object is the intervening
  entering-crossing pivot. `StructuralChargingSelectedBranchPivot.lean` proves
  selected-child membership and pivot injectivity, and reduces simultaneous
  retained-core ownership to an explicit capacity inequality. The first
  geometry-sensitive gate now passes. `StructuralChargingPivotOverflow.lean`
  proves that the minimum lower vertex cones any upper three-cap of canonical
  pivots into a forbidden parent four-cap. Thus no parent four-cap and no
  parent `u`-cup force fewer than `u` hidden-lower pivots, with a color-dual
  theorem for hidden upper gaps. This rules out the apparent nine-pivot versus
  eight-core leak at `(4,8,8,3,4)`, `10+13`, and constructs one actual
  published upper slice retaining every pivot.
  `StructuralChargingHigherCone.lean` now proves the all-parameter cone: no
  parent `(a+1)`-cap makes the complete hidden-lower pivot seed avoid an
  `a`-cap, with the color-dual cup theorem. Inherited decomposability plus the
  strictly smaller `DecomposableStateUpper a u k` sharpens the seed bound to
  `decomposableThreshold a u k` and constructs one actual selected published
  slice retaining every pivot. At `(5,8,8)`, this replaces the unusable
  ordinary bound 28 by 22 against a 23-vertex core.
  `StructuralChargingSaturatedPredecessor.lean` now embeds this bridge in the
  required well-founded shell. Validity of either saturated branch gives the
  exact successor equality, strict descent in `a + u`, and the local parent
  avoidance needed to select a pivot-containing core using only a strictly
  smaller state. A single dispatcher chooses the unique valid branch. This is
  conditional induction machinery, not the outer E3 transition.
  `StructuralChargingRootTransition.lean` now proves that, at every positive
  threshold, the full hereditary state is equivalent to one root-local
  transition whose two children already satisfy the outer bound. It also
  extracts an exact threshold-plus-one subsplit and turns simultaneous pivot
  retention into a source-count bound. The latter is not enough by itself.
  `StructuralChargingTreePivotCounterexample.lean` additionally shows that
  canonical pivot values can collide across nested set-level split data, so
  untagged all-node pivot injectivity is unavailable.
  `StructuralChargingVisibleAdjacency.lean` through
  `StructuralChargingCapExtremaReserve.lean` make the proposed one-split
  payment exact and then refute it at the `(4,8,8)`, `10+13` boundary: the
  central cut leaves at most one hidden lower gap and at least eight visible
  lower adjacencies. The successful replacement is
  `StructuralChargingCupBlocks67Symbolic.lean`. Its direct symbolic Lean proof
  shows that ordered cup blocks of sizes `6+7` or `7+6` force a four-cap,
  eight-cup, or strong eight-set. Consequently every open upper child has at
  most twelve vertices, `10+13` is impossible, and an exact 23-vertex root is
  narrowed to `11 ≤ lower.card` and `upper.card ≤ 12`.
  `StructuralChargingResidualWindow488.lean` closes every remaining split by
  crossing cup/cap pairs `(5,3)`, `(6,2)`, or `(7,1)`, and proves the
  unconditional hereditary theorem `decomposableStateUpper_488`. The proof is
  elementary rather than enumerative and passed an independent frozen-file
  audit. The next bottom-up fixed-`k=8` target is `(5,7,8)`, before the
  `(5,8,8)` higher-cone consumer. Its exact critical root has two residual
  tails: lower sizes `1..10` against upper sizes `41..32`, and the oriented
  `41+1` extreme. Lean reduces the first family to a singleton-lower `1+32`
  gate and proves that its two upper sweep sides have sizes `11..21` and each
  contains a five-cup. The tempting extracted `5+q+5` gate is false: an
  explicit recursively decomposable 11-vertex counterexample is now proved in
  Lean. The replacement cap-reservoir invariant now compiles: every
  23-vertex upper restriction contains a four-cap, every such cap straddles
  the root, and three can be selected disjointly. A checked 13-vertex model
  shows those three caps alone are insufficient, so the lower-tail route must
  retain the full density and decomposition-tree ownership. A nine-vertex
  transversal and avoidance-free strict span descent are now formally
  retired: the former is equivalent to the full gate, and an exact
  recursively decomposable `32/23` common-cut construction refutes the latter
  in Lean while explicitly containing a seven-cup. The surviving terminal-cap
  reduction compiles. Its open span has at most 21 vertices, leaving at least
  nine outer-tail vertices with only the two endpoint bridge failures. At its
  unique lowest separating tree split, the cap has a `1+3` or `2+2` child
  profile; strong-eight avoidance forbids respectively a lower five-cup or
  six-cup, and the strict `(5,5,8)` predecessor bounds the first lower child
  by 20. In the `2+2` branch, the unique cap word is
  lower--upper--upper--lower, so the internal endpoint bridges add no new
  information. An exact nine-vertex recursive Lean counterexample refutes the
  five-internal-tail shortcut. Lower-sibling supports along a cap path are now
  proved pairwise disjoint and ordered, and a four-cap fully covered with
  singleton fibers in those buckets is impossible. Global `32/23` density
  supplies a minimum terminal-tail transversal of size at least six; every
  selected tail owns a distinct private four-cap and is internal or has a
  concrete lower-cap/upper-tail first-exit address. This package is threaded
  into the actual state-578 obstruction. Two shortcuts are kernel-refuted:
  a secondary cap need not consume two tails, and six distinct target-free
  private caps may share one three-vertex core. A general deep-split word law
  confines the lower vertices of every mixed four-cap to its sweep endpoints.
  The selected whole-cap trace layer is complete: the shallowest escape of a
  private cap is either a true-directed endpoint peel or a certified
  two-vertex lower-sibling collision, and the actual state returns three
  owners with this residual. An exact eight-vertex terminal, decomposable,
  target-free Lean example realizes the collision-free true-peel/later-false-
  owner branch. This formally expires independent cap-by-cap tracing. Density
  proves that no shared core of at most five vertices hits the entire residual
  cap family, but does not bound overlap among the six chosen private caps.
  The pre-vetted overflow has therefore moved to the upper-singleton extreme:
  Lean reduces its `41+1` color-dual tail to an exact 32-vertex swapped gate
  and proves four-cup density in every decomposable 23-vertex restriction.
  Conditional on the strict `(4,5,8)` predecessor, that reservoir now has a
  compiling global packing of three disjoint four-cups and three further
  disjoint four-caps. Pairwise lowest joint splits, dual endpoint laws, and a
  six-witness common-split defense compile. A target-free reverse-separated
  pair formally expires address equality alone. Regenerating a cap inside the
  12 cup vertices has the exact `2+2+0` or `2+1+1` incidence split. Both
  branches are now formally refuted as local closing routes: one minimal
  12-vertex recursively decomposable, sweep-realizable Lean model realizes
  both while avoiding five-caps, five-cups, seven-caps, and strong eight-sets.
  The exact 32-vertex gate remains open because it additionally supplies three
  external caps. Lean now retains that full seven-witness package: the
  regenerated cap and external caps are pairwise disjoint, the `3+3` packing
  occupies 24 vertices, and eight reservoir vertices remain. Lean now
  saturates this to six disjoint four-caps on 24 vertices. The `2+2+0` branch
  yields a protected disjoint one-cup/five-cap packing; the all-hit `2+1+1`
  branch remains explicit. Global `32/23` density proves every four-cup
  transversal has at least ten vertices and refines the original cup support
  to either a fourth disjoint cup or an injective ledger of 10--12 private
  cups with exterior vertices. A checked relaxed incidence model expires
  counting-only and raw-deletion-ledger closure. One selected cup now lies
  wholly in the owner transversal, producing a four-owner private-cup star.
  Lean couples this star to the six cap blocks as a full `4 × 6`
  first-joint-split matrix; every row and column is a prefix chain. An exact
  seven-vertex common-tail example formally expires star-only tail nonreuse.
  The remaining boundary-exchange contract also compiles: replacing `4r`
  protected owners by at most `3r` boundary vertices while preserving all cup
  hits produces a forbidden transversal of size at most nine. Lean now builds
  a seven-vertex spine/private-cup carrier and local three-vertex boundary for
  every full selected cup. Their total boundary respects the `3r` budget, so
  density forces a residual cup which escapes every old carrier. That cup
  meets a full spine and has a vertex outside its old carrier, yielding a
  compiling expanding-carrier invariant. In the tight one-spine branch, four
  owner-indexed partial exchanges cannot all reuse one cup and form a second
  `4 × 6` residual-cup/six-cap matrix. Lean now repairs the sampled mixed
  classification and expands the second matrix to every residual four-cup.
  Its rows and columns are prefix chains with a global minimum. Opposite
  strict directions force all six cells of the distinguished spine row to
  stay at that minimum, leaving an exact one-sided-or-anchor-plateau
  classification. This full matrix reconnects to the 32-vertex gate. On
  eight vertices, Lean further identifies a three-boundary with a five-set
  containing no four-cup and now proves the complete decomposable
  eight-vertex lemma by seven certificate-free root-profile arguments. The
  stronger root-only theorem needs no recursive child hypotheses. Hence every
  decomposable eight-vertex carrier has either a five-cup or a three-vertex
  four-cup transversal. Under global five-cup avoidance, the exact unused
  eight-vertex remainders of the six-cap, original `3+3`, and protected
  one-cup/five-cap packages all carry such a boundary. The active theorem is
  now the crossing-to-remainder bridge: residual cups may cross the selected
  24 vertices, so the unused boundary does not yet complete the global
  exchange. Lean has taken the first exact step: in the tight one-spine branch
  density produces a residual cup disjoint from the unused boundary which
  necessarily meets the selected six-cap support, so it is a genuine crossing
  row of the full address matrix. Full-family localization and the exact
  complementary-child boundary now compile, but a relaxed 32-vertex model
  refutes the identification of the selected/unused support cut with the
  common-minimum split. The reviewed 24-row cap-vertex-deletion ledger also
  compiles. Exact decomposable, sweep-realizable Lean counterexamples show
  that one cap column may reuse a common three-vertex cup core with identical
  endpoint shapes, and that two residual cups may have disjoint lower
  sweep-middle pairs below two shared upper endpoints while avoiding every
  target. Thus address-only, one-column deletion, and two-middle-pair closure
  are expired. The surviving bracket theorem proves that, under five-cup and
  seven-cap avoidance, two upper vertices can strictly bracket at most six
  lower vertices. The direct common-bracket target is now retired: an exact
  cardinality-minimal nine-vertex Lean model realizes two full deletion
  columns with only one upper endpoint per row. The surviving global theorem
  gives a `24 → 18 → 9` exterior fan: nine saturated cap sources lie on one
  side of the upper span, every corresponding deletion row has exactly one
  upper endpoint, and those sources occupy at least three cap columns. An
  exact 13-vertex decomposable and sweep-realizable Lean model realizes that
  three-column fan while avoiding five-cups, seven-caps, and strong
  eight-sets. Lean now uses all six columns essentially: every one-upper fan
  row misses at least three cap blocks, so one column is missed by at least
  five source-indexed rows. Exact `32/23` density independently supplies two
  cups avoiding that blocker with disjoint sweep-middle pairs. A total
  deletion-branch theorem exposes source-disjoint and lower-local rows instead
  of hiding the fan constructor's premises. The direct three-boundary repair
  is refuted by an independently checked relaxed 32-vertex incidence/address
  model, and an exact 13-vertex target-free Lean model proves that five local
  deficit rows alone need not have a two-cover of their middle pairs. The
  next target was the precise full-family synchronization: retain
  another cap column or the complete residual matrix while coupling the five
  selected fan rows to the arbitrary blocker-avoiding density witnesses. That
  synchronization now compiles. Lean indexes every four-cup avoiding the
  selected blocker, pairs it with all six caps, and proves a common-minimum
  one-sided/minimum-column/mixed-rectangle classification. Five deficit
  entries represent at least two distinct cups because a one-upper row carries
  at most three indexed sources. The raw escape branches also sharpen: a
  source-disjoint row avoids a second cap column, while a lower-local row has
  all six cells strictly descend into the lower subtree. The strengthened
  trichotomy reconnects to the exact 32-vertex color-dual gate. A checked
  relaxed full-matrix model shows that these address/incidence facts alone do
  not force a five-boundary; exact restricted transversal numbers are
  `9,9,9,9,10,10`. The color-sensitive mixed branch now closes: opposite
  strict cells put a four-cup below and a four-cap above one deep split,
  forcing a strong eight-set. The compiling reduced trichotomy leaves
  one-sided localization of the 24-vertex cap support or a universal minimum
  column. The full residual-family version now compiles, including local
  three-boundaries on both one-sided branches. A universal minimum column
  yields either a residual cup disjoint from that cap or a four-owner private
  residual-cup star with exact singleton intersections. Thus ticket 0008
  lands as Outcome 2: the mixed branch is eliminated, while four named
  residual obstructions pass to ticket 0009. Exact-small decomposable models
  refute projected consumers of those branches but omit the full 32-vertex
  state package. State `(5,7,8)` therefore remains open, neither proved nor
  refuted. In parallel, the proposed symmetric predecessor-fiber shelling is
  kernel-refuted on four vertices. The uniform Pascal branch succeeds: Lean
  replaces the state-specific middle-window arithmetic by two generic
  binomial-width tail gates, and recovers the state-578 `32/41` split as an
  exact instance. Those geometric tail-gate families are now the principal
  all-parameter E3 frontier. The next uniform layer now compiles as one
  ordered two-side consumer in both color orientations. Its first unresolved
  instance is exactly the earlier `(5,6,7)` two-cap-free-sides bound, while
  the `(4,5,5)`, `(4,6,6)`, and `(4,8,8)` controls compile without finite
  certificates. A new diagonal interface proves the reservoir identity
  `2k-3`, consumes a parameterized `(k-2)+(k-1)` cup-block theorem, and
  unifies every `(4,k,k)` singleton gate through `k=8`, including the omitted
  `(4,7,7)` control. Its first new case `k=9` now compiles completely: generated
  Lean proofs connect every retained semantic clause to two kernel-checked
  LRAT contradictions, and normalization plus arbitrary-block transport prove
  `diagonalCupBlocksForce4kk_nine`. The complementary extreme-exchange layer
  now also compiles end to end: all seven strong-ten helpers, 48 semantic CNF
  chunks, both orientations, and `extremeExchangeK9FinSeventeen` are checked
  by Lean. These are exact finite `k=9` results; certificate mining found no
  honest all-parameter propagation rule. State 567 separately reduces to two
  exact 22-point deletion-packing obligations. Every nondual 22-point split is
  likewise UNSAT computationally, but neither obligation has a Lean proof.
  Exact residual-ten incidence counting now compiles and gives at least 30
  complementary bad four-block probes, each with a carrier-touching strong-six
  escape. The resulting theorem
  `exists_sameOccupancyCollision_or_threeCarrierWitness567` now compiles: it
  yields either two distinct escapes with the same coarse carrier occupancy or
  one incident strong six using at least three carrier vertices. A second
  exact incidence argument sharpens the latter branch to a carrier-only
  strong six, with overlap profiles `1+5` through `5+1`. In the collision
  branch, Lean now proves exact one- or two-vertex residual replacement data
  and amplifies a light collision to four pairwise-distinct light repairs with
  triangular residual avoidance. A relaxed 12-carrier omission-rectangle
  encoding is UNSAT in two independent computational formulations, but its
  large external certificate is not a Lean proof. Lean now separately packages
  the exact no-collision branch as a normalized finite omission-rectangle
  system: every anchor pair is covered, and rectangles of distinct witnesses
  are edge-disjoint. Lean now proves the exact area-profile dichotomy for this
  system: it consists either of four `3×3` rectangles or of four area-5 and
  two area-8 rectangles; the balanced four-grid extraction also compiles. A
  tempting local color closure from the six strong pair-unions is false even
  for an exact integer planar configuration. The counterexample is
  nondecomposable, so the surviving terminal must use decomposability or the
  full packed-22/residual-ten provenance. The preferred next repair retains
  the balanced grid together with the universal ten-residual escape.  Canonical
  provenance, the three-carrier transversal, and the residual-touching escape
  now compile.  The exact hitting/targeted-packing bridge also compiles, reducing
  the required packing interface from 597,500,904 eager witness occurrences to
  960,960 targeted occurrences.  Its arbitrary-carrier Fin22 downstream
  consequence is nevertheless SAT with all 120 targeted deletions checked, so
  the next repair must restore canonical grid/bad-block provenance or stronger
  global packing rather than treat the compression as a terminal law.  The
  separate same-occupancy four-repair negation is now directly certified UNSAT
  in the exact full Fin22 cut context, with independent reconstruction and
  pure-RUP replay; its 994-MiB proof is computational evidence, not a Lean
  theorem.  In the parallel five-class route, the exact packed `3+3`
  partner/failure reduction compiles and its full-context negation is likewise
  independently certified UNSAT.  Its 336-MiB proof still requires semantic
  compression before the terminal can be promoted. The
  generic residual counting kernel has nevertheless been extracted: a
  division-free seed-cover theorem and its `112 < choose 10 3` state-567
  specialization compile. This is not yet a uniform Pascal recurrence. The
  local middle-profile capacity also compiles, but independently replayed exact
  567 coordinate computation and its 657 dual refute the first ambient
  profile-multiplicity theorem at the computational-evidence tier; a new
  cross-endpoint invariant is required. The color-sensitive terminal remains
  open. The finite
  `k=9` results validate the diagonal interface and
  certificate workflow; they do not yet provide the uniform successor step.
  In the parallel
  state-578 branch, all four private deletion
  owners force one full six-column plateau cup which misses two foreign cap
  blocks. This is a sharper Outcome-2 obstruction, not closure of state 578.
  The subsequent global-cover interface and universal seed-escape theorem
  compile, but explicit replacement/address cycles stop the current invariant
  family. The state-578 main route is suspended under a precise
  complete-family/color-sensitive revival gate; the state itself remains
  open. `DecompositionPrime.lean` begins the unrestricted
  Layer-F replacement by proving that every finite indecomposable support
  contains a deletion-minimal prime support. The realizable one-or-two
  deletion proposal is now kernel-refuted by a seven-point integer-coordinate
  prime coloring with no strong six-set and no prime remainder after any one
  or two deletions. The original unthresholded normalization contracts are
  also kernel-refuted by their empty instance. Their exact-threshold
  replacements compile, and `PrimeCoreCount χ = 0` is proved equivalent to
  decomposability on nonempty ground sets. Mutation locality and exact
  created-versus-destroyed accounting now compile, as does the zero law for a
  highest-cardinality-first stratified prime-core rank. Complete seven-point
  and selected eight-point abstract controls support a three-step endpoint
  drop while confirming that intermediate monotonicity is too strong. A
  target-free realizable highest-stratum descent above the exact threshold is
  the surviving hard construction proposal, with one kernel-checked geometric
  mutation into the decomposable class as a positive control. A structurally
  independent predecessor-bicoloring interface also compiles: such a
  bicoloring gives the exact doubling recurrence directly. Two independent
  computational encodings pass its stronger balanced eight-vertex `k=5`
  gate, but the general bicoloring theorem remains open. The complete
  implication hierarchy from integral bicoloring through fractional cover and
  a predecessor-free half-subset to exact doubling now compiles.  The exact
  `PredecessorHalfMassAt` interface now makes the weighted middle layer
  explicit: fractional cover implies half-mass by finite double counting,
  uniform half-mass implies a half-subset, and half-mass feeds the recurrence.
  The orientation-sensitive weighted producer remains open. A uniform
  certificate-free theorem proves predecessor bicoloring below
  `2*k-3` vertices for `k>=5`; exact computation extends the positive `k=6`
  evidence through 12 vertices, with the 1.23-GB `n=12` LRAT remaining
  computational rather than kernel evidence. Maximum-support exchange,
  neighborhood-only weighting, signed local transition charging, and the first
  collective exterior-score invariant are stopped by exact rational
  eight-point controls; none refutes the hierarchy itself. The compiling pure
  deep-split producer is now the primary predecessor route. Its first bounded
  gate succeeds on all 2,862 strong-five-free members of the complete
  decomposable Fin8 census, and two independent complete encodings extend the
  survival result to all 19,870 strong-five-free rank-three Fin8 signotopes.
  The compact counterexample-UNSAT core has now been promoted to Lean:
  `halfPureDeepSplitAtFiveFinEight_of_oneChange` proves the exact Fin8
  one-change/no-strong-five implication with a kernel-checked semantic bridge
  and LRAT replay. The thresholded singleton-fan producer now has a compiling
  consumer into the predecessor half-subset recurrence. At `k=5,n=9`, Lean
  reuses the existing ES5 certificate to prove
  `containsStrongFiveFinNine_of_oneChange`, so the corresponding fan result is
  vacuous rather than structural. At the first informative `k=6,n=10`
  boundary, two independent complete encodings support the singleton-fan
  conclusion and separate target-free controls are satisfiable, so this gate
  is nonvacuous. Its Lean certificate promotion and the uniform arbitrary-size
  producer remain open.
  The independent rooted-circuit branch stops: a seven-point rational Lean
  counterexample refutes preservation of two signed triangle anchors.
- `ErdosSzekeres/Extremal.lean` constructs the classical `2^(n-2)`-point
  lower-bound examples for every `n ≥ 3`.
- `docs/wayfinder/frontier-portfolio.md` is the canonical inclusive registry of
  every currently valuable thread, with explicit mechanism-family, dependency,
  scope-ceiling, evidence, consumer, next-gate, and expiry fields. Temporary
  execution slates are selected from it but do not define membership or count
  as independent proof routes. The known quantitative upper-bound ladder and
  unrestricted exact-six theorem are separate gated entries with supporting
  milestones; neither changes the open universal upper-bound edge.
- `docs/formalization_plan.md` records the intermediary lemma ladder and
  historical execution plans from the sweep model to the exact conjecture.
- `docs/literature_review.md` records the initial research synthesis.
- `docs/bibliography.md` is the living source ledger.
- `docs/agents/README.md` defines the repository's bounded multi-agent
  orchestration protocol, durable specialist profiles, and task/result
  evidence contracts. The Wayfinder remains the sole strategic tracker.
- `docs/wayfinder/map.md` is the canonical strategic index, paired with the
  frontier portfolio above. Its load-bearing dependency ledger, rather than
  portfolio activity or entry counts, records proof distance. Ticket 0002 owns
  the generic E3 route selection, while claimed ticket 0010 owns the exact
  state-578 side branch.

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
