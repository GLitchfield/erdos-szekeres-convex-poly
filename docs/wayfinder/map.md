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
  threshold 16. Finite interval Helly and its cap-witness specialization now
  compile, as does the sharp fact that two separated four-caps reserve seven
  vertices. A checked eight-vertex countercontrol shows that separation alone
  forces no target outcome. The normalized `4+5` cup-block gate now compiles
  by a nine-witness symbolic proof; reversal and sorted restriction transport
  close both arbitrary orientations and give an unconditional eight-vertex
  cup-block charge. The exact eight-vertex exterior bound remains open and
  isolates the missing cross-gap bridge. The root-aware target
  `SingletonRootSeparatedCapChargeAtSix` now compiles outright: the endpoint
  transition proves that two weakly separated upper four-caps force a parent
  five-cap. Hence an open singleton-root parent lies entirely in the common-cut
  branch, with every upper four-cap straddling the root. The next structural
  target is to descend that common-cut family to its first separating
  decomposition node and extract coupled Pascal/cup contributions, without
  invoking the state-566 certificate or an equivalent finite upper theorem.
  The common-cut statement itself now compiles uniformly: for every positive
  `a`, absence of a parent `(a+1)`-cap makes the singleton root a common cut
  for all upper `a`-cap witnesses. A separate structural-descent theorem now
  extracts some recursive split separating any witness set of cardinality at least two,
  while deliberately making no unformalized canonical-firstness claim.
  The next candidate statement, that two separated four-caps crossing this
  split force a `(5,6,6)` outcome, is refuted by an independently replayed
  complete census through eight vertices. The disjoint-cap strengthening also
  fails. The surviving root information is the at-most-two lower endpoint
  ports of each crossing cap; the next lemma must charge those ports
  quantitatively rather than demand an immediate outcome.
  That local endpoint-port lemma now compiles: in any weakly ordered family of
  crossing caps, each lower-child vertex has multiplicity at most two, and the
  total lower incidence is at most twice the lower-child cardinality. The next
  obstruction is global allocation: the proof must assign each witness to one
  decomposition-tree occurrence so local charges can be summed without
  duplication.
  Explicit decomposition trees and Boolean node addresses now compile, as do
  the specification and uniqueness of the lowest separating-node allocation
  inside a chosen tree. The active target is to define the `k = 6` endpoint
  demand attached to that address and prove that its Pascal contribution is
  bounded by the local two-port capacity.
  The intervening allocation-to-port theorem also compiles: an ordered family
  of four-caps assigned to one address has at most twice as many members as
  lower-child vertices. This sharp local count does not imply the 16-point
  bound. An initial blind Sol/Fable review rejects selecting a weighted
  overflow-token route before its semantic source is defined, but its proposed
  follow-ups were stale: the singleton boundary is already closed locally and
  deterministic incoming-star refinement is already stopped. In the corrected
  audit, Sol finds that even the proposed finite classification is not yet
  well-posed from the packet it received. Direct recovery from the journal
  proof now resolves that objection: the child contribution is an actual
  retained vertex subset chosen at a maximal threshold index, and the adjacent
  term bounds its actual complement. This selection, its exact cardinal
  inequality, and the uniform fact that index one forces a singleton child now
  compile. The `(4,5,5,1,3)` branch consequently reduces to
  `singleton_root_card_le_seven` and is closed in Lean. The next route-selection
  item is to classify the remaining positive auxiliary indices below the
  active Pascal window and freeze the smallest structural transition covering
  them. The corrected Fable run exhausted its provider session quota, so the
  new source-based contract still needs a fresh bounded review.
  An independently replayed arithmetic census through `k = 20` now performs
  that classification. After removing index-one singleton branches, all 6,120
  feasible scalar failures have one saturated auxiliary parameter and one
  parameter below the dual active-window endpoint. The smallest state is
  `(4,6,6,3,2)`, with child sizes `(2,10)` or `(3,9)` and scalar defect five.
  The saturation pattern now compiles uniformly in Lean: nonsaturated child
  thresholds occupy disjoint prefix/suffix allocations of the outer Pascal
  window and cannot realize complementary child cardinalities. The pending
  route decision is therefore the structural one. Lean now extracts the first
  shared resource at `(4,6,6,3,2)` without a finite certificate: an upper
  three-cap whose sweep interval contains every lower-child vertex. The next
  invariant must consume or transport that covering-cap resource uniformly,
  with the two/three-vertex lower-child state as its first falsification gate.
  That first gate now closes by a stronger certificate-free theorem: every
  open `(4,6,6)` split with nonempty lower child and decomposable upper child
  has at most eight upper vertices. Hence both `(2,10)` and `(3,9)` are
  impossible. The proof turns the upper gap sides around any lower vertex into
  ordered cup blocks and applies the symbolic `4+5/5+4` theorem. Certificate-free
  color duality also eliminates the reversed `(10,2)` and `(9,3)` pairs. Its
  uniform kernel says that no parent `(r+1)`-cap makes each gap side
  `r`-cap-free. A corrected bounded review should decide whether higher
  cap-free gap-side bounds are the next uniform state before this route is
  promoted; unavailable Fable quota does not pause Lean implementation or
  falsification work.
  The first `k = 7` state `(4,7,7,3,2)` and its dual now close by an
  elementary two-gap cardinal theorem. At `(4,7,7,3,3)`, the 13-vertex child
  also closes. Both residual leaves of the normalized `5+6/6+5` theorem now
  compile by explicit cup/cap/strong witnesses. Reversal, sorted restriction
  transport, and the application shell therefore close sizes 11 and 12 and
  every color-dual child pair without importing a SAT certificate. The active
  boundary is `(5,6,7,4,2)`. A bounded Sol/Fable review judged its proposed
  two-four-cap-free-sides bound logically sufficient but unproved. Lean now
  freezes that exact dependency as `TwoCapFreeSidesBound567` and proves its
  full conditional application and dual shells. The ordinary `(4,6)`
  cup--cap recurrence now compiles under `OneChangeOn` and bounds each side by
  15; hence the unresolved core has both side sizes in `[7,15]`. The `(4,4)`
  and `(4,5)` recurrences give two four-cups and a five-cup, and the completed
  cup-block theorem converts them into either a four-cap crossing the cut or a
  strong six-set. A second bounded Sol/Fable review accepted the exact
  one-vertex failure certificates but rejected them as quantitative
  invariants. Lean now proves those certificates, consecutive localization
  for cap extension failure, forced and nested bridge colors from a five-cup,
  and the equivalence between strong polygons and middle-determined triple
  colors. Small validated SAT controls refute an unconditional identical
  witness-profile collision lemma. The middle-determinacy encoding resolves
  the previously open 22-point cuts 10 and 11 as UNSAT in 278 and 289 seconds;
  together with cuts 1--9 and the sharp validated 21-point model, every split
  now supports the proposed bound computationally. No UNSAT certificate has
  been imported into Lean. The next proof item is a global counting lemma
  combining five-cup bridges, consecutive cap failures, and middle-color
  disagreement on every seven-subset. Endpoint cap failures are now
  deterministic, pairwise middle-disagreement certificates compile, and a
  two-probe theorem compresses every later five-cup extension in the
  no-strong-six branch to an outer-left or inner-right obstruction. The active
  target is to bound the evolution and multiplicities of these two classes
  along the opposite cap-free side. Probe changes now force both later-pair
  anchor colors, and simultaneous changes to distinct new probe colors give
  an explicit coupled middle disagreement. The unresolved transition cases
  have an unchanged probe or equal new probe colors and must be coupled to the
  crossing-cap failure signatures. Those signatures now compile in exact gap
  form: one at each outer gap and two, three, and two across the interior
  gaps. The active count must bound multiplicities across this
  `1+2+3+2+1` family rather than merely count signature types; a
  decomposable-only refinement remains the fallback. Lean now packages the
  family as an exact nine-element signature type and constructs a realized
  total charge for every outside vertex. The proposed sharp selector is now
  retired: independently checked Hall-deficient matchings on validated sharp
  21-point models refute even its permissive capacity-two relaxation, and its
  17-slot conclusion is circular for the 18 outside vertices of a 22-point
  counterexample. A bounded Sol/Fable review at packet SHA-256
  `52f4db63c5a7c2bd0c748a090ed8b6fba056b14cf0dff2335a6c5e468f5fb0f7`
  agreed on a strong-six branch split. Lean now transports the checked
  16-vertex `(5,6,6)` certificate and closes the entire no-strong-six branch
  with ambient bound 15. At size 22 every six-vertex deletion leaves a strong
  six, so designated witnesses have disjoint partners and mutual middle
  failures. Except at the exact `11+11` split, the checked `(4,6,6)` state
  produces a strong six wholly inside the larger cap-free side; every vertex
  on the opposite ordered side then has a forced endpoint-role extension
  failure. The internal polygon has exactly one right-colored middle
  position, proved in Lean, leaving four signatures. Every endpoint failure
  now realizes a member of a literal five-element Lean type: one of four
  indexed internal anomalies or a final-middle fan variation. A fan change
  forces the earlier fan and bridge colors to equal the later polygon-middle
  color. Independently replayed sharp 21-point models refute a useful capacity
  bound on these five labels alone: one class may cover every opposite vertex,
  and cut 11 can require uniform assignment capacity four. The endpoint route
  must therefore couple transitions to unused large-side vertices. The
  balanced branch now has an exact incidence form: each of its 22 vertices
  supplies either a three-vertex cap residue or a five-vertex strong-six
  residue on the opposite side. The final local bound reduces directly to
  this residue branch plus the endpoint branch. Shared cap residues now have
  one of four monotone external-pair words. Shared strong residues satisfy an
  exact gluing obstruction: absence of a strong seven forces pair-profile
  variation or an extension disagreement at the first residue middle. Fully
  checked `11+2` and `11+3` controls show that neither repetition alone has a
  small fiber bound. Lean now proves that among three strong five-residues in
  an eleven-set, two share at least two vertices. The next balanced invariant
  is now connected conditionally to this overlap: if crossing strong sixes of
  types `2+4`, `3+3`, and `4+2` are absent, deletion packing forces at least
  seven extreme-split residue carriers, at least four on one side, and hence
  three residues with a pair overlap. The immediate obstruction is therefore
  to derive a target outcome or an extreme replacement from every middle
  crossing split; after that, the shared-pair agreement case remains. The
  naive local `3+3` replacement is false: an independently checked 12-point
  model contains two disjoint `3+3` strong sixes while avoiding `(5,6,7)` and
  side four-caps. Lean instead proves the honest transition obtained by
  deleting one witness: a disjoint mutually middle-obstructed partner, one of
  five crossing splits, and weight-one-or-two middle words on both polygons.
  All twelve directed failures now have a compiling side-aware three-state
  normalization. For a left-side probe, a right-endpoint failure has its three
  earlier comparison vertices in the left side; the dual statement holds for
  a right-side probe and a left-endpoint failure. This has now been refined to
  a literal 19-class anomaly/fan state: internal positions are indexed, anomaly
  endpoints are canonical, and one-change forces explicit bridge equalities
  in the canonical, boundary-fan, internal-fan, and fresh-middle-fan branches.
  The 19 classes now map to one four-vertex bridge certificate, and deletion
  packing supplies all twelve directed certificates. Interior certificates
  anchor to their three-polygon frame, so two probes on one frame have equal
  outer-pair colors. An exhaustive five-vertex audit proves this is the exact
  bare-certificate limit: it forces neither a strong five nor any equality
  involving a triple through both probes. The proposed three-probe repair is
  now retired by an independently replayed twelve-vertex SAT model. The model
  has two mutually obstructed `3+3` strong sixes and shared frames in both
  directions, yet avoids every target outcome and every extreme `1+5` or
  `5+1` strong six. The SAT properties remain route-selection evidence, but
  Lean now proves that the exact coloring is sweep-realizable from explicit
  rational coordinates. A bounded Sol/Fable review selected global packing
  conditionally. Sharp-model censuses refute broad extremization, and an LRAT
  dependency shrink for the exact no-internal `7+8` packing contradiction
  still uses 704 deletion clauses across every split. Thus neither a modest
  multi-deletion lemma nor stronger local realizability data survives its
  gate. The pre-vetted fallback returns to designing a new uniform E3 state;
  it must pass the existing all-root transition tests before promotion.
  Bounded countermodels also rule out reducing the route to bare `5+5`,
  `6+4`, or `6+7` block data.
  The first new-state oracle now exhausts all 186,888 decomposable
  eight-vertex colorings under all 18 singleton root contexts at `k=6`.
  Property-relative all-gap observations refine from 5,917 to 7,159 residual
  classes and separate the committed all-gap collision, but the complete
  pair-rank collision remains equivalent. Extreme insertions add no state;
  the new splits come from interior near-threshold chain extensions. The full
  residual truth table is not a candidate invariant. A bounded Sol/Fable
  review at packet SHA-256
  `4058cc55c5850b4630e70a9b413a8773bdbc0251ba00f87cbab7138e5ea7d304`
  rejects freezing the rooted-footprint sketch before its critical-cut
  container, domination order, endpoint incidence, and `k`-only bound are
  defined. The active bounded task is specification and falsification: test
  critical-cut convexity first, then singleton congruence, before any Lean
  promotion or route selection.
  That specification gate now passes after correcting its premise. Successful
  singleton cuts are not one convex interval but two side-labelled endpoint
  rays; Lean proves their closure, external disjointness, exact extension iff,
  and an explicit counterexample to unsplit convexity. The resulting exact
  endpoint-span rank footprint retains the two endpoint gaps of every
  near-threshold cup and cap. Independent programs exhaust all 186,888
  children and 3,363,984 `k=6`, `8 -> 9` singleton extensions: all direct
  observations are readable from the footprint, all singleton transitions are
  collision-free, and both committed profile collisions are separated. The
  raw carrier has 46,699 child classes and one entry per ambient endpoint pair,
  so it is not the desired `k`-only invariant. The complete uniform singleton
  transition now compiles: exact span thresholds have endpoint-comparison
  updates and erase/recover iff laws, the opposite-color mixed chain has size
  at most three, and terminal strong-`k` creation has the expected child
  strong-set or `(k-1)`-chain characterization. The pre-vetted two-vertex gate
  also passes independently: all 762,912 `k=6`, `7+2 -> 9` parents, including
  720,528 interleaved transitions, have zero footprint collisions. The active
  obstruction is no longer singleton or smallest-root congruence but the
  ambient endpoint identities. Lean now proves the first sound dominance
  operation: at a fixed far endpoint, a no-smaller rank whose near endpoint is
  farther toward the singleton supplies every left or right extension of the
  dominated span, for cups and caps. This licenses directional Pareto pruning,
  but it neither forgets the far endpoint nor preserves incidence between
  quotient classes and therefore gives no `k`-only count. Define and falsify
  that incidence-preserving quotient before route selection; reserve the
  larger `8+2 -> 10` census for a concrete quotient candidate. The first
  concrete candidate retains clipped exact-rank histograms, directional
  frontier tags, and coarse endpoint-local incidence types. It is a finite
  `k`-only carrier, merges 80 of the 46,699 raw classes, separates both
  regressions, and passes all 3,363,984 singleton plus 762,912 small two-root
  transitions. The reserved larger gate is decisive: the raw footprint itself
  has zero collisions across all 16,819,920 `8+2 -> 10` parents, but the
  quotient has 320 independently replayed collisions across its 80 nontrivial
  fibers. The first swaps exact ranks three and four between two spans sharing
  a far endpoint. Boundary exact-rank repairs eliminate the failures only by
  becoming injective on every observed raw class. Reject this quotient. The
  pending bounded route review must choose between a rooted-interface state,
  a proof that finite boundary depth stabilizes, or returning the raw
  footprint to a structural counting argument.
  That review ran at evidence-packet SHA-256
  `593e6f8cc88c4c7d7c26175f5d1a864472af90f80e179aa0c83ab783d5cc8aa6`;
  both reviewers selected one final rooted-interface definition and gate,
  with a mandatory structural-count redirect on collision or injectivity.
  The cut-relative candidate retains exact recursive side states and clips the
  distances of crossing rank ports. At depth three it remains noninjective at
  every eight-vertex cut, but an independently replayed lower-root context at
  `[0,5]` gives equal child states and unequal rooted parent states. Depth four
  is already injective on all 46,699 raw classes at the decisive middle cut.
  Lean additionally proves that two-sided dominance has arbitrarily large
  equal-rank diagonal antichains, so retaining the full ordered frontier has
  no dominance-derived `k`-only bound. The finite-interface route is stopped.
  The named structural redirect has passed its first bounded gate. Lean now
  defines the adjacent demand `choose (k-2) (rank-1)`, proves that it bounds
  both one-step published threshold jumps, and packages a unique
  lowest-separating-node allocation for distinct endpoints with an
  opposite-child theorem. Independent programs exhaust all 376,764 compatible
  roots through eight vertices at `k=6`; none of 631,474 exact-rank frontier
  groups exceeds its demand. Lean now defines the exact allocated frontier,
  proves its endpoint antichain and ordering laws, reduces exact parent ranks
  to exact child-ray ranks, and derives the crossing-pair complementary-rank
  bound under no strong `k`-set. It packages the missing combinatorics as
  `AllocatedExactRankSlotting` and proves that such a slot injection implies
  the Pascal bound. The exhaustive gate separately refutes direct cup--cap on
  either endpoint projection, including 996 rank-three groups where both
  projections fail. A two-endpoint transition-ideal construction now survives
  all 631,474 groups, while left-only, right-only, and fixed-label negative
  controls fail. Lean proves that its rectangular lower ideals inject into the
  exact Pascal layer and that the full Hall condition constructs the required
  slotting and capacity bound. The geometry-specific Hall condition is false
  for these endpoint profiles: a kernel-checked decomposable `n=12`, `k=7`,
  rank-three coloring has two distinct allocated spans whose four endpoint
  ideals are all the full `2 x 3` ideal, so their candidate sets are the same
  singleton and even pair expansion fails. This does not violate the frontier
  cardinal bound. A bounded blind Sol/Fable review selects only a falsification
  gate, not a repaired route: rotate-complement one crossing orientation while
  permuting the same untagged Pascal-slot carrier. The gate must first prove
  the involution and encoding laws in Lean, then pass the complete frozen
  frontier and all 631,474 existing `k=6` groups, while targeting
  same-orientation rigid pairs, reflection-fixed ideals, and triple-rigid
  collisions. Any failure stops this repair; only a complete pass permits a
  structural child-ray-incidence lemma and then the global injection into
  `decomposableBinomialWindow`.

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
