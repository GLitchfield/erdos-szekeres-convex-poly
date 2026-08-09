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
  cardinal bound. A bounded blind Sol/Fable review selected a falsification
  gate: rotate-complement one crossing orientation while permuting the same
  untagged Pascal-slot carrier. That gate now passes. Lean proves the
  involution, exact boundary-slot reversal, unchanged Hall-to-capacity bridge,
  and full-versus-empty separation of the frozen pair. Independent cell-mask
  and row-height implementations find no Hall failure on the complete frozen
  `n=12` root frontier or any of the 631,474 existing `k=6` groups, and no
  same-orientation rigid pair, reflection-fixed opposite pair, or triple-rigid
  collision. This is the first positive bounded support for the repair, not a
  general theorem. The structural bridge now compiles. At the unique lowest
  separating node, an exact parent span exposes the forced one of four
  predecessor/successor child rays; the endpoint profile incident to that ray
  is a member of the deterministically orientation-reflected candidate family.
  This removes post-hoc orientation choice but does not prove injectivity or
  Hall. Lean now formalizes closed blocks of the ordered exact-rank frontier,
  proves their left/right endpoint descriptions agree, and identifies them
  with nonempty intrinsic consecutive subfamilies. The direct active-profile
  proof is refuted by an independently replayed five-span `k=6` block whose
  representatives are `0,f,0,f,0`. The innovation proposal to retain the
  whole active endpoint interval also fails the predeclared block gate: in the
  frozen `n=12`, `k=7` root, adjacent cap/rank-three spans `(2,5)` and `(4,6)`
  both have singleton reflected active interval `{3f}`, giving union size one
  for a two-span block. Lean kernel-checks their exact ranks, frontier
  adjacency, candidate equalities, and `activeBlockExpansion_fails`. This does
  not refute the full reflected two-endpoint block target, but it shows that
  the inactive endpoint cannot simply be discarded. The active bounded task
  is now the predeclared skew Bollobás
  set-pair encoding of actual ray events: freeze its noncircular cross-incidence
  hypothesis and exact Pascal accounting, then falsify it on the frozen root
  before attempting Lean. The contrarian contract uses locally constructed
  incident/nonincident event sets of sizes `rank-1` and `k-rank-1`, with
  `earlier.present ∩ later.absent` nonempty; the first gate asks whether
  `(2,5)` has any actual incident event missing at `(4,6)`. That pair gate
  passes, but the complete frozen frontier refutes the exact proposed event
  key: direction/chain/mark makes the first four present sets pairwise
  disjoint, so the fifth span needs four hits in an absent set of size three.
  The active bounded decision now compares a semantic event quotient, exact
  incidence-matrix accounting, and a proof retaining both reflected endpoint
  intervals. The preferred direction/role/complementary-depth quotient also
  fails the frozen adjacent pair: `(2,5)` and `(4,6)` have identical coarse
  incidence keys, so no fiberwise-absent later set can meet the earlier
  present set. The event proposals are stopped. A bounded route audit selected
  exact reflected endpoint-row independence as the sharpest falsifier; Sol
  returned a high-confidence `partially_supported` review, while Fable
  returned a zero-token connection error and no consensus is claimed. The
  exact matrices refute that mechanism on the same root: ranks are `5 < 6`
  for cap/rank three and `3 < 4` for cup/rank four. The remaining two-lane
  proposal now has a precise local boundary. Fixed meet-earlier/join-later is
  false, while either locally valid assignment passes all 738 frozen adjacent
  ideal pairs. Lean proves that the flexible rule plus every two-family
  expansion test is abstractly insufficient: three identical two-element
  transition intervals have no SDR. The first exact one-hole rule now passes
  all 5,208 frozen cap/rank-three states: every blocked singleton-family hole
  reaches a 7-, 9-, or 10-candidate hole after one ownership transfer and is
  then fillable. Lean proves generic completion, transfer preservation,
  cardinality exit, well-founded descent-to-SDR, and the reviewed
  singleton-or-block-large implication. That profile fails on the frozen
  seven-span cup/rank-three group, whose intermediate family sizes are
  `6,6,3,6`. The unchanged priority then fails on its complete 78,236-state
  graph: 72 states reach 36 two-cycles. A direct length-two augmentation
  bypasses the cycles: all 4,888 blocked states in the four full groups, and
  all 5,977 blocked states in their 62 nonempty consecutive subblocks, have an
  exit in independent cell-mask and row-height checks. Lean proves that an
  explicit exit completes the SDR and yields block Hall. Lean now identifies
  the obstruction exactly: a closed saturated actual-owner star is equivalent
  to a blocked state with no two-step exit. A block-large actual star forces an
  exit, while the stronger state-free feasible-owner-star profile implies that
  actual-star bound. With a separately supplied one-hole state on each
  nonempty block, the profile proves consecutive-block expansion; reflected
  endpoint families are formally nonempty. Experiment 0041 passes that
  state-free profile for all 247 feasible owner maps on the 62 frozen blocks,
  with minimum slack `+1`. Reflection is now normalized in Lean as an
  order-reversing lattice involution preserving transition intervals.
  Experiment 0042 passes the stronger block-large reached-owner profile on all
  247 maps, again with minimum slack `+1`, and Lean proves that this profile
  implies owner-star expansion. A clean zero-round Sol review selected a
  deterministic facing-lane gap charge as the cheapest falsifier; Fable was
  unavailable at its usage limit. Experiment 0043 refutes that rule on the
  tight cap witness because the second charge faces the rigid singleton lane
  `{3f}`. Experiment 0044 passes the active block-large profile on all 631,474
  decomposable `k = 6` reflected frontier groups through eight vertices. Its
  3,792 nonvacuous block/hole checks have minimum bottleneck slack `+1`, and
  Lean proves that profile failure is exactly a feasible injective map into
  block-small owners. All 3,792 also have a normalized endpoint-extreme ideal
  with no compatible block-small owner; Lean proves that this forced-extreme
  contract implies the active profile. Experiment 0045 refutes maximum single-lane cell spread
  as the missing bridge: the tight cap owner has seven candidates but spread
  bound `5 < 6`. The active task is still to prove the arbitrary genuine
  block-large reached-owner profile from exact-rank two-lane incidence.
  Experiment 0046 refutes the forced-extreme strengthening on four frozen
  `k = 7` cup holes; the first instead has a two-ideal anchor `{f,1f}` with one
  block-small neighbor. The active local contract is therefore the compiled
  small-owner deficiency, which permits a multi-ideal anchor. Experiments
  0047--0048 identify its surviving shape on all 3,056 nonvacuous holes over
  decomposable `k = 7` roots through eight vertices, but that census did not
  test the certificate obligation on the other 2,419,060 holes. Experiment
  0050 appeared to close that bounded evidence gap, but a post-audit found its
  shared group generator explicitly required `rank >= 3`. Its 2,422,116 holes
  and 514 genuine two-gap paths therefore support only the active-ray range.
  Dedicated Experiment 0051 changes the route. A rank-two lane path fails at
  support size five, reflected Hall fails at size six, and a complete
  independent census through size eight finds 2,896 direct Pascal-capacity
  violations among 732,172 rank-two groups. Lean now proves the conceptual
  normal form: exact rank-two spans exclude active-child interior vertices,
  and the retained frontier is exactly the adjacent child changes in sweep
  order. A kernel-checked open decomposable seven-vertex example has six such
  spans against `publishedSpanPascalDemand 7 2 = 5`, so its
  `AllocatedExactRankSlotting` type is empty. The individual-frontier Pascal
  allocation is therefore retired at rank two, not merely missing a proof.
  The rank-at-least-three trace/Hall subroute remains unrefuted, but it cannot
  by itself yield the advertised all-rank local recurrence. The active route
  decision must either group rank-two alternations into at most `k - 2`
  charged objects or replace the per-rank frontier recurrence with a coupled
  accounting that pays for rank two elsewhere. Neither replacement may assume
  Hall, slotting, the disputed capacity bound, or finite enumeration. The
  first reviewed replacement—sum local rank-two adjacencies at their unique
  lowest separating nodes and bound them by the global `support.card - 1`
  gaps—is also retired. Lean checks a three-vertex interleaved tree whose root
  contributes `(0,1),(1,2)` and whose child contributes `(0,2)`, giving three
  distinct local charges against two global gaps. The route now needs a
  quotient or coupled arithmetic contract that survives both this example
  and the seven-vertex alternating `6 > 5` obstruction.
  Experiment 0052 supplies the first replacement that survives those gates.
  In the binary merge word, all but the first crossing transition are paired
  with hidden child gaps. Hidden lower gaps give cap spans of ambient rank at
  least three and hidden upper gaps give cup spans; Lean proves both color
  bridges and the run-count identity. A complete independent `k = 7` census
  through size eight makes 392,562 color-compatible promotions and finds no
  capacity or endpoint-candidate failure in 1,913,894 adjusted groups. The
  promoted gaps are noncrossing, however, so they lie outside the existing
  allocated-frontier carrier. The active theorem-design target is an explicit
  ambient promoted carrier and canonical run-gap matching, followed by a
  noncrossing rank-ideal incidence bridge and a coupled recurrence theorem.
  The carrier is now compiled: every compatible hidden gap receives an exact
  parent-support rank, a nonempty endpoint-ideal family, and nonempty encoded
  Pascal-slot candidates without assuming crossing or Hall. The canonical
  run-gap matching is also compiled as an exact equivalence between hidden
  sources plus one initial transition and all parent crossings. Its fixed-color
  corollary identifies the residual rank-two cardinality as the opposite-color
  hidden count plus one. `AdjustedHigherRankDemand` now combines fixed-rank
  crossing and promoted carriers; Lean proves common exact-rank semantics,
  incident endpoint-profile corners, and that adjusted Hall would imply the
  published Pascal capacity. Experiment 0053 now refutes that exact target.
  An explicit open decomposable alternating ten-point root has seven crossing
  and four promoted cap/rank-three demands, so Lean proves `11 > 10`, negates
  adjusted Hall, and makes the proposed slotting type empty. The independent
  certificate also computes 36 raw adjusted obligations across both colors
  and all ranks against 31 nonempty slots in one untagged Pascal window, so
  additive cross-rank aggregation is retired as well. The hidden-gap genealogy
  remains valid local machinery. A bounded Sol review rates that conclusion
  `partially_supported`; Fable returned zero tokens at its usage limit. The
  next bounded route gate tested an exclusive-choice conservation model on the
  exact ten-point witness: each hidden source and canonical transition became
  one charge with alternative representations in the single untagged
  32-element carrier. It also fails. The 27-charge graph has maximum matching
  20, with a compact Hall witness of 20 demands and 13 neighbors. A bounded
  review then selected common-span cross-color reuse as the sharpest next
  falsifier. Experiment 0054 merges the seven identical-endpoint cap/cup
  rank-three pairs and intersects their candidate families; the resulting
  20-charge graph has a perfect matching. The apparent repair has no published
  semantics. Lean proves that all seven pairs are genuine common frontiers,
  that their cup and cap rays live in disjoint lower and upper retained cores,
  and that no nonempty retained subset lies in both. It also proves the exact
  arithmetic obstruction: the two `k = 7`, rank-three successor thresholds
  total 32, whereas the two bases plus one shared ten-element coefficient
  total 22. Common endpoints alone are therefore retired as a proof-reuse
  rule. Containment-minimal frontiers remain parked without a semantic
  dominance theorem. The next theorem-design target is a branch-indexed,
  tree-global conserved charge with an owned retained object and an explicit
  nonreuse law; it must pass both the three-vertex local/global-gap obstruction
  and the ten-point witness before any new Hall theorem is selected. That
  conservation target now compiles. Gap-or-sentinel tokens are equivalent to
  actual support vertices, merge owner-preservingly across disjoint splits,
  agree with the hidden-gap genealogy, and fold over an explicit decomposition
  tree with leaf-address nonreuse. Exact three- and ten-point regressions pass.
  Lean also selects the unique saturated published branch and its actual core.
  A bounded Sol review at packet SHA-256
  `fbdd71e0ca938691364140abbf35412390107762248744033d25690758808b12`
  rated the bridge only `partially_supported`; Fable returned zero tokens at
  its usage limit, so no consensus is claimed. Sol's cheapest owner-membership
  gate is now formally refuted at the first `(4,6,6,3,2)` scalar boundary: a
  hidden lower gap keeps its right-endpoint owner in the lower child although
  the unique saturated branch is upper. The corrected active object is the
  entering-crossing pivot. Lean proves that these pivots lie in the selected
  opposite child, are injective over hidden sources, and can all be placed in
  one published core conditional on the exact core-capacity inequality. Pure
  source-child counting cannot prove that inequality: the feasible
  `(4,8,8,3,4)`, `10+13` scalar gate permits nine source adjacencies against an
  eight-vertex upper core. The first geometry-sensitive theorem now closes
  that leak. The minimum lower vertex is a common left cone point for every
  canonical hidden-lower pivot. No parent four-cap makes the complete pivot
  seed a cup, so no parent `u`-cup bounds it by `u-1`; Lean proves the
  color-dual result as well. At `(4,8,8,3,4)`, `10+13`, the source count is at
  most seven and all pivots fit in one actual eight-vertex published upper
  core. The higher-index cone bridge now compiles. No parent `(a+1)`-cap makes
  the complete hidden-lower pivot seed avoid an `a`-cap, with a color-dual cup
  theorem. Ordinary cup--cap counting is insufficient—at `(5,8,8)` it gives
  28 against a 23-vertex core—but inherited decomposability and the strictly
  smaller `DecomposableStateUpper 4 8 8` bound the seed by 22. Uniformly, a
  predecessor state at the selected index constructs one actual published
  slice retaining every pivot. The well-founded state-transition shell now
  compiles: validity of either saturated branch gives the exact successor
  equality, strict descent of the joint measure `a + u`, and the corresponding
  local parent avoidance. Using only a strictly smaller predecessor state,
  Lean selects an actual published core containing every canonical pivot; a
  single dispatcher first chooses the unique valid saturated branch. An
  independent frozen-diff review accepted the equality directions,
  predecessor uses, compilation, and axiom profile. The result is still
  conditional machinery, not the outer state. The outer recursion has now
  been isolated exactly: at every positive threshold, the hereditary
  `DecomposableStateUpper` is equivalent to a single root-local transition for
  two already-bounded children. Lean also extracts a nonempty decomposable
  threshold-plus-one subsplit from any larger root, and turns simultaneous
  root-pivot retention into a source-cardinality bound by the selected core.
  That scalar bound does not close the transition: the `(4,8,8)`, `10+13`
  boundary remains consistent with eight sources paid by an eight-vertex
  predecessor core. Moreover, nested set-level split data can reuse the same
  canonical pivot at distinct candidate addresses; this is not yet a realized
  colored decomposition-tree counterexample, but it blocks untagged all-node
  injectivity as a general set-theoretic lemma. Bounded route review at evidence
  packet SHA-256
  `bf8dfc26718600f2874fb8530fef8e097c3db89f3bd1197cea9882b9579e16cd`
  returned Fable `GO` and Sol `MODIFY`; both prioritized the root-local route
  and treated the interface as architectural rather than the missing
  combinatorics. The ensuing exact accounting compiles: visible and hidden
  child adjacencies partition the source gaps, and residual payment is
  equivalent to a visible-core bound. The central-cut theorem refutes that
  payment at `(4,8,8)`, `10+13`: there is at most one hidden lower gap and at
  least eight visible adjacencies. A two-extrema core reserve is valid but too
  weak. The cut instead produces ordered upper cup blocks of sizes six and
  seven. `StructuralChargingCupBlocks67Symbolic.lean` proves directly that
  every such `6+7` or `7+6` one-change configuration contains a four-cap, an
  eight-cup, or a strong eight-set. Arbitrary-set transport therefore gives
  `upper.card ≤ 12`, eliminates `10+13`, and narrows an exact 23-vertex root to
  `11 ≤ lower.card` and `upper.card ≤ 12`. That entire residual window now
  closes by an elementary three-regime staircase: the children contain
  crossing cup/cap pairs `(5,3)`, `(6,2)`, or `(7,1)`, each of which glues to
  a forbidden strong eight-set. Lean proves both
  `criticalRootImpossible_488` and the unconditional hereditary theorem
  `decomposableStateUpper_488`; an independent frozen-file review accepted the
  proof and reported only the standard Lean axioms. Four proposed smaller
  cup-block shortcuts are separately SAT-refuted. The next bottom-up fixed-`k=8`
  state is `(5,7,8)`, before the `(5,8,8)` state that consumes `(4,8,8)`
  through the higher cone. Exact index arithmetic excludes lower sizes
  `11..40` but leaves two oriented tails: `1..10` against `41..32`, and
  `41+1`. Color duality does not identify them inside the asymmetric state.
  The first bounded gate restricts the small-lower tail to `1+32`. Its two
  upper sweep sides are four-cap-free, have sizes `11..21`, and each contain a
  five-cup, but the extracted `5+q+5` force statement is false by an explicit
  kernel-checked recursively decomposable counterexample. The active lower
  route now has a compiled cap-reservoir invariant: every 23-vertex upper
  restriction contains a four-cap, all such caps straddle the root, and three
  can be selected disjointly. A checked 13-vertex model shows that those three
  caps alone are insufficient, so the next gate must retain the full density
  and decomposition-tree ownership. The upper-singleton extreme remains
  separate. The tree-global ledger returns only if a reservoir charge
  forces descendant aggregation. No new Hall
  theorem or Boolean-code injection is selected. A bounded independent
  lemma-forge pilot rejected duplicate
  four-point localization, parked insertion-signature and universal
  binary-fingerprint proposals, and retained only planar rooted-triangle
  circuit elimination for a sharper consumer audit. A bounded Sol/Fable
  review then rejected a nine-vertex cap transversal: density forces every
  transversal to have at least ten vertices, and Lean proves that the proposed
  nine-transversal gate is equivalent to the full singleton-lower gate.
  Common-root straddling also makes the existing weakly ordered cap-family
  capacity theorem vacuous beyond one cap. Threshold-frontier extraction and
  minimum-span selection compile, but the avoidance-free strict-span
  recurrence is now refuted in Lean by an exact recursively decomposable
  `32/23` dense common-cut construction. The construction contains a compiled
  seven-cup and therefore is not an open `(5,7,8)` counterexample. The
  surviving open-state reduction chooses a terminal cap: its open span has at
  most 21 vertices, leaving at least nine genuine outer-tail vertices with
  only the before/after endpoint bridge failures. At the cap's unique lowest
  separating tree split, strong-eight avoidance forces either a `1+3` profile
  with no lower five-cup or a `2+2` profile with no lower six-cup. The strict
  `(5,5,8)` predecessor further bounds the first lower child by 20. In the
  `2+2` branch the cap word is necessarily lower--upper--upper--lower, making
  every internal endpoint bridge automatic. A nine-vertex recursive Lean
  counterexample refutes the resulting five-internal-tail force gate. The
  surviving exact residual has either five internal tails or five external
  tails; every external tail has a concrete first-exit address where the cap
  is wholly in the lower child and the tail is in the upper child. The
  lower-sibling supports along that path are pairwise disjoint and ordered;
  any four-cap fully covered by them must have a two-vertex bucket collision.
  Global `32/23` density now yields a minimum residual-cap transversal of at
  least six terminal tails. Each selected tail owns a distinct private
  four-cap and is routed internally or to a lower first exit, so the actual
  state has three private owners of one route class. This does not yet give
  additive cap charges: a 17-vertex Lean counterexample refutes forcing two
  tails in every secondary cap, while a separate nine-vertex target-free
  decomposable example has six distinct private caps sharing one three-point
  core. Lean nevertheless proves the general mixed-cap word law: both middle
  sweep vertices are upper and lower vertices are confined to endpoints. The
  post-result Sol/Fable review selects a single owner-aware interface: an
  external private cap either has a non-owner vertex uncovered by all path
  buckets or has a two-vertex bucket collision. That theorem now compiles.
  The finite whole-cap trace milestone is now complete. A cap's shallowest
  false step forces its two middle vertices into one sibling bucket, so an
  external private cap either first peels at a true step or has a certified
  collision. The actual state supplies three owners with this residual. An
  exact eight-vertex terminal, decomposable, target-free Lean example realizes
  a true peel followed by the owner's false exit with no collision. This
  triggers the recorded formal expiry of cap-by-cap tracing. The one density
  reserve proves that every set of at most five vertices misses a residual
  cap, but cannot bound overlap among the six chosen caps. The active overflow
  is therefore the `41+1` tail. It now reduces to an exact 32-vertex
  color-dual `(7,5,8)` singleton-lower gate, and every decomposable 23-subset
  of that reservoir contains a four-cup. Conditional on the strict `(4,5,8)`
  predecessor, that density now yields three disjoint four-cups and three
  further disjoint four-caps. Their first joint splits obey exact endpoint
  classifiers, and any common split carries a three-vertex defense on one
  color. Pairwise address synchronization is nevertheless expired: Lean
  certifies a target-free reverse-separated cup--cap pair. Regenerating a cap
  inside the 12 cup vertices leaves the precise disjoint-cup or `2+1+1`
  incidence alternative. A target-free signotope realizes the latter but is
  not recursively decomposable, while a bounded 50,000-tree decomposable
  sample found no witness. The active theorem must therefore use recursive
  decomposability essentially to eliminate those two regeneration branches;
  neither singleton tail is closed.

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
