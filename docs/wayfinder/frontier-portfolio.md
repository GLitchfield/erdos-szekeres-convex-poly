---
title: Exact Erdős--Szekeres frontier portfolio
artifact: frontier-portfolio
schema_version: 2
status: canonical
last_updated: 2026-08-15
---

# Frontier portfolio

This file is the canonical registry of every currently credible thread that
could materially advance the exact Erdős--Szekeres project.  It is deliberately
broader than the set of threads being worked on in any one session.

The portfolio answers:

> Which mathematical or research-system threads remain potentially valuable,
> what evidence supports them, and what result would advance, suspend, merge,
> revive, or retire each one?

It does **not** answer:

> Which threads should occupy the available worker slots in the next execution
> block?

That second question is an execution-planning decision made from a snapshot of
this registry.  Keeping the two questions separate prevents temporary resource
limits, agent availability, or a recent local success from silently deleting
other valuable approaches.

## Formal definition

Let `P` be the frontier portfolio.  An entry belongs to `P` when it has all of
the following:

1. a plausible contribution path to the exact formula, a prerequisite theorem,
   a documented obstruction, or a research-system capability that measurably
   improves mathematical throughput or evidence reliability;
2. an explicit model tier and evidence level;
3. a named downstream consumer or route-level payoff;
4. a current open obstruction;
5. a bounded next discriminating gate; and
6. a success payoff plus an expiry, suspension, merge, or revival condition.

Portfolio membership does not imply architectural independence.  Every entry
also identifies the stable mechanism family whose evidence streak it inherits,
the exact load-bearing dependency it can affect, the strongest scope its
current evidence reaches, and the generalization bridge still missing.

A vague idea without a consumer or discriminating gate belongs in Wayfinder
fog, a ticket, an experiment note, or a lemma-forge batch—not yet in `P`.

An execution slate `E` is a temporary selection satisfying

```text
E ⊆ {t ∈ P | t is presently executable under its gate and dependencies}.
```

The size of `E` is determined by available concurrency, approval, resource, and
evidence-isolation constraints.  Selection into or omission from `E` does not
change membership in `P`.  In particular:

- a valuable thread is not demoted merely because all worker slots are full;
- a selected thread is not promoted merely because work was performed on it;
- an unselected thread retains its evidence, next gate, and revival condition;
- scheduling metadata—agent names, slot numbers, wall-time forecasts, and task
  packets—does not belong in this file.

## Record schema

Every registry entry has a stable `FP-NN` identifier and the following required
fields:

- **Contribution:** how the thread can advance the exact project.
- **Mechanism family:** the stable mathematical architecture shared with any
  correlated parent, child, or sibling entries.
- **Named destination dependency:** the exact edge in the load-bearing ledger,
  or a named subordinate dependency, that the thread can close.
- **Strategic role:** one of `direct`, `bridge`, `generalization`, `hedge`,
  `fallback`, `discovery`, or `research-system`.
- **State:** one of `advancing`, `probing`, `gated`, `parked`, `suspended`,
  `merged`, `completed`, or `retired`.
- **Model tier:** the precise mathematical universe in which its claims live.
- **Scope ceiling:** the strongest finite, restricted-class, or uniform claim
  that the current admitted evidence can support.
- **Best evidence:** the strongest current evidence, using repository claim
  levels and never upgrading computation or consensus into a theorem.
- **Missing generalization bridge:** what must still be proved before the
  current scope can affect a uniform parent route.
- **Last forward result:** the most recent compiling theorem that closed or
  strictly reduced a named dependency, or an explicit statement that none has
  occurred on the load-bearing ledger.
- **Downstream consumer:** the theorem, ticket, or route enabled by success.
- **Open obstruction:** the smallest honest unresolved issue.
- **Next discriminating gate:** the cheapest bounded work that materially
  changes the route disposition.
- **Success payoff:** what becomes available if that gate succeeds.
- **Expiry or revival gate:** the exact evidence that stops, suspends, merges,
  or reactivates the thread.
- **Children:** stable subthread identifiers, or `none`.

`State` records mathematical disposition, not current scheduling:

- `advancing` means recent forward proof movement and a ready next gate capable
  of producing a compiling theorem that closes or strictly reduces a named
  dependency;
- `probing` means proof movement is not claimed, but a concrete reproducible
  observation supports a bounded, high-information test between live
  mathematical explanations;
- `gated` means valuable but waiting on a prerequisite or discriminating test;
- `parked` means no current gate justifies resources, although a new mechanism
  could reactivate it;
- `suspended` means known controls forbid ordinary continuation and a stated
  revival condition is mandatory;
- `merged` means the result remains valuable through another portfolio entry
  but has no independent execution lane;
- `completed` means its intended bounded contribution is finished; and
- `retired` means decisive evidence rejects the contribution path.  Retired
  entries move to the historical register rather than disappearing.

## Frontier execution cycle

Every substantial multi-thread research block follows the same closed loop:

1. **Close and integrate the previous run.** Every selected thread must land on
   its predeclared outcome, an explicit bounded stop, or a documented
   carry-forward point. Verify the evidence claim, report every thread, perform
   serialized integration, and record actual time and resource use.
2. **Reconcile this portfolio.** Update every affected stable entry from the
   admitted results, including newly valuable children or main threads and
   preserved counterexamples. Name the exact load-bearing ledger edge changed,
   or state that none changed. Validate the registry before making a new
   selection.
3. **Select an execution slate of size `N`.** Choose from the now-current
   executable entries using leverage, readiness, independence, information
   gain, calibrated cost, concurrency, and focus expiry. Label every slot
   `proof-producing` or `information-gathering`, count both kinds, and assess
   independence by mechanism family. Record the selection rationale separately
   from the registry.
4. **Plan the entire slate.** Plan each selected thread as far ahead as its
   dependency tree honestly permits. Freeze exact targets, outcome branches,
   evidence gates, budgets, approval needs, and stop conditions, and state what
   work follows each outcome. Present the complete slate for user approval.
5. **Execute the approved slate.** Use immutable packets, disjoint ownership,
   parallel mathematical breadth, serialized builders and integration, and
   regular progress reports. At the execution boundary, return to step 1.

This order matters. Results cannot alter the registry until their evidence is
admitted, and a new slate cannot be selected until the registry reflects the
previous run. Planning “as far ahead as possible” means branching where future
work depends on an unresolved outcome; it does not mean pretending that one
branch is already known to hold.

## How to use the portfolio

### Orient research

At the start of strategic work:

1. read `docs/wayfinder/map.md`;
2. run `python3 scripts/wayfinder_status.py`;
3. read this file before proposing an execution slate; and
4. inspect the ticket and evidence named by each candidate thread.

The map states the destination and major decisions.  This portfolio inventories
the viable contribution paths.  Tickets resolve sharp decisions.  Experiment
notes and Lean files carry evidence.

### Select an execution slate

Selection is a separate planning operation.  Compare executable portfolio
entries using:

1. distance and load-bearingness to the exact formula;
2. readiness of a precise theorem or falsifier;
3. independence of failure modes and downstream consumers;
4. expected information gained on success **or failure**;
5. empirical cost and resource compatibility; and
6. focus-expiry history, especially repeated open-ended work on one obstruction.

The resulting plan references `FP-NN` identifiers and gives each selected work
item its own outcome contract, forecast, approvals, immutable packet, and stop
conditions.  Those execution artifacts do not redefine the portfolio.

By default, no more than half the slots in one slate should belong to the same
mechanism family.  A more concentrated slate requires an explicit mathematical
justification.  A slate with no proof-producing slot is an exploration slate,
not a proof-advancement block.

As a default breadth rule, a substantial batch should include distinct
mathematical functions—for example one unrestricted producer, one concrete
decomposable obstruction, and one generalization or falsification lane.  This
is a scheduling heuristic, not a membership rule.

### Interpret results

At an integration boundary, report for every selected thread:

- the predeclared outcome that occurred;
- its exact evidence level;
- what changed in the contribution path;
- the before/after unresolved obligation sets and strict measure decrease for
  any claimed reduction;
- the new obstruction and next gate; and
- whether the portfolio state changed.

Agent activity, elapsed time, solver agreement, or prose consensus alone never
changes a thread's evidence level.

## How to update the portfolio

Update this file when a result changes any required record field, when a new
credible contribution path appears, or when a route is merged, parked,
suspended, revived, completed, or retired.

1. **Admit evidence.** Verify the relevant Lean gate, independent computation,
   source, or reviewed proposal and state its exact model tier.
2. **Update in place.** Preserve the stable ID.  Replace stale evidence,
   obstruction, next gate, payoff, expiry, scope ceiling, missing bridge, and
   last-forward-result text; do not append a second competing status paragraph.
3. **Add a thread conservatively.** Require every schema field.  If the idea is
   still indistinct, keep it in fog or under `FP-13` until it acquires a named
   consumer and falsifier.
4. **Preserve negative knowledge.** Mark a thread `retired`, `merged`,
   `parked`, or `suspended` with the decisive control.  Do not erase it and
   allow a later session to rediscover the same failed route.
5. **Review strategic changes.** Adding a new main route, retiring one, or
   materially changing the leading route requires the bounded Sol/Fable review
   used by Wayfinder.  Ordinary evidence refresh and implementation of an
   already-vetted contract do not.
6. **Align summaries.** Keep the concise portfolio link and strategic summary
   in `map.md` current.  Detailed execution history may remain in
   `docs/formalization_plan.md`, but that file is not the live registry.
7. **Validate.** Run `python3 scripts/check_frontier_portfolio.py`, then the
   normal repository gates before committing.

A finite or restricted-class theorem advances a uniform parent only when it
closes a required base case in an already-defined induction or proves a
parameterized lemma used beyond that instance.  After an exact SAT or UNSAT
gate, further certificate work needs either a named Lean theorem it can close
or a frozen semantic-extraction hypothesis; proof shrinking alone is not a new
mathematical gate.

When evidence suggests several possible child attacks but none yet merits a
new main entry, assign stable child IDs such as `FP-02.A`.  Promote a child to a
new `FP-NN` entry only when it has a distinct contribution path or failure mode
that deserves independent retention and scheduling consideration.

## Current registry

### FP-01 — Predecessor half-subset producer

- **Contribution:** Produce a strong-`(k-1)`-free support containing at least
  half the vertices and feed it directly to the unrestricted exact recurrence.
- **Mechanism family:** predecessor-half.
- **Named destination dependency:** `D-HALF`, the uniform
  `PredecessorHalfSubsetAt k` producer.
- **Strategic role:** direct.
- **State:** suspended.
- **Model tier:** sweep-realizable colorings for the uniform claim; bounded
  controls also cover abstract `OneChangeOn` colorings.
- **Scope ceiling:** a uniform recurrence consumer plus exact Fin8/Fin10 fan
  theorems and bounded Fin9--Fin11 controls; no uniform producer.
- **Best evidence:** the generic consumer into `PredecessorHalfSubsetAt`
  compiles; exact Fin8 and nonvacuous Fin10 fan theorems compile.  Deleting
  only the Fin10 certificate's OneChange clauses makes it satisfiable, and the
  independently checked model violates `OneChangeOn` on 77 four-sets.  This
  confirms that the already proved four-point law is causally essential to the
  finite theorem; it is diagnostic rather than a new producer.  The complete
  Fin11 synchronized-fan negation has independently replayed computational
  evidence through both the 479,434-addition full LRAT and an exhaustive
  depth-six decomposition into 64 independently certified cubes.  Cube leaves
  reduce to 17,089--61,302 additions and at most 28.4 MiB each, but every leaf
  retains 9,181--12,010 semantic base clauses.  The predeclared 8,000-base gate
  therefore stopped before Lean, so no Fin11 theorem is claimed.  A bounded
  2026-08-13 literature synthesis, at analysis rather than theorem level,
  identifies the exact split-polygon down-set injection and its missing common
  endpoint as a candidate semantic mechanism.  The repository already defines
  the underlying pair ranks and down-set membership, while
  `exists_realizable_pairRankState_collision` formally rules out using a
  clipped child pair-rank matrix as a recursive state.  A read-only
  adversarial audit has now frozen the arbitrary-coloring endpoint lemma
  `ambientEndpoint_separated_or_crossed`: a nonsaturated cap/cup pair-rank
  maximizer either creates a strict full-ambient down-set difference at the
  next endpoint or the two maximizing endpoints cross.  The compiled Fin9
  collision realizes exactly the crossed branch, so it does not refute the
  lemma.  That exact dichotomy, its clipped-rank extension helper, the
  structured `AmbientDownsetThresholdHalfSupportAtSix` producer interface, and
  the noncircular consumer into `PredecessorHalfSubsetAt 6` now compile.  An
  independent proof-boundary review accepted the signatures, model tier, and
  absence of same-`k` circularity.  The exact rational Fin9 counterexample now
  compiles at the sweep-realizable tier: all 84 determinants are nonzero, all
  84 six-subsets fail the strong-polygon law, the Boolean full-ambient rank
  bridge is proved, and `not_ambientDownsetThresholdHalfSupportAtSix` closes all
  16 threshold cells and complements.  Thus the single-cell support card is
  formally expired, while the local endpoint dichotomy, synchronized fans,
  and `PredecessorHalfSubsetAt 6` remain alive.  Its first genuinely collective
  successor also has bounded evidence: an adaptive Boolean combination of two
  full-ambient cells succeeds on the stored Fin9 witness, all 3,210 target-free
  models in the reused rational domain, and all 60 target-free models in a
  fresh Fin9/Fin10 domain.  The hardest tested model still admits 34 of the
  4,096 classifiers.  Independent replay and three corruption controls pass;
  this is computational evidence for a candidate, not a uniform selector or
  theorem.
- **Missing generalization bridge:** a canonical all-`k`, all-size mechanism
  selecting or synchronizing a half-sized predecessor-free support; arbitrary
  existence among many finite classifiers is insufficient.
- **Last forward result:** `halfPureSingletonFanAtSixFinTen_of_oneChange`
  compiles at the first nonvacuous finite boundary.  The later single-cell,
  selector, local-exchange, and interval/Helly outcomes are backward or neutral
  and did not change `D-HALF`.
- **Downstream consumer:** `sweepExactUpperAt_of_predecessorHalfSubset`, then
  the unrestricted exact upper bound.
- **Open obstruction:** the common choice of one pivot, direction, and
  half-sized predecessor-free support remains the producer.  The cell pair and
  truth table may currently depend arbitrarily on the coloring; finite rational
  survival does not explain how sweep geometry selects them.  Merely
  controlling crossed or clipping-saturated transitions cannot repair the
  formally refuted single-cell producer.
  The first frozen noncircular selector, based on robust orientation balance
  and pair-rank distance, passed all 3,271 inherited target-free controls
  generated from 429,123 rational configurations.  An independently checked
  held-out rational Fin9 family nevertheless refutes it at admitted ordinal
  1,459.  That model still has 22 successful Boolean two-cell supports, so the
  selector is expired but the existential collective card remains alive.
  A second selector mechanism is now formalized separately: the full 4,096
  classifier domain, defect, radius-one/radius-two exchange relation, adaptive
  cardinality lemma, and conditional consumer into `PredecessorHalfSubsetAt 6`
  compile.  Exhaustive independently replayed controls refute the required
  local descent.  The stored Fin9 model has 535 positive-defect radius-one
  local minima and 265 radius-two local minima while retaining 44 successful
  classifiers.  Thus bounded local exchange is expired as a producer, but the
  collective existence card remains unrefuted.  Net proof movement for this
  mechanism is backward: the conditional consumer is reusable infrastructure,
  but no destination dependency closed and the selector obligation is not
  smaller.  The planning consequence is expiry of bounded local exchange.
  A realization-cell interval/Helly audit now expires another descendant.
  Pair-line cells can control the pivot-versus-pair signs, but not the separate
  five-ary purity condition.  Putting the global support, pivot, and direction
  into an interval frame simply restores the original selector; removing them
  loses the direct half-support consumer.  No strict measure decreases, and
  the still-blind held-out family was not opened.
  Separately, an exact indexed grouping compresses the minimum Fin11 cube from
  9,181 ground base clauses to 3,527 complete object/unit families, with
  literal-for-literal expansion and omitted-index/corrupted-family rejection.
  The first monolithic FromLRAT leaf still exhausted the 16-GiB gate, so
  kernel-memory structure rather than family count is now the certificate
  blocker.  After a kernel Fin11 theorem, turn
  compatible ten-point singleton fans into one half-sized fan with a common
  pivot and direction for arbitrary size.
- **Next discriminating gate:** none while suspended.  Do not retune the
  selectors, enlarge the exchange radius, open the held-out family for the
  interval descendant, or repackage the common support as a frame.  Revival
  requires a genuinely new positive theorem or published mechanism that
  constructs a common support without assuming a global selector.  Fin11
  certificate work remains separate in `FP-14.B`.
- **Success payoff:** a credible uniform producer for the unrestricted route.
- **Expiry or revival gate:** the single-cell ambient-threshold producer is
  formally expired by the compiling exact rational Fin9 counterexample.  A
  checked realizable target-free
  counterexample to synchronized compatible fans retires that separate child;
  the two-cell collective card expires on one checked target-free model with no
  successful classifier and advances only through a noncircular selector.  The
  frozen robust orientation-balance/rank-distance selector is specifically
  expired by the held-out Fin9 model and must not be retuned in place.  Any
  producer whose only progress measure is strict defect descent within
  Hamming radius one or two is also expired by the exact local minima.  The
  interval/consecutive-ones descendant is expired because its interval
  producer contains the original global support choice.  The mechanism-family
  negative streak now triggers suspension under the portfolio rules; revive
  only on a genuinely new positive producer.
- **Children:** `FP-01.A` synchronized singleton fans; `FP-01.B` ambient
  endpoint-synchronized down-sets; `FP-01.C` adaptive two-cell Boolean
  down-set support; `FP-07` integral Property B; `FP-08` fractional cover.

### FP-02 — State-567 ten-residual system

- **Contribution:** Close the first concrete packed decomposable obstruction
  using two strong six-carriers, an exact ten-point residual, and repeated
  deletion packing.
- **Mechanism family:** decomposable-pascal.
- **Named destination dependency:** the state-567 subordinate obligation of
  `D-DECOMP`.
- **Strategic role:** direct.
- **State:** advancing.
- **Model tier:** ordered `TripleColoring` with the exact packed state-567
  hypotheses; realizability or decomposability is added only when retained by
  an explicit bridge.
- **Scope ceiling:** the exact packed state-567 branch; current Lean evidence
  closes the mixed omission profile but not the balanced or collision
  terminals, `k=7` as a whole, or the uniform decomposable theorem.
- **Best evidence:** probe reuse, carrier normalization, omission rectangles,
  area profiles, canonical provenance, and the full mixed six-rectangle normal
  form compile.  The quotient-free all-order certificate, all semantic clauses,
  arbitrary-placement transport, and exact public theorem
  `mixedCarrierOnlyOmissionNormalForm_forces_target567` compile.  The exact
  `packedInternalPair_has_sameOccupancyCollision_or_balancedGrid567` consumer
  now compiles, formally eliminating the mixed omission profile.  The
  color-free `15 > 4*3` pair-cover theorem supplies a three-point carrier
  transversal meeting both carriers and all four grid witnesses.  With
  canonical provenance and a new use of global deletion packing,
  `packedInternalPair_has_balancedResidualTouchingEscape567_of_noCollision`
  compiles: after deleting that transversal and any residual triple, a strong
  six remains and must genuinely meet the ten-point residual.  A source-level
  compression audit now factors this conclusion through a three-carrier
  transversal hitting every carrier-contained strong six and only the 120
  deletions formed with residual triples.  The exact raw witness ledger falls
  from 597,500,904 occurrences to 960,960, a factor of 621.775.  The exact
  interfaces `HitsEveryCarrierStrongSix567`,
  `TargetedResidualTriplePacking567`, their residual-touching equivalence, and
  the global-to-targeted packing bridge now compile.  However, an exact
  arbitrary-carrier Fin22 encoding of that compressed downstream consequence
  is SAT: 355,069 variables and 12,992,289 clauses yield an independently
  checked target-free model with both strong carriers, all twelve mutual-middle
  failures, a three-carrier transversal hitting all 46 carrier-contained
  strong sixes, and witnesses for all 120 targeted residual deletions.  The
  model expires the compressed consequence as a standalone color terminal; it
  does not satisfy or refute the omitted canonical-grid/bad-block provenance,
  full global packing, decomposability, or realizability premises.
  Auxiliary-blind provenance replay now decides that omission on the fixed
  model: all 210 residual four-blocks are bad, but there are 44 canonical mixed
  witnesses rather than four; their rectangles overlap and cover only 28 of 36
  anchor pairs.  Thus the fixed model fails the balanced canonical system
  sharply.  An exact augmentation enforcing family cardinality four, `3x3`
  shape, and full 36-pair coverage has 951,973 variables and 19,484,071
  independently reconstructed clauses, but CaDiCaL reached the 30-minute gate
  without SAT or UNSAT.  This is a resource stop, not evidence for either
  disposition.
  The same fixed model supplies separate collision diagnostics: it directly
  satisfies global deletion packing and an exact four-light-repair network,
  including equal initial probe blocks, while avoiding all targets.  It is not
  a full-context collision countermodel because every admissible 7--15 cut has
  a side cap-four.  Adding exactly the cut to the stronger targeted-packing CNF
  is UNSAT, but that compressed result cannot certify the collision terminal.
  The direct full-context collision falsifier has now been run without that
  shortcut: its 199,713-variable, 3,172,823-clause formula retains the exact
  ordered cut, full four-repair network, and all same-occupancy cases, with no
  targeted-packing, rectangle, or provenance variables.  Independent clause
  reconstruction and a 1,283,493-addition pure-RUP replay certify UNSAT.  This
  is strong computational evidence that the frozen four-repair terminal is
  true, but its 3.17-million-clause base and 994-MiB trace are not a Lean proof.
  Net proof movement for this gate is neutral: confidence changed, but the
  formal terminal and its semantic difficulty remain open.  The parent is
  retained without promotion and raw reruns are expired.  Removing only the
  `OneChangeOn` clauses also makes both the packed `3+3` and direct repair
  formulas satisfiable; their checked models contain thousands of OneChange
  violations.  This confirms that the existing geometric law is load-bearing
  but proves no new theorem.  The first authenticated nonstretchability
  boundary is now formal: `ringelNine_not_rankThreeVectorRealizable` compiles
  from an independently checked 59-row final-polynomial certificate, and the
  public `IsSweepRealizable` and `IsDecomposableOn` restriction exclusions
  compile.  The Ringel class occurs in exactly 60 of the 497,420 nine-subsets
  of the admitted TP-SAT model, but that earlier model filter still does not
  close a full-context terminal.  A source-frozen convention adapter now also
  admits the separate family-layer assignment: all 17,245,219 clauses and the
  auxiliary-blind cardinality-four family semantics replay, and 67 of its
  497,420 nine-subsets are Ringel-equivalent.  That model has shapes `1+5`,
  `3+3`, and `5+1`, overlapping rectangles, and only 16/36 coverage, so it does
  not test the stronger balanced layer.  A read-only producer audit finds no
  supported deterministic selector: the natural transversal-plus-escape
  nine-set leaves 64 of 84 signs uncontrolled.  Exact realizable controls
  refute grid/incidence-only forcing but do not refute the stronger exact
  canonical-family/provenance producer.
- **Missing generalization bridge:** close the two remaining full-context color
  terminals, integrate them into the decomposable `k=7` transition, and then
  extract a parameterized Pascal mechanism rather than another isolated state.
- **Last forward result:**
  `mixedCarrierOnlyOmissionNormalForm_forces_target567` kernel-checks the full
  mixed normal-form branch.  The separate local theorem
  `ringelNine_not_rankThreeVectorRealizable` and its sweep/decomposable
  restriction consumers now compile, but no theorem connects them to the full
  packed state-567 context.
- **Downstream consumer:** the packed state-567 reducer and ultimately the
  uniform decomposable exact upper theorem.
- **Open obstruction:** close two full-context color terminals: the
  provenance-coupled balanced grid and the same-anchor same-occupancy
  four-repair network.  The direct collision negation is computationally
  UNSAT, while the first exact provenance augmentation remains solver-hard.
  The remaining collision obstruction is semantic proof extraction: isolate a
  cut-sensitive color lemma or compact core that closes the Lean terminal.
  The realizability-filter obstruction is now specifically a producer: prove
  that the retained packed/decomposable context forces a Ringel-nine
  restriction, rather than merely excluding that restriction once supplied.
- **Next discriminating gate:** for the balanced branch, reduce the exact
  19.48-million-clause canonical-family augmentation before another solve:
  incrementally separate family-cardinality, rectangle-disjointness, and
  36-pair coverage, retaining arbitrary carriers, and freeze the smallest
  first inconsistent or solver-hard layer.  For the collision branch, mine
  the independently replayed direct UNSAT proof for the smallest cut-sensitive
  semantic lemma, then state and prove that lemma in Lean.  Do not rerun the
  same formula with another seed or attempt a monolithic certificate import.
  A separate bounded child, `FP-02.F`, supplies the first genuinely new local
  realizability filter beyond `OneChangeOn`: the nonstretchable uniform
  rank-three Ringel class is now formally excluded from sweep-realizable and
  decomposable restrictions.  Its next admissible step is a full-context
  producer proving that the retained packed/provenance hypotheses force such a
  restriction.  The saved family assignment has completed its one authorized
  convention-correct replay and must not be rescanned or extended by automatic
  CEGAR.  Its 67 occurrences may be used only as frozen pattern examples.  A
  future Ringel gate must first freeze a selector or bounded candidate family
  using canonical-family exactness and residual provenance, and the
  information-only streak requires adversarial route review before scheduling
  that refinement.
- **Success payoff:** discharge one or both exact state-567 terminal profiles.
- **Expiry or revival gate:** the standalone hitting-plus-targeted-packing
  terminal is expired by TP-SAT.  Only a target-free model satisfying the full
  packed/provenance context retires the parent balanced branch.  Fixed-color
  UNSAT cores and UNSAT formulas strengthened by targeted packing do not
  advance the general leaf unless their hypotheses follow from canonical
  provenance.  The current provenance formula may be retried only after exact
  structural compression.  The direct collision formula has completed its
  computational gate and may advance only through semantic core mining or a
  cut-sensitive structural theorem, not additional raw solver seeds.
- **Children:** `FP-02.A` balanced canonical transversal; `FP-02.B` mixed
  normal-form terminal; `FP-02.C` decomposability-retention bridge;
  `FP-02.D` symbolic packing/provenance compression; `FP-02.E`
  same-occupancy four-repair terminal; `FP-02.F` nonstretchable-nine-minor
  realizability filter.

### FP-03 — Uniform Pascal-tail lift

- **Contribution:** Generalize the residual bad-block and witness-reuse kernel
  so finite state-567 progress becomes a reusable inductive mechanism.
- **Mechanism family:** decomposable-pascal.
- **Named destination dependency:** `D-DECOMP`, specifically a uniform
  `PascalTailTwoSideBound` transition.
- **Strategic role:** generalization.
- **State:** gated.
- **Model tier:** generic finite-set incidence over exact ordered-coloring
  producers, with each color terminal stated separately.
- **Scope ceiling:** generic local profile/counting lemmas and the exact
  state-556 bound; no all-parameter Pascal-tail theorem.
- **Best evidence:** generic seed cover, division-free collision/large-fiber
  counting, the state-567 specialization, unequal carriers, and the exact
  state-556 collision-or-ten-fiber normalization compile.  Proof mining exposed
  a stronger witness-free Fin14 contradiction; its checkpointed certificate,
  15,951-clause semantic bridge, generic ordered-set transport, both advertised
  state-556 leaves, and the existing consumer now compile through
  `PascalTailTwoSideBound 5 5 6`.  Exact origin reconstruction of all 15,951
  retained clauses shows that 5,473 `strong_five_iff` clauses and 692 dead
  strong-four definitions are existentially eliminable certificate residue:
  6,165 clauses, or 38.6% of the retained core.  The remaining load-bearing
  interface is 4,186 OneChange clauses, 2,995 live strong-four lacing clauses,
  2,584 profile-hole clauses, and 21 cut/window clauses.  The proposed
  `StrongPolygonMiddleProfileInPascalWindow` now compiles generically: a strong
  polygon's two endpoint-middle color classes partition its internal vertices,
  and cap/cup holes bound their cardinalities.  The 556, 567, and color-dual
  specializations compile with exact profile capacities 6, 10, and 10.  The
  actual profile coefficient embeds in a compiling local capacity and then in
  `decomposableBinomialWindow`; the old state-567 middle-word result is freshly
  rederived without invoking its state-specific proof or a Pascal-tail bound.
  Independently replayed exact computation refutes the first ambient
  multiplicity proposal on an integer-coordinate seven-point sweep model: two
  individually strong
  six-extensions of one five-core have the identical profile, satisfy
  OneChange and the 567 cap/cup holes, but their union is not a strong seven.
  The fiber has size two where the proposed bound is one; vertical reflection
  gives the 657 dual.  Independent replay checked all determinants and rejected
  a coordinate corruption.  No Lean counterexample theorem is claimed.
- **Missing generalization bridge:** an independently produced cross-endpoint
  lacing equality that excludes the exact 567/657 countermodel and scales to
  every Pascal state used by the induction.
- **Last forward result:** the generic
  `StrongPolygonMiddleProfileInPascalWindow` theorem and the kernel-checked
  `pascalTailTwoSideBound_556` specialization compile.  The proposed ambient
  multiplicity lift was subsequently refuted.
- **Downstream consumer:** `PascalTailTwoSideBound`, then the uniform
  decomposable recurrence.
- **Open obstruction:** produce the missing cross-endpoint equality between two
  same-profile extensions from published-slice geometry.  OneChange, a common
  strong core, identical profiles, and individual strong extensions are
  insufficient.  The 556 control is vacuous for this six-carrier mechanism.
- **Next discriminating gate:** freeze `PascalAdjacentProfilePairLacing` for
  `s = k - 1`, with the explicit condition that all ordered core pairs see the
  same color on the two extension endpoints.  Audit whether an existing
  published-slice or lowest-separated producer supplies that condition; do not
  schedule Lean unless it excludes the exact 567/657 countermodel.
- **Success payoff:** validate the residual mechanism at an adjacent parameter
  state and expose a credible uniform Pascal theorem.
- **Expiry or revival gate:** `PascalMiddleProfileLacingCapacity` is
  operationally expired at abstract and sweep-realizable tiers by exact
  computational counterevidence; kernel promotion remains open.  Revive
  ambient multiplicity only with
  an explicit cross-endpoint invariant produced upstream; if it exists only at
  one adjacent state, retain it as finite infrastructure.
- **Children:** `FP-03.A` variable-carrier state-556 leaves; `FP-03.B`
  cross-endpoint adjacent-profile lacing.

### FP-04 — Layer-F highest-stratum mutation descent

- **Contribution:** Normalize unrestricted target-free realizable colorings to
  decomposable ones by a bounded mutation macro that strictly lowers the top
  decomposition-prime stratum.
- **Mechanism family:** normalization-descent.
- **Named destination dependency:** `D-NORMALIZE`.
- **Strategic role:** bridge.
- **State:** gated.
- **Model tier:** sweep-realizable target-free colorings and single-triple
  mutation paths.
- **Scope ceiling:** conditional rank-descent consumers, mutation-locality
  theorems, and small exact controls; no uniform normalization producer.
- **Best evidence:** prime-core ranks, their decomposable characterization, and
  locality of at-most-three mutation macros compile.  The stronger
  `ThreeStepPrimeCoreFamilyShrinksAboveAt` producer now has a compiling consumer
  all the way to `SweepExactUpperAt`.  Explicit target-creation and
  persistent-split shields, their strict-family consumer, and the exact rational
  positive control compile.  Complete bounded screening shows target-free
  endpoint descent within radius three, but refutes monotone prime-core
  inclusion at every intermediate edge on four Fin7 and ten selected Fin8
  controls.  A frozen endpoint-only persistent-split shield, which permits
  transient intermediate core creation, now passes all fourteen controls at
  the abstract rank-three signotope tier.  An independent checker recomputed
  the endpoint predicates and rejected a corrupted shield flag.  This is
  bounded computational evidence, not a producer theorem or realizability
  claim.  A read-only dependency audit now gives an exact Lean-shaped consumer
  chain from carrier cover plus endpoint split shield, through filtered
  cardinality-stratum containment and one destroyed source core, to strict
  `PrimeCoreCountAtCard` and `StratifiedPrimeCoreRank` descent.  The chain is
  noncircular and uses no edgewise inclusion.  However, after carrier cover is
  assumed, the endpoint shield is extensionally the no-new-cardinality-`m`
  half of the desired descent, so this remains a reviewed interface rather than
  a geometric theorem.  A rooted-circuit split-surgery proposal is now frozen
  only as a possible sufficient geometric interface; no strict logical
  separation from the endpoint shield is claimed:
  changed circuits remain within source split sides, while one unique crossing
  mutation activates a split of a source prime support.  It is noncircular and
  passes all fourteen admitted abstract Fin7/Fin8 controls under fresh replay,
  and exact rational Fin8 extraction now supplies five nonvacuous
  carrier-interior persistence witnesses plus a unique-crossing activation.
  The exact local theorem
  `HasDeepBelowSplit.persists_of_singleMutation_internal` and the
  cardinality-restricted conditional consumer
  `HasCarrierInternalSourceSplitsAboveAt.to_endpointSplits` now compile.  They
  use only a source split, one changed triple, and containment of that triple
  in one split side.  No theorem produces the source condition.  Exact
  factorization of the first Fin17 architecture shows that its endpoint `8+8`
  activation layer alone is unit-inconsistent after 510 propagations; the
  advertised persistent top split is unnecessary.  This expires that control
  architecture and gives no evidence for the uniform producer.
- **Missing generalization bridge:** prove that every above-threshold
  target-free realizable nondecomposable coloring admits the required bounded
  macro and strict rank decrease, without assuming the no-new-core half of the
  conclusion.
- **Last forward result:** the at-most-three mutation localization, prime-core
  rank consumer infrastructure, and local carrier-internal split-persistence
  lemma compile.  The latter is conditional infrastructure, so no theorem has
  changed the load-bearing `D-NORMALIZE` edge.
- **Downstream consumer:** `TargetReflectingDecomposableNormalizationAt`, then
  any uniform decomposable exact theorem.
- **Open obstruction:** prove a genuinely geometric source-side producer for
  `HasCarrierInternalSourceSplitsAboveAt` on a named target-free mutation
  family, and show that it supplies strict prime-core descent rather than only
  a cardinality-filtered endpoint split.  The fixed Fin17 activation control
  is empty and cannot test that question.
- **Next discriminating gate:** do not retune the empty Fin17 architecture.
  First state a source theorem that constructs carrier-internal splits from an
  independently recognizable circuit or cell condition and has a direct
  strict-rank consumer.  Test that frozen condition on the surviving rational
  controls and one separately generated nonempty above-threshold family; stop
  if its producer is merely the old endpoint shield in source notation.
- **Success payoff:** an unrestricted-to-decomposable reduction independent of
  the half-subset producer.
- **Expiry or revival gate:** a realizable target-free closed component or
  highest-stratum local minimum retires this rank; a new noncircular rank may
  revive mutation descent.
- **Children:** `FP-04.A` carrier-internal rooted-circuit split persistence.
  This child must prove that a source split persists when every changed carrier
  is wholly inside one side, and must then show that the resulting source-side
  producer is strictly weaker than the existing endpoint shield.  A compiling
  locality lemma alone is infrastructure, not movement on `D-NORMALIZE`.

### FP-05 — State-567 balanced five-class leaves

- **Contribution:** Attack the same exact 22-point decomposable obstruction
  through crossing-split and residue classes independent of the rectangle
  route.
- **Mechanism family:** decomposable-pascal.
- **Named destination dependency:** a balanced state-567 subordinate
  obligation of `D-DECOMP`.
- **Strategic role:** hedge.
- **State:** gated.
- **Model tier:** full packed `11+11` ordered split with side cap exclusions and
  repeated deletion packing.
- **Scope ceiling:** an exact structural reduction for the finite 3+3 leaf;
  its terminal and the other four balanced leaves remain open in Lean.
- **Best evidence:** the five-way shell, universal clean `2+4` normalization,
  and middle-word infrastructure compile.  The new exact `3+3` reduction also
  compiles: any packed witness has a disjoint mutually obstructed partner,
  bounded middle words, proper splits, and all twelve normalized failures.
  The exact full-context `3+3` negation is independently reconstructed and
  computationally UNSAT (83,468 variables, 1,583,924 clauses, and 1,653,441
  independently replayed pure-RUP additions).  Its 336-MiB proof is above the
  promotion gate, so the color terminal is not yet a completed Lean result.
  Removing only its OneChange clauses produces a checked SAT model, but that
  model loses 11,737 of the 74,613 deletion-packing consequences.  This is a
  causal diagnostic for the already formalized geometric law, not evidence
  for or against the full packed terminal.
  Net proof movement is forward only for the compiling structural reduction;
  the computational terminal is neutral and does not close a dependency.  The
  thread therefore remains gated.
- **Missing generalization bridge:** a compiling proof of the 3+3 terminal or
  another exact leaf, followed by integration into state-567 and a
  parameterized transition beyond that finite state.
- **Last forward result:** `StructuralChargingBalancedThreeThree567.lean`
  compiles the proper-partner, bounded-word, and twelve-failure reduction.  The
  subsequent full-context UNSAT result is neutral computational evidence.
- **Downstream consumer:** the balanced obligation in the state-567 reducer.
- **Open obstruction:** extract a compact semantic proof of the now-supported
  `3+3` terminal, or close one of the other four leaves while visibly using the
  exact packed context.
- **Next discriminating gate:** mine the `3+3` proof for a small color lemma or
  shared semantic core that can be stated independently and proved in Lean.
  Do not repeat the same SAT instance or substitute the pair-only weakening.
- **Success payoff:** an independent state-567 closure path if `FP-02` stalls.
- **Expiry or revival gate:** an exact full-context model retires the selected
  leaf; the direct `3+3` computational gate is complete and revives only for a
  materially smaller certificate or structural theorem.  Repeated reductions
  inherited by the 12- or 21-point controls trigger suspension and route review.
- **Children:** none.

### FP-06 — Finite `k=9` extreme-exchange bridge

- **Contribution:** Supply a trusted finite successor base and engineering
  pattern for diagonal extraction.
- **Mechanism family:** decomposable-pascal.
- **Named destination dependency:** the finite base subordinate to FP-09 and
  ultimately `D-DECOMP`.
- **Strategic role:** bridge.
- **State:** merged.
- **Model tier:** exact finite `OneChangeOn` statements at `k=9`.
- **Scope ceiling:** the fixed `k=9`, `Fin 17` extreme-exchange theorem.
- **Best evidence:** `extremeExchangeK9FinSeventeen` compiles end to end.
- **Missing generalization bridge:** a noncircular symbolic successor valid at
  `k=10` and then uniformly in `k`.
- **Last forward result:** `extremeExchangeK9FinSeventeen` closed the declared
  finite base and is now consumed only through FP-09.
- **Downstream consumer:** `FP-09` symbolic diagonal successor.
- **Open obstruction:** none within this bounded lane; uniform extraction is a
  separate problem.
- **Next discriminating gate:** no independent execution; use the theorem only
  when testing `FP-09`.
- **Success payoff:** already realized as a finite base.
- **Expiry or revival gate:** revive only for a regression or a precise helper
  required by a surviving symbolic successor—not for another isolated case.
- **Children:** none.

### FP-07 — Integral predecessor Property B

- **Contribution:** Bipartition the predecessor hypergraph so either color
  class supplies a half-sized predecessor-free support.
- **Mechanism family:** predecessor-half.
- **Named destination dependency:** `D-HALF` through the stronger integral
  bicoloring producer.
- **Strategic role:** hedge.
- **State:** gated.
- **Model tier:** exact predecessor hypergraphs induced by ordered or
  sweep-realizable colorings; relaxed hypergraphs are falsification controls.
- **Scope ceiling:** compiling recurrence and small-cardinality theorems plus
  bounded `k=6,n≤12` evidence; no uniform Property-B theorem.
- **Best evidence:** the recurrence consumer and small-cardinality results
  compile; bounded integral behavior survives through checked `k=6,n≤12`;
  finite semantic promotion remains incomplete.
- **Missing generalization bridge:** an all-`k` orientation-sensitive
  bicoloring law for exact predecessor hypergraphs.
- **Last forward result:** the small-cardinality integral bicoloring theorems
  and their recurrence consumer compile; no later result changed `D-HALF`.
- **Downstream consumer:** `FP-01` and its half-subset recurrence.
- **Open obstruction:** find an all-`k` structural bicoloring law rather than a
  sequence of finite certificates.
- **Next discriminating gate:** finish one bounded semantic bridge or state one
  new ordered-hypergraph property with an exact countermodel gate, not both.
- **Success payoff:** a stronger integral producer for `PredecessorHalfSubsetAt`.
- **Expiry or revival gate:** a realizable non-bicolorable predecessor
  hypergraph retires the integral route but not `FP-08` or `FP-01`.
- **Children:** none.

### FP-08 — Fractional predecessor cover

- **Contribution:** Obtain the half-subset property by a rational independent-
  set cover of total weight at most two.
- **Mechanism family:** predecessor-half.
- **Named destination dependency:** `D-HALF` through the weaker fractional
  producer.
- **Strategic role:** hedge.
- **State:** gated.
- **Model tier:** exact predecessor hypergraphs from sweep-realizable colorings,
  with relaxed hypergraphs used only to separate logical strengths.
- **Scope ceiling:** compiling fractional-to-half implication interfaces and
  bounded exact/relaxed controls; no weighted producer.
- **Best evidence:** the exact `PredecessorHalfMassAt` interface now compiles.
  A rational cover of total weight at most two implies half-mass by a finite
  double count; uniform half-mass implies `PredecessorHalfSubsetAt`; and
  half-mass feeds the exact sweep recurrence.  All declarations use only the
  standard project axioms.  Relaxed exact controls reproduce both a fractional-
  not-integral separator and a complete 4-uniform `K7` obstruction, while no
  integral/fractional/half separator appears through checked `k=6,n≤12`.  Net
  proof movement is forward only for the easy implication interface; the
  weighted producer and its estimated difficulty are unchanged, so the route
  remains gated.
- **Missing generalization bridge:** an orientation-sensitive inequality that
  constructs total fractional cover weight at most two for every exact
  target-free predecessor hypergraph.
- **Last forward result:** none on the load-bearing ledger; the compiling
  double-counting implications are reusable specification infrastructure.
- **Downstream consumer:** `FP-01`.
- **Open obstruction:** prove a geometric or orientation-sensitive weighted
  inequality that cannot be cloned by relaxed hypergraphs.
- **Next discriminating gate:** freeze one orientation-sensitive weighted
  inequality whose hypotheses hold for exact predecessor hypergraphs but fail
  on the relaxed `K7` obstruction, then test it on exact rational controls
  before Lean work.  A generic LP-duality restatement is not sufficient.
- **Success payoff:** a producer strictly weaker than integral Property B.
- **Expiry or revival gate:** an exact realizable fractional-cover obstruction
  retires this route; failure of one local weighting merely returns to the LP
  dual formulation.
- **Children:** none.

### FP-09 — Diagonal extreme-exchange successor

- **Contribution:** Turn the finite diagonal bases into a genuine symbolic
  successor step using core extraction and opposite-extreme cup gluing.
- **Mechanism family:** decomposable-pascal.
- **Named destination dependency:** a diagonal successor subordinate to
  `D-DECOMP`.
- **Strategic role:** generalization.
- **State:** gated.
- **Model tier:** ordered `OneChangeOn` cup-block configurations, with finite
  `k=9` the trusted base.
- **Scope ceiling:** exact finite `k=9` diagonal and exchange theorems; no
  symbolic successor.
- **Best evidence:** exact diagonal and extreme-exchange `k=9` theorems compile;
  clause mining found no honest all-parameter law.
- **Missing generalization bridge:** an extraction premise strictly weaker
  than the next diagonal theorem that survives `k=10` and scales in `k`.
- **Last forward result:** the exact `k=9` diagonal and extreme-exchange
  theorems compile; they remain finite bases rather than a uniform transition.
- **Downstream consumer:** the diagonal component of a uniform decomposable
  upper proof.
- **Open obstruction:** state an extraction premise strictly weaker than the
  next diagonal theorem.
- **Next discriminating gate:** freeze one symbolic candidate and test it at
  `k=10` before formalization.
- **Success payoff:** a true diagonal successor rather than additional finite
  cases.
- **Expiry or revival gate:** a bounded `k=10` counterexample retires the
  candidate; failure to state any noncircular premise keeps the finite theorem
  as a base only.
- **Children:** none.

### FP-10 — State-567 finite-certificate fallback

- **Contribution:** Close one exact packed leaf or mine a compact semantic
  pattern when structural work stalls.
- **Mechanism family:** decomposable-pascal.
- **Named destination dependency:** finite state-567 leaves subordinate to
  `D-DECOMP`, now owned by FP-02 and FP-05.
- **Strategic role:** fallback.
- **State:** merged.
- **Model tier:** fixed finite state-567 ordered colorings, with independent
  semantic reconstruction and certificate replay.
- **Scope ceiling:** the exact mixed state-567 finite terminal, now formally
  closed and transported to arbitrary placement.
- **Best evidence:** the authoritative quotient-free checkpoint certificate,
  all 14,773 retained semantic clauses, arbitrary-placement transport, and
  `mixedCarrierOnlyOmissionNormalForm_forces_target567` compile.  Remaining
  balanced and collision certificate work is tracked by FP-02 and FP-05.
- **Missing generalization bridge:** the mixed finite branch needs no further
  bridge; the parent still needs its other state-567 terminals and a uniform
  Pascal transition.
- **Last forward result:** the kernel-checked mixed normal-form theorem closed
  this fallback's intended finite branch.
- **Downstream consumer:** FP-02's packed state-567 reducer.
- **Open obstruction:** none independently; unresolved finite leaves belong to
  FP-02 or FP-05 rather than a duplicate certificate lane.
- **Next discriminating gate:** no independent execution; attach any future
  frozen semantic-extraction hypothesis to its owning mathematical parent.
- **Success payoff:** already realized as the mixed branch closure.
- **Expiry or revival gate:** revive only for a regression in the mixed theorem
  or a precise parent-owned certificate helper, not for another isolated state
  search.
- **Children:** none.

### FP-11 — Inverse stepping-up and decomposition extraction

- **Contribution:** Extract predecessor-free pieces or a useful deep split
  directly from a large target-free geometric configuration.
- **Mechanism family:** predecessor-half.
- **Named destination dependency:** `D-HALF`, or secondarily a structural
  producer for `D-DECOMP`.
- **Strategic role:** hedge.
- **State:** parked.
- **Model tier:** sweep-realizable planar configurations.
- **Scope ceiling:** no current theorem-producing mechanism; the surviving
  singleton-fan child is already represented in FP-01.
- **Best evidence:** the useful singleton-fan branch graduated to `FP-01`;
  deletion, two-piece, and one-anchor proposals are false, circular, or inert.
- **Missing generalization bridge:** a new geometric extraction theorem with a
  noncircular producer and direct recurrence or decomposable consumer.
- **Last forward result:** the singleton-fan mechanism graduated to FP-01; no
  independent forward result remains in this parked entry.
- **Downstream consumer:** `FP-01` or a uniform decomposable theorem.
- **Open obstruction:** no remaining geometric mechanism has both a
  noncircular producer and a named consumer.
- **Next discriminating gate:** none until a new geometric mechanism survives
  the existing rational controls.
- **Success payoff:** an alternative unrestricted structural reduction.
- **Expiry or revival gate:** a new precise half-support, two-piece, or deletion
  theorem with a direct recurrence consumer revives this entry.
- **Children:** none.

### FP-12 — State-578 strict-gate revival

- **Contribution:** Reuse the extensive state-578 matrix, density, and residual
  infrastructure only if a genuinely new invariant can turn it into descent or
  closure.
- **Mechanism family:** decomposable-pascal.
- **Named destination dependency:** the fixed state-578 subordinate obligation
  of `D-DECOMP`.
- **Strategic role:** hedge.
- **State:** suspended.
- **Model tier:** the exact decomposable 32-point state with full residual
  family, colors, density, and decomposition data.
- **Scope ceiling:** fixed `k=8` state-578 structural infrastructure; no closed
  state theorem or uniform transition.
- **Best evidence:** extensive Lean infrastructure compiles, but relaxed and
  exact-small carrier/address cycles refute current cover and rank consumers.
- **Missing generalization bridge:** a complete-family exact-color invariant
  that defeats all recorded cycles and yields a cover, strict predecessor, or
  well-founded descent usable beyond state 578.
- **Last forward result:** the terminal carrier-cover and universal seed-escape
  interfaces compile, but subsequent cycle countermodels prevent them from
  closing the state or changing `D-DECOMP`.
- **Downstream consumer:** the state-578 Pascal-tail obligation.
- **Open obstruction:** every known local/cardinality/address invariant permits
  replacement cycles or lacks full residual coverage.
- **Next discriminating gate:** none unless a complete-family exact-color-and-
  density candidate both defeats all recorded cycles and constructs a cover,
  strict predecessor, or well-founded descent.
- **Success payoff:** revive a previously central decomposable branch with a
  model-distinguishing invariant.
- **Expiry or revival gate:** ticket 0010 is binding; inherited candidates are
  rejected without allocating a builder.
- **Children:** none.

### FP-13 — Goal-driven intermediary lemma forge

- **Contribution:** Generate a small number of route-independent, Lean-shaped
  lemmas with named consumers and cheap falsifiers when primary routes expose
  a missing invariant.
- **Mechanism family:** route-discovery.
- **Named destination dependency:** whichever parent ledger edge is named by a
  frozen card; FP-13 closes no destination edge independently.
- **Strategic role:** discovery.
- **State:** probing.
- **Model tier:** varies per frozen card and must be explicit before screening.
- **Scope ceiling:** individual proposal or intermediary-lemma cards with
  explicit parent consumers.
- **Best evidence:** several cards have graduated into `FP-02` and `FP-03`;
  negative and inert cards are retained as controls.  Child `FP-13.A` now has
  a compiling exact rightmost-extension equivalence for `OneChangeOn` and an
  independently replayed labeled census of sizes 8, 62, and 908 through six
  vertices.  Child `FP-13.B` adds a compiling realizable-to-one-change theorem
  and exact four-point equivalence.  It now also has the compiling exact
  realization-sensitive right-extension recurrence, which retains the
  existential parent coordinates and reconstructs the full configuration.
  Independently checked certificates cover all 62 five-point and 908 six-point
  states by 780 decomposition trees plus 190 exact six-point coordinate
  witnesses.  Two realizations of the same five-point type have different
  rightmost extension sets for 43 of 62 checked parents.  Child `FP-13.C` has
  now graduated its local boundary:
  `ringelNine_not_rankThreeVectorRealizable` and the public sweep-realizable
  and decomposable restriction exclusions compile from an exact
  final-polynomial proof.  Child `FP-13.D` now has a compiling exact
  abstract/fixed/union right-extension-fiber API and an independently checked
  fixed-coordinate atlas through child size six.  Its enriched labeled wiring
  exactly encodes every checked fixed arrangement, but is neither compression
  nor an abstract-parent invariant.
- **Missing generalization bridge:** a surviving card must prove a reusable
  theorem under its parent mechanism rather than remain true but inert.  For
  `FP-13.A`, no strictly smaller parent invariant survived its first bounded
  gates.  Child `FP-13.B` shows at computational tier that no additional local
  realizability restriction appears through six, but its five/six universal
  Lean promotion has no load-bearing consumer.  Fixed-representative cells are
  not an order-type invariant, and the exact coordinate-retaining recurrence
  does not by itself reduce a consumer.  `FP-13.C` has completed the local
  nonstretchability bridge, but no full-context theorem produces its Ringel
  restriction.  The completed `FP-13.D` slate rejects bare labeled-wiring
  compression, abstract localization as geometric realizability, fixed-fiber
  connectivity as a useful consumer, the tested majority class, and blind
  seven-point enumeration.  It does not decide whether realization-space wall
  changes, chamber-stable invariants, bounded infeasibility certificates, or
  the abstract-to-geometric lower-set gap expose a different mechanism.
- **Last forward result:** the fixed Ringel-nine homogeneous
  nonrealizability theorem and its sweep/decomposable restriction exclusions
  compile.  This is a real local theorem, but no named load-bearing destination
  edge changes without a full-context producer.  The five/six equality and
  extension-sensitivity results remain checked computation.
- **Downstream consumer:** whichever numbered mathematical thread names the
  missing lemma.
- **Open obstruction:** avoid producing true but strategically inert statements
  or a second informal backlog while preserving room to discover a delicate
  geometric mechanism.  A state-dependent sum over all parent colorings is not
  a compressed recurrence, and a labeled wiring that reconstructs every cell
  of one arrangement is not a parent-coloring invariant.  The live question is
  whether changes across realization-space chambers admit a smaller stable
  description that constrains the extension hypergraph.
- **Next discriminating gate:** run one bounded through-six mechanism-discovery
  slate over the admitted atlas: compare adjacent realization chambers across
  a single degeneracy wall; test chamber-stable summaries smaller than atomic
  wiring; seek small fixed-fiber infeasibility or Helly certificates; and
  measure the exact gap between abstract lower-set extensions and geometrically
  realizable children.  Each probe must freeze a falsifier and a short consumer
  ladder before outcomes.  Do not open the seven-point atlas unless a
  through-six probe yields reproducible nonsymmetric structure and a credible
  named bridge toward `D-HALF`, `D-NORMALIZE`, or state-567.  Ringel work
  remains with the full-context `FP-02.F` producer rather than another local
  certificate or catalog scan, and the expired `FP-13.A` summary may not be
  retuned.
- **Success payoff:** a new proof-ready subthread or a decisive route
  retirement.
- **Expiry or revival gate:** probing receives one bounded through-six
  incubation slate.  Close each explanation on its preregistered falsifier and
  return the parent to `gated` or `parked` if the slate yields no stable
  nonsymmetric invariant, exact decomposition, or source-backed mechanism.  A
  card without a falsifier and short consumer ladder is rejected; a surviving
  card graduates to its parent or a new `FP-NN` entry.
- **Children:** `FP-13.A` local geometric constraint hierarchy (bounded child
  closed; recurrence asset retained, first compression expired); `FP-13.B`
  finite sweep-realizability boundary (bounded child closed; four-point theorem
  compiled, five/six computational equality retained); `FP-13.C` first local
  nonstretchability boundary (local theorem completed and merged into
  `FP-02.F`; full-context producer remains there); `FP-13.D` geometric
  right-extension fibers (bounded atlas slate closed; exact API and
  fixed-coordinate atlas retained; parent mechanism probing realization-space
  chamber structure while the named failed descendants remain closed).

### FP-14 — Formal-research system and template feedback

- **Contribution:** Reduce proof latency and evidence mistakes through better
  orchestration, certificate chunking, reproducibility, approval preflight, and
  calibrated estimates.
- **Mechanism family:** research-system.
- **Named destination dependency:** none; this entry cannot close a
  mathematical ledger edge.
- **Strategic role:** research-system.
- **State:** gated.
- **Model tier:** project process; it never constitutes mathematical evidence
  for the exact formula.
- **Scope ceiling:** process reliability, evidence admission, and certificate
  feasibility only.
- **Best evidence:** immutable packets, outcome contracts, serialized builders,
  independent certificate checks, empirical timing records, and the closed
  portfolio execution cycle operate in the repository.  Checkpoint replay made
  the state-556 and mixed state-567 certificates kernel-feasible.  The Fin11
  cube audit separated learned-proof complexity from semantic-base complexity.
  A slate-completion manifest/checker now prevents omitted terminal lanes, and
  the guarded command runner enforces wall time, aggregate RSS, Lean-compiler
  count, process-group cleanup, and machine-readable heartbeats.  It caught a
  14-compiler Lake fan-out before another WSL resource failure.  The bounded
  2026-08-13 literature workflow retained 63 seed records, downloaded 70 open
  full texts, deep-read 26 papers, and produced a 54-item follow-up queue; these
  counts evidence a reproducible discovery process, not a mathematical result
  or an exhaustive bibliography.  On the unique minimum Fin11 depth-six cube,
  a deterministic indexed ledger now compresses 9,181 exact base clauses into
  3,527 complete family/index facts.  Independent reconstruction expands them
  literal-for-literal to the frozen core; omitted-index and corrupted-family
  controls reject, and native replay checks all 18,349 LRAT additions.  The
  one authorized Lean leaf nevertheless failed with `std::bad_alloc` after
  226.95 seconds at 14,908,088 KiB maximum RSS under the 16-GiB cap.  This is
  process evidence only; no Fin11 Lean theorem is claimed.
- **Missing generalization bridge:** none exists from process improvement to
  mathematics; a mathematical parent must still supply every theorem and
  producer.
- **Last forward result:** none on the proof ledger.  Checkpointing has enabled
  parent-owned finite theorems, whose proof movement is recorded under those
  mathematical entries.
- **Downstream consumer:** all mathematical entries, through safer and broader
  execution.
- **Open obstruction:** the Fin11 family count is no longer the immediate
  blocker.  The remaining failure is monolithic kernel memory across the
  3,527-family semantic context and proof replay, while preserving the same
  trusted Lean/LRAT boundary.  Process work must not become a substitute for
  the mathematical endpoint producer in `FP-01.B`.
- **Next discriminating gate:** build a streaming or balanced-checkpoint
  interface for this same selected leaf, targeting less than 12 GiB and keeping
  the exact reconstructed families, proof, and corruption controls unchanged.
  Only after that leaf compiles should one representative indexed semantic
  producer be promoted.  Do not expand to all cubes or Fin12 first.
- **Success payoff:** faster route comparison, fewer repeated dead ends, and a
  durable memory of all potentially valuable work.
- **Expiry or revival gate:** the measured 14.9-GiB failure permits one bounded
  streaming/checkpoint prototype.  Another monolithic replay, any weakening of
  kernel trust, or no credible sub-12-GiB design returns the slot to a
  mathematical thread; successful bounded replay revives the entry.
- **Children:** `FP-14.A` large-certificate proof mining and checkpointed Lean
  replay; `FP-14.B` indexed semantic-base compression and completion signaling.

### FP-15 — Uniform quantitative upper-bound ladder

- **Contribution:** Formalize an authenticated strict uniform improvement over
  the repository's classical binomial upper bound, then conditionally build the
  Suk and Holmsen--Mojarrad--Pach--Tardos quantitative machinery without
  confusing any rung with the exact conjecture.
- **Mechanism family:** quantitative-cup-cap.
- **Named destination dependency:** `Q-UPPER`, a supporting quantitative
  milestone that does not close or strictly reduce universal `D-UPPER` without
  a separate proved implication.
- **Strategic role:** bridge.
- **State:** gated.
- **Model tier:** general-position planar configurations and their
  sweep-realizable presentations.  The first rung is the source-authenticated
  Tóth--Valtr theorem
  `ES(n) <= choose (2*n-5) (n-2) + 2` for `n >= 3`; later rungs are Suk's
  point-set argument and the point-specialized
  Holmsen--Mojarrad--Pach--Tardos argument.
- **Scope ceiling:** the best authenticated published point-set upper bound
  `2^(n + O(sqrt(n*log n)))`, reached only through the outcome-gated ladder.
  The immediately frozen theorem is the explicit Tóth--Valtr bound plus its
  strict comparison with `classical_binomial_upper` for `n >= 4`.  No exact
  Erdős--Szekeres threshold follows from any quantitative rung.
- **Best evidence:** `tothValtr_upper` compiles for every `n >= 3`, and
  `tothValtr_strictly_improves_classical` compiles for every `n >= 4`.  The
  proof constructs an explicit rational projective normalization after a
  determinant-one shear and quarter turn, proves exact orientation-sign and
  finite-subset convexity preservation, extends every transformed cap through
  the anchor, and invokes the existing cup--cap theorem.  Deterministic exact
  rational controls cover three configurations, 297 convexity subsets, 99 cap
  extensions, and three rejected coordinate corruptions.  The first Suk finite
  kernel now also compiles: `finiteDilworth_chain_or_antichain`, the exact
  support-region vocabulary, the triangle-containment partial order on a
  finite one-sided general-position set, its chain/antichain specialization,
  and the conditional adjacent-region gluing theorem
  `SukAdjacentRegionCertificate.inConvexPosition_union`.  Exact rational
  controls realize two adjacent three-point chains and reject three coordinate
  corruptions.  The missing local producer now compiles as well:
  `SukAdjacentSupportData.toCertificate` derives both arrangement-cell fields
  and both opposite-pair supporting-line fields from five cap anchors, two
  actual adjacent support-region chains, their anchor-extended caps,
  disjointness, and ambient general position.  Its proof uses explicit
  Grassmann--Pluecker sign identities and assumes none of the certificate
  fields.  Holmsen--Mojarrad--Pach--Tardos remains a later source rung, not a
  current Lean result.
- **Missing generalization bridge:** prove the published geometric predicates
  equivalent to the repository's realizable sweep predicates, then extract a
  parameterized lemma actually consumed by `D-HALF`, `D-DECOMP`, or
  `D-NORMALIZE`; a smaller numerical coefficient alone supplies no such bridge.
- **Last forward result:** supporting milestone `Q-UPPER` is closed by the
  compiling unconditional theorem `tothValtr_upper`.  Within `FP-15.B`, the
  generic finite height--width theorem, the region partial order under explicit
  one-sided general-position hypotheses, the support-chain-to-certificate
  producer, and the certificate-to-convex-union consumer compile.  This closes
  one named local geometric edge in the quantitative route but changes no
  load-bearing exact-conjecture dependency.
- **Downstream consumer:** the next quantitative consumer is Suk's finite
  positive-fraction architecture.  Any claim of progress on the exact route
  still requires a separate theorem into `D-HALF`, `D-DECOMP`, or
  `D-NORMALIZE`.
- **Open obstruction:** no exact-route consumer uses the completed frame.  In
  the Suk route, the local adjacent-support geometry is closed, but no theorem
  selects sufficiently large anchor-extended chains in enough adjacent support
  regions or turns their repeated gluing into the published positive-fraction
  support estimate.  The chain-coloring, Pór--Valtr support theorem, recurrence,
  and asymptotic bound remain open.
- **Next discriminating gate:** formalize the transitive two-color cup--cap
  theorem on one `SukRegionLE` chain and state the exact global selection lemma
  that supplies adjacent chain/cap data at the needed cardinalities.  The next
  slate must freeze its finite inequalities and a direct consumer into the
  positive-fraction support count before proof search.  Do not spend another
  slot refining the now-closed local sign algebra or begin asymptotic
  optimization before the global selection lemma compiles.
- **Success payoff:** the geometric producer makes the compiled gluing theorem
  usable and unlocks the chain two-color cup--cap layer.  Only that layer plus
  a formal Pór--Valtr support theorem unlocks Suk's integer recurrence; only a
  completed Suk architecture unlocks the point-specialized current-best bound.
- **Expiry or revival gate:** `FP-15.A` is complete and endpoint variants are
  parked because the reuse audit found no exact-route consumer.  `FP-15.B` is
  no longer parked at the local certificate producer; that edge is complete.
  It remains gated at global chain selection and positive-fraction assembly.
  Arithmetic, a restated certificate, or asymptotic bookkeeping alone is not
  progress.  Revive exact-route use of the frame only with a theorem-shaped
  consumer into a named load-bearing edge.
- **Children:** `FP-15.A` completed explicit Tóth--Valtr bound and projective frame;
  `FP-15.B` Suk positive-fraction/partial-order finite kernel and explicit
  asymptotic assembly; `FP-15.C` point-specialized
  Holmsen--Mojarrad--Pach--Tardos current-best bound.

### FP-16 — Exact unrestricted `ES(6)=17`

- **Contribution:** Prove the next unrestricted exact case through the public
  repository API, exercising the geometric abstraction and certificate path
  at the first case not already compiled in Lean.
- **Mechanism family:** finite-exact-upper.
- **Named destination dependency:** `D-UPPER(6)`, a fixed-instance subordinate
  milestone that does not close or strictly reduce universal `D-UPPER` without
  an already-defined uniform induction consuming it.
- **Strategic role:** fallback.
- **State:** gated.
- **Model tier:** general-position planar configurations through
  sweep-realizable colorings.  The external Isabelle/HOL development is a
  read-only reference whose order-type, realizability, and strong-polygon
  semantics still require an explicit correspondence audit.
- **Scope ceiling:** the unrestricted public theorem
  `erdosSzekeresFormulaAt_six : ErdosSzekeresFormulaAt 6`; no statement for
  arbitrary `k` and no uniform transition.
- **Best evidence:** the mathematical equality `ES(6)=17` and a formal
  Isabelle/HOL proof are recorded in the source ledger.  This repository
  compiles the unrestricted cases through five, the all-parameter lower bound,
  and the decomposable upper theorem at six, but it has no unrestricted Lean
  forcing theorem at six.
- **Missing generalization bridge:** map every external abstraction and
  certificate obligation to `IsSweepRealizable`, target containment, the
  planar bridge, and the public forcing API.  Beyond the fixed theorem, a
  separately frozen parameterized semantic-extraction lemma with a named
  uniform consumer would be required.
- **Last forward result:** none on universal `D-UPPER`; unrestricted exact six
  has not compiled in this repository.  Exact cases through five and the
  decomposable six theorem are prior baselines.
- **Downstream consumer:**
  `erdosSzekeresFormulaAt_six : ErdosSzekeresFormulaAt 6`, assembled from an
  unrestricted forcing theorem, the explicit geometric bridge, and existing
  sharpness.
- **Open obstruction:** no checked correspondence table yet shows that the
  Isabelle definitions, finite reduction, and certificate hypotheses match
  the repository's realizable sweep semantics without a stronger hidden
  assumption.
- **Next discriminating gate:** audit the Isabelle sources and primary paper,
  produce a clause-by-clause and predicate-by-predicate semantic
  correspondence table, and freeze the smallest noncircular Lean bridge target
  before generating, replaying, or compressing another certificate.
- **Success payoff:** either an exact proof architecture for the first missing
  unrestricted case or a precise incompatibility that prevents wasted
  certificate engineering; eventual success closes `D-UPPER(6)` only.
- **Expiry or revival gate:** an unmapped stronger premise, absent geometric
  bridge, or certificate plan without a named public theorem parks the route.
  Once `erdosSzekeresFormulaAt_six` compiles, stop fixed-case certificate work;
  continue only under one frozen parameterized extraction hypothesis with a
  consumer beyond `k=6` and an adjacent-parameter falsifier.
- **Children:** none.

## Current subthreads

Subthreads are tracked here because they are independently useful work units,
but they inherit the contribution path and strategic disposition of their
parent unless promoted.

- **FP-01.A — Synchronized singleton fans.**  Sixty-four exhaustive depth-six
  cubes replay independently.  Learned traces are now small, but every leaf
  retains at least 9,181 semantic base clauses, above the frozen Lean gate.
  Compress/share that base interface, then prove restriction/relabeling and
  compatible-window synchronization.  A realizable target-free counterexample
  expires the mathematical producer.
- **FP-01.B — Ambient endpoint-synchronized down-sets.**  Literature analysis
  identifies a split-profile injection whose cap and cup share one endpoint but
  need an additional ambient correlation to synchronize the other endpoint.
  The exact full-ambient endpoint dichotomy, clipped extension helper,
  `AmbientDownsetThresholdHalfSupportAtSix` interface, and noncircular consumer
  into `PredecessorHalfSubsetAt 6` compile and passed independent review.  The
  single-cell threshold producer is formally expired by the compiling exact
  rational Fin9 counterexample described under `FP-01`, while the local
  endpoint dichotomy remains valid infrastructure.  Any recurrence factoring
  through the clipped child pair-rank matrix is already refuted by the compiled
  collision.  Revive this child only with a multi-cell, weighted, or collective
  support rule that excludes the Fin9 model; recovery of only standard local
  injectivity remains inert infrastructure.
- **FP-01.C — Adaptive two-cell Boolean down-set support.**  For each coloring,
  choose two full-ambient threshold cells and one Boolean truth table; the
  selected support must be strong-five-free and contain at least half the
  vertices.  The frozen card survives the stored Fin9 obstruction and all 3,270
  target-free models in two independently replayed rational domains, but the
  choice is adaptive and no selector theorem exists.  The first frozen robust
  orientation-balance/rank-distance selector passed 3,271 inherited controls
  but is independently refuted by held-out rational Fin9 ordinal 1,459, which
  still admits 22 successful supports.  A compiling defect/exchange framework
  for all 4,096 classifiers is also refuted as a producer: the stored Fin9
  model has 535 radius-one and 265 radius-two positive-defect local minima,
  despite 44 successful classifiers.  Treat the used families as training
  data, preserve the still-blind cubic-sevenths family, and test only a frozen
  genuinely nonlocal selector.  One checked target-free model with zero
  classifiers expires this child.
- **FP-02.A — Balanced canonical transversal.**  The three-carrier transversal
  and residual-touching packing conclusion are proof-ready.  The next invariant
  must be placement-independent; fixed carrier signatures are expired.
- **FP-02.B — Mixed omission normal form.**  Completed finite terminal: the
  quotient-free checkpointed certificate, semantic bridge, arbitrary-placement
  finite theorem, and exact public normal-form consumer compile.  Retain this
  child as a closed dependency of `FP-02`; schedule only integration or upstream
  case-split consumption.
- **FP-02.C — Decomposability retention.**  Determine whether the packed
  reducer retains ambient decomposability strongly enough to restrict it to the
  twelve carrier vertices before using decomposable-only exclusions.
- **FP-02.D — Symbolic packing/provenance compression.**  Replace the
  597,500,904 eager six-deletion witness occurrences by an exact indexed
  bad-block, canonical-family, or hitting statement that also retains arbitrary
  carriers, the balanced transversal, and all 120 residual-triple obligations.
  A Lean-ready proposal now uses a transversal hitting every carrier-contained
  strong six and only the 120 targeted deletions, reducing the raw ledger to
  960,960 occurrences.  The hitting, targeted-packing, residual-touching, and
  global-to-targeted interfaces now compile, completing that bounded bridge.
  The exact compressed consequence is nevertheless SAT, so it cannot replace
  provenance as the terminal invariant.  Fixed-model replay finds 44
  overlapping canonical witnesses and only 28/36 anchor-pair coverage.  The
  first exact canonical-family augmentation times out at 19,484,071 clauses;
  split its structural layers before another solver attempt.  A weakened
  hitting-plus-targeted model is explicitly expired.
- **FP-02.E — Same-occupancy four-repair terminal.**  The exact frozen terminal
  retains the 22-point ordered split, side cap-four exclusions, mutual strong
  carriers, global packing, and `LightSameOccupancyFourRepairNetwork567`, with
  no distinct-initial-block premise.  The old TP-SAT model directly realizes
  the network and global packing but has no admissible side cut.  Adding the
  cut to the stronger targeted-packing CNF is UNSAT and therefore
  inconclusive for this child.  The direct full-context formula is now
  independently reconstructed and certified UNSAT: 199,713 variables,
  3,172,823 clauses, and a 1,283,493-addition pure-RUP proof.  Its 994-MiB trace
  is not promotion-ready.  Next mine a compact cut-sensitive semantic lemma and
  prove it in Lean; do not rerun the same formula with another seed.
- **FP-02.F — Nonstretchable-nine-minor realizability filter.**  The public
  Ringel example and the 4,382-versus-4,381 catalog counts authenticate the
  unique nonrealizable uniform rank-three nine-element reorientation class.
  Two independent classifiers enumerate 120,960 labeled quotient
  representatives and find exactly 60 matching restrictions among all 497,420
  nine-subsets of the admitted TP-SAT model; exact realizable controls reject
  the class.  The exact theorem `ringelNine_not_rankThreeVectorRealizable` now
  compiles from a 59-row final-polynomial proof, together with public
  `IsSweepRealizable` and `IsDecomposableOn` no-restriction consumers.  This
  closes the local realizability-filter boundary but remains neutral for the
  destination ledger.  The child is now gated only on a theorem forcing a
  Ringel restriction from the retained full packed/provenance context.  A
  corrected replay admits the family-layer assignment and finds 67 Ringel
  restrictions, but its shapes and coverage fail the stronger balanced layer.
  No supported deterministic selector follows from current interfaces; the
  exact canonical-family/provenance producer remains open.  Expire
  grid/incidence-only forcing and any producer that assumes decomposability.
  Do not rescan either saved model or treat the external catalog as a Lean
  premise.  Another Ringel refinement requires adversarial route review and a
  frozen selector using exact family exhaustion plus residual provenance.
- **FP-03.A — Variable-carrier state 556.**  Completed finite adjacent state:
  both advertised leaves and their consumer compile, via a stronger witness-free
  Fin14 contradiction, through `PascalTailTwoSideBound 5 5 6`.  The live child
  question is parameter extraction from that stronger core.
- **FP-03.B — Cross-endpoint adjacent-profile lacing.**  The common-core
  multiplicity theorem is operationally refuted by independently replayed
  exact 567/657 coordinate controls, with kernel promotion still open.  The
  smallest surviving consumer says that two same-profile `s = k - 1`
  extensions form a strong `k`-set if all core pairs see one common color on
  the two new endpoints.  No current published-slice theorem produces this
  equality.  Revive only with such a producer that excludes the stored model.
- **FP-04.A — Carrier-internal rooted-circuit split persistence.**  The exact
  local theorem `HasDeepBelowSplit.persists_of_singleMutation_internal` and its
  cardinality-restricted source-side conditional consumer compile.  This is
  infrastructure, not endpoint-descent progress: no geometric theorem produces
  `HasCarrierInternalSourceSplitsAboveAt`, and the fixed Fin17 endpoint
  activation layer is already unit-inconsistent before the persistent top
  split is added.  Expire that control architecture.  Revive the child only
  with an independently stated source circuit/cell producer and a direct
  strict-rank consumer; reject a source-language restatement of the old
  endpoint shield.
- **FP-13.A — Local geometric constraint hierarchy.**  **Bounded child
  closed.**  `oneChangeOn_univ_succ_iff` compiles and exactly decomposes an
  `n+1` constraint system into its first `n` vertices plus one compatibility
  law for each old triple and the three new pair colors.  Independent producer
  and brute-force checker agree on 8, 62, and 908 labeled states through six,
  of which 8, 62, and 718 are recursively decomposable.  The frozen
  pair-principal spectrum failed its preregistered training gate: all equal
  spectra were already explained by color reflection and order reversal, so it
  demonstrated no semantic compression and the seven-point gate remained
  unopened.  Expire that summary without retuning.  The exact state-dependent
  sum and census remain regression assets, not a compressed recurrence or
  proof movement.  The separate `FP-13.B` child has now supplied exact checked
  realizability coverage through six without creating a load-bearing consumer.
- **FP-13.B — Finite sweep-realizability boundary.**  **Bounded child closed.**
  Lean proves the general `IsSweepRealizable -> OneChangeOn` implication and
  the exact equivalence at four points using all eight explicit integer
  configurations.  Independent exhaustive replay covers all 62 five-point and
  908 six-point states by 780 recursive decomposition trees and 190 additional
  exact six-point coordinate realizations.  Five/six universal Lean promotion
  is deliberately not performed: the consumer audit shows it changes neither
  the nine-local `FP-02.F` obstruction nor the global 17-point `FP-16` forcing
  problem.  Exact cell enumeration also finds that two realizations of one
  five-point order type can admit different rightmost extensions (43/62 parent
  comparisons), so representative-cell recurrences are invalid without a
  realization-independence theorem.  The exact theorem
  `isSweepRealizable_succ_iff_exists_rightExtensionData` now gives the lawful
  alternative by retaining one existential parent realization and all new
  determinant signs.  It is compiling infrastructure, but no load-bearing
  consumer extracts a smaller cell summary, so its net proof movement is
  neutral.
- **FP-13.C — First local nonstretchability boundary.**  **Local boundary
  completed; merged into `FP-02.F`.**  The exact Ringel-nine homogeneous
  nonrealizability theorem and its sweep/decomposable restriction exclusions
  compile.  This closes the intermediary card but no load-bearing edge.  Any
  further Ringel work must prove the full-context `FP-02.F` producer; do not
  run a blind larger census or duplicate the local certificate.
- **FP-13.D — Geometric right-extension fibers.**  **Bounded slate closed;
  parent mechanism probing.**
  `TripleColoringExtensionFiber.lean` compiles and distinguishes abstract
  compatible links, extensions of one fixed swept realization, and the union
  of geometric children over every realization of a parent coloring.  The
  exact union membership theorem is representation infrastructure, not a
  reduction of child realizability.  Independent exact-rational producer and
  checker implementations cover child sizes four through six: 327 frozen
  realizations and 2,739 fixed cells.  Canonical pair-line labels, boundary
  order, and atomic equal-abscissa crossing slices replay every fixed fiber;
  this is an exact arrangement encoding rather than compression.  The source
  audit finds that Las Vergnas localizations and signotope lower sets stop at
  abstract extension, while fixed-coordinate Helly feasibility does not pass
  through the union over realization space.  Fixed target-free fibers are not
  uniformly gated, and an exact Fin9 model refutes the direct majority-class
  strong-support consumer.  Net proof movement is neutral and no ledger edge
  changed.  Those candidate-local and subfamily failures remain closed, but
  they do not exhaust realization-space wall changes, chamber-stable
  invariants, bounded fixed-fiber infeasibility certificates, or the lower-set
  gap between abstract and geometric children.  Retain the API and atlas as
  `probing` infrastructure for one bounded through-six incubation slate.  Keep
  `n = 7` closed until a preregistered probe finds reproducible nonsymmetric
  structure with a short named consumer ladder.
- **FP-14.A — Large-certificate kernel replay.**  Checkpointing succeeds for
  state-556 and mixed state-567.  For Fin11, exhaustive depth-six cubes reduce
  learned traces to 17,089--61,302 additions, but the 9,181-clause minimum base
  still blocks the frozen Lean gate.  Do not deepen the same cube tree without
  a semantic-base compression mechanism.
- **FP-14.B — Indexed semantic-base compression and completion signaling.**
  One Fin11 leaf now has an exact 3,527-fact indexed ledger expanding to all
  9,181 base clauses, with corruption controls, but a monolithic FromLRAT leaf
  failed at 14.9 GiB.  Replace that replay by a sub-12-GiB streaming or balanced
  checkpoint architecture without changing the trusted facts or proof.  Keep
  this compression-only outcome separate from an endpoint-repair theorem.  The
  signaling half is complete: execution slates require
  one validated terminal result per task, the root may not finish while a lane
  is live, and guarded commands emit heartbeats and kill their whole process
  group on wall-time, aggregate-RSS, or compiler-count violations.  The serial
  artifact follow-up is complete for the state-556 and mixed state-567
  certificates, including restored umbrella imports.  Expire the Fin11 proof
  bridge if it re-expands beyond the 16 GiB gate or weakens kernel trust; retain
  the signaling/resource repair independently.
- **FP-15.A — Explicit Tóth--Valtr upper bound.**  **Completed:** the explicit
  projective normalization frame, orientation-sign and convexity transfer,
  cap-anchor extension, exact cup--cap consumer, unconditional forcing theorem,
  and strict comparison with the classical bound all compile.  `Q-UPPER` is
  closed; the bounded reuse audit found no exact-route consumer.
- **FP-15.B — Suk finite quantitative kernel.**  The generic finite Dilworth
  inequality, support-region vocabulary, region partial order under explicit
  one-sided general-position hypotheses, exact adjacent-support-chain producer,
  and adjacent-region gluing consumer compile.  In particular,
  `SukAdjacentSupportData.toCertificate` derives the arrangement-cell and
  supporting-pair fields without assuming them.  The child is now gated at the
  transitive chain cup--cap theorem and global selection/positive-fraction
  assembly.  Recurrence and asymptotic optimization remain locked until those
  geometric counting layers compile.
- **FP-15.C — Point-specialized current-best upper bound.**  Locked behind a
  compiling Suk architecture.  Formalize the point-set specialization of the
  Holmsen--Mojarrad--Pach--Tardos spike and two-partial-order proof through an
  explicit integer theorem implying `2^(n + O(sqrt(n*log n)))`.  General
  pseudo-configurations are optional only after the point-set endpoint lands.

## Historical register

Retired routes and detailed execution history remain in tickets, experiment
notes, counterexample theorems, and `docs/formalization_plan.md`.  Do not copy
their full narratives here.  A retired main entry should remain as a concise
record until its negative knowledge is discoverable by stable links; a merged
entry such as `FP-06` remains in the current registry because its theorem is a
live asset of another thread.
