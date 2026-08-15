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
- The dated [sober proof-distance assessment](proof-distance-assessment-2026-08-14.md)
  records the rationale for the current dependency ledger and frontier
  discipline; it is a snapshot, not a second tracker.
- The map may carry bounded execution when a ticket predeclares its inputs,
  resource limit, outcome branches, and independent certificate.
- Strategic selection, redirection, closure, and frontier promotion receive a
  bounded Sol/Fable review under `docs/adversarial-review.md`.

## Load-bearing dependency ledger

This ledger, rather than the number of frontier entries or active workers,
records proof distance to the destination.  The portfolio is an inclusive
registry of possible contributions; several entries may attack the same edge
below and therefore do not constitute independent routes.

| Edge | Required result | Status | Exact evidence and remaining gap |
| --- | --- | --- | --- |
| `D-LOWER` | Sharpness examples of size `2^(k-2)` for every `k ≥ 3` | closed | `classical_lower_sharpness` compiles for all `k`. |
| `D-MODEL` | Planar general-position sets reduce exactly to sweep colorings, and strong polygons reflect convex subsets | closed | Swept presentation, realizability, restriction, and the strong-polygon/convex-position equivalence compile. |
| `D-UPPER` | `SweepExactUpperAt k` for every `k ≥ 3` | open | This is the load-bearing universal upper bound.  Neither route below currently supplies it. |
| `D-HALF` | `PredecessorHalfSubsetAt k` for every `k ≥ 4`, feeding the exact doubling recurrence | open | The consumer compiles, but no uniform producer is known.  Finite fan theorems and bounded selector controls do not close this edge. |
| `D-DECOMP` | `DecomposableExactUpperAt k` for every `k ≥ 3` | open | The theorem compiles at `k=5,6`; the uniform induction and the first `k=7` state-567 obstruction remain open. |
| `D-NORMALIZE` | Normalize every above-threshold target-free realizable coloring to the decomposable class while reflecting targets | open | Conditional consumers compile, but no normalization or well-founded mutation-descent producer is proved. |
| `D-ASSEMBLE` | Combine the universal sweep upper, planar bridge, and sharpness into `ErdosSzekeresConjecture` | gated | Routine formal assembly is blocked only by `D-UPPER`; no theorem claiming the destination exists. |

There are presently two logical ways to close `D-UPPER`: prove `D-HALF`, or
prove both `D-DECOMP` and `D-NORMALIZE`.  Work on finite decomposable states,
certificates, selectors, or research infrastructure changes this ledger only
when it closes or strictly reduces one of those named edges.

The following supporting milestones are intentionally outside the
load-bearing ledger.  Closing one is a real scoped theorem, but changes no
destination edge unless a separate implication is proved.

| Milestone | Required result | Status | Scope firewall |
| --- | --- | --- | --- |
| `Q-UPPER` | A source-authenticated strict uniform improvement over `classical_binomial_upper` | closed | `tothValtr_upper` and `tothValtr_strictly_improves_classical` compile.  Quantitative improvement alone neither closes nor strictly reduces exact `D-UPPER`. |
| `D-UPPER(6)` | Unrestricted `erdosSzekeresFormulaAt_six : ErdosSzekeresFormulaAt 6` | gated | This fixed case has no known uniform consumer and does not close exact `D-UPPER`. |

**Latest reconciliation:** no load-bearing destination dependency changed.
The explicit Tóth--Valtr theorem still closes supporting milestone `Q-UPPER`
at `choose (2*n-5) (n-2) + 2`.  The local Suk finite checkpoint is now stronger:
the finite height--width theorem, common-base region order,
support-chain-to-certificate producer, and certificate-to-adjacent-convex-union
consumer all compile.  In particular, the arrangement-cell and opposite-pair
support fields are derived from two actual adjacent support-region chains
rather than assumed.  `FP-15.B` is now gated at global chain selection,
transitive chain cup--cap, and positive-fraction assembly.  The parallel small
geometric-forcing tests otherwise changed search information only: OneChange
is causally essential in three finite encodings; a Ringel nine-minor filters one
relaxed state-567 model without a Lean realizability bridge; and a local
carrier-internal mutation lemma compiles without a uniform producer.  None of
these results reduces `D-HALF`, `D-DECOMP`, `D-NORMALIZE`, or exact `D-UPPER`.
`D-UPPER(6)` remains a separate subordinate milestone.

## Decisions so far

<!-- One linked, one-line gist per closed ticket. Detail stays in the ticket. -->

- [Small geometric forcings close one local Suk edge but no exact edge](tickets/0012-test-small-geometric-forcings.md):
  OneChange and Ringel-minor tests are diagnostic, carrier-internal split
  persistence is conditional infrastructure, and the support-chain certificate
  producer is the slate's sole forward theorem.

- [The state-578 crossing-row address/deletion route is expired](tickets/0003-consume-state-578-crossing-row.md):
  exact Lean counterexamples refute address-only, one-column endpoint, and
  two-middle-pair consumers; the surviving bracket theorem redirects the
  route to a genuinely collective six-cap synchronization problem.
- [The state-578 local upper-bracket route reduces to an exterior fan](tickets/0004-force-state-578-upper-bracket.md):
  Lean proves a nine-source one-sided fan, while exact nine- and 13-vertex
  target-free models refute two-column brackets and every three-column
  fan-only consumer; the next invariant must use full residual density.
- [The state-578 exterior fan yields a six-column deficit, not a boundary](tickets/0005-couple-state-578-exterior-fan-density.md):
  Lean concentrates five one-upper rows away from one cap column and couples
  that blocker to two density cups, while relaxed 32-vertex and exact local
  countermodels refute direct three-boundary and post-selection two-cover
  consumers.
- [The state-578 deficit rows now share the complete blocker-family matrix](tickets/0006-synchronize-state-578-deficit-density.md):
  Lean proves five deficits contain two distinct cups, converts the two raw
  deletion escapes into a two-blocker cup or strict six-cell lower descent,
  and reconnects the result to the exact gate; a relaxed full-matrix model
  isolates the missing color-sensitive intersection anchor.
- [The state-578 mixed blocker rectangle is impossible](tickets/0007-consume-state-578-blocker-matrix.md):
  Lean glues a false-extension cup below the common minimum to a
  true-extension cap above it, producing a forbidden strong eight-set; the
  surviving one-sided localization and minimum-column alternatives remain
  open and exact-small models refute their projected forms.
- [The full state-578 matrix reduces to four exact residual obstructions](tickets/0008-consume-state-578-localized-cap-or-minimum-column.md):
  opposite directions are impossible in the full residual matrix; localized
  branches now retain a complementary three-boundary and escaping residual
  cup, while a universal column yields either a disjoint cup or a four-owner
  private residual star.
- [The state-578 private star contains a six-column plateau and two foreign caps](tickets/0009-consume-state-578-localized-escape-or-private-star.md):
  Lean uses all four private owners and all six disjoint cap blocks to replace
  the raw star by one plateau cup disjoint from two foreign columns; the three
  other residual branches remain open.
- [The present state-578 residual-cycle route is suspended](tickets/0010-consume-state-578-plateau-or-localized-escape.md):
  a terminal seven-carrier cover and universal seed-escape theorem compile,
  while relaxed and exact-small cycles refute the current cardinality/address
  ranks; revival requires a complete-family, exact-color invariant that fails
  those controls and constructs a cover, strict predecessor, or true descent.
- [Quantitative and exact-six upper bounds are separate gated intermediaries](tickets/0011-organize-upper-bound-intermediaries.md):
  `FP-15` owns a source-authenticated uniform quantitative ladder and `FP-16`
  owns unrestricted `ES(6)=17`; both are supporting milestones with explicit
  firewalls against claims about universal `D-UPPER`.

## Open frontier

### Frontier portfolio snapshot (2026-08-14)

The canonical, inclusive registry is
[`frontier-portfolio.md`](frontier-portfolio.md). It retains every currently
credible progress thread, including work that is gated, parked, suspended, or
merged. The numbered summaries below are a navigational snapshot; entry fields,
current evidence, next gates, and state transitions are maintained in the
registry.

The project no longer allocates an entire research block to one unresolved
leaf. The portfolio deliberately separates direct recurrence producers, the
first concrete decomposable obstruction, uniformization, unrestricted-bridge
work, and bounded certificate engineering. The latest literature-to-frontier
review is recorded in
`runs/reviews/20260813-literature-frontier-run/ADVISORY-SUMMARY.md`. Both blind
reviewers rated the proposed update partially supported and recommended one
conservative child under Thread 1, with a process-only cross-reference under
Thread 14; the reciprocal critique failed operationally, so this is advisory
rather than a complete harness result. Subsequent admitted execution demoted
Thread 14 to gated after its exact indexed Fin11 compression still exhausted
the 16-GiB Lean gate. Work blocks select a temporary execution slate from this
inventory; the number of slots and the current slate do not define which
threads remain valuable.

1. **Predecessor half-subset producer (primary unrestricted route).**  Seek
   `PredecessorHalfSubsetAt k` directly.  Integral bicoloring and fractional
   cover remain stronger possible producers, but bounded tests must classify
   them separately.  The stopped maximum-support two-deletion exchange is not
   to be retried.  Exact computation finds no integral/fractional/half
   separator through `k=6,n=12`.  The first pure deep-split boundary now
   compiles exactly at `k=5,Fin 8`.  A thresholded singleton-fan producer now
   has a compiling noncircular consumer into `PredecessorHalfSubsetAt`; its
   `k=5,Fin 9` gate is vacuous because the existing nine-point signotope
   certificate already forces a strong five.  At the first meaningful
   `k=6,Fin 10` boundary, two independent complete encodings prove the fan
   negation UNSAT while target-free controls are SAT.  That nonvacuous result
   now compiles as `halfPureSingletonFanAtSixFinTen_of_oneChange`: a
   438-variable dense core, 2,405 semantic leaves, and 2,007 LRAT additions are
   checked through 76 generated chunks.  Its 388 concrete fan branches remain
   Fin-10-specific, so the uniform producer is still the mathematical target.
   Mining those branches rejects both arbitrary fan extension and maximal-fan
   growth, including on exact planar controls.  The surviving candidate is
   synchronization across overlapping ten-point restrictions: a common pivot
   and direction whose compatible five-fans cover a half-sized side.  This has
   a noncircular consumer into the thresholded singleton-fan producer.  Its
   exact abstract `Fin 11` negation is certificate-replayed UNSAT: 1,881
   variables, 26,862 clauses, and 479,434 independently checked additions cover
   all 4,620 side/pivot/direction branches.  Exhaustive splitting on six
   orientation variables now yields 64 independently certified leaves with
   17,089--61,302 additions.  On the unique minimum leaf, 3,527 indexed facts
   reconstruct all 9,181 base clauses exactly with corruption controls, but a
   monolithic Lean replay exhausted the 16-GiB gate at 14.9 GiB.  The next
   certificate action is a streaming or balanced-checkpoint replay of that
   same leaf, not deeper splitting of the same cube tree.  Neither the Fin11
   theorem nor the all-`n` synchronization/relabeling bridge is proved.  A new
   literature-informed child studies full-ambient pair-rank down-sets as the
   possible synchronization mechanism.  Its first gate is local
   strict-extension with clipping non-saturation.  The resulting proposal says
   that a nonsaturated cap/cup maximizer either creates a strict full-ambient
   down-set difference or the two maximizing endpoints cross.  The compiled
   realizable Fin9 collision falls exactly into the crossed branch, so the
   local lemma survives.  The exact endpoint dichotomy, clipped extension
   helper, threshold producer interface, and noncircular consumer into
   `PredecessorHalfSubsetAt 6` now compile and passed independent review.  The
   exact rational Fin9 counterexample to the single-cell threshold producer:
   every threshold side is too small or contains a strong five.  Its exact
   geometric bridge, Boolean full-ambient rank computation, and public negation
   theorem now compile, so the single-cell producer is formally expired.
   The local dichotomy remains infrastructure.  An adaptive Boolean combination
   of two ambient cells survives the stored model and all 3,270 target-free
   configurations in two bounded rational domains.  The first frozen geometric
   selector passed all inherited controls but is refuted by a new held-out
   rational Fin9 model that still admits 22 successful classifiers.  Thus the
   collective card survives, while selector design—not existential search—is
   the sharpened obstruction.  The complete classifier cube now has a
   compiling defect, exchange relation, and conditional recurrence consumer,
   but exact replay finds 535 radius-one and 265 radius-two positive-defect
   local minima in the stored Fin9 model.  Local exchange of radius at most two
   is therefore expired; any next selector must be genuinely nonlocal (or the
   route must return to synchronized fans).
2. **State-567 ten-residual occupancy leaves (primary decomposable route).**
   Use the compiling mutually-middle-obstructed pair and universal four-block
   escape normalization.  Close, or exactly refute, the residual-only,
   one-carrier, and two-carrier branches.  Every valid contradiction must use
   the ten-point residual and repeated deletion packing; pair-only arguments
   are expired by the 12-point control.  The no-collision carrier-only branch
   now has a compiling exact omission-area dichotomy: either four disjoint
   `3×3` rectangles or four area-5 plus two area-8 rectangles.  A six-strong-
   set color closure for the balanced profile is false even for exact integer
   planar configurations; any repair must use decomposability or the full
   packed-22/residual-ten provenance essentially.  The bare claim that every
   carrier-contained strong six is a carrier or one of four grid witnesses is
   false: the planar control has 46 such sets, including 40 extras.  The
   canonical repair now compiles as
   `carrierContainedStrongSix_classification_of_canonical567`: one bad
   residual four-block promotes every mixed carrier-contained strong six into
   the actual probe family.  The exact
   `packedInternalPair_has_sameOccupancyCollision_or_balancedGrid567` consumer
   now compiles and formally eliminates the mixed profile.  A color-free
   `15>4*3` argument proves the balanced grid has a three-carrier transversal;
   canonical provenance and a new use of global packing then prove that
   deleting the transversal with any residual triple forces a genuinely
   residual-touching strong six.  A fixed 22-point carrier extension
   is certificate-replayed UNSAT, with strong-seven avoidance decisive, but
   its minimized core depends on 96 carrier colors that are individually
   flexible under canonical grid provenance.  It is therefore an
   instance-specific control, not a terminal proof.  In the mixed branch, the
   full six-rectangle normal form (or its transpose), including pointwise
   incidence types and `6+6` carrier cardinalities, now compiles.  Its exact
   all-interleaving color terminal is independently certified UNSAT twice: an
   authoritative quotient-free encoding replays 134,821 RUP additions, and an
   independent Aut-768 cross-section encoding replays 2,958,768.  The
   checkpointed quotient-free certificate, all 14,773 retained semantic
   clauses, arbitrary-placement finite theorem, and exact public structural
   consumer now compile.  The mixed omission profile is formally closed; the
   live state-567 work is now exactly the balanced residual-touching color law
   plus the separate same-occupancy collision terminal.  A new mathematical
   compression factors the balanced branch through a transversal hitting every
   carrier-contained strong six and only the 120 residual-triple deletions,
   reducing the raw witness ledger from 597,500,904 to 960,960 occurrences.
   The exact hitting, targeted-packing, residual-touching equivalence, and
   global-to-targeted implication now compile.  An independently reconstructed
   arbitrary-carrier Fin22 encoding of the compressed consequence is SAT and
   its model directly passes all 120 targeted deletions, so that consequence is
   not a terminal color law.  Direct replay now shows the fixed model fails
   canonical provenance with 44 overlapping witnesses and only 28/36 pair
   coverage; the exact 19.48-million-clause canonical augmentation reaches its
   30-minute resource gate without a decision.  Separately, the model realizes
   the complete light four-repair collision network and global packing but has
   no admissible cap-four-free ordered cut.  The direct full-context collision
   negation has now been encoded without targeted-packing or provenance
   shortcuts and independently certified UNSAT (3,172,823 clauses and
   1,283,493 pure-RUP additions).  Its 994-MiB proof is computational evidence,
   not a Lean theorem.  The next gates must compress the provenance
   augmentation and extract a cut-sensitive semantic lemma from this direct
   collision proof, rather than rerunning either raw formula.
3. **Uniform Pascal-tail lift (primary generalization route).**  Extract the
   state-567 proof's numerical and structural kernel into a parameterized
   two-carrier/residual-escape theorem and consume it through
   `PascalTailTwoSideBound`.  The first milestone is a genuine parameterized
   lemma whose specialization proves, rather than assumes, a state-567 leaf.
   If the finite proof spends an equality peculiar to `(5,6,7)`, retain that
   finite theorem and redesign the uniform invariant instead of disguising a
   one-case proof as induction.  The generic bad-block seed-cover and
   collision-or-large-fiber count now compile, including the exact state-567
   specialization `112 < choose 10 3 = 120`.  This is reusable finite-set
   machinery, but not a uniform Pascal-tail theorem: the smaller diagonal
   controls do not even instantiate the two-disjoint-carrier residual setup.
   A genuinely unequal `5+1` carrier producer now compiles at state `(5,5,6)`:
   it leaves an eight-point residual with at least ten bad triples.  Its first
   all-in-one terminal is equivalent to the desired finite two-side bound and
   is only a packaging boundary.  The honest generic
   `(R,B,C,M)=(8,3,1,9)` collision-or-ten-fiber disjunction now compiles:
   either two distinct strong-five deletion witnesses occur, or one witness
   serves at least ten bad residual triples.  Two explicit local color-leaf
   interfaces retain the full ordered fourteen-point context, and their
   compiled consumer recovers the old terminal.  Both exact Fin14 leaf
   negations are independently certified UNSAT: the distinct-witness proof has
   16,434 RUP additions, and the genuine ten-distinct-block fiber proof has
   14,315.  Proof mining found a stronger witness-free Fin14 contradiction;
   its checkpointed certificate, semantic bridge, exact ordered-set transport,
   both advertised leaves, and existing consumer now compile through
   `PascalTailTwoSideBound 5 5 6`.  Complete origin reconstruction shows that
   6,165 of the 15,951 retained clauses—every strong-five definition and 692
   dead strong-four definitions—are eliminable certificate residue.  The
   surviving generic strong-polygon middle-profile window now compiles: cap
   and cup holes bound the two endpoint-color counts, with exact 556, 567, and
   dual capacities 6, 10, and 10.  The coefficient embeds in the local
   binomial window, and the old state-567 middle-word result has a fresh
   noncircular derivation.  Independently replayed exact computation refutes
   the first ambient lacing-capacity theorem on an integer-coordinate 567 model
   and its 657 reflection: identical
   profiles and individually strong extensions do not force their union strong.
   Revival requires an upstream cross-endpoint equality absent from OneChange
   and the local profile window.
4. **Layer-F highest-stratum mutation descent (unrestricted sidecar).**  Test
   and then prove or refute `ThreeStepTopPrimeStratumDropsAboveAt`.  Only exact
   realizable, target-free controls can decide the route; below-threshold
   abstract censuses are diagnostics.  A realizable closed component or
   highest-stratum local minimum expires the candidate.  Its final payoff
   remains conditional on a uniform decomposable upper theorem.  Lean now
   proves that any at-most-three target-free mutation macro localizes every
   endpoint prime-core change to supports containing one of at most three
   changed triples.  The stronger creation-free producer
   `ThreeStepPrimeCoreFamilyShrinksAboveAt` has a compiling consumer through
   stratified descent, target-free normalization, and `SweepExactUpperAt`.
   Explicit target-creation and persistent-split shields, their strict-family
   consumer, and the exact rational positive control now compile.  Independent
   bounded replay still finds target-free endpoint descent within radius three,
   but refutes monotone prime-core inclusion at every intermediate edge on four
   Fin7 and ten selected Fin8 controls.  A frozen endpoint-only persistent-split
   shield that explicitly allows those transient cores passes all fourteen
   controls under independent replay and corruption rejection.  A read-only
   audit gives the exact noncircular cardinality-stratum subset/count-drop
   consumer chain, but also shows that carrier cover plus the endpoint shield
   already packages the no-new-core half of descent.  A noncircular rooted-
   circuit split-surgery sufficient-interface proposal passes all fourteen
   small abstract controls and now has a nonvacuous exact rational Fin8 witness
   with five persistence supports.  Its first exact Fin17 architecture is
   independently unit-refutable before candidate replay, so the next task is to
   locate the inconsistent architectural layer and construct a nonempty
   above-threshold control.  No strict logical weakening of the endpoint shield
   is claimed, and a wrapper-only theorem remains strategically inert.
5. **State-567 balanced five-class leaves (parallel decomposable branch).**
   Prove the mechanical five-way exhaustion, then attack the `2+4`, `3+3`,
   `4+2`, left-right residue, and right-left residue terminal classes.  Pair
   dual branches only after an explicit reversal/color-duality transport is
   available.  The exact `11+11` split, side cap exclusions, and repeated
   packing must remain visible in every terminal contract.  The exact `3+3`
   structural reduction now compiles, and the corresponding full-context
   negation is independently certified UNSAT (1,583,924 clauses and 1,653,441
   pure-RUP additions).  The 336-MiB proof exceeds the Lean-promotion gate, so
   semantic compression of this supported terminal is now the live task.
6. **Finite `k=9` extreme-exchange Lean bridge (completed; merged into 9).**
   `extremeExchangeK9FinSeventeen` now compiles end to end, including all seven
   former strong-ten blockers.  The bounded engineering route has reached its
   stop condition.  Retain the theorem as a finite base and move any further
   work to Thread 9's symbolic successor extraction; do not accumulate another
   isolated finite case.
7. **Integral predecessor Property-B producer.**  Finish the finite semantic
   control only with a bounded architecture, then seek an all-`k` structural
   bicoloring theorem for the predecessor hypergraph.  The large Fin-8 bridge
   is a diagnostic/base theorem, not the destination.
8. **Fractional predecessor-cover producer.**  Use rational LP duality,
   averaging, or exact weighted charging to prove total cover weight at most
   two.  This route survives failure of integral Property B and already has a
   compiling recurrence consumer.
9. **Diagonal extreme-exchange successor.**  Replace the stopped monolithic
   double-deletion gluing statement by a genuine core-extraction theorem plus
   the compiling opposite-extreme cup gluing lemma.  The new premise must be
   strictly weaker than the next diagonal theorem.  The exact `k=9` extraction
   theorem is now available; clause mining found no honest uniform statement,
   so the next gate is a separately stated symbolic candidate tested at
   `k=10`, not more certificate inspection.
10. **State-567 finite-certificate fallback (merged into 2 and 5).**  The
   quotient-free mixed certificate, semantic bridge, arbitrary-placement
   transport, and exact public theorem now compile, so that finite branch is
   closed.  Remaining balanced and collision certificates are owned by their
   mathematical parents.  This entry has no independent execution lane; a
   finite state closure is not a substitute for the uniform Pascal mechanism.
11. **Inverse stepping-up/decomposition extraction.**  Test whether a large
   target-free realizable configuration canonically yields two smaller
   predecessor-free pieces, a half-size predecessor-free support, or an exact
   deep split.  Reject any formulation equivalent to the desired recurrence.
   The successful singleton-fan direction has graduated to Thread 1; the
   two-piece and deletion alternatives remain parked until a new geometric
   mechanism distinguishes them from the stopped controls.
12. **State-578 strict-gate revival.**  Keep the route dormant unless a
    complete-residual-family, exact-color-and-density invariant defeats every
    recorded carrier/address cycle and constructs a cover, strict predecessor,
    or true descent.
13. **Goal-driven intermediary lemma forge.**  At portfolio checkpoints,
   screen at most three route-independent Lean-shaped statements with named
   consumers, exact model tiers, bounded falsifiers, and expiry conditions.
   The current cards are the mixed `(4 area-5)+(2 area-8)` full-context
   terminal, a decomposability-retention bridge for the carrier union, and a
   variable-carrier repair of the generic residual count.  The balanced-grid
   residual escape has graduated to Thread 2.
14. **Formal-research system and template feedback.**  Improve certificate
    chunking, immutable task packets, approval preflight, measured time
    calibration, tool/skill cataloging, and parallel-route orchestration when
   those changes reduce proof latency or evidence mistakes.  Process work is
   never credited as mathematical completion.  The current ledger has 269
   completed rows, median actual/midpoint ratio `0.240`, and only `15.2%`
   inside the old forecast ranges; future estimates must use category- and
   size-conditioned empirical bands rather than raw task-list sums.
15. **Uniform quantitative upper-bound ladder.**  The authenticated
    Tóth--Valtr bound now compiles through an explicit projective normalization
    frame and the existing cup--cap theorem, closing `Q-UPPER`.  The next child
    is Suk's finite partial-order and adjacent-region kernel; the
    point-specialized current-best bound remains gated behind that architecture.
    No exact-route consumer has been proved, so exact `D-UPPER` is unchanged.
16. **Exact unrestricted `ES(6)=17`.**  Audit the Isabelle/HOL abstraction and
    certificate against the repository's realizable sweep semantics before
    replay work.  The terminal is the public Lean theorem
    `erdosSzekeresFormulaAt_six`; after it compiles, stop fixed-instance
    engineering unless one parameterized extraction hypothesis has a named
    consumer beyond six.

### Newly surfaced subthreads

These are children of the reviewed portfolio, not new top-level routes.

- **T1.A — Fin10 singleton-fan certificate promotion.**  **Completed:** the
  exact `halfPureSingletonFanAtSixFinTen_of_oneChange` theorem compiles.  The
   synchronized compatible-ten-window candidate survives the exact `n=11`
   gate.  Exhaustive depth-six splitting gives 64 independently certified
   cubes and reduces learned traces to 17,089--61,302 additions, but every leaf
   retains at least 9,181 semantic base clauses and misses the frozen 8,000-leaf
   gate.  The next child task is indexed semantic-base compression on one of
   the eleven otherwise proof-small leaves; only after a compiling Fin11
   theorem should the route attempt restriction/relabeling and overlap
   synchronization.
- **T1.B — ambient endpoint-synchronized down-sets.**  Literature analysis,
  not a theorem, isolates the split-profile endpoint mismatch as a candidate
  mechanism.  Work in the sweep-realizable tier, using OneChange/decomposable
  models only as controls.  Compile the local full-ambient down-set lemma,
  freeze a noncircular endpoint-repair/half-support card, and attack it first
  with the realizable Fin9 collision.  A compression-only outcome belongs to
  T14.B; a recurrence through clipped child ranks is already refuted.
- **T2.A — balanced canonical-provenance branch.**  The universal four-block
  escape is redundant once rectangle coverage is known, and the bare
  carrier-contained classification is false.  Canonical provenance compiles;
  the three-vertex transversal and residual-touching packing theorem are now
  proof-ready.  Direct promotion of the fixed-extension UNSAT core is expired
  because its necessary carrier literals are not consequences of the grid.
  The remaining terminal must couple residual-touching witnesses through a
  genuinely placement-independent color law.
- **T2.B — mixed omission-profile terminal.**  **Completed finite terminal:**
  carrier cardinalities `6+6`, the complete pointwise/six-rectangle normal
  form, quotient-free checkpointed certificate, 14,773-clause semantic bridge,
  arbitrary-placement theorem, and exact public relabeling consumer all
  compile.  Consume this theorem in the state-567 case split; new proof work
  belongs to the balanced profile or upstream normal-form production.
- **T2.C — decomposability-retention bridge.**  Audit whether ambient
  decomposability can be retained through the packed reducer and restricted to
  the twelve carrier vertices.  If so, test a decomposable-grid color theorem;
  otherwise expire this repair rather than assuming a premise the leaf erased.
- **T3.A — variable-carrier Pascal repair.**  **Completed adjacent finite
  state:** the unequal `5+1` carrier system, choice-free witness universe,
  collision-or-ten-fiber theorem, both advertised leaves, and their consumer
  compile through `PascalTailTwoSideBound 5 5 6`.  Proof mining found a stronger
  witness-free Fin14 contradiction.  The next task is parameter extraction from
  that semantic core, tested at adjacent Pascal states before any uniform claim.
- **T14.A — large-certificate kernel replay.**  Checkpointing closed the
  state-556 and mixed state-567 certificates.  Fin11 cube decomposition makes
  the learned traces small enough but leaves 9,181--12,010 semantic clauses per
  leaf.  Do not deepen the same cube tree until an indexed semantic-base bridge
  or proof-bearing snapshot passes on one proof-small leaf.
- **T14.B — guarded completion and certificate promotion.**  The protocol now
  forbids final responses while a slate worker is live, requires frequent
  root-owned commentary, and validates one terminal result per task with
  `scripts/check_agent_slate.py`.  `scripts/run_lean_guarded.py` additionally
  enforces wall time, aggregate RSS, Lean-compiler count, and whole-process-
  group cleanup; it caught a 14-compiler Lake fan-out before WSL failed.  The
  deferred state-556 and mixed state-567 artifacts have now been rebuilt
  serially and their umbrella imports restored.  The next gate is an indexed
  semantic-base bridge on one Fin11 cube, testing the full-ambient down-set
  comparisons from T1.B with omitted-index and corrupted-family controls and
  keeping certificate compression distinct from mathematical producer proof.

Threads 1--3 are the most direct paths to the exact upper recurrence.  Threads
4--11 hedge distinct mathematical and formalization failure modes; 12 is
dormant; 13--14 improve discovery and throughput.  No reserve or process
thread may displace all three primary routes at once.  State 578 remains
suspended under ticket 0010 until its stated revival gate is met.

- [Choose the canonical formal model](tickets/0001-choose-formal-model.md)
  before committing the unrestricted bridge. Deletion-minimal
  decomposition-prime supports compile, but an exact realizable seven-point
  Lean counterexample stops one-or-two deletion descent. The original
  unthresholded mutation contracts are also kernel-refuted by their empty
  instance. Their exact-threshold replacements compile, as does the
  characterization `PrimeCoreCount χ = 0 ↔ IsDecomposable χ` on nonempty
  ground sets. Mutation locality now compiles: changing one ordered triple can
  alter prime-core status only on supports containing all three changed
  vertices, with exact created-versus-destroyed accounting in every
  cardinality stratum. The raw count is retained as a diagnostic, while the
  primary candidate is now `StratifiedPrimeCoreRank`; its zero/decomposable
  characterization compiles. Lean now also proves the decisive arithmetic
  bridge: equality above one positive stratum plus a strict prime-core loss at
  that stratum strictly decreases the stratified rank, and freezes the exact
  three-step geometric contract that feeds the threshold-normalization
  consumer.  The stronger creation-free interface
  `ThreeStepPrimeCoreFamilyShrinksAboveAt` and its consumer into the exact sweep
  upper theorem now compile.  A complete seven-point mutation census and all
  2,158 selected hard eight-point promotions find an endpoint whose complete
  prime-core family is a strict subset within three target-free abstract
  mutations; exactly two seven-point sources require all three. These are
  below-threshold computational controls, not realizable descent proofs. The
  hard Layer-F target is now an ambient lifting law that simultaneously
  preserves sweep realizability, excludes crossing strong targets, and prevents
  creation of every ambient prime core, or a realizable threshold obstruction
  refuting that proposal.
  A genuinely independent unrestricted bridge is now also admitted:
  `StrongPredecessorBicoloringAt k` asks for a two-coloring whose classes avoid
  strong `(k-1)`-polygons. Its `SweepExactUpperAt (k-1) → SweepExactUpperAt k`
  consumer and the `k=3` base compile, and two independent abstract audits pass
  the stronger balanced `k=5`, eight-vertex gate. Its exact counterexample CNF
  has an independently replayed exhaustive certificate and a bare Lean LRAT
  contradiction, but the generated semantic theorem still exceeds the
  16-GiB bridge budget. Exact core minimization removed only 16 of 1,211
  clauses while enlarging the certificate, so the bicoloring theorem and even
  this bounded semantic promotion remain open. A separate prefix-free
  middle-word frontier proposal is stopped by a six-vertex abstract
  counterexample and is no longer an active route. The predecessor hierarchy
  now compiles all the way from integral bicoloring through fractional cover
  and a single predecessor-free half-subset to the exact recurrence.  The new
  exact `PredecessorHalfMassAt` interface also compiles: fractional cover gives
  half-mass by finite double counting, uniform half-mass gives the half-subset,
  and half-mass feeds the recurrence.  This closes the easy direction without
  importing LP duality; an orientation-sensitive weighted producer remains
  open. A
  certificate-free theorem proves the integral bicoloring for every
  strong-`k`-free coloring on at most `2*k-3` vertices when `k>=5`. At `k=6`,
  independent exact finite checks find no integral/fractional/half separator
  through 12 vertices, but only the range through nine is a Lean theorem; the
  independently replayed `n=12` LRAT is 1.23 GB and remains computational
  evidence. A maximum-support two-deletion exchange, neighborhood-only
  weighting, and the first signed consecutive-transition charge are retired
  by exact rational eight-point controls. The 2026-08-11 predecessor-pivot
  Sol/Fable review (report SHA-256
  `64cffcc21fb0443e7568bad9ff35ab5b9162bf5563d1f326af5b0019c9476994`)
  expires local eligibility charging and ranks the already defined pure
  deep-split producer first, followed by exactly one genuinely collective
  multi-exterior invariant. Integral and fractional producers remain reserves;
  `n=13` receives resource preflight only. The half-subset hierarchy remains
  live and unproved in general. Its primary pure-split producer survives the complete
  Fin8 boundary: every one of the 19,870 strong-five-free rank-three
  signotopes has the unchanged `HalfPureDeepSplitAt 5` conclusion in two
  independent enumerations. The bounded statement is now a completed Lean
  theorem: `halfPureDeepSplitAtFiveFinEight_of_oneChange` connects the exact
  semantics to a compact certificate replay. This is not a uniform theorem;
  the next warranted target is structural rather than larger enumeration.
- [Test E3 and select a repair strategy](tickets/0002-test-e3-and-select-repair.md)
  now focuses on the uniform `PascalTailTwoSideBound`; its first open instance
  is exactly the state-567 two-cap-free-sides theorem. The diagonal `a=4`
  cup-block interface and all cases through `k=8` now compile, isolating
  `k=9` (`7+8/8+7`) as the first new uniform test. Both `k=9`
  orientations and all nondual 22-point state-567 cuts are UNSAT in fresh
  bounded audits. The two reduced `k=9` propositional cores, every retained
  semantic clause, both normalized `Fin 15` consequences, and arbitrary-block
  transport now compile, proving `diagonalCupBlocksForce4kk_nine`.
  The first noncircular successor repair has also been isolated. Lean proves
  that cup extensions of one core by opposite extreme vertices glue to a
  larger cup. Both normalized 17-point `k=9` extreme-exchange extraction gates
  are now fully kernel-checked: all seven strong-ten helpers, all 48 semantic
  chunks, both orientation roots, and `extremeExchangeK9FinSeventeen` compile.
  The theorem is an exact finite successor base, not an all-parameter
  extraction theorem. A read-only mining audit found that its clauses
  reconstruct ten-point middle colors by explicit finite cases and expose no
  stable uniform propagation rule, so uniformity by clause inspection is
  stopped.
  State 567 remains formally reduced to two exact 22-point packing obligations.
  In the packed internal branch, Lean now constructs the disjoint mutually
  middle-obstructed partner, proves that the pair leaves exactly ten residual
  vertices, and obtains an avoiding strong-six for every carrier pair and
  residual four-block. Exact no-strong-seven incidence counting now compiles:
  the ten-point residual contains at least 30 non-strong six-subsets, hence at
  least 30 complementary four-block probes, and repeated packing supplies a
  carrier-touching strong-six escape for every counted probe. Choice-free
  fiber counting and a residual-triple cover now compile. The sharpened
  theorem `exists_sameOccupancyCollision_or_carrierOnlyWitness567` yields
  either two distinct escapes with the same coarse occupancy or a strong six
  wholly contained in the carriers. Lean normalizes the latter to the five
  overlap profiles, and packages its no-collision witnesses as a finite family
  of pairwise edge-disjoint omission rectangles covering every anchor pair.
  In the collision branch, exact light replacement data and a four-repair
  triangular avoidance network also compile. A relaxed Fin12 rectangle
  terminal is computationally UNSAT but not kernel-checked. The exact
  The carrier-only rectangle system now has a compiling exact area-profile
  dichotomy and balanced four-grid extraction.  A consecutive-block complete
  strong-six grid is computationally UNSAT, but the arbitrary-block lemma is
  false: an independently replayed 12-vertex counterexample has an exact
  integer planar realization while being nondecomposable.  Therefore neither
  OneChange nor sweep realizability can close the local balanced grid; the next
  consumer must spend decomposability of the union or the stronger packed
  provenance.  The exact color-sensitive consumers remain open. The completed `k=9` bridge validates the finite
  diagonal interface and certificate workflow but does not itself supply the
  uniform successor step. The historical route
  record follows. The scalar recurrence, maxima-only
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
  inside the 12 cup vertices has the exhaustive `2+2+0` or `2+1+1` incidence
  split, but both branches are now formally expired. A minimal 12-vertex
  recursive tree realizes both profiles while avoiding a five-cap, five-cup,
  seven-cap, and strong eight-set; Lean also transports it to an actual swept
  planar configuration. Thus decomposability, realizability, local root
  profiles, and incidence alone cannot close the gate. The full 32-vertex
  state retains information absent from that counterexample: three external
  caps make four pairwise-disjoint caps with the regenerated cap, the original
  `3+3` packing occupies exactly 24 vertices, and exactly eight reservoir
  vertices remain unused. That global package now yields six pairwise-disjoint
  four-caps with a `24+8` split. In the `2+2+0` branch, protecting the missed
  cup yields a disjoint one-cup/five-cap 24-vertex package; the other branch is
  retained explicitly as an all-hit `2+1+1` state. More importantly, the
  `32/23` density proves that every four-cup transversal has at least ten
  vertices. The original 12 cup vertices therefore either miss a fourth cup
  entirely or contain a minimum 10--12-owner transversal with injectively
  chosen private cups, each using a vertex outside the original cup support.
  A checked relaxed 32-vertex incidence model realizes all of these counts and
  collapses the raw deletion ledger to two cups, so incidence/cardinality and
  shared-middle arguments alone are expired. One selected cup is now proved
  wholly inside the owner transversal and supplies a four-owner private-cup
  star. Its 24 pairings with the six cap blocks form a compiling `4 × 6`
  first-joint-split matrix whose rows and columns are prefix chains. A
  seven-vertex sweep-realizable common-tail example formally expires star-only
  tail nonreuse. Lean also proves the exact terminal contract: an exchange
  replacing `4r` protected owners by at most `3r` boundary vertices while
  preserving cup hits constructs the impossible nine-vertex transversal.
  Experiment 0071 now treats all full selected cups simultaneously. Their
  protected union has exact size `4r`, while local seven-vertex
  spine/private-cup carriers each admit a three-vertex cup transversal. The
  union of these local boundaries has size at most `3r`; density forces a
  residual cup outside every old carrier. Lean packages the result as an
  expanding seven-vertex carrier: the new cup meets a full spine but contains
  a vertex outside that spine's old carrier. In the tight one-spine branch,
  four owner-indexed partial exchanges cannot all reuse one cup and form a
  second `4 × 6` residual-cup/six-cap address matrix. Experiment 0072 repairs
  a vacuous mixed branch in the sampled classification by retaining explicit
  opposite strict cells and their cross-minimum witnesses. More importantly,
  Lean now indexes every residual four-cup against all six caps. The complete
  matrix has prefix-chain rows and columns and a global minimum. Intersecting
  cup rows cannot strictly leave that minimum in opposite directions, so
  mixed strict directions force every cell of the distinguished four-owner
  spine row to remain at the minimum. The route is therefore reduced to a
  one-sided matrix or this exact anchor plateau and reconnects to the actual
  32-vertex gate. On an eight-vertex carrier, Lean also proves that a
  three-vertex four-cup transversal is equivalent to a five-subset with no
  four-cup, and closes the decomposable singleton-lower root case. Two
  independent bounded enumerators found the transversal in all 121,577
  five-cup-free decomposable colorings on eight vertices. Lean now proves the
  stronger root-only density theorem by explicit arguments for all seven
  nonempty split profiles and derives a five-cup-or-three-boundary dichotomy
  on every decomposable eight-vertex carrier. This closes the local plateau.
  Applied to the exact `24+8` packages, the unused eight vertices outside the
  six-cap, original `3+3`, and protected one-cup/five-cap supports each carry
  a three-boundary under global five-cup avoidance. The full anchor plateau
  remains open because residual cups may cross the selected 24 vertices. The
  next target is a crossing-to-remainder bridge coupling such a residual cup
  to the unused boundary or to a forbidden outcome through the six-cap
  matrix. A post-result blind Sol/Fable review rejected direct boundary hits
  and selected witness packaging first. Lean now proves the exact repaired
  statement in the tight one-spine branch: a residual cup evades both the six
  unprotected owner vertices and the unused three-boundary, hence cannot lie
  in the unused eight vertices and must meet the selected six-cap support.
  This supplies a genuine crossing row of the full matrix. The next target is
  to consume that row at the common-minimum node using full-matrix cap
  localization and the at-most-eight child theorem. The full-family
  localization and complementary-child boundary now compile. In a localized
  branch each residual row is wholly inside the large child or stays at the
  minimum in all six columns, with the exact endpoint/reverse-separation
  profile retained at every base cell. A kernel-checked relaxed 32-vertex
  model proves that crossing the selected `24+8` support split need not meet
  the small decomposition child; an all-base address model also satisfies the
  bare prefix contracts. Thus address-only closure is expired. The reviewed
  replacement, a 24-row cap-vertex-deletion ledger, now compiles, including
  its exact per-column distinctness and endpoint alternatives. Exact Lean
  counterexamples show that all four rows of one cap column may share a
  three-vertex core, a common root address, and the same endpoint shape while
  avoiding every target. Density nevertheless proves a six-vertex lower
  bound for transversals after blocking one cap and hence extracts two
  residual cups with disjoint sweep-middle pairs. A cardinality-minimal
  ten-vertex decomposable, sweep-realizable Lean model shows that even two
  such pairs may lie in the lower child beneath two shared upper endpoints
  without a target. The surviving theorem turns this obstruction around:
  every lower set strictly bracketed by two upper vertices is cap-colored
  under five-cup avoidance, so at most six such vertices exist when seven-caps
  are forbidden. Ticket 0003 therefore closes with Outcome 3. Ticket 0004
  now closes with Outcome 2: a cardinality-minimal nine-vertex model refutes
  two-column closure, while the exact global replacement gives a
  `24 → 18 → 9` exterior fan using at least three cap columns. An exact
  13-vertex decomposable, sweep-realizable model realizes that complete local
  fan without any target. Tickets 0005--0010 subsequently added the full
  density matrix, eliminated opposite strict extensions, and isolated the
  terminal seven-carrier cover. The present branch is now suspended because
  all identified seed, address, and carrier-cardinality ranks admit explicit
  cycles; Experiment 0094 records the exact revival gate.
## Not yet specified

- A geometric/combinatorial equivalence layer for convex position, cups, caps,
  strong polygons, and realizable orientation configurations.
- Formal reproduction of the known exact cases `n ≤ 6` and extraction of the
  structural obstruction that first appears at `n = 7`.
- Formal use of the Erdős--Tuza--Valtr equivalence and the 2026 decomposable-set
  theorem to constrain a minimal counterexample.
- A new structural recurrence or decomposition theorem strong enough to close
  the gap between the lower construction and the best general upper bound.
- A complete-residual-family, exact-color state-578 invariant which fails the
  known cycle controls and constructs a seven-carrier cover, strict
  predecessor, or well-founded descent. Until such a statement is concrete,
  state 578 is not a main-route work item.

## Out of scope

- Empty-polygon (hole), colored, higher-dimensional, convex-body, game, and
  projective variants are not independent destinations. They enter only when a
  precise lemma or formal technique advances the exact planar formula.
- Numerical evidence, SAT satisfiability/unsatisfiability, or an informal proof
  without a Lean kernel check cannot close the destination.
