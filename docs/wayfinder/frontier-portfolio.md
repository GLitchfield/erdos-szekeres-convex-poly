---
title: Exact Erdős--Szekeres frontier portfolio
artifact: frontier-portfolio
schema_version: 1
status: canonical
last_updated: 2026-08-12
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
- **Strategic role:** one of `direct`, `bridge`, `generalization`, `hedge`,
  `fallback`, `discovery`, or `research-system`.
- **State:** one of `advancing`, `gated`, `parked`, `suspended`, `merged`,
  `completed`, or `retired`.
- **Model tier:** the precise mathematical universe in which its claims live.
- **Best evidence:** the strongest current evidence, using repository claim
  levels and never upgrading computation or consensus into a theorem.
- **Downstream consumer:** the theorem, ticket, or route enabled by success.
- **Open obstruction:** the smallest honest unresolved issue.
- **Next discriminating gate:** the cheapest bounded work that materially
  changes the route disposition.
- **Success payoff:** what becomes available if that gate succeeds.
- **Expiry or revival gate:** the exact evidence that stops, suspends, merges,
  or reactivates the thread.
- **Children:** stable subthread identifiers, or `none`.

`State` records mathematical disposition, not current scheduling:

- `advancing` means positive evidence and a ready next gate;
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
   preserved counterexamples. Validate the registry before making a new
   selection.
3. **Select an execution slate of size `N`.** Choose from the now-current
   executable entries using leverage, readiness, independence, information
   gain, calibrated cost, concurrency, and focus expiry. Record the selection
   rationale separately from the registry.
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

As a default breadth rule, a substantial batch should include distinct
mathematical functions—for example one unrestricted producer, one concrete
decomposable obstruction, and one generalization or falsification lane.  This
is a scheduling heuristic, not a membership rule.

### Interpret results

At an integration boundary, report for every selected thread:

- the predeclared outcome that occurred;
- its exact evidence level;
- what changed in the contribution path;
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
   obstruction, next gate, payoff, and expiry text; do not append a second
   competing status paragraph.
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

When evidence suggests several possible child attacks but none yet merits a
new main entry, assign stable child IDs such as `FP-02.A`.  Promote a child to a
new `FP-NN` entry only when it has a distinct contribution path or failure mode
that deserves independent retention and scheduling consideration.

## Current registry

### FP-01 — Predecessor half-subset producer

- **Contribution:** Produce a strong-`(k-1)`-free support containing at least
  half the vertices and feed it directly to the unrestricted exact recurrence.
- **Strategic role:** direct.
- **State:** advancing.
- **Model tier:** sweep-realizable colorings for the uniform claim; bounded
  controls also cover abstract `OneChangeOn` colorings.
- **Best evidence:** the generic consumer into `PredecessorHalfSubsetAt`
  compiles; exact Fin8 and nonvacuous Fin10 fan theorems compile.  The complete
  Fin11 synchronized-fan negation has independently replayed computational
  evidence through both the 479,434-addition full LRAT and an exhaustive
  depth-six decomposition into 64 independently certified cubes.  Cube leaves
  reduce to 17,089--61,302 additions and at most 28.4 MiB each, but every leaf
  retains 9,181--12,010 semantic base clauses.  The predeclared 8,000-base gate
  therefore stopped before Lean, so no Fin11 theorem is claimed.
- **Downstream consumer:** `sweepExactUpperAt_of_predecessorHalfSubset`, then
  the unrestricted exact upper bound.
- **Open obstruction:** compress or share the retained Fin11 semantic-clause
  bridge; learned-trace size is no longer the primary blocker.  After a kernel
  Fin11 theorem, turn compatible ten-point singleton fans into one half-sized
  fan with a common pivot and direction for arbitrary size.
- **Next discriminating gate:** on one of the eleven proof-small depth-six
  leaves, replace thousands of individual semantic leaf theorems by an indexed
  family theorem or proof-bearing semantic snapshot.  Attempt Lean only if the
  resulting imported base interface is materially smaller than 8,000 facts.
- **Success payoff:** a credible uniform producer for the unrestricted route.
- **Expiry or revival gate:** a checked realizable target-free counterexample
  to synchronized compatible fans retires this producer; abstract-only failure
  demotes the model tier but does not refute the realizable statement.
- **Children:** `FP-01.A` synchronized singleton fans; `FP-07` integral
  Property B; `FP-08` fractional cover.

### FP-02 — State-567 ten-residual system

- **Contribution:** Close the first concrete packed decomposable obstruction
  using two strong six-carriers, an exact ten-point residual, and repeated
  deletion packing.
- **Strategic role:** direct.
- **State:** advancing.
- **Model tier:** ordered `TripleColoring` with the exact packed state-567
  hypotheses; realizability or decomposability is added only when retained by
  an explicit bridge.
- **Best evidence:** probe reuse, carrier normalization, omission rectangles,
  area profiles, canonical provenance, and the full mixed six-rectangle normal
  form compile.  The quotient-free all-order certificate, all semantic clauses,
  arbitrary-placement transport, and exact public theorem
  `mixedCarrierOnlyOmissionNormalForm_forces_target567` now compile.  This
  formally closes the mixed omission profile.  A three-carrier transversal and
  residual-touching escape remain proof-ready proposals for the balanced
  profile.
- **Downstream consumer:** the packed state-567 reducer and ultimately the
  uniform decomposable exact upper theorem.
- **Open obstruction:** the balanced residual-touching family still lacks a
  placement-independent relational color law; upstream production of the mixed
  or balanced normal form also remains explicit.
- **Next discriminating gate:** consume the compiled mixed theorem in the exact
  state-567 case split, then screen only genuinely relational balanced escape
  laws that retain residual ten and repeated packing.
- **Success payoff:** discharge one or both exact state-567 terminal profiles.
- **Expiry or revival gate:** a full-context target-free model retires the
  affected terminal.  Fixed-color UNSAT cores do not advance the general leaf
  unless their hypotheses follow from canonical provenance.
- **Children:** `FP-02.A` balanced canonical transversal; `FP-02.B` mixed
  normal-form terminal; `FP-02.C` decomposability-retention bridge.

### FP-03 — Uniform Pascal-tail lift

- **Contribution:** Generalize the residual bad-block and witness-reuse kernel
  so finite state-567 progress becomes a reusable inductive mechanism.
- **Strategic role:** generalization.
- **State:** advancing.
- **Model tier:** generic finite-set incidence over exact ordered-coloring
  producers, with each color terminal stated separately.
- **Best evidence:** generic seed cover, division-free collision/large-fiber
  counting, the state-567 specialization, unequal carriers, and the exact
  state-556 collision-or-ten-fiber normalization compile.  Proof mining exposed
  a stronger witness-free Fin14 contradiction; its checkpointed certificate,
  15,951-clause semantic bridge, generic ordered-set transport, both advertised
  state-556 leaves, and the existing consumer now compile through
  `PascalTailTwoSideBound 5 5 6`.
- **Downstream consumer:** `PascalTailTwoSideBound`, then the uniform
  decomposable recurrence.
- **Open obstruction:** identify which structural part of the stronger Fin14
  base contradiction generalizes with the carrier/residual parameters; the
  current theorem is still one adjacent finite Pascal state.
- **Next discriminating gate:** mine the compiled Fin14 semantic core by clause
  family, freeze one parameterized cut/target-free lemma, and test it at the
  next adjacent Pascal states before attempting a uniform Lean theorem.
- **Success payoff:** validate the residual mechanism at an adjacent parameter
  state and expose a credible uniform Pascal theorem.
- **Expiry or revival gate:** exact countermodels to both leaves, or proof that
  the required producers exist only at the state-567 equality, demote this to
  finite infrastructure.
- **Children:** `FP-03.A` variable-carrier state-556 leaves.

### FP-04 — Layer-F highest-stratum mutation descent

- **Contribution:** Normalize unrestricted target-free realizable colorings to
  decomposable ones by a bounded mutation macro that strictly lowers the top
  decomposition-prime stratum.
- **Strategic role:** bridge.
- **State:** gated.
- **Model tier:** sweep-realizable target-free colorings and single-triple
  mutation paths.
- **Best evidence:** prime-core ranks, their decomposable characterization, and
  locality of at-most-three mutation macros compile.  The stronger
  `ThreeStepPrimeCoreFamilyShrinksAboveAt` producer now has a compiling consumer
  all the way to `SweepExactUpperAt`.  Explicit target-creation and
  persistent-split shields, their strict-family consumer, and the exact rational
  positive control compile.  Complete bounded screening shows target-free
  endpoint descent within radius three, but refutes monotone prime-core
  inclusion at every intermediate edge on four Fin7 and ten selected Fin8
  controls.
- **Downstream consumer:** `TargetReflectingDecomposableNormalizationAt`, then
  any uniform decomposable exact theorem.
- **Open obstruction:** construct a local-to-ambient macro that preserves sweep
  realizability and target-freedom stepwise while proving prime-core-family
  inclusion only between macro endpoints.  Temporary intermediate core creation
  must be permitted.
- **Next discriminating gate:** freeze one endpoint shield that accounts for
  every core created and later destroyed inside an at-most-three path; test it
  on the fourteen new hard controls before any theorem-threshold search.
- **Success payoff:** an unrestricted-to-decomposable reduction independent of
  the half-subset producer.
- **Expiry or revival gate:** a realizable target-free closed component or
  highest-stratum local minimum retires this rank; a new noncircular rank may
  revive mutation descent.
- **Children:** none.

### FP-05 — State-567 balanced five-class leaves

- **Contribution:** Attack the same exact 22-point decomposable obstruction
  through crossing-split and residue classes independent of the rectangle
  route.
- **Strategic role:** hedge.
- **State:** gated.
- **Model tier:** full packed `11+11` ordered split with side cap exclusions and
  repeated deletion packing.
- **Best evidence:** the five-way shell, universal clean `2+4` normalization,
  and middle-word infrastructure compile; all five color terminals remain open.
- **Downstream consumer:** the balanced obligation in the state-567 reducer.
- **Open obstruction:** close one of `2+4`, `3+3`, `4+2`, or the two directed
  residue-overlap leaves while visibly using the exact packed context.
- **Next discriminating gate:** select the smallest terminal with a full-context
  falsifier and prove or refute it without pair-only weakening.
- **Success payoff:** an independent state-567 closure path if `FP-02` stalls.
- **Expiry or revival gate:** an exact full-context model retires the selected
  leaf; repeated reductions inherited by the 12- or 21-point controls trigger
  suspension and route review.
- **Children:** none.

### FP-06 — Finite `k=9` extreme-exchange bridge

- **Contribution:** Supply a trusted finite successor base and engineering
  pattern for diagonal extraction.
- **Strategic role:** bridge.
- **State:** merged.
- **Model tier:** exact finite `OneChangeOn` statements at `k=9`.
- **Best evidence:** `extremeExchangeK9FinSeventeen` compiles end to end.
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
- **Strategic role:** hedge.
- **State:** gated.
- **Model tier:** exact predecessor hypergraphs induced by ordered or
  sweep-realizable colorings; relaxed hypergraphs are falsification controls.
- **Best evidence:** the recurrence consumer and small-cardinality results
  compile; bounded integral behavior survives through checked `k=6,n≤12`;
  finite semantic promotion remains incomplete.
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
- **Strategic role:** hedge.
- **State:** gated.
- **Model tier:** exact predecessor hypergraphs from sweep-realizable colorings,
  with relaxed hypergraphs used only to separate logical strengths.
- **Best evidence:** fractional-to-half and direct recurrence consumers compile;
  no integral/fractional/half separator appears through checked `k=6,n≤12`.
- **Downstream consumer:** `FP-01`.
- **Open obstruction:** prove a geometric or orientation-sensitive weighted
  inequality that cannot be cloned by relaxed hypergraphs.
- **Next discriminating gate:** freeze one weighted candidate and test it on
  exact rational controls plus the known relaxed separators before Lean work.
- **Success payoff:** a producer strictly weaker than integral Property B.
- **Expiry or revival gate:** an exact realizable fractional-cover obstruction
  retires this route; failure of one local weighting merely returns to the LP
  dual formulation.
- **Children:** none.

### FP-09 — Diagonal extreme-exchange successor

- **Contribution:** Turn the finite diagonal bases into a genuine symbolic
  successor step using core extraction and opposite-extreme cup gluing.
- **Strategic role:** generalization.
- **State:** gated.
- **Model tier:** ordered `OneChangeOn` cup-block configurations, with finite
  `k=9` the trusted base.
- **Best evidence:** exact diagonal and extreme-exchange `k=9` theorems compile;
  clause mining found no honest all-parameter law.
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
- **Strategic role:** fallback.
- **State:** gated.
- **Model tier:** fixed finite state-567 ordered colorings, with independent
  semantic reconstruction and certificate replay.
- **Best evidence:** the all-interleaving mixed normal-form terminal is
  independently certified UNSAT by two semantically distinct encodings; the
  smaller authoritative proof has 134,821 RUP additions.  No state-567 terminal
  certificate is kernel-checked, and fixed balanced cores remain too
  instance-specific for promotion.
- **Downstream consumer:** one exact leaf of `FP-02` or `FP-05`, or a symbolic
  lemma returned to `FP-02`, `FP-03`, or `FP-05`.
- **Open obstruction:** translate the quotient-free mixed certificate into a
  tractable kernel proof and connect its twelve labels to the compiling mixed
  structural normal form.
- **Next discriminating gate:** promote the authoritative mixed encoding before
  running another state-567 search; reactivate discovery only if that semantic
  bridge fails for a structural reason.
- **Success payoff:** a finite branch closure or a trustworthy pattern miner.
- **Expiry or revival gate:** resource growth, an unbridgeable semantic core,
  or instance-specific units park the certificate; a new rigid normal form can
  reactivate it.
- **Children:** none.

### FP-11 — Inverse stepping-up and decomposition extraction

- **Contribution:** Extract predecessor-free pieces or a useful deep split
  directly from a large target-free geometric configuration.
- **Strategic role:** hedge.
- **State:** parked.
- **Model tier:** sweep-realizable planar configurations.
- **Best evidence:** the useful singleton-fan branch graduated to `FP-01`;
  deletion, two-piece, and one-anchor proposals are false, circular, or inert.
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
- **Strategic role:** hedge.
- **State:** suspended.
- **Model tier:** the exact decomposable 32-point state with full residual
  family, colors, density, and decomposition data.
- **Best evidence:** extensive Lean infrastructure compiles, but relaxed and
  exact-small carrier/address cycles refute current cover and rank consumers.
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
- **Strategic role:** discovery.
- **State:** gated.
- **Model tier:** varies per frozen card and must be explicit before screening.
- **Best evidence:** several cards have graduated into `FP-02` and `FP-03`;
  negative and inert cards are retained as controls.
- **Downstream consumer:** whichever numbered mathematical thread names the
  missing lemma.
- **Open obstruction:** avoid producing true but strategically inert statements
  or a second informal backlog.
- **Next discriminating gate:** screen at most three cards chosen from current
  parent-thread obstructions, each with a consumer, falsifier, and expiry rule.
- **Success payoff:** a new proof-ready subthread or a decisive route
  retirement.
- **Expiry or revival gate:** a card without a consumer or falsifier is rejected;
  a surviving card graduates to its parent or a new `FP-NN` entry.
- **Children:** none.

### FP-14 — Formal-research system and template feedback

- **Contribution:** Reduce proof latency and evidence mistakes through better
  orchestration, certificate chunking, reproducibility, approval preflight, and
  calibrated estimates.
- **Strategic role:** research-system.
- **State:** advancing.
- **Model tier:** project process; it never constitutes mathematical evidence
  for the exact formula.
- **Best evidence:** immutable packets, outcome contracts, serialized builders,
  independent certificate checks, empirical timing records, and the closed
  portfolio execution cycle operate in the repository.  Checkpoint replay made
  the state-556 and mixed state-567 certificates kernel-feasible.  The Fin11
  cube audit separated learned-proof complexity from semantic-base complexity.
  A slate-completion manifest/checker now prevents omitted terminal lanes, and
  the guarded command runner enforces wall time, aggregate RSS, Lean-compiler
  count, process-group cleanup, and machine-readable heartbeats.  It caught a
  14-compiler Lake fan-out before another WSL resource failure.
- **Downstream consumer:** all mathematical entries, through safer and broader
  execution.
- **Open obstruction:** preserve useful breadth without allowing process work
  or scheduling metadata to become a competing mathematical roadmap; safely
  promote heavyweight generated certificates whose normal umbrella build
  exceeds the aggregate compiler/RSS envelope.
- **Next discriminating gate:** prototype an indexed semantic-base bridge on one
  proof-small Fin11 cube.  Separately rebuild the deferred state-556 and mixed
  state-567 generated modules with an explicit one-module `lean -j1` sequence,
  then restore their umbrella imports only after guarded `make test` passes.
- **Success payoff:** faster route comparison, fewer repeated dead ends, and a
  durable memory of all potentially valuable work.
- **Expiry or revival gate:** schedule process work only for a measured
  bottleneck or demonstrated evidence failure; otherwise return the slot to a
  mathematical thread.
- **Children:** `FP-14.A` large-certificate proof mining and checkpointed Lean
  replay; `FP-14.B` indexed semantic-base compression and completion signaling.

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
- **FP-03.A — Variable-carrier state 556.**  Completed finite adjacent state:
  both advertised leaves and their consumer compile, via a stronger witness-free
  Fin14 contradiction, through `PascalTailTwoSideBound 5 5 6`.  The live child
  question is parameter extraction from that stronger core.
- **FP-14.A — Large-certificate kernel replay.**  Checkpointing succeeds for
  state-556 and mixed state-567.  For Fin11, exhaustive depth-six cubes reduce
  learned traces to 17,089--61,302 additions, but the 9,181-clause minimum base
  still blocks the frozen Lean gate.  Do not deepen the same cube tree without
  a semantic-base compression mechanism.
- **FP-14.B — Indexed semantic-base compression and completion signaling.**
  Replace thousands of concrete clause theorems by a small indexed family or
  proof-bearing snapshot on one Fin11 leaf, with corrupted-index and omitted-
  family controls.  The signaling half is complete: execution slates require
  one validated terminal result per task, the root may not finish while a lane
  is live, and guarded commands emit heartbeats and kill their whole process
  group on wall-time, aggregate-RSS, or compiler-count violations.  The safe
  promotion follow-up is a serial artifact manifest for heavyweight generated
  modules.  Expire the proof bridge if it re-expands beyond the 16 GiB gate or
  weakens kernel trust; retain the signaling/resource repair independently.

## Historical register

Retired routes and detailed execution history remain in tickets, experiment
notes, counterexample theorems, and `docs/formalization_plan.md`.  Do not copy
their full narratives here.  A retired main entry should remain as a concise
record until its negative knowledge is discoverable by stable links; a merged
entry such as `FP-06` remains in the current registry because its theorem is a
live asset of another thread.
