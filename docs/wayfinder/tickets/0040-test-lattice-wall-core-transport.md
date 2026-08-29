---
title: Test lattice-wall transport of decomposition-prime cores
type: research
mode: HITL
status: closed
claim: codex-lattice-wall-core-transport-2026-08-19
blocked_by: none
---

# Ticket 0040: test lattice-wall transport of decomposition-prime cores

## Question

Can the exact rank-one wall update coming from the Grassmannian/lattice
representation canonically transport every newly created decomposition-prime
core to destroyed prime-core mass of at least equal stratified weight, with a
strict surplus, and thereby produce the already-defined mutation rank descent
without assuming its endpoint comparison?

This ticket is a bridge-first test of the rotation/lattice representation.  It
is not another survey of invariants, a fit to successful mutation endpoints, or
an attempt to formalize the representation for its own sake.

## Exact destination bridge

The repository already defines `createdPrimeCores`, `destroyedPrimeCores`,
`StratifiedPrimeCoreRank`, `ThreeStepMutationRankDescendsAboveAt`, and the
consumer

```text
ThreeStepMutationRankDescendsAboveAt
  -> TargetFreeMutationNormalizesAboveAt
  -> TargetReflectingDecomposableNormalizationAt
  -> SweepExactUpperAt, given DecomposableExactUpperAt.
```

The first new mathematical arrow must therefore have the form

```text
recognizable source wall geometry
  -> canonical created-to-destroyed transport
  -> strict StratifiedPrimeCoreRank decrease.
```

An arbitrary matching, fractional flow, or inequality chosen after inspecting
the two endpoint prime-core families is merely a certificate for the desired
rank comparison.  It is admissible as a checker specification but not as the
missing producer.

## Frozen transport semantics

For a single-triple mutation from `chi` to `psi`, cancel all prime cores common
to both endpoints.  A transport certificate consists of one of the following,
listed from strongest to weakest.

1. A deterministic injection from `createdPrimeCores chi psi` into
   `destroyedPrimeCores chi psi`, with every created support mapped to a
   support of at least equal stratified weight and with either one unmatched
   destroyed support or one strict weight inequality.
2. A source-defined bipartite relation between created and destroyed supports
   whose Hall inequalities imply such an injection.
3. A source-defined integral transport of stratified mass with strictly more
   destroyed than created mass.

The local rule may use only:

- the changed triple and its signed rank-one circuit update;
- support membership, cardinality, intersection, union, and symmetric
  difference with that triple;
- the wall-side triangle-containment order;
- source chirotope signs and source decomposition data; and
- a fixed canonical tie-breaker independent of endpoint success.

It may not use:

- whether `psi` is decomposable;
- the truth of the final rank comparison;
- a shortest or preselected successful path;
- a lookup table indexed by the complete endpoint coloring;
- metric phase or angle data unless invariance across realizations of the same
  order type is proved; or
- a support, matching, or flow selected only because it succeeds.

For paths of length two or three, the transport must compose from the
individual wall rules.  A macro-level matching recomputed after seeing both
endpoints does not count as a wall producer.

## Why this is distinct from the expired shield

The existing endpoint and carrier-internal split shields prevent specified new
prime cores.  The top-apex card had zero abstract source coverage and failed a
mandatory premise-deletion discriminator.  The present proposal allows new
prime cores.  It seeks to charge them canonically to destroyed cores, possibly
at lower cardinality strata, so the stratified rank can fall without family
inclusion.

If every surviving rule reduces definitionally or extensionally to "no new
core at the highest changed stratum", this ticket returns
`TRANSPORT-OLD-SHIELD` and does not revive `FP-04`.

## Stage 0: mandatory adversarial review

Before authoring an evaluator, send the frozen ticket and exact interfaces to
the bounded Sol/Fable review.  The reviewers must answer:

1. Is any transport class strictly weaker than the desired rank comparison,
   or is it only a dual/certificate restatement?
2. What additional source-local restriction would make a canonical map a
   genuine producer rather than a chosen witness?
3. Does rank-one circuit or wall-side geometry plausibly supply that
   restriction?
4. Which smallest exact wall transition would falsify each class?
5. Should the route stop before computation?

The review is advisory.  Every material objection is checked locally before
the disposition changes.

## Stage 1: exact transition corpus

Reuse existing exact data only:

- the complete admitted Fin7 mutation controls;
- the selected exact-rational Fin8 mutation paths;
- exact N=8 rotation-circle wall crossings;
- only those N=9 rational crossings whose complete labels can be reconstructed
  within the default cap;
- the independent square, packet, collision, and codimension-two loop
  fixtures; and
- the endpoint-shield and top-apex failures as negative controls.

Two independently implemented builders must agree on the source/endpoint
chirotopes, changed triple, realizability and target-free labels,
decomposition-prime families, created/destroyed families, local circuit data,
and wall-side order.  No candidate result may be inspected before both ledgers
terminate.

## Stage 2: bounded candidate search

Freeze a typed grammar of deterministic support maps and relations before
execution.  A bounded genetic component may recombine only real typed
primitives from the frozen grammar.  It retains complete ancestry and uses no
undefined predicate, endpoint label, or final rank comparison as a feature.

Use lineage-separated training and held-out families.  Candidate disposition
is Pareto-based on exact coverage, held-out coverage, locality, simplicity,
loop consistency, and realization invariance.  Do not collapse those fields to
one quality score.

Every survivor receives premise deletion and corruption controls.  One exact
admitted falsifier kills that frozen candidate.  There is no post-outcome
feature addition, threshold tuning, rerun, or enlargement of N in this ticket.

## Outcomes

- `TRANSPORT-CIRCULAR`: the certificate or generator stores the desired rank
  comparison, successful endpoint, or an equivalent global matching.
- `TRANSPORT-OLD-SHIELD`: every surviving rule is the expired no-new-core
  source family in different notation.
- `TRANSPORT-FALSIFIED`: an exact admitted wall transition refutes the frozen
  local rule.
- `TRANSPORT-COVERAGE-FAIL`: local rules exist sporadically but cannot cover
  the frozen nondecomposable controls.
- `TRANSPORT-SURVIVES`: one source-local frozen rule survives all bounded
  controls.  This is search information only.
- `TRANSPORT-THEOREM-READY`: a survivor additionally has a symbolic
  Pluecker/circuit/Hall proof outline, a literal Lean producer statement, and a
  direct consumer into existing rank descent.  Lean remains separately gated.
- `TRANSPORT-CHECKER-MISMATCH`, `TRANSPORT-MODEL-GAP`, or
  `TRANSPORT-RESOURCE`: operational stop without mathematical inference.

Every branch stops this ticket.  Only `TRANSPORT-THEOREM-READY` permits a
separate proof-producing plan.

## Evidence and resource boundary

This is one information-gathering slot in the normalization-descent mechanism
family.

- Provider review: one bounded reciprocal Sol/Fable run.
- Computation: at most 30 minutes, 8 CPU cores, 16 GiB RAM, and 5 GiB under
  `runs/`.
- No software installation, destructive operation, process termination,
  commit, push, Lean, or Lake command is authorized.
- Durable edits are limited to this ticket and the terminal Wayfinder
  reconciliation.  Transient code and evidence remain under ignored `runs/`.

The user approved this plan on 2026-08-19.

## Proof-distance accounting

- **Net proof movement before execution:** neutral.
- **Evidence:** advisory review and bounded checked computation unless a later
  Lean ticket is separately approved.
- **Difficulty displaced:** none.  The complete source-side producer for
  `D-NORMALIZE` remains open.
- **Strict measure:** a future compiling theorem must eliminate or strictly
  reduce the producer obligation for
  `ThreeStepMutationRankDescendsAboveAt`; a local checker equivalence alone is
  neutral.
- **Counterfactual:** the run is useful only if it exposes a noncircular local
  producer or decisively rules out transport from the frozen wall data.
- **Planning consequence:** survival may gate one theorem-first ticket;
  circularity, old-shield equivalence, falsification, or coverage failure keeps
  `FP-04` suspended and retains the lattice framework only as an experimental
  substrate.
- **Load-bearing ledger:** no edge changes in this information-gathering
  ticket.

## Decision criteria

Admit a later proof-producing ticket only if a deterministic source-local rule
canonically names, for every potentially created core, a source-prime support
that the wall must destroy, with adequate stratified weight, an injective or
Hall consumer, and strict surplus.  The rule must be stated without endpoint
prime-core membership, final rank comparison, successful-path selection, or a
complete endpoint lookup, and it must have one independently motivated exact
positive example.  If no such rule can be frozen before computation, stop as
`TRANSPORT-CIRCULAR`; do not manufacture a grammar from successful endpoints.

## Resolution

Closed as `TRANSPORT-CIRCULAR` on 2026-08-19, before corpus construction or
candidate search.

The source audit does yield one exact local normal form.  If a support becomes
decomposition-prime after a single-triple mutation, prime-core locality forces
it to contain the changed triple.  It had a proper source split, and every such
split must put changed vertices on both sides: a split containing the whole
changed triple in one side would persist by
`HasDeepBelowSplit.persists_of_singleMutation_internal`, contradicting endpoint
primality.  Reversing the mutation gives the dual statement for a destroyed
support and its endpoint splits.

That normal form constrains each changed support separately but supplies no
correspondence between created and destroyed supports.  In particular, none of
support union, intersection, complement outside the changed triple, split-side
exchange, the wall-side containment order, or the rank-one circuit update
selects a source-prime support that the wall is forced to destroy.  Requiring a
chosen destination to belong to `destroyedPrimeCores` tests the endpoint
prime-core family and reconstructs the desired rank comparison.  An arbitrary
matching, Hall relation, or flow built that way is therefore a certificate for
rank descent rather than its source-side producer.

The bounded reciprocal review unanimously returned `not_supported` with high
confidence.  Its minimal missing fact is a source-local forced-neighbor lemma:
for each potentially created support, the wall data must canonically name a
source-prime destination of at least equal weight, prove that the wall destroys
it, prove injectivity or Hall expansion, and provide strict surplus.  The
review and the local derivation found no such rule.  With no independently
motivated typed grammar to freeze, the ticket's pre-computation stop applies.
No transition corpus, evaluator, genetic search, solver, Lean, or Lake command
ran.

The first provider attempt used the requested Fable 5 role but stopped at a
provider quota limit before reciprocal review.  The exact frozen packet was
then reviewed without mathematical changes using Claude Sonnet 4.6 in that
role and `gpt-5.6-sol`; all four initial and reciprocal outputs agreed.  This
fallback is advisory evidence only.

**Net proof movement:** neutral.  **Evidence:** compiling locality and split-
persistence infrastructure, an exact source-level derivation, and advisory
review; no new compiling theorem or checked candidate computation.
**Difficulty displaced:** none; the forced-neighbor producer and all of
`D-NORMALIZE` remain open.  **Counterfactual:** knowing this outcome earlier
would prevent spending a corpus/search/Lean block on endpoint-selected
transport, but it would not reduce the remaining destination proof.
**Planning consequence:** keep `FP-04` suspended, do not launch a generic
transport grammar, and retain lattice-wall data only as an experimental
representation.  Revival requires a genuinely new source-local forced-neighbor
theorem or rule with an independently motivated positive example.  No
load-bearing dependency changed.

## Evidence

- `ErdosSzekeres/DecompositionPrimeMutationLocality.lean`
- `ErdosSzekeres/DecompositionPrimeRootedCircuitPersistence.lean`
- `runs/reviews/20260819-lattice-wall-core-transport/question.md`
- `runs/reviews/20260819-lattice-wall-core-transport/sol-fable/manifest.json`
- `runs/reviews/20260819-lattice-wall-core-transport/sol-sonnet/REPORT.md`
- `runs/reviews/20260819-lattice-wall-core-transport/sol-sonnet/manifest.json`
- `runs/experiments/20260819-lattice-wall-core-transport/summary.md`
- `runs/experiments/20260819-lattice-wall-core-transport/result.json`
