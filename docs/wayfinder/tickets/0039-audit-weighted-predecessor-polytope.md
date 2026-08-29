---
title: Audit the weighted predecessor support polytope
type: research
mode: HITL
status: closed
claim: codex-weighted-predecessor-polytope-2026-08-19
blocked_by: none
---

# Ticket 0039: audit the weighted predecessor support polytope

## Question

Can an independently sourced orientation-sensitive weighted inequality place
the half vector in the predecessor-free support polytope for every target-free
sweep-realizable coloring, without assuming or selecting the desired support?

This is a source-first audit of the weaker `FP-08` route.  It is not an
attempt to fit the 381 complementary bicolorings found by ticket 0038.

## Exact object

For one finite predecessor hypergraph `H` on vertex set `V`, let `F(H)` be its
hereditary family of predecessor-free vertex subsets and define

`I(H) = conv {1_S : S in F(H)} subset [0,1]^V`.

Three finite statements must be kept distinct until their implications are
proved:

1. `H` has an integral predecessor bicoloring: both `S` and `V \ S` lie in
   `F(H)` for one `S`.
2. The half vector lies in `I(H)`, equivalently there is a distribution over
   predecessor-free supports with every vertex marginal at least one half.
3. Every normalized nonnegative vertex weighting gives at least half of its
   mass to some predecessor-free support.

The project already compiles the easy implications from
`FractionalPredecessorCoverAt` through `PredecessorHalfMassAt` and
`PredecessorHalfSubsetAt` to the exact recurrence.  Reproving finite
LP duality or the convex-hull equivalence is specification infrastructure,
not a producer and not proof movement.

## Strategic gate

The predecessor-half mechanism family has repeated negative and
information-only descendants.  Before selecting a theorem card, run the
bounded Sol/Fable review under
`runs/reviews/20260819-weighted-predecessor-polytope/`.  The review must reject
any proposal that:

- assumes the half vector, a successful support, or a separating inequality
  equivalent to the desired conclusion;
- selects or scores supports using their final predecessor-free status;
- is merely generic LP duality, fractional coloring terminology, or a
  restatement of `PredecessorHalfMassAt`;
- fits only the stored affine witness or the existing small corpus; or
- imports a theorem at the wrong model tier without a proved bridge to exact
  sweep-realizable predecessor hypergraphs.

If the review rejects the mechanism as target-equivalent, close this ticket
without computation or Lean work.

## Source-first machinery audit

Search primary literature and official source records in the following
families, without presuming that any applies:

- weighted independence and fractional coloring of geometric hypergraphs;
- discrepancy or property-B criteria with orientation-sensitive hypotheses;
- convexity-space, fractional-Helly, or transversal inequalities;
- stable-set-polytope inequalities produced by order type or oriented-matroid
  structure; and
- wall-crossing or mutation statements that preserve a weighted support
  inequality rather than an already chosen support.

For every candidate record the exact source theorem, hypotheses, model tier,
project translation, missing bridge, and cheapest falsifier.  A source is not
a card merely because its terminology resembles the project definitions.

## Candidate admission

At most three theorem cards may reach computation.  Each must have:

1. a literal weighted inequality or structural premise stated independently
   of successful supports;
2. a proposed source from sweep realizability plus target avoidance;
3. a direct finite consumer into `FractionalPredecessorCoverAt` or
   `PredecessorHalfMassAt`;
4. a deletion test for every load-bearing premise; and
5. a reason it should fail on at least one relaxed obstruction while remaining
   plausible on exact geometry.

Cards lacking an independent producer are `PRODUCER-GAP`, not candidates.

## Bounded controls

Only cards surviving source and anti-circularity review may be evaluated on:

- complete exact target-free eight- and nine-point corpora already frozen in
  the repository run ledger;
- ticket 0037's exact 13-point affine falsifier, which ticket 0038 proves has
  abundant unrestricted solutions;
- the existing relaxed complete-uniform fractional obstruction;
- held-out exact rational controls selected before evaluator outcomes; and
- premise-deletion and target-equivalent fake-card corruptions.

Two implementations must agree on the exact predicate.  Default aggregate
cap: 30 minutes, 8 CPU cores, 16 GiB RAM, and 5 GiB under `runs/`.  No
post-outcome card repair or rerun is allowed.

## Outcomes

- `WEIGHTED-CARD-SURVIVES`: one independently sourced card passes every frozen
  semantic and corruption gate.  This is search information only; freeze a
  separate Lean theorem contract before proof work.
- `WEIGHTED-CARD-FALSIFIED`: an exact admitted control violates the card.
- `WEIGHTED-PRODUCER-GAP`: every plausible inequality lacks an independent
  source from the project hypotheses.
- `WEIGHTED-TARGET-EQUIVALENT`: every candidate assumes, selects, or merely
  separates the desired half support.
- `WEIGHTED-SOURCE-NONE`: no primary-source theorem translates to the exact
  model with a credible missing bridge.
- `WEIGHTED-CHECKER-MISMATCH`, `WEIGHTED-MODEL-GAP`, or `WEIGHTED-RESOURCE`:
  operational stop without mathematical inference.

Every branch stops this ticket.  No algebraic fitting, higher-dimensional
lift, mutation propagation, or Lean implementation is automatically
authorized by survival.

## Proof-distance accounting

- **Execution slate:** zero proof-producing slots; one information-gathering
  mechanism-family slot with source and optional computation stages.
- **Net proof movement before execution:** neutral.
- **Evidence:** advisory review, primary-source audit, and optionally checked
  finite computation.
- **Difficulty displaced:** none unless a later compiling theorem proves an
  independently produced weighted inequality.
- **Counterfactual:** the ticket is useful only if it identifies one
  noncircular producer worth proving or retires the weighted family; finite
  survival alone does not reduce the destination proof.
- **Planning consequence:** survival permits a separate theorem-first ticket;
  producer gap, target equivalence, or source absence suspends further
  predecessor-polytope refinements and redirects execution to `D-DECOMP`.
- **Load-bearing ledger:** no edge changes in this ticket.

## Approval and resource boundary

The user approved this plan on 2026-08-19.  The block authorizes the bounded
provider review, primary-source web research, packet-owned prose and exact
control artifacts, and one terminal Wayfinder reconciliation.  It authorizes
no Lean/Lake command, software installation, resource escalation, destructive
action, commit, push, or external mutation.

## Decision criteria

Admit a later proof ticket only for a literal orientation-sensitive weighted
inequality with an independent source from sweep realizability and target
avoidance, an exact consumer into the existing fractional route, and a frozen
control that distinguishes its load-bearing hypotheses from a relaxed
obstruction.  Equivalent polytope, LP, polymatroid, range, or intersection
encodings are not sufficient.  If no such source theorem survives, close this
ticket without computation and suspend further mechanism-family refinements.

## Resolution

Closed as `WEIGHTED-SOURCE-NONE` on 2026-08-19.  The exact finite audit shows
that fractional-cover weight at most two, membership of the half vector in the
hereditary predecessor-free support polytope, and the weighted half-mass
condition are equivalent presentations of the existing `FP-08` obligation.
This is useful specification infrastructure but no new producer.

Seven primary-source machinery families were screened.  Fractional-coloring
and polymatroid sources validate equivalent encodings; range-hypergraph,
tuple-coloring, fractional-Helly, positive-fraction, and mutation sources all
lack a bridge from exact sweep realizability and target avoidance to the
weighted conclusion.  Zero theorem cards therefore qualified for computation.
No exact corpus, relaxed obstruction, solver, Lean, or Lake command ran.

The provider review packet was frozen, but Claude's expired OAuth session
stopped the harness before either advisory answer.  This is operational only;
no review consensus is claimed and no rerun occurred.

**Net proof movement:** neutral.  **Evidence:** exact finite reasoning and a
bounded primary-source audit.  **Difficulty displaced:** none; the
orientation-sensitive producer remains the entire open `FP-08` obligation.
**Counterfactual:** the result avoids spending computation or formalization on
equivalent algebraic encodings but does not shorten the destination proof.
**Planning consequence:** suspend `FP-07` and `FP-08` with the rest of the
predecessor-half mechanism family until a genuinely new positive source
theorem appears; redirect the next route selection to `D-DECOMP`.  No
load-bearing dependency changed.

## Evidence

- `ErdosSzekeres/StrongPredecessorBicoloring.lean`
- `ErdosSzekeres/StrongPredecessorFractionalDual.lean`
- `docs/wayfinder/tickets/0032-select-post-hmpt-exact-route.md`
- `docs/wayfinder/tickets/0038-autopsy-unrestricted-predecessor-core.md`
- `runs/experiments/20260819-unrestricted-predecessor-core/result.json`
- `docs/wayfinder/frontier-portfolio.md`
- `runs/experiments/20260819-weighted-predecessor-polytope/equivalence-note.md`
- `runs/experiments/20260819-weighted-predecessor-polytope/source-ledger.md`
- `runs/experiments/20260819-weighted-predecessor-polytope/summary.md`
- `runs/experiments/20260819-weighted-predecessor-polytope/result.json`
- `runs/reviews/20260819-weighted-predecessor-polytope/sol-fable/manifest.json`
