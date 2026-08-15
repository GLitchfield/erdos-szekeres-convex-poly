---
title: Organize quantitative upper-bound and exact-six intermediaries
type: research
mode: AFK
status: closed
claim: codex-upper-bound-intermediaries-2026-08-14
blocked_by: none
---

## Question

Should the portfolio add two separate main entries for (1) a known strict
uniform quantitative improvement over the classical binomial upper bound and
(2) the exact unrestricted Lean theorem `ES(6)=17`, or should either goal remain
a child of an existing route?

The proposed organization is:

1. `FP-15 — Uniform quantitative upper-bound ladder`, mechanism family
   `quantitative-cup-cap`, closing a supporting quantitative edge `Q-UPPER`
   while explicitly leaving exact `D-UPPER` open; and
2. `FP-16 — Exact unrestricted ES(6)=17`, mechanism family
   `finite-exact-upper`, closing only the fixed-instance subordinate edge
   `D-UPPER(6)`.

## Decision criteria

- Portfolio structure must reflect mathematical mechanism and failure
  correlation rather than agent, file, or certificate boundaries.
- A new main entry needs a credible contribution path, exact scope ceiling,
  named consumer, bounded discriminating gate, and expiry rule.
- Do not fold the quantitative route into `FP-01` unless its published
  endpoint/good-point mechanism actually produces or strictly reduces
  `PredecessorHalfSubsetAt`; superficial similarity to pair-rank profiles is
  insufficient.
- Do not place the exact-six theorem under `FP-14`: certificate tooling may be
  supplied there, but the theorem and mathematical evidence require a
  mathematical owner.
- `Q-UPPER` and `D-UPPER(6)` are supporting milestones, not substitutes for
  the universal exact edge `D-UPPER`; their closure must not promote an exact
  route without a proved implication.
- The quantitative route's first gate must authenticate the exact published
  statement and dependency graph before freezing a Lean theorem.  The first
  proof-producing gate should be a parameterized endpoint/good-point lemma
  with a falsifier against existing rank-profile controls.
- The exact-six route succeeds only when the unrestricted public theorem
  `erdosSzekeresFormulaAt_six : ErdosSzekeresFormulaAt 6` compiles through an
  explicit geometric abstraction bridge.  Certificate compression without
  that theorem or a frozen semantic-extraction hypothesis is stopped.
- A speculative attempt to beat the published state of the art remains a card
  under `FP-13` until it has an exact theorem contract, mechanism, consumer,
  and falsifier.
- Evaluate whether adding two main entries improves strategic clarity enough
  to justify expanding the registry, or whether one should begin as a stable
  child with an explicit graduation gate.

## Candidate outcomes

1. Add both `FP-15` and `FP-16` as separate gated main entries with distinct
   mechanism families and supporting milestones.
2. Add the quantitative route as a main entry but retain exact six as a stable
   child or bounded execution milestone, with a precise graduation rule.
3. Keep one or both proposals under `FP-13` until a source audit or theorem
   contract passes, then reconsider promotion.
4. Reject a proposal because its likely machinery is too disconnected from the
   exact destination or duplicates an existing entry.

## Resolution

Accept Outcome 1 with scope and admission revisions.  Add `FP-15` and `FP-16`
as separate gated main entries because each has a destination-relevant public
endpoint, a distinct mathematical failure mode, a bounded first gate, and a
hard expiry rule.  This is an inclusive-registry decision, not a claim that the
two entries are new independent proofs of the conjecture.

The review packet SHA-256 is
`8960f91b4c8edab8cfe0cf8cb46b744bf09425eccf0f0f0ac315ce912fe353d8`.
Sol returned `partially_supported` with high confidence and an explicit
`ACCEPT-WITH-REVISIONS`; its result SHA-256 is
`312946f34356744bca0aed914ea559fca5dffed7ca298d8a21d5474316bb857d`.
Fable returned HTTP 429 with zero tokens because its Fable 5 quota was
exhausted; the recorded envelope SHA-256 is
`aa3c5a1552c4665344c8eef1d77aeb3f80cfb0f0064cf95506b956f94385c80f`.
There is therefore no two-reviewer consensus, and Sol's agreement is not the
basis for this resolution.

The material concerns are disposed as follows:

1. Add `Q-UPPER` and `D-UPPER(6)` to a separate supporting-milestone table,
   outside the load-bearing dependency ledger.  Closing either changes no
   status on universal `D-UPPER` without a separately proved implication.
2. Keep `FP-15` information-gated.  Its first task is a primary-source audit of
   the exact theorem, constants, parameter range, and proof dependencies.  No
   Lean contract is admitted from the present approximate survey summary.
3. Keep `FP-15` separate from `FP-01` and `FP-03` only while the authenticated
   good-point/endpoint mechanism remains distinct.  If its principal lemma
   proves or assumes an existing producer, merge it rather than manufacturing
   route breadth.
4. Give `FP-16` mathematical ownership of the unrestricted public theorem;
   `FP-14` may supply certificate tooling but cannot own or claim the result.
   Its first task is a predicate- and clause-level Isabelle-to-repository
   semantic correspondence audit, not a solver run.
5. After exact six compiles, stop fixed-case certificate engineering unless a
   single frozen parameterized extraction hypothesis has a named consumer
   beyond `k=6` and an adjacent-parameter falsifier.

These restrictions make the two entries honest scoped intermediaries.  They
do not alter the assessment that every load-bearing unrestricted upper-bound
edge remains open.

### Exact-six source follow-up

The official `HappyEnding.zip` was retrieved and exactly audited on
2026-08-15.  The safe archive contains two Isabelle theories and one formula
generator, but no license, session root, generated `6/17` formula, proof
artifact, or final six-point theorem; its checked declarations stop at cases
through five.  This is an operational source stop, not evidence against
`ES(6)=17`.  `FP-16` is therefore suspended rather than repeatedly refined.
It revives only from a complete licensed formal distribution or a separately
reviewed independent finite-proof packet.  `D-UPPER(6)` remains gated and no
load-bearing universal edge changed.

## Evidence

- `docs/wayfinder/proof-distance-assessment-2026-08-14.md`
- `docs/wayfinder/map.md`
- `docs/wayfinder/frontier-portfolio.md`
- `docs/literature_review.md`
- `docs/bibliography.md`
- `runs/literature/20260813-combinatorics-ramsey/notes/deep_reading_notes.md`
- `ErdosSzekeres/CupCap.lean`
- `ErdosSzekeres/ES5Certificate.lean`
- `ErdosSzekeres/E3FiniteReduction.lean`
- `runs/reviews/20260814-upper-bound-intermediaries-review/evidence-packet.txt`
- `runs/reviews/20260814-upper-bound-intermediaries-review/codex.initial.json`
- `runs/reviews/20260814-upper-bound-intermediaries-review/raw/claude.initial.stdout`
