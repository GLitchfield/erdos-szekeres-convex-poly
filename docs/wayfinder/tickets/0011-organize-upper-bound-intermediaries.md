---
title: Organize quantitative upper-bound and exact-six intermediaries
type: research
mode: AFK
status: open
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

Open pending the bounded Sol/Fable review and independent disposition of its
material objections.

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
