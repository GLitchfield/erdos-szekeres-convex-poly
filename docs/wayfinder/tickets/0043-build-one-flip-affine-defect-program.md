---
title: Build the one-flip affine defect research program
type: research
mode: HITL
status: closed
claim: codex-one-flip-affine-defect-program-2026-08-19
blocked_by: none
---

# Ticket 0043: build the one-flip affine defect research program

## Question

Can the checked deletion-minimal, distance-one affine defect family be turned
into a noncircular geometric mechanism for constructing predecessor
bicolorings, or can a prospective held-out family sharply delimit that idea?

This is an exploration program around the suspended `FP-07.A` child.  It is
not a claim that affine topes work, and it is not a relabeling of the false
affine producer.  The only possible route back to `D-HALF` is a genuinely
non-affine source theorem with a direct consumer into the already compiling
predecessor recurrence.

## Checked starting point

Ticket 0042 independently checks the following on one exact witness, twelve
bad target-free wall neighbors, and 64 bounded adversarial descendants.

- The witness has 156 nontrivial affine topes, minimum defect one, six
  minimum-defect topes, blocker number five, nine minimum blocker covers, and
  Hamming distance one from unrestricted predecessor bicolorings.
- Every one-point deletion has a valid affine tope.
- Of thirteen target-free one-wall neighbors, twelve remain affine failures;
  the sole escape flips triple `{0,7,9}` and creates two valid topes.
- The 77 bad chirotopes have 73 recorded structural signatures.  All 77 are
  deletion-minimal and distance one from an unrestricted valid bicoloring;
  76 have defect one and one has defect two.

These are checked finite facts and search information.  The current corpus is
not a valid train/test split: later mutations may descend from earlier parents,
and the last mutation label does not establish genealogical independence.

## Core mathematical objects

For a realizable uniform rank-three oriented matroid `M` on `P`, let `H(P)` be
the hypergraph of convex predecessor subsets, `T(M)` the nontrivial affine
topes, and `B(H)` the unrestricted predecessor bicolorings.  For a sign vector
`t`, let `flip(t,v)` reverse coordinate `v`.

Define the repair incidence relation

```text
R(P) = {(t,v) : t in T(M) and flip(t,v) in B(H(P))}.
```

The first candidate model is

```text
OneFlipAffine(P) : B(H(P)) intersects the Hamming-one neighborhood of T(M).
```

This is strictly weaker than the refuted affine-tope producer and strictly
stronger than unrestricted Property B.  A sign vector one bit outside `T(M)`
is a virtual chamber of the dual line arrangement.  Exact infeasibility of
that virtual chamber has a signed-circuit/Farkas certificate supported on at
most four homogeneous point vectors.  Deletion minimality supplies a second
description through valid topes of `M \ v` and their two sign extensions.

## Scientific hypotheses

The program separates these hypotheses; survival of one does not rescue the
others.

1. **H-distance:** every target-free realizable configuration in the tested
   scope satisfies `OneFlipAffine`.
2. **H-minimum:** some minimum-defect tope participates in `R(P)`.
3. **H-circuit:** a source-selected signed Radon circuit of a virtual chamber
   identifies a repair coordinate without testing the repaired coloring.
4. **H-deletion:** a valid tope of a deletion and its extension obstruction
   identify a repair pair `(t,v)`.
5. **H-blocker:** common minimum-cover structure restricts repair candidates to
   a relabeling-equivariant bounded set.
6. **H-wall:** repair incidence transports across bad-to-bad mutations and
   changes by a controlled local rule at an escape wall.
7. **H-bounded-set:** even if no canonical single repair exists, source data
   produces a bounded set all of whose members are safe, or one of which is
   safe for an independently proved reason.

`H-distance` alone is an existence reformulation, not a producer.  A fitted
classifier, a rule that evaluates `flip(t,v) in B(H)`, or a premise asserting
that one candidate works is target-equivalent and cannot become a theorem
card.

## Question inventory

### Repair incidence and symmetries

1. How many affine topes are repairable, and how many safe coordinates does
   each have?
2. Are all repairable topes minimum-defect topes?  Are all minimum-defect
   topes repairable?
3. When defect is one, must a safe coordinate lie in the unique monochromatic
   predecessor edge?
4. Which flips create a new monochromatic edge of the opposite color?
5. Is repair incidence antipodally symmetric exactly, and what remains after
   quotienting by color complement?
6. What are the automorphism orbits of repair pairs?  Does symmetry obstruct a
   unique equivariant selector?
7. Can a set-valued selector be equivariant with uniformly bounded size when a
   single-valued selector cannot?

### Deletion and single-element extension

8. Does every valid deletion tope lift to an affine tope, a safe virtual
   chamber, both, or neither?
9. For which vertices does a valid deletion tope have exactly one feasible
   sign extension?
10. Can the infeasible sign extension be certified by one circuit containing
    the deleted vertex?
11. Is every bad type minimal under deletion only, or also under oriented-
    matroid contraction or other natural minors?
12. Can all bad single-element extensions of a fixed good deletion be
    described by cells in the extension arrangement?
13. Does the blocker core arise only after reinsertion, and which edge appears
    first?

### Radon, Farkas, and projective structure

14. What are the support sizes and `3+1` versus `2+2` Radon types of minimal
    infeasibility certificates for safe virtual chambers?
15. Is the flipped coordinate present in every minimal certificate, or in a
    canonical intersection of them?
16. Do certificate signs distinguish safe virtual chambers from arbitrary
    infeasible sign vectors without consulting predecessor validity?
17. Is there a Gale-dual or projective description of the unique target-free
    escape wall `{0,7,9}`?
18. Does allowing one negatively oriented homogeneous lift give a natural
    oriented-matroid class with a useful elimination theorem?

### Tope graph and discrete potential

19. Are low-defect sublevel sets connected, gated, convex, or dismantlable in
    the tope partial cube?
20. Are the six defect-one topes of the witness isolated local minima, and is
    that pattern stable across the family?
21. Can defect be decomposed along Djokic--Winkler theta classes or a discrete
    Morse matching?
22. Is every distance-one valid bicoloring adjacent to a nonfacet coordinate
    of its source tope, and what circuit blocks that missing chamber?
23. Is the blocker number bounded on the whole distance-one family, or is the
    observed `5/6` split accidental?

### Wall and family geometry

24. Is the bad locus connected in the realizable mutation graph?
25. Which repair pairs persist across a bad-to-bad wall?
26. At an escape wall, is a valid tope born, a blocker edge destroyed, or both?
27. Do the twelve bad wall directions form a local cone or fan with a concise
    chirotope description?
28. Are the 73 structural signatures genuinely distinct after quotienting by
    relabeling and projective equivalence?

### Scope and consumers

29. Does `OneFlipAffine` survive a prospectively generated bad family with no
    ancestry from the 77 discovery types?
30. What is the first exact configuration with Hamming distance at least two,
    if one exists?
31. Is a `q`-flip statement meaningful uniformly in the polygon parameter, or
    does `q` necessarily grow?
32. Can a bounded repair set feed the compiling predecessor recurrence without
    hiding the desired bicoloring in a choice premise?
33. Which finite statement would be a required base case of a declared
    induction rather than another certificate-only closure?

## Stage 0: mandatory adversarial route review

The predecessor-half family has more than three consecutive information-only
or negative outcomes.  Before any new evaluator is authored, run one bounded
Sol/Fable review of this ticket, ticket 0042's exact result, the current
portfolio entry, and the relevant project interfaces.  The review must decide:

1. whether `OneFlipAffine` is a genuinely new intermediate or merely Property
   B with a witness encoded;
2. which of H-circuit, H-deletion, H-blocker, and H-wall has a noncircular
   source statement;
3. which primary-source oriented-matroid, arrangement, Farkas/Radon,
   critical-hypergraph, or threshold-function tools apply literally;
4. what prospective held-out generator is independent enough to discriminate;
5. whether any proposed consumer strictly reduces a named obligation; and
6. which branches should stop before computation.

Review rejection suspends the program without spawning a refined descendant.

### Stage-0 outcome

The bounded reciprocal review was attempted on the frozen question SHA-256
`6f57387c2d06b36b6f5da35a56a381bc420015d2770713e89cad300187d0116f`
and evidence-packet SHA-256
`5575519c8751bb8ea51a4bdf1854794f1cb4b056d0f1b0a0b4aff66a07740ce4`.
Claude Fable returned HTTP 429 before consuming any input tokens because its
usage limit was exhausted, so there is no reciprocal review or Sol/Fable
consensus.  The blind Codex Sol answer (SHA-256
`7fbfb092027a7b60fad193a72ea5b18003314316dc9b2d5fc8298da788d1c79c`)
returned `not_supported` with high confidence.

Sol's decisive objections survive independent source checking.

- `OneFlipAffine` is a genuine logical restriction on Property B, but no
  source construction chooses the affine tope and repaired coordinate.
- Signed circuits literally certify nonrealizability of a sign vector, but no
  cited circuit theorem implies that the repaired sign vector avoids every
  predecessor edge.  The rank-three support bound is not the missing bridge.
- A tope graph is literally a partial cube, but no cited result makes the
  predecessor-defect sublevel set convex, gated, or repair-selecting.
- Reinsertion over deletion minors already exposed by the discovery family is
  a fiber test, not a genealogy-independent heldout test.  A credible split
  must reserve whole deletion-minor equivalence classes and all descendants.
- A canonical selector first needs an automorphism fixed point in the safe
  repair relation; a bounded set-valued selector needs a uniformly bounded
  invariant union of safe orbits.  Neither condition was checked.

Because the predeclared gate required a positive noncircular source primitive,
one blocking review plus the absent Fable judgment is insufficient to proceed.
F1--F4 did not run.  The possible automorphism-orbit preflight is recorded as
the cheapest future discriminator, not spawned as a descendant.

## Work package F1: exact repair-incidence atlas

On the 77 discovery types, compute and independently check:

- all repair pairs, complement quotients, automorphism orbits, and safe-set
  cardinalities;
- unique bad edges, opposite-color creation risks, and their descriptive
  relation to safe flips;
- deletion-tope extension matrices;
- every minimal signed circuit/Farkas certificate for virtual repairs;
- repair persistence across the twelve bad and one good target-free wall
  directions; and
- tope-graph low-defect sublevels, local minima, and theta-class summaries.

The descriptive atlas may use outcome labels.  Candidate-rule features are
recorded separately and must declare whether they are available before testing
`flip(t,v)`.

Possible F1 outcomes are `REPAIR-ATLAS-CHECKED`, `REPAIR-ATLAS-MISMATCH`,
`REPAIR-ATLAS-MODEL-GAP`, or `REPAIR-ATLAS-RESOURCE`.

## Work package F2: prospective held-out family

The current mutation labels are not independent genealogies.  Freeze a new
generator before candidate rules are selected.  Its preferred mechanism is a
single-element-extension walk: start from the thirteen good deletion minors,
reinsert a point through exact cells of the line arrangement of each minor,
and retain target-free affine failures.  The generator must not descend from
the 77 bad realizations except through the disclosed deletion minor, and its
random seeds or deterministic cell schedule are committed before execution.

The held-out configurations, repair labels, and summary counts stay sealed
until F3 rules are frozen.  A second implementation checks general position,
target avoidance, chirotope identity, affine failure, and provenance.  If an
exhaustive cell enumeration is not practical, the scope must say precisely
which cell walk was sampled; it may not claim all single-element extensions.

Possible F2 outcomes are `HELDOUT-BAD-FAMILY-READY`, `HELDOUT-NO-SIGNAL`,
`HELDOUT-PROVENANCE-FAIL`, `HELDOUT-CHECKER-MISMATCH`, or
`HELDOUT-RESOURCE`.

## Work package F3: source-only candidate grammar

Construct a small, explicit, relabeling-equivariant grammar of rules for
choosing one pair `(t,v)` or a bounded candidate set.  Rule primitives may use
the chirotope, affine-tope graph, convex-predecessor hypergraph, point/deletion
incidence, blocker structure, and signed circuits.  They may not test whether
the proposed flip is valid, use a successful bicoloring as a stored witness,
or rank rules on held-out outcomes.

Every rule receives:

- a normalized symbolic description;
- its exact invariance and tie-breaking behavior;
- a source/consumer ledger;
- the cheapest discovery-corpus falsifier;
- an automorphism audit;
- a target-equivalence audit; and
- a theorem-shaped statement identifying the missing proof.

Rules are selected by Pareto criteria across discovery strata, not by one
aggregate score.  At most three rules cross the blind boundary.  No post-
heldout repair or backfill is allowed.

Possible F3 outcomes are `NO-NONCIRCULAR-RULE`, `RULES-FROZEN`,
`SYMMETRY-OBSTRUCTION`, or `TARGET-EQUIVALENT`.

## Work package F4: blind held-out test and theorem extraction

Apply the frozen F3 rules once to the sealed F2 family.  Report per-rule and
per-stratum failures, not only aggregate accuracy.  First test H-distance
itself; a held-out bad type with `rho >= 2` falsifies the one-flip model even if
a selector happens to work elsewhere.

Possible terminal outcomes are:

- `ONE-FLIP-FALSIFIED`;
- `SELECTOR-FALSIFIED`;
- `SET-VALUED-SURVIVES`;
- `ONE-FLIP-SURVIVES-HELDOUT`;
- `ONE-FLIP-THEOREM-READY`; or
- `BLIND-CHECKER-MISMATCH`, `BLIND-MODEL-GAP`, or `BLIND-RESOURCE`.

Finite survival is search information.  `ONE-FLIP-THEOREM-READY` additionally
requires a literal symbolic statement, a noncircular producer outline, a
direct project consumer, and a strict before/after proof-obligation ledger.
Lean work needs a separate approved ticket.

## Execution slate and concentration

The proposed program has zero proof-producing and four information-gathering
work packages.  All belong to the predecessor-half mechanism family and their
failures are correlated.  This exceeds the default family concentration only
because the user explicitly requested a focused scientific program around the
newly checked defect family; it is exploration, not a claim of four independent
proof routes.  The packages are sequentially gated: F1 and sealed F2 may run
after Stage 0, F3 requires F1, and F4 requires frozen F2 and F3.

## Resources and approvals

The full block is forecast at four to seven hours.  Each exact producer or
checker is capped at 1,800 seconds, eight CPU cores, 16 GiB RAM, and 2 GiB
output; aggregate stored output is at most 5 GiB.  The route review uses the
already authorized exact prefix `python3 scripts/adversarial_review.py run`.
Primary-source web access is read-only.

No software installation, destructive action, process termination, external
repository mutation, commit, push, Lean, or Lake is included.  Any need for a
larger cap, new dependency, or formal proof pauses only that branch for fresh
approval.  Parallel agents may be used only if the user explicitly approves
this slate including delegation; their write sets must be disjoint and root
must serialize integration.

## Proof-distance accounting

- **Net proof movement before execution:** neutral.
- **Evidence:** prospective review and checked computation.
- **Difficulty displaced:** none.  The missing uniform non-affine producer is
  not smaller merely because finite repairs exist.
- **Strict measure:** only a compiling source-selected one-flip or bounded-set
  theorem that directly feeds `PredecessorHalfSubsetAt` can decrease the open
  `D-HALF` obligation.  Finite atlas size, prediction rate, and held-out
  survival do not.
- **Counterfactual:** the program is valuable if it falsifies one-flip on a
  prospectively independent family or isolates a literal circuit/deletion
  theorem.  Merely explaining the 77 examples is search information.
- **Planning consequence:** a theorem-ready survivor may request a separate
  proof ticket; otherwise retain or suspend the family according to the
  predeclared streak rules.
- **Load-bearing ledger:** no edge changes during this exploration program.

## Decision criteria

Proceed beyond Stage 0 only if reviewers identify at least one noncircular
source primitive and approve the held-out design.  Proceed from F1/F2 to F3
only with independently checked semantics and sealed heldout labels.  Proceed
to F4 with at most three source-only rules frozen before unsealing.  Never call
finite survival proof progress, never train on the held-out genealogy, and
never repair a failed rule after its blind outcome.

## Resolution

Stopped at Stage 0.  No full Sol/Fable consensus exists because Fable exhausted
its usage limit, while the available blind Sol review rejects continuation on
the exact source/consumer criterion.  Keep `FP-07.A` suspended.  Do not run the
atlas, heldout generator, selector grammar, blind test, or Lean work.  Reopen
only with new positive source evidence connecting a circuit, deletion, wall,
or invariant repair set to predecessor validity; provider availability alone
does not supply that bridge.

## Evidence

- `docs/wayfinder/tickets/0037-test-affine-tope-predecessor-funnel.md`
- `docs/wayfinder/tickets/0038-autopsy-unrestricted-predecessor-core.md`
- `docs/wayfinder/tickets/0039-audit-weighted-predecessor-polytope.md`
- `docs/wayfinder/tickets/0041-test-arithmetic-walls-and-affine-obstructions.md`
- `docs/wayfinder/tickets/0042-retry-affine-obstruction-morphology.md`
- `runs/experiments/20260819-arithmetic-affine-microscope/affine-v2/result.json`
- `runs/experiments/20260819-arithmetic-affine-microscope/affine-v2/summary.md`
- `runs/reviews/20260819-one-flip-defect/provider/manifest.json`
- `runs/reviews/20260819-one-flip-defect/provider/evidence-packet.txt`
- `runs/reviews/20260819-one-flip-defect/provider/codex.initial.json`
- `runs/reviews/20260819-one-flip-defect/provider/raw/claude.initial.stdout`
- `docs/wayfinder/frontier-portfolio.md`
