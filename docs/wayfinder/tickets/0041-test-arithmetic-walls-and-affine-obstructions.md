---
title: Test arithmetic wall invariants and affine obstruction morphology
type: research
mode: HITL
status: closed
claim: codex-arithmetic-wall-affine-obstruction-2026-08-19
blocked_by: none
---

# Ticket 0041: test arithmetic wall invariants and affine obstruction morphology

## Question

Can either of two deliberately separate representation studies expose a new
theorem-bearing mechanism before the project returns to `D-DECOMP`?

1. Does modular, automorphic, signed-tropical, or cluster/Grassmannian
   machinery supply a canonical wall invariant or cocycle that survives the
   realization fiber and has more content than conservation?
2. What exact structure makes the thirteen-point affine-tope witness block
   every affine predecessor cut while retaining hundreds of unrestricted
   predecessor bicolorings?

This is an exploration slate with zero proof-producing and two
information-gathering slots.  The arithmetic-wall and affine-obstruction
tracks are separate mechanism families.  Neither finite survival nor a fitted
representation changes a load-bearing dependency.

## Prior evidence and negative knowledge

The rotation/lattice atlas already proves or checks the following at proposal
or finite-computation level.

- A planar affine realization is faithfully represented by its centered row
  plane, or homogeneously by a point of `Gr(3,N)`, and its triple orientations
  are signs of Pluecker coordinates.
- Rational realizations exist in every uniform realizable order-type stratum,
  while a generic realization of the same order type lies in no proper
  rational subspace.  Arithmetic data of a selected lattice lift are therefore
  not automatically order-type invariants.
- Ordinary cluster combinatorics and ordinary tropical Pluecker valuations
  lose the sign chamber.  A wall `p_T=0` leaves the cluster torus and is not an
  ordinary cluster mutation.
- Ordinary Tutte, characteristic, Orlik--Solomon, and Chow invariants see only
  the uniform underlying matroid and are constant here.
- Additive Cordovil wall changes telescope around square and four-packet loops.
  No canonical multiplicative transport or nonlinear holonomy exists.
- Ticket 0040 found no source-local created-to-destroyed core transport.

The affine witness has exact coordinates

```text
(0,2), (1,-486), (2,7), (3,9), (4,-51), (5,-24), (6,35),
(7,36), (8,126), (9,42), (10,44), (11,82), (12,422).
```

It is in general position, has no convex six-set, has no valid affine
predecessor half-support, and has no two-sided predecessor-free affine cut.
Independent exact computation nevertheless finds 381 unrestricted bicoloring
pairs and 506 predecessor-free seven-subsets.  Five convex pentagons cover all
156 oriented nontrivial affine cut cells.  A root-side exploratory read of the
frozen ledgers suggests minimum affine defect one and minimum distance one to
the unrestricted solution set; those two derived metrics are not admitted
until independently replayed in this ticket.

## Stage 0: mandatory reciprocal review

Before authoring an evaluator, send this frozen ticket and the relevant atlas,
affine, and unrestricted-core evidence to one bounded reciprocal review.  The
reviewers must answer:

1. Which arithmetic-wall candidates remain genuinely untested after the
   atlas, and which are already ruled out by realization-fiber variation,
   sign loss, trivial valuation, or conservation?
2. Is there a literal primary-source theorem that supplies a divisor,
   character, cocycle, positivity statement, or cluster/tropical wall
   identity at the correct model tier?
3. Which affine morphology quantities are non-tautological and could
   distinguish a mechanism rather than redescribe failed cuts?
4. Is low polynomial-threshold degree strategically meaningful, or only a
   fitted encoding of a known successful bicoloring?
5. What minimum bad-order-type coverage is needed before any repair rule may
   be proposed?
6. Should either track stop before computation?

Fable 5 is currently quota-blocked.  The exact packet may use Claude Sonnet
4.6 in that review role with `gpt-5.6-sol`, but the result must be labeled as a
fallback rather than Sol/Fable consensus.

### Stage-0 reconciliation

The fallback reciprocal review completed on the frozen packet.  All four
initial and reciprocal outputs returned `partially_supported` with high
confidence.  Root accepts these binding corrections before evaluator work.

- Track A has no admitted A2 card and stops before evaluator authoring.  The
  enriched signed-tropical and real cluster-boundary ideas remain research
  prompts only; no literal canonical nonconservative object or applicable
  source theorem is present.
- The 1,820 ticket-0037 records are the total search corpus, not 1,820 affine
  failures.  Local replay confirms exactly one record has zero two-sided and
  zero one-sided affine predecessor support.
- Track B may run descriptive deletion, wall-neighbor, blocker, defect, and
  distance morphology.  Polynomial threshold degree is encoding-only.
- Raw bad-type count is not sufficient for repair admission.  A repair card
  additionally requires distinct deletion-minor behavior, blocker or nerve
  type, defect regime, wall-neighbor creation mechanism, and a held-out
  genealogy.  With only one structural type, no repair grammar is authored.

## Track A: arithmetic and Grassmannian wall machinery

### A1. Source-first candidate ledger

Audit only primary sources and exact constructions in these classes.

1. Theta or modular invariants of rational row or column lattices.
2. Automorphic forms whose divisors are special Grassmannian hyperplanes.
3. Signed-tropical Pluecker functions or balanced fan cocycles retaining the
   chirotope phase.
4. Real cluster or boundary-chart quantities that remain defined when one
   Pluecker coordinate crosses zero.

For each candidate freeze the mathematical object, basis-change behavior,
realization dependence, wall increment, codimension-two relation, proposed
project consumer, missing bridge, and cheapest falsifier.  Similar terminology
or a modular transformation law is not a candidate.

### A2. Admission firewall

A candidate reaches computation only if all of these are explicit.

- The lattice or arithmetic object is canonical, or the claimed consequence
  holds uniformly over every admissible lift.
- The claim is invariant under integer basis change and under scaling choices.
- Variation inside one fixed order-type realization stratum is either absent
  or controlled by a proved uniform inequality.
- The wall increment is defined from source data and the changed Pluecker
  coordinate, without endpoint rank, witness count, or successful-path data.
- Square and four-packet loop consistency is a literal identity.
- The candidate is neither identically zero nor only a telescoping
  conservation law.
- A direct route to an existing project interface is stated without importing
  the desired convex witness or rank comparison.

Failure of canonicality or realization-fiber control is
`ARITHMETIC-FIBER-FAIL`.  If no card survives, stop Track A before computation.

### A3. Bounded exact pilot

Only admitted cards may be tested.  Reuse the exact square, four-packet,
collision, fixed-lattice, rational wall, and same-order-type realization
fixtures.  At least two independently constructed realizations of each tested
order type are required for any metric candidate.  Candidate generation may
not use convex-witness counts, endpoint prime-core families, or outcome labels;
those are opened only after both candidate ledgers are frozen.

Possible outcomes are:

- `ARITHMETIC-NO-CARD`: no primary-source or exact candidate survives A2;
- `ARITHMETIC-FIBER-FAIL`: the object varies incompatibly inside one order
  type or with the lattice lift;
- `ARITHMETIC-CONSERVATION-ONLY`: loop consistency holds but supplies no
  monotone or positive consequence;
- `ARITHMETIC-FALSIFIED`: an exact admitted fixture refutes the frozen card;
- `ARITHMETIC-SURVIVES`: a frozen card survives bounded tests, as search
  information only; or
- `ARITHMETIC-THEOREM-READY`: a survivor has a literal symbolic statement,
  noncircular producer, exact consumer, and primary-source or self-contained
  proof outline.  Lean remains separately gated.

## Track B: affine obstruction morphology

### B1. Frozen exact objects

For a point configuration `P`, let `E(P)` be its convex-five subsets, `T(P)`
its oriented nontrivial strict affine topes, and `B(P)` its unrestricted
predecessor bicolorings.  Freeze these quantities.

- `defect(t)` is the number of edges of `E(P)` contained in either color of
  `t`; `delta(P)` is its minimum over `T(P)`.
- `beta(P)` is the minimum number of predecessor edges whose monochromatic
  tope sets cover all of `T(P)`, and is null when a valid tope exists.
- `rho(P)` is the minimum Hamming distance from `T(P)` to `B(P)`, and is null
  when `B(P)` is empty.
- The defect landscape is `defect` on the affine-tope adjacency graph.
- The blocker nerve records nonempty intersections among forbidden tope sets,
  while all minimum blocker covers are retained explicitly.
- The polynomial threshold degree of a fixed bicoloring is the least
  `d <= 3` for which one strict rational polynomial sign separator of total
  degree `d` exists.  Feasibility and infeasibility require exact rational
  primal or Farkas certificates.

The independent checker must reconstruct convexity, topes, bicolorings,
adjacency, distances, covers, and polynomial certificate validity without
calling the producer implementations.

### B2. Corpus and coverage

The immutable baseline consists of:

- all complete existing target-free `N=8` and `N=9` affine-tope controls;
- all 1,820 exact `N=10`--`N=13` records from ticket 0037;
- the exact thirteen-point witness and all thirteen one-point deletions;
- every exact admitted realizable target-free one-wall neighbor produced by a
  frozen local crossing rule; and
- all 381 unrestricted bicoloring pairs of the witness.

If fewer than twenty distinct affine-failing sorted-x chirotopes are available,
one pre-frozen bounded adversarial generator may search near the witness.  It
may retain at most 256 failures, must use at least four genealogies, and no one
genealogy may exceed one half of the retained corpus.  Coordinate perturbations
with the same chirotope count once.  A repair rule additionally requires the
structural-diversity fields frozen in the Stage-0 reconciliation and one
held-out genealogy.  Failure of either count or diversity is
`AFFINE-BAD-COVERAGE-FAIL`; no general repair rule may then be claimed.

### B3. Questions tested

1. Is the witness deletion-minimal or does it contain a smaller affine-failing
   minor?
2. Which wall crossing covers the last valid tope, and which predecessor edge
   performs that cover?
3. Do minimum blockers share a bounded intersection, cyclic-order, recursive-
   block, or allowable-sequence signature across independent bad types?
4. Are unrestricted solutions uniformly near the tope set, or is `rho=1`
   special to this witness?
5. What fractions of successful bicolorings have degree-one, degree-two, or
   degree-three strict separators?
6. For defect-one topes, can any pre-frozen relabeling-compatible rule choose a
   point of the unique bad pentagon to flip using only source geometry?

Low-degree separation is morphology only.  A rule chosen after seeing which
bicoloring succeeds, or one whose premise states that its flip is valid, is
`AFFINE-REPAIR-CIRCULAR`.

Possible outcomes are:

- `AFFINE-BAD-COVERAGE-FAIL`;
- `AFFINE-ISOLATED-OBSTRUCTION`;
- `AFFINE-MINOR-RIGID`;
- `AFFINE-DEFECT-FAMILY`;
- `AFFINE-LOW-DEGREE-SIGNAL`;
- `AFFINE-REPAIR-CIRCULAR`;
- `AFFINE-REPAIR-SURVIVES`; or
- `AFFINE-CHECKER-MISMATCH`, `AFFINE-MODEL-GAP`, or `AFFINE-RESOURCE`.

Every result short of a separately approved compiling theorem is search
information.  A survivor must pass held-out chirotopes from a different
genealogy before it can become a theorem card.

## Execution and resource boundary

Owned root:

`runs/experiments/20260819-arithmetic-affine-microscope/`

After sources, cases, manifests, exact commands, and hashes are frozen:

- Track A may use at most one producer and one independent checker, each
  bounded by 1,200 seconds, four CPU cores, 8 GiB RAM, and 1 GiB output.
- Track B may use at most one producer and one independent checker, each
  bounded by 1,200 seconds, eight CPU cores, 16 GiB RAM, and 2 GiB output.
- Aggregate live use is at most eight CPU cores and 16 GiB RAM.  Aggregate
  stored output is at most 5 GiB.
- Outputs remain sealed until their corresponding producer and checker are
  terminal.  No post-outcome semantic repair, feature addition, threshold
  tuning, rerun, or larger-`N` continuation is allowed.

Primary-source web access is read-only.  The provider review uses exactly the
repository's authorized `python3 scripts/adversarial_review.py run` prefix.
No software installation, Lean, Lake, SAT/LRAT certificate engineering,
destructive operation, external mutation, commit, or push is authorized.

The user approved this plan on 2026-08-19.

## Proof-distance accounting

- **Net proof movement before execution:** neutral.
- **Evidence:** primary-source audit, exact checked computation, and advisory
  review.
- **Difficulty displaced:** none.  `D-NORMALIZE`, `D-HALF`, and `D-DECOMP`
  remain unchanged unless a later compiling theorem closes a named edge.
- **Strict measure:** a later result must eliminate or strictly weaken a named
  producer obligation; a new invariant, classifier, fit, or obstruction atlas
  is neutral.
- **Counterfactual:** this block is useful if it retires a seductive arithmetic
  analogy or identifies a reproducible affine obstruction mechanism.  Merely
  adding representations or examples does not improve the destination proof.
- **Planning consequence:** only a noncircular theorem-ready card may schedule
  proof work; otherwise close and return route selection to `D-DECOMP`.
- **Load-bearing ledger:** no edge changes in this exploration ticket.

## Decision criteria

Proceed with Track A computation only for a literal candidate that passes the
canonicality, realization-fiber, source-locality, loop, and nonconservation
firewalls.  Proceed with an affine repair card only after at least twenty
distinct and structurally diverse bad chirotopes exist, a different genealogy
is held out, and the rule is frozen without success labels.  Otherwise report
the exact negative or coverage outcome and stop.  Do not turn failed modular,
cluster, tropical, affine, or low-degree encodings into new descendants merely
by adding features.

## Resolution

The arithmetic track closes as `ARITHMETIC-NO-CARD`.  Bounded reciprocal
review and a primary-source audit found no canonical modular, automorphic,
cluster, or signed-tropical wall object at the correct model tier.  Borcherds
products live on orthogonal lattice domains rather than the ordinary real
Grassmannian used here; ordinary cluster/tropical machinery has the already
recorded sign/boundary defects; signed tropical extensions are representations
without a source-selected monotone or nonconservative consumer.

The affine morphology track closes as `AFFINE-RESOURCE`, with no mathematical
outcome.  After source freeze, the producer stopped in 0.21 seconds and
31,876 KiB RSS before writing output.  Its increasing-index symmetry breaker
for minimum set cover is incomplete when a selected uncovered cell is covered
by a later edge while the same valid cover contains an earlier unrelated edge.
The checker therefore did not run.  The frozen no-repair/no-rerun boundary was
honored: no deletion, wall-neighbor, blocker-nerve, distance, or adversarial-
search statistic from this run is admitted.

**Net proof movement:** neutral.  **Evidence:** primary-source/advisory audit
for Track A and an operational stop for Track B.  **Difficulty displaced:**
none; `D-HALF`, `D-DECOMP`, and `D-NORMALIZE` are unchanged.  **Counterfactual:**
the arithmetic result avoids another ill-typed experiment and the operational
failure identifies a harness repair, but neither reduces the destination
proof.  **Planning consequence:** expire the present arithmetic-wall prompt,
keep `FP-07.A` suspended, and authorize no affine repair claim.  A fresh
morphology run would first need a complete exact-cover enumerator independently
preflighted on the stored incidence matrix and an adversarial synthetic cover.
No load-bearing ledger edge changed.

## Evidence

- `runs/experiments/20260818-open-world-math-pilot/campaign-synthesis.md`
- `runs/experiments/20260818-open-world-math-pilot/investigations/01-faithfulness.md`
- `runs/experiments/20260818-open-world-math-pilot/investigations/03-phases.md`
- `runs/experiments/20260818-open-world-math-pilot/investigations/09-wall-groupoid.md`
- `runs/experiments/20260818-open-world-math-pilot/investigations/10-varchenko-gelfand.md`
- `runs/experiments/20260818-open-world-math-pilot/investigations/11-fixed-3d-lattices.md`
- `runs/experiments/20260818-open-world-math-pilot/investigations/14-cluster-tropical-toric.md`
- `docs/wayfinder/tickets/0037-test-affine-tope-predecessor-funnel.md`
- `docs/wayfinder/tickets/0038-autopsy-unrestricted-predecessor-core.md`
- `docs/wayfinder/tickets/0040-test-lattice-wall-core-transport.md`
- `runs/experiments/20260819-affine-tope-funnel/result.json`
- `runs/experiments/20260819-unrestricted-predecessor-core/result.json`
- `runs/reviews/20260819-arithmetic-affine-microscope/sol-sonnet/REPORT.md`
- `runs/experiments/20260819-arithmetic-affine-microscope/arithmetic/source-ledger.md`
- `runs/experiments/20260819-arithmetic-affine-microscope/arithmetic/result.json`
- `runs/experiments/20260819-arithmetic-affine-microscope/affine/manifest.json`
- `runs/experiments/20260819-arithmetic-affine-microscope/affine/result.json`
- `runs/experiments/20260819-arithmetic-affine-microscope/affine/summary.md`
