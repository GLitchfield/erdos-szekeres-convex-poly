---
title: Test E3 and select a repair strategy
type: research
mode: AFK
status: open
claim: codex-e3-adversarial-2026-08-01
blocked_by: none
---

## Question

Is `DecomposableExactUpperAt k` true for the repository's abstract recursive
deep-below model for every `k ≥ 3`, and, if so, which strengthened invariant
has the best bounded evidence for repairing the failed published induction?
If it is false, what is the smallest counterexample, and is that counterexample
sweep-realizable by an actual planar point configuration?

## Decision criteria

- Treat the truth and falsity directions symmetrically.  A search that only
  reproduces expected extremal examples cannot select the proof route.
- Use the exact repository definitions of `HasDeepBelowSplit`,
  `IsDecomposableOn`, cup, cap, and strong polygon.  Record separately whether
  a generated abstract coloring satisfies the signotope law and whether it is
  known to be realizable by straight-line planar points.
- First perform an exact exhaustive enumeration at the largest feasible small
  size, deduplicating colorings rather than merely sampling decomposition
  trees.  The producer and independent checker must not import one another.
- The default computation budget is 30 minutes, 8 CPU cores, 16 GiB RAM, and
  5 GiB under `runs/`.  Deterministic shards, seeds, conventions, and coverage
  counts are required.
- A counterexample branch advances only with a compact coloring/decomposition
  certificate independently checked against every defining predicate.  It
  refutes the repository's E3 statement only if sweep realizability is also
  certified; otherwise it redirects the abstraction boundary.
- A proof branch advances only when a candidate invariant survives exhaustive
  small cases, explains the `(4,5,5,1,3)` boundary regression, has an explicit
  inductive transition, and yields a nontrivial compiling Lean lemma.  Pattern
  agreement or reviewer consensus is not enough.
- Classify an inconclusive search by its exact coverage bound.  Do not infer
  the all-`k` theorem from a finite negative search.
- Before selecting the route, obtain a bounded blind and reciprocal Sol/Fable
  review of the evidence packet, then independently dispose of every material
  objection.

## Candidate strategies under review

1. **Endpoint-profile injection.** Refine the scalar cup/cap maxima by left and
   right endpoint-extension states, and inject vertices or recursive blocks
   into the `2^(k-2)` binary profiles.
2. **Rank-downset compression.** Start from the classical injective map from a
   sweep vertex to its cup/cap predecessor downset.  Search for the additional
   pairwise restriction imposed by recursive deep-below structure and absence
   of a strong `k`-gon.
3. **Context-carrying induction.** Repair the three-parameter recurrence by
   carrying an external cup/cap supplied by ancestor blocks.  A saturated
   off-diagonal child must pay for the binomial term that currently overflows.
4. **Minimal-counterexample descent.** Assume a smallest E3 counterexample,
   choose its root split, and use the exact crossing characterization plus
   saturation/straddling lemmas to contradict minimality or expose a smaller
   rooted counterexample.
5. **Falsification.** Enumerate recursive colorings and optimize/SAT-search for
   more than `2^(k-2)` vertices with no strong `k`-gon, then separately test
   signotope and straight-line realizability constraints.

## Resolution

Open.  The published scalar induction cannot be used: Lean checks a boundary
instance where the claimed two contributions are eight and the outer threshold
is seven.  Local endpoint transitions compile, but no global profile count has
yet been proved.  This ticket deliberately reopens the theorem's truth value
instead of assuming that an endpoint repair must exist.

The first falsification round is complete through eight leaves.  Independent
implementations agree on 186,888 distinct eight-leaf colorings, none of which
contradicts the proposed five-vertex base lemma.  All recursively decomposable
colorings are now proved in Lean to satisfy the signotope law, and the existing
nine-point LRAT certificate consequently proves
`decomposableExactUpperAt_five`.  The all-`k` statement remains open; the
reciprocal Sol/Fable route review and the general anchor-context transition are
still pending.

Both off-diagonal `k = 6` states are now closed in Lean.  Generated semantic
bridges connect kernel-checked LRAT proofs to
`exists_cap_four_or_cup_six_or_strong_six` on twelve vertices and
`exists_cap_five_or_cup_six_or_strong_six` on sixteen vertices.  Restriction
promotes them to the hereditary invariants `decomposableStateUpper_466` and
`decomposableStateUpper_566`.  The audited dual-state reduction then proves
`decomposableExactUpperAt_six : DecomposableExactUpperAt 6`.

The large sixteen-vertex proof is represented by 256 kernel-checked
checkpoints rather than one monolithic Lean declaration.  Its committed
segments contain the complete 496,453,316-byte trimmed LRAT trace and compose
to a proof of the empty clause.  This settles the finite `k = 6` milestone but
not the ticket's all-`k` question; selecting and proving a uniform strengthened
invariant remains open.

The semantic side is also complete and independently checked.  Its 155,064
canonical clauses are covered by 769 semantic chunks, 4,096 raw aggregation
modules, and 1,024 midpoint modules.  Short named midpoint propositions form a
compact root, and Lean accepts a single `rfl` bridge identifying that tree with
the checkpoint's full clause proposition.  The independent checker in
`scripts/check_e3_state566_aggregation.py` reparses the DIMACS source and
verifies every range, proposition, import, alias, hypothesis, elimination
leaf, and root association without importing either generator.

A bounded reciprocal Sol/Fable review of the pre-redesign aggregation packet
had SHA-256
`1c50d5ec1789727a630e1f34579968d11389cc2af3d26cb9e8ee3dd300f9247a`.
Both reviewers returned `partially_supported` at medium confidence and asked
for the independent whole-data checker, the named-proposition proof shape, a
successful root build, and an axiom audit.  All four checks are now complete.
Lean reports only `propext`, `Classical.choice`, and `Quot.sound` for
`decomposableExactUpperAt_six`; no project axiom or `sorryAx` occurs.  This
disposes of the material aggregation objections but does not answer the open
uniform all-`k` question.

A fresh post-six reciprocal review now selects one narrower next obligation,
not a uniform route.  Against packet SHA-256
`09beb042e541117ef77f30f73353e91f5c0dae50968753eb216f2b347584ca55`,
both final reviewers converged at `partially_supported`, medium confidence, on
formalizing the hereditary diagnostic
`decomposableStateUpper_455 : DecomposableStateUpper 4 5 5`.  They agree that
the proposed context state is still undefined, minimal-counterexample descent
is circular without such a rooted state, and a global endpoint injection lacks
both completeness and injectivity.

The review's finite gate has been independently discharged.  The canonical
eight-vertex `(4,5,5)` signotope instance has 56 variables and 1,134 clauses
(CNF SHA-256
`56ea4a13b8f976fbb266ef58e8a8c7074de38e08a201fda0477b59642abc49c1`).
CaDiCaL 1.7.3 returned UNSAT with a 39,037-byte LRAT trace (SHA-256
`5401621fc275e55a42077cecd293b5b303969da341bd6a0dc25973eaf5287861`),
and a temporary Lean `FromLRAT` probe kernel-checked it in 4.4 seconds.

The selected theorem is now complete. The CNF and LRAT data are committed,
eight generated semantic chunks connect all clauses to the repository
predicates, and an independent checker reconstructs the aggregation directly
from DIMACS without importing either generator. Lean proves
`decomposableStateUpper_455 : DecomposableStateUpper 4 5 5` and its dual
`decomposableStateUpper_545`; both have only `propext`, `Classical.choice`, and
`Quot.sound` in their axiom audit. This certifies that the `8 > 7` regression
is a proof-method defect, but it remains explicitly diagnostic rather than the
missing uniform transition.

The all-root directional context-profile replay is complete through eight
leaves. Two independent implementations agree on 243,102 compatible roots,
1,896,168 anchor/four-chain records, 4,343,048 restriction comparisons, and
all canonical hashes. Same-gap and cross-anchor summaries have open
composition collisions. The complete all-gap word has no open `k = 5`
collision in the covered range, but the generalization fails at the next
nonvacuous probe: a targeted `k = 6`, `n = 9` singleton-root search finds
2,055 collision observations among 85,797 open parents. A compact certificate
contains two explicit decomposition trees with equal child words and unequal
parent profiles, and a separate checker reconstructs every defining
predicate. Candidate B's maxima-only state is rejected. The live redirect is
to a correlation-preserving rank/downset state or a bounded transition
congruence that separates this pair; neither route is selected until bounded
Sol/Fable review is disposed and its first transition is stated precisely.
The fixed-ambient definition layer has begun in Lean:
`ContainsCupSetAtGap.mono` and `ContainsCapSetAtGap.mono` compile and preserve
the same directional chain witness under subset enlargement.  The maxima
aggregation and collision theorem remain pending.

The first clean advisory review attempt used packet SHA-256
`5ba9b4a4b2ad34b02486a2593dfc03d0ac5383007e46c77951d60cb4928ab6d2`
at revision `48cb924`. Sol returned `partially_supported`, agreed with rejecting
maxima-only candidate B, and recommended a concrete singleton-root
rank/downset falsification gate before a replacement Lean transition. Fable
was unavailable because its provider returned repeated HTTP 429 session-limit
responses; reciprocal critiques did not run. This is not reviewer consensus,
and the replacement route remains unselected.

The requested rank/downset falsification gate is now complete at the first
nonvacuous singleton-root target `k = 6`, `n = 9`. A deterministic producer
and an independently written full replay agree on all 186,888 decomposable
upper-child colorings and 85,797 open parents. The ordered child downset word
has 9,535 collision observations, and even the complete child pair-rank matrix
has 481: in each case equal child state produces unequal parent state. Raw
parent downsets remain vertex-injective in every covered parent, but the exact
34-vertex compatibility graph has a maximum clique of size 27, exceeding the
target `2^(6-2) = 16`. Thus deterministic rank-state composition and the
pairwise incompatibility counting shortcut are both rejected. Higher-order
rank restrictions and realizability-sensitive transitions remain logically
open; the witnesses have decomposition trees but no planar realization
certificate. No replacement uniform route is selected pending bounded
Sol/Fable review of this gate.

The first Sol audit returned `partially_supported` and agreed with all three
bounded rejections. It correctly identified two provenance/semantic gaps in
the first packet: the certificate called its pre-generation commit simply
`revision`, and both full implementations used the same rank recurrence. The
certificate now calls that value `generation_base_revision`, binds the exact
producer source by SHA-256, and the checker verifies it. A new direct-chain
oracle exhaustively checks every triple coloring through five vertices at
clips one through five against the dynamic ranks and downsets, with zero
differences. The audit's remaining scope warnings agree with the ticket:
abstract decomposability is not planar realizability, and the observed
injectivity does not prove or refute the global counting theorem. A clean
post-disposition review remains pending before selecting the next Lean package.

## Evidence

- [`ErdosSzekeres.Decomposable`](../../../ErdosSzekeres/Decomposable.lean)
- [`ErdosSzekeres.E3FiniteReduction`](../../../ErdosSzekeres/E3FiniteReduction.lean)
- [Formalization plan](../../formalization_plan.md)
- [Literature review](../../literature_review.md)
- [Profile-search prototype](../../../scripts/decomposable_profile_search.py)
- [Exact coloring producer](../../../scripts/enumerate_decomposable_colorings.py)
- [Independent enumeration checker](../../../scripts/check_decomposable_enumeration.py)
- [Exact enumeration design and results](../../experiments/0002-e3-adversarial-design.md)
- [Post-six route review and disposition](../../experiments/0003-e3-post-six-route-review.md)
- [All-root context replay and collision redirect](../../experiments/0004-e3-all-root-context-profile.md)
- [Compact `k=6`, `n=9` collision certificate](../../../data/derived/e3-context-k6-n9-singleton-collision.json)
- [Independent collision checker](../../../scripts/check_decomposable_context_collision.py)
- [Rank/downset gate and interpretation](../../experiments/0005-e3-rank-downset-gate.md)
- [Compact rank/downset certificate](../../../data/derived/e3-rank-k6-n9-singleton.json)
- [Independent rank/downset checker](../../../scripts/check_decomposable_rank_profiles.py)
