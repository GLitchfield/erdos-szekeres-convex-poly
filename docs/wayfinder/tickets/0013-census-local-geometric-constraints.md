---
title: Census local geometric constraints and extension recurrence
type: research
mode: AFK
status: closed
claim: codex-local-geometric-constraint-hierarchy-2026-08-14
blocked_by: none
---

## Question

For the ordered triple coloring induced by planar points, what constraints are
already forced on four, five, and six vertices, how do valid states extend when
one rightmost vertex is added, and does that extension relation factor through
a smaller invariant that survives a blind seven-point test?

This ticket separates four model tiers: arbitrary triple colorings,
`OneChangeOn` colorings, `IsSweepRealizable` colorings, and target or
decomposability overlays.  A constraint is called geometric only when it
separates the first two relevant tiers by an admitted theorem or complete
certificate.  A finite census is information, not proof movement.

## Selected gates

1. Prove a parameterized Lean rightmost-extension theorem: `OneChangeOn` on
   `n+1` is equivalent to `OneChangeOn` on the first `n` vertices together with
   one `TurnSequenceAllowed` condition for every old ordered triple and the
   three pair colors incident to the new last vertex.
2. Independently reconstruct the complete labeled five- and six-point
   `OneChangeOn` catalogs, all restriction/extension edges, and the existing
   regression values.  The checker may not import producer logic and must
   reject a changed color, omitted state, false symmetry, and corrupted edge.
3. Before opening six-to-seven extension outcomes, freeze one compressed parent
   summary with an exact collision falsifier.  Search for two six-point parents
   with the same summary but different seven-point extension behavior.
4. Audit exact `IsSweepRealizable` coverage only far enough to decide whether a
   named consumer needs full five/six rational certification.  Failure to find
   coordinates is never nonrealizability evidence.  Full 908-state coordinate
   promotion is deferred unless a consumer is identified.

## Canonical outputs

- complete labeled catalogs before any quotient;
- minimal forbidden partial assignments only when an exact irredundant
  definition is frozen;
- the rightmost restriction/extension graph;
- inherited versus first-appearing constraints;
- cup, cap, strong-subset, and decomposability annotations;
- a state-dependent count identity distinguished from any proposed compressed
  recurrence.

Only order reversal or color reflection may be used as symmetries, and only
after their action on the fixed sweep order is independently checked.

## Decision criteria

- Keep the four model tiers separate in every theorem, manifest, and report.
- Require independent enumeration and corruption rejection at both five and
  six points.
- Count a recurrence as compressed only when a strictly smaller frozen parent
  summary determines held-out extension behavior.
- Do not revise the summary after inspecting the seven-point collision gate.
- Do not infer nonrealizability from absent coordinates or an incomplete
  catalog.
- Do not promote a finite catalog into the proof portfolio without a compiling
  theorem and named consumer.

## Candidate outcomes

1. **`EXTENSION-LAND`:** the parameterized Lean extension theorem compiles.
2. **`CENSUS-56`:** independent implementations agree on the exact five/six
   catalogs and extension graph; this remains computational evidence.
3. **`PROFILE-SURVIVES`:** the one frozen summary predicts held-out seven-point
   extension behavior and receives a named Lean consumer.
4. **`PROFILE-REFUTED`:** an exact same-summary/different-extension pair rejects
   the compressed recurrence; retain the witness and do not retune on it.
5. **`REALIZABILITY-SEPARATES`:** an admitted theorem or complete certificate,
   not coordinate-search failure, separates `OneChangeOn` from
   `IsSweepRealizable` at five or six and changes a named consumer.
6. **`LOCAL-EQUALITY-56`:** exact coverage shows no additional straight-line
   restriction through six.  Record the boundary without crediting proof
   movement.
7. **`CATALOG-STOP`:** source, completeness, verification, or resource admission
   fails; make no mathematical inference.

The first two outcomes may occur together.  Neither alone changes a
load-bearing dependency.

## Portfolio disposition

Track the work initially as `FP-13.A`, a discovery child, with cross-references
to the realizability filter `FP-02.F` and exact-six thread `FP-16`.  Promote it
only if a local realizability theorem changes a full-context terminal or a
parameterized compressed invariant has a named exact-route consumer.

## Review status

The bounded blind Sol/Fable review completed at commit `4506fae` with evidence
packet SHA-256
`18af123c89997adbb7483cb1e0da5be27129dde6499d066e347a12d78c57d9f9`.
Fable returned `supported` with medium confidence; Sol returned
`partially_supported` with high confidence.  Both supported admission only as
a bounded `FP-13` child and independently recommended proving the generic
recurrence first, reproducing the finite counts independently, and deferring
the full 908-state realizability catalog until a consumer needs it.  This is
advisory route criticism, not mathematical evidence.

## Resources and stop conditions

- at most 30 minutes, 8 CPU cores, and 16 GiB per process;
- at most 5 GiB under the ignored run tree;
- no blind-seven retuning after the summary is frozen;
- no `native_decide`, unverified oracle, or monolithic certificate promotion;
- no claim that a state-dependent finite sum is a compressed recurrence;
- no application to `FP-02` before a compiling realizability theorem and
  full-context consumer exist.

## Resolution

The bounded child is closed with two accepted outcomes and one upstream summary
failure.

- **`EXTENSION-LAND`:** `oneChangeOn_univ_succ_iff` compiles.  It proves the
  exact parameterized rightmost-extension equivalence without realizability,
  target, or cardinality assumptions.
- **`CENSUS-56`:** independent recursive and brute-force implementations agree
  on 8, 62, and 908 labeled `OneChangeOn` colorings at four, five, and six
  vertices.  They agree on every restriction edge, annotation, and frozen E3
  regression; 718 of the six-point states are recursively decomposable.
- **`TRAINING-FAIL-NONCOMPRESSION`:** the preregistered
  `pair-principal-spectrum-v1` has constant extension counts on its training
  classes, but every collision at four and five vertices lies in the validated
  color-reflection/order-reversal orbit.  It therefore demonstrates no
  compression.  The seven-point outcome was neither generated nor inspected,
  and the summary is expired without retuning.

No realizability equality or separation was proved.  The exact finite
state-dependent sum is not a compressed recurrence, and no load-bearing edge
changed.  Retain the Lean theorem and finite census as infrastructure and
regression data.  Revive the child only for a structurally different summary
with a named consumer and a genuine nonsymmetric training collision, or for an
exact realizability restriction required by an active parent.

## Evidence

- `ErdosSzekeres/Sweep.lean`
- `ErdosSzekeres/StructuralCharging.lean`
- `scripts/enumerate_decomposable_colorings.py`
- `docs/experiments/0088-decomposition-prime-layer-f.md`
- `docs/experiments/0097-layer-f-stratified-rank-gate.md`
- `docs/wayfinder/frontier-portfolio.md`
- `runs/reviews/20260814-local-constraint-hierarchy/output/REPORT.md`
- `runs/reviews/20260814-local-constraint-hierarchy/output/manifest.json`
- `ErdosSzekeres/TripleColoringExtension.lean`
- `scripts/enumerate_local_constraint_hierarchy.py`
- `scripts/check_local_constraint_hierarchy.py`
- `scripts/test_local_constraint_hierarchy.py`
- `runs/agents/20260814-local-constraint-hierarchy/census/census-56/catalog.json`
- `runs/agents/20260814-local-constraint-hierarchy/census/census-56/check-report.json`
- `runs/agents/20260814-local-constraint-hierarchy/census/census-56/training-report.json`
