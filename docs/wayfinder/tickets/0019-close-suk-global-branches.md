---
title: Close the Suk global branches and point-set source producer
type: research
mode: AFK
status: closed
claim: codex-suk-branch-closing-2026-08-15
blocked_by: none
---

## Question

Can the compiled raw-pool chain/antichain split be turned into a convex-subset
theorem in both branches, and can the assumed `PorValtrCyclicSupportData`
object be produced from an arbitrary sufficiently large planar point set?

The immediate target remains the quantitative Suk--Pór--Valtr route `FP-15.B`.
This ticket does not claim the exact Erdős--Szekeres upper bound.  Its purpose
is to close the three named downstream obligations left by ticket 0018:

1. consume a consecutive run of actual chain witnesses;
2. consume a pairwise-nonadjacent packing of actual antichain witnesses; and
3. construct the actual Pór--Valtr cyclic support data from a point set.

## Decision criteria

### Proof-distance measure

Before this run, the viable quantitative route has three branch/source
obligations before its generic finite composition and asymptotic wrapper:

- `C-chain`: chain-run witnesses imply a convex subset;
- `C-anti`: nonadjacent antichain witnesses imply a convex subset; and
- `C-source`: a sufficiently large point set produces source-faithful cyclic
  support data with the corrected minus-one pool count.

A result is forward only if a compiling theorem closes one of these exact
obligations without assuming its conclusion, an equivalent global selector,
or a preselected branch.  A local helper counts only when it is consumed in
the same module or by an already-frozen downstream theorem and strictly
reduces the remaining dependency count.

After the two approved runs, `C-chain`, `C-anti`, and `C-source` are closed and
the generic finite branch disjunction is eliminated.  Thus the ticket's three
top-level branch/source obligations decrease from three to zero, while the
internal source-stage count decreases from six to zero.  The distinct
positive-fraction parameter assembly and asymptotic wrapper lie downstream of
this ticket and remain open.

## Approved execution slate

The user approved this block on 2026-08-15.  It contains three
proof-producing threads, all in `FP-15.B`.  The concentration is deliberate:
`FP-15.B` is the sole advancing portfolio route, and these are the three
serially composable obligations exposed by the previous forward theorem.
Their failures are correlated and will be reported as such rather than as
three independent route bets.

Lean builders are serialized.  While the chain consumer owns the builder
lane, the antichain and source threads may perform only read-only proof
architecture, source audit, and control design.  Each receives a separately
frozen builder packet only after the prior builder has released the lane.

### Thread A: chain-run consumer

Freeze a theorem that restricts a global raw-pool chain run to selected point
pools, proves the adjacent-pool interface for those pools, applies
`sukConsecutiveChainPools_containsConvexSubset`, and reconnects this to
`SukConsecutiveRawPools.chainRun_or_antichainPacking`.  The public conclusion
must be an actual convex subset of the original carrier or the unchanged
antichain-packing alternative.

Outcomes: `SUK-CHAIN-CONSUMER-LAND`, `SUK-CHAIN-CONSUMER-MISMATCH`,
`SUK-CHAIN-CONSUMER-INERT`, `SUK-CHAIN-CONSUMER-REFUTED`, or
`SUK-CHAIN-CONSUMER-RESOURCE`.

### Thread B: antichain-union consumer

Use the compiled common-base strict-side theorem to prove the cross-region
support needed to union caps extracted from pairwise-nonadjacent antichains.
Two architectures are predeclared: a common sweep/projective order aligned
with the strict cap sequence, or an order-free supporting-cap witness.  The
thread may choose between them before the first Lean outcome, but may not add
an assumed common cap, selected union, or target convex subset after a failed
gate.  If both architectures fail their exact geometric obligation, stop for
review rather than inventing a third decorated premise.

Outcomes: `SUK-ANTICHAIN-UNION-LAND`, `SUK-ANTICHAIN-UNION-MISMATCH`,
`SUK-ANTICHAIN-UNION-INERT`, `SUK-ANTICHAIN-UNION-REFUTED`, or
`SUK-ANTICHAIN-UNION-RESOURCE`.

### Thread C: Pór--Valtr point-set producer

Work from the authenticated 2002 Pór--Valtr source and the corrected count
`ceil (N / 2^(32*r)) - 1`.  The target is a theorem whose carrier is the input
point set and which produces `PorValtrCyclicSupportData` without taking marked
edges, source pools, cyclic support regions, or their cardinalities as
premises.  The intended stages are a convex `2*r` support polygon, exterior
cells, the product/count selection of `r` rich marked edges, exact source-pool
selection, and packaging into the existing structure.

An upstream source lemma is retained only if it is immediately consumed and
strictly reduces the frozen producer dependency count.  Otherwise the result
is partial search information, not forward proof movement.

Outcomes: `PV-POINTSET-PRODUCER-LAND`, `PV-POINTSET-PRODUCER-PARTIAL`,
`PV-POINTSET-PRODUCER-SOURCE-MISMATCH`, `PV-POINTSET-PRODUCER-INERT`, or
`PV-POINTSET-PRODUCER-RESOURCE`.

## Execution result and integration

Thread A reached `SUK-CHAIN-CONSUMER-LAND`:
`SukConsecutiveRawPools.containsConvexSubset_or_antichainPacking` converts an
actual chain run into the compiled adjacent-pool recurrence and preserves the
unchanged antichain alternative.

Thread B reached `SUK-ANTICHAIN-UNION-LAND`.  The four frozen declarations
derive a common projective order from raw signs, extract an immediate cup or a
base-supported cap from each actual antichain, transport support across
nonadjacent pools, and prove the exact cap union convex.  A separate read-only
formal review reached `ANTIREVIEW-PASS`; that review is proposal evidence, not
an additional proof gate.

The conditional integration gate reached `SUK-GLOBAL-BRANCH-LAND`:
`SukConsecutiveRawPools.containsConvexSubset_of_globalParameters` eliminates
the chain/antichain disjunction under the frozen finite arithmetic hypotheses.
It adds no selected cap, selector, branch, or target premise.

Thread C first froze six honest original-carrier obligations and reached
`PV-PERIODIZATION-LAND`:
`exists_clockwiseStrictCapPeriodization` constructs a periodic strict-cap
enumeration of any supplied finite convex general-position set without x-sort
or a carrier transformation.  The approved continuation then reached
`PV-SUPPORT-PRODUCT-LAND` and `PV-POINTSET-PRODUCER-LAND`.
`exists_porValtrSupportProductData` proves the full cyclic open-cell product
bound from an arbitrary sufficiently large general-position point set, using
an ordered-even-support double count and exact odd-point reconstruction.
`porValtr_exists_rich_half` extracts exactly `r` rich cells at the corrected
ceiling-minus-one threshold, and `exists_porValtrCyclicSupportData` packages
every source field with `carrier = P`.  A separate read-only review reached
`PV-SOURCE-REVIEW-PASS` and reproduced the final producer directly.

Do not infer an asymptotic or exact `D-UPPER` claim from this closure.  The next
gate is the unchanged positive-fraction parameter theorem that composes the
source data, raw-pool bridge, compiled global branch theorem, and density
slack; the asymptotic wrapper remains after it.

All eight prior task/result pairs and all five continuation pairs validate,
both independent formal reviews passed, the umbrella imports and strategic
documents are reconciled, and `make test` passes.  Root alone owns the
exact-file commit and push to
`origin/codex/state-578-tree-reservoir`.

## Innovation and review decision

No new Sol/Fable route review is required: the main route, scope, and branch
contracts were selected and source-audited in ticket 0018, and this block is
ordinary implementation of those vetted obligations.  The innovation check
reuses the already recorded antichain architecture and Pór--Valtr source audit;
it does not dispatch a new scout or treat implementation difficulty as a route
change.  A materially different premise or source model requires a fresh
ticket and review.

## Resources and stops

- Global ceiling: 8 CPU cores, 16 GiB RAM, and 2 GiB of new run artifacts.
- Each Lean or computation process: at most 30 minutes; one Lean/Lake process
  at a time.
- No SAT solver, network retrieval, software installation, provider call,
  destructive operation, external mutation, or unbounded search.
- No `sorry`, `admit`, unsafe axiom, `native_decide`, theorem weakening, or
  unverified external oracle.
- Stop a thread on a source mismatch, false frozen theorem, equivalent target
  premise, resource cap, or after both predeclared antichain architectures fail.

## Resolution

Closed.  Net proof movement is forward on `C-chain`, `C-anti`, generic finite
branch assembly, and `C-source`; their top-level obligation count decreases
from three to zero and the frozen source-stage count decreases from six to
zero.  The counterfactual test is positive: the compiling theorems remove both
global cases and the full original-carrier source producer without relocating
them into supplied selectors, cells, pools, or target objects.  Evidence is
compiling Lean theorems, targeted builds, standard-only axiom audits,
deterministic controls, and an independent formal review.  Difficulty
displaced: none within this ticket; the separate positive-fraction parameter
assembly and asymptotic wrapper remain.  Planning consequence: retain
`FP-15.B` as advancing and make that unchanged positive-fraction composition
the next bounded theorem gate.  `D-UPPER`, `D-HALF`, `D-DECOMP`, and
`D-NORMALIZE` remain open, `D-ASSEMBLE` remains gated, and no load-bearing
destination edge has changed.

## Evidence

- `ErdosSzekeres/SukChainRunConsumer.lean`
- `ErdosSzekeres/SukAntichainUnionConsumer.lean`
- `ErdosSzekeres/SukGlobalBranchConsumer.lean`
- `ErdosSzekeres/PorValtrClockwisePeriodization.lean`
- `ErdosSzekeres/PorValtrSupportProduct.lean`
- `ErdosSzekeres/PorValtrPointSetProducer.lean`
- Schema-valid task/results and independent controls under ignored
  `runs/agents/20260815-suk-branch-closing-slate/` and
  `runs/agents/20260816-por-valtr-source-slate/`
