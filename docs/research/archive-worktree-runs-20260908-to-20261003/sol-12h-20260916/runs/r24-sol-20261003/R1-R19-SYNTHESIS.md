# What R1–R19 already say about Q4

2026-10-03. This synthesis precedes R24 numerical probes. Sources are the shared journal, the handoffs named below, and the current compiled-environment status. Old handoff headings saying “active” are historical, not current job state. No result below is recomputed here.

## The central distinction

`Ctx.Context.bound` (B) is a guessed arithmetic recurrence on a **word with a fixed number of child letters**. `Ctx.Satisfies` itself fixes the actual child's cardinality to that number. In contrast, the coordinator's N is an extremal function of **zones with free occupancies**, endpoint cup/cap matrices and a strong limit. Comparing B with N requires saying whether each represented run must be nonempty. Neither a successful arithmetic falsifier nor a compiling conditional reduction certifies B=N.

The current general proof idea is profile-indexed induction using DS. The persistent obstruction in this history is that induction creates an extra external level and new run geometry. The root hypothesis cannot simply be applied to its parts. Reoptimizing the split can rescue a parent equality even when an individual part changes.

## Record by mathematical mechanism

| Runs | What is established | Consequence for Q4 |
|---|---|---|
| R1 | Single-run additivity was reduced to run contraction plus an alternating-comb inequality. “Interior-level count” and “adjacent gap” contraction laws were diagnostically refuted. Parts of apparently stable roots can fail contraction. | The guessed recurrence is sensitive to global cut geometry, not just nearby gaps. No exact-N comparison was established. |
| R2, R4 | Workstream C and separate labelling/absorption exploration do not establish context-bound exactness. | No B=N evidence can be inferred from those activities. |
| R3 | Reflection of B is Lean-certified. The fixed-k endpoint saving invariant stalled because the saving did not inherit through every equality-charge cut. | Reflection is a reusable symmetry. Independent local charges discard a correlation; the failed invariant is not an N formula. |
| R5 | The compiled C evaluator was introduced and checked against the Python recurrence on finite fixtures. | Enables fast diagnostic B evaluation; it is not an independent exact extremal solver. |
| R6–R7 | Boolean run compression/alternating reductions and recurrence infrastructure were developed under explicit contraction assumptions. | A reduction with an unresolved structural hypothesis does not prove B or N additivity. |
| R8 | External-letter deletion monotonicity for isolated children, with another occurrence of the same level/side retained, is Lean-certified. | Last-occurrence/presence semantics matter. The theorem is about B, not automatically about N. |
| R9–R11 | Conditional single-run additivity reductions and the bridge from one-level-root contraction to parts are Lean-certified with their hypotheses explicit. Single-run contexts can normalize their old history into endpoint capacities. | These explain a possible proof of B additivity if root contraction is proved, but do not certify sharpness. |
| R12 | Sandwich/three-block/uniform-separator compositions were checked with the named open dependencies. Their receipts still contain inherited `sorryAx`. | No unconditional additivity result from these compositions. |
| R13–R14 | Arbitrary singleton-part bases, unit-axis zero, single-level limits and singleton attainment with at most three child letters are certified; root singleton exchange/attainment remains open. A minimum-capacity selector and fixed-position leaf lifting failed diagnostically. | A paying leaf may have to change position, orientation and coupling. Small-cardinality attainment does not imply general exactness. |
| R15 | Singleton-only flip candidates can be absent for membership pattern 00110011. The corrected maximal-segment route and conditional reduction leave exchange open. | The combinatorial reduction changes which partitions are available; it does not answer N. |
| R16–R17 | One-level endpoint-selector scopes were certified. Global first/last-only selection has a kernel counterexample. Larger-axis scalar/rank charging and general singleton exchange remain open. | Endpoint restriction is not a valid universal optimization principle. More helper scopes do not identify a general formula. |
| R18 | ROOT-NF remains open. Componentwise domination by normalized cuts fails even with free coupling/orientation; paired values can be rescued. The general contraction counterexample is diagnostically reachable as a part of a legal one-level root. | Individual child normalizations need not preserve the paired sum. The proof needs a joint invariant, not independently stable parts. |
| R19 | Full raw PEEL is kernel-refuted. An actual-history k6 context requires a middle singleton, not a global end. FLANK-SWAP is certified with physical-presence hypotheses; absent flanks give exact B=10 versus B=4. Arbitrary formal parts of a satisfied parent can be infeasible. | Attainment of B does not imply feasible split attainment or sharp cardinality. Raw unused-level contexts and actual ancestor histories must be separated. |

This table records the relevant content, not theorem counts or progress toward the headline conjecture. For R6–R7/R17, the audited downstream handoffs and current modules are the evidence; no missing run-local final report is invented.

## Already sufficient to rule out universal profile exactness

The accepted `ctx_bound_adjacent_letter_contraction_counterexample` predates these trials and remained part of their evidence:

    (a,u,k)=(5,5,6), maxima=(1,1)
    word S 1L 2U S S: B=12
    word S 1L 2U S:   B=9.

Both words induce the same two-run endpoint profile. Within a run, extension counts are constant; adjacent child multiplicity changes no external order or side. The cap and cup matrices are both `[[3,4],[0,3]]`, with strong limit 5 (matrix calculation to be independently replayed in R24). Consequently any N determined solely by this profile has the same value for both words, whereas the two kernel-certified B values differ. **B cannot equal that N on every context.** This does not yet say which B value is wrong, or claim that this is a globally minimal witness.

Current node status: CLOSED, unchanged type hash `a2406241d44ddf61`, no sorry, standard axioms only. Shared journal records the 2026-09-07 certificate at commit `2227993f189b5ad7fe3de193629686368a32e1eb`; current source is `ESBlueprint/B/CtxBoundAdjacentLetterContractionCounterexample.lean`. R24 read the statement and proof. No new Lean theorem is claimed for the profile interpretation.

## Important accepted R19 witnesses

- Raw PEEL: `(4,4,5)`, `3U4LSS1L2USS`, maxima 1111. Kernel proves WellFormed, B>=2 and every singleton cut sum 1; exact B=2 is diagnostic. Receipt `9159d9e9c8b436a7edd362410be34693c221562de3d85dcfca000cbb2c7ee3f5`.
- Actual-history k6: `(5,5,6)`, `SSS1L3L2LS`, maxima 111. Exact B=8, middle singleton leaf 2 plus remainder 6, all other singleton positions <=7. Receipt `f2d86d2b78a2888f86ed602b7adc5c32e04d850e5616102b720b5348c4a89c38`, commit `1cd0281b18dddb1177d47d876c1e6b87f15fc741`. Actual seven-vertex history receipt `d882dc65055b3a1af3920b833c3e518df688494e481c51e80b25075ff88f965d`, commit `d3b81e384ff288237fbef7fa380c985dd0ded1ca`. The actual child has four vertices; neither receipt establishes an eight-point feasible child.
- FLANK-SWAP: exact B preservation when both opposite flanks are physically present; receipt `882f635458f3cf58aef80fc3acbf82181564022088875761b02342a0811a0343`, commit `e05ed9a3a90443aff49d04047dda17f97ba4627b`.
- Absent flanks: `(5,5,6)`, `SS`, declared maxima (1,2) versus (3,2), B=10 versus 4. Receipt `b6b07830e79402c133ded8f19180ce85d5a8135d5b24280d4866dbc435346e84`, commit `c6cbb39d5f845059595734204ca0d1c9a561a497`. These contexts have different join constraints even though no external letter is present. They do not refute the accepted physical-flank theorem.
- Arbitrary-part infeasibility: the k6 parent satisfies a four-point constant-right coloring, but its p0 upper3 cut has a remainder with two designated vertices and cup limit 1. Receipt `739ee383947782d1c2d2ebb2bb7f19e20f6f804fd1d5834ccf1a2ac4e252ce81`, commit `6b5dce7e7d26dc99172f89b72e9b4bebcefd51fc`. Actual DS split transfer has stronger premises than arbitrary formal `part`.

## Evidence locations

Shared journal snapshots: `journal-initial.json`, `journal-single-run.json`, `journal-multi-run.json` in this R24 directory; targeted live journal reads for unrestricted contraction and the R19 end-cut reconciliation.

Read-only historical sources in the primary checkout: `runs/claude-comb-reduction-20260929/HANDOFF.md`, `runs/claude-comb-closedform-20260930/HANDOFF.md`; R8–R15 handoffs; `runs/r18-sol-20261001/MATHEMATICAL-HANDOFF.md`; the R19 PEEL, END-CUT-RECONCILIATION, FLANK-SWAP, ABSENT-FLANK, K6-EXACT, K6-HISTORY and PART-FEASIBILITY handoffs. R3/R12/R16 accounts reside under `runs/worktrees/main-integration-20260928/runs/`. R23's worktree was not accessed.

## Next test and why it matters for generalization

Find the true maxima of the contraction profile and the R19 k6 profile using audited DS/SAT/class semantics. If the contracted B is too small, finite word resolution is missing attainable splits; if the expanded B is too large, a paired construction or base sharpness is failing. Compare optional-zone N with mandatory-run N separately. Then search bounded k=5..7 families for the smallest structural discrepancy rather than rerun already accepted B normal-form counterexamples.
