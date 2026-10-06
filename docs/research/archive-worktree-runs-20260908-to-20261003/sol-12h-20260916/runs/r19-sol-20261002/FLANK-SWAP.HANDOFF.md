# FLANK-SWAP: exact bound preservation

Agent `codex:01a0fc94-0467-7b90-823c-bce1e6fe6128`; R19 research window
`window-cc1a814a160145d6`; reviewed 2026-10-02 13:25 UTC.
Branch `node/CtxBoundEqFlankSwap`, independently based on
`e3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8`. No merge or push.

## Accepted theorem and receipt

`ErdosSzekeres.ctx_bound_eq_flank_swap` in
`ESBlueprint/B/CtxBoundEqFlankSwap.lean` is CLOSED. Its unchanged registered type
hash is `eaf60b57131f1361`. Original-source check
`20261002-092340-20d151` passed: Lean build 22.866 seconds, peak 805 MiB.
Receipt `882f635458f3cf58aef80fc3acbf82181564022088875761b02342a0811a0343`
is saved without truncation as `FLANK-SWAP.original-check.json`.
No sorry, blocked dependencies, uncovered or nonstandard axioms; only
`propext`, `Classical.choice`, `Quot.sound`. Axiom audit and layers pass.
All 378 inherited statement-lock objects are structurally unchanged.

The theorem concerns well-formed contexts with both first levels physically
present, on opposite flanks of every child, in either orientation, with arbitrary
older letters. Swapping their labels preserves the full recursive bound.
Different sides exchange their maxima. Equal sides use `(M,M-1)`, where
`M=max(m1,1+m2)`, with the stated legal-range assumption. Physical presence is
essential: merely vacuous flank predicates do not assert the intended mechanism.

## Why the equality holds

In every descendant, the designated pair shifts together to levels `L,L+1`.
Every new younger marker and every remaining child stays between the two flanks.
Taking a part commutes exactly with normalization, including the two list updates
to maxima. Both flanks remain present. Older markers need no position restriction.

For equal sides the admissible sorted level lists are unchanged. A walk using both
special levels keeps its list: its younger prefix remains between the flanks, and
there one flank step is inactive in each direction, so the two steps commute.
A walk using at most one special level permutes its labels and remains sorted.
This gives a two-way matching of full walk states, and hence exact left/right
extension counts for every truncation except `L+1`.

Presence of both flanks makes the between orientation unique. At the exceptional
interface, the first flank adds exactly one extension across the left and right
directions, on its own side. Therefore the two original strong terms are
`alpha+m1` and `alpha+1+m2`; their maximum is `alpha+M`. Both normalized terms
equal `alpha+M`, since `M>=1`. All other strong terms and the pure chain term are
unchanged. Cup/cap limits and single-run bases agree. Induction on recurrence fuel
then matches every cut and yields equality of the full bounds.

For different sides the proof reuses the existing certified
`ctx_bound_opposite_level_swap`, which already permits arbitrary word geometry.

## Searches, failures, and diagnostic evidence

Searches before drafting: `es search 'adjacent levels flank commuting extension walk'`
and `es search 'levelsOn append singleton extension count'` found no existing
matching helper. Searches for `ctx_bound_opposite_level_swap`, the merge theorem,
and extension/part transport identified the reused certified implementation.
`MergeLevels.ctx_ext`, `MergeLevels.sublist_of_pairwise_lt`, and the existing
part/step lemmas are reused rather than exported as duplicate statements.

Meaningful compiler failures were logged before repair. Jobs
`20261002-090013-c63e2a`, `20261002-090524-3cec61` failed at record layout;
`20261002-090621-740fa8`, `20261002-090740-53344a` at local context inference and
the shifted-level arithmetic fact; `20261002-090942-528a56` at unrestricted simp
rewriting filter options before their equations and map-congruence;
`20261002-092005-3dea3d`, `20261002-092227-3fd43b` at substitution direction,
literal True conditionals, and definitional `norm.k` equality. None exposed a
mathematical counterexample. Intermediate compiling bodies retained one explicit
placeholder and received no theorem credit.

The broad finite diagnostic `20261002-084644-b079e0` checked 161,280 k=5 contexts
with one older marker in every gap, including outside the flanks, all legal axes
and maxima, both orientations and flank multiplicities 1..2. It found no differences
in 12.713 seconds / 20 MiB. `FLANK-SWAP.OUTER-LETTERS.k5.jsonl` records it.
The clean absent-level diagnostic `20261002-083642-6bb0ca` found bounds 10 and 4
for the vacuous `SS` case at `(5,5,6)` with maxima `(1,2)` before normalization.
These evaluator results are diagnostic, not kernel-certified counterexamples.

## Review and remaining research

The body and the run's probe were self-reviewed under the fixed Sol-only contract;
an Astra/coordinator review remains available at integration. The probe reuses
`harness.research.context_bound.compiled_evaluator`, closes its persistent memo,
has explicit finite coverage and progress output, and is one-off mathematics.
No new general workflow or evaluator was introduced; no library promotion is
needed for this probe. The reusable mathematical result is the registered theorem.

PEEL remains open: an arbitrary child should attain a singleton cut in every legal
context with globals at least four, at least two runs, and bound at least two.
The cost-based child-selection principle is still unproved. FLANK-SWAP resolves
the outer-flank rotation calculation; it does not settle the interior selection or
the stalled sibling penalty. The next work is exact registration with a falsifier,
then explaining the k=6 middle-child examples and testing the binding-cost proof
idea without another unsupported narrowing.

Commit `e05ed9a3a90443aff49d04047dda17f97ba4627b`, created by guarded commit
job `20261002-092657-69e739`. Only this node's module, root import, lock and
generated node/status records are committed. The worktree is clean.
