# R9 mathematical handoff

Worktree: `runs/worktrees/main-integration-20260928`.
Branch: `node/CtxBoundAdditiveSingleRunAlternatingOfRunContractionAndDeletion`.
Agent: `codex:01a0f26d-e09b-7080-9c4e-2bf4a8d1ab7c`, configured
`gpt-6.1-sol` / `xhigh`; no delegation.

## Exact obligation and trust boundary

Prove the fixed registered theorem
`ErdosSzekeres.ctx_bound_additive_single_run_alternating_of_run_contraction_and_deletion`,
type hash `2f0a94ddbcb29ccf`. For a WellFormed context with at most one run,
at least two children, parity `r < 2`, and `1 ≤ d ≤ k-2`, the registered
alternating keep list and its child-position complement satisfy both oriented
additivity inequalities. Assumptions remain explicit:

- C1: adjacent child contraction preserves bound when every strict internal
  child span contains only child letters or external level-one letters on the
  specified side.
- DelMono: deleting an external letter from a WellFormed context with isolated
  children cannot decrease bound, provided another letter of that same level
  and side remains.

R9 proves the reduction. It does not prove C1 or DelMono, or unconditional C3.
The registered signature and docstring are unchanged. Header equality is
recorded in `STATEMENT.original.lean.txt` and `STATEMENT.candidate.lean.txt`.

## Proof and reusable observations

All helpers are local `have` bindings inside the fixed theorem. R6 machinery
is reused from `CtxBoundAdditiveSingleRunOfRunContractionAndAlternating.lean`:
`hCtxEq`, one-run interval/reconstruction, preservation of WellFormed under
word replacement, child positions of a block, bound-to-base and base transport,
Boolean keep/paint, and parity/complement bookkeeping.

Write the parent word as `L ++ replicate n child ++ R`, with no children in
`L ++ R`. Boolean labels select children; false labels become `ext 1 side`;
old external levels shift by one and maxima become `m :: parent.maxima`.
`alt n b` alternates the Boolean labels, starting at `b`.

`hPaintIsolated` proves no two retained children are adjacent, using the
alternating-label property and R6's exact child-position filter.
`hPaintDelete` applies DelMono to a false label and identifies the deleted-word
context with the part of a parent shortened by one child. An explicit second
false label supplies the retained same-level letter.
`hPaintTrueContract` reuses R6's word/span machinery to apply C1 to two adjacent
true labels and identify the part of a parent shortened by one further child.

`hShorten` combines those operations for every side and admissible maximum:
an alternating `(j+4)`-child part has bound at most its `(j+2)`-child part.
For true-start labels, delete the separator at original index 1, then merge
the two teeth at indices 0 and 2. For false-start labels, delete the separator
at index 2, then merge indices 1 and 3. The two paired parts thus remove
indices `{1,2}` in the original parent. The outer word and all context fields
other than word remain identical; the new maxima are identical as well.

`hAll` performs strong induction on `n`. At `n=2` it invokes the closed
prefix/suffix theorem with lengths `(1,1)`. At `n=3` it invokes the closed
singleton-ended sandwich theorem with middle length 1. False-start cases swap
the two inequalities and commute the sum. For `n≥4`, shortening is applied
to both parts with the same coupling and side, followed by the induction
hypothesis. Parent bound equality follows from the single-run base reduction
and R6's repeated use of `ctx_base_child_letter_contraction`.

Finally, interval reconstruction and `hParityKeep` identify the registered
getD/filter keep list. `hComplement` and `hAltNot` identify its complement.
The proof covers both residues, both orientations, every WellFormed external
context, and every allowed coupling.

## Receipts and current state

- `20260930-091036-e68c6b`, `baseline.log`: closed bases and base contraction
  available; each uses only `propext`, `Classical.choice`, `Quot.sound`.
- `20260930-091123-25e15a`, `helpers-01.log`: copied R6 helper block compiles.
- `20260930-091520-b0efeb`, `Parity.lean` / `parity-01.log`: parity helpers pass.
- `20260930-091633-9c87fa`, `Helpers-03.lean` / `helpers-03.log`: isolation,
  separator deletion, and true-child contraction helpers pass.
- `20260930-091803-0dd131`, `Helpers-04.lean` / `helpers-04.log`: shortening passes.
- `20260930-092105-0ec2df`, `Helpers-06.lean` / `helpers-06.log`: induction passes.
- `20260930-092305-f4b7af`, `Target.lean` / `target-02.log`: full fixed statement
  passes in 17.11s; `#print axioms` lists exactly the three standard axioms.

Targeted check `20260930-092622-ee8406` completed rc=0, cgroup peak 2362 MiB;
its durable output is `targeted-check.log`, which names immutable artifact
`a5c33d421cad204e34c740c56f576815f14c19fed0906008e24ca39599d0f153`.
The full receipt is copied to `CHECK-RECEIPT.json`: status closed, sorry false,
axioms exactly the three standard axioms, uncovered axioms empty, unchanged
type hash `2f0a94ddbcb29ccf`, targeted true, incremental true. Node build took
22.774884462356567s. The initial generic async check
`20260930-092404-84d216` was cancelled while queued, before any process or
compile started, because its 20G reservation blocked admission. The replacement
invokes the identical `es check <node> --targeted` under a guarded 6G reservation.
No full extract has been requested.

Commit job `20260930-092916-755d72` completed rc=0 and produced
`4cf96422ce0f5b6d99ad03d3eaa703c6333470f4`. Exactly the target module and derived
`harness/nodes.json` / `harness/status.md` are committed; working tree is clean.
Research window ended with one accepted result. Separate final review and
maintenance account is in `CODE-REVIEW.md`.

Consumer validation `20260930-093734-c64ab7`, `ConsumptionInline.lean` /
`consumption-inline.log`, passed rc=0 in 10.00s. It imports committed R9, includes
the unchanged R6 source, and supplies R9 directly as R6's alternating hypothesis.
The anonymous example obtains arbitrary-keep single-run additivity from explicit
C1+DelMono. Both named theorem axiom prints are standard-only. This is consumer
validation, with no new registered theorem or extra closure credit.

## Failures and their resolutions

All are compiler bookkeeping failures, not counterexamples or failed
mathematical routes. Sources and logs are retained.

- `20260930-091301-d536b3`, `Helpers-02.lean` / `helpers-02.log`: two
  `decide membership = true` versus propositional-membership errors in
  `hPaintIsolated`. Fixed by `of_decide_eq_true`. Broad `simp_all` made this
  compile take 127.05s; narrow simplification/direct Boolean contradiction
  reduced subsequent compiles to about 13–17s. Its progress checkpoint was
  reviewed; it was never killed.
- `20260930-091940-8e153f`, `Helpers-05.lean` / `helpers-05.log`: n=3 sandwich
  endpoint `1 + (L.length + 1)` versus `L.length + 2`. Fixed by associative
  and commutative addition normalization.
- `20260930-092200-5cd7e6`, `Target-01.lean` / `target-01.log`: a cyclic parity
  equivalence caused simp recursion depth; splitting the two residues fixed it.
  Complement rewriting also changed the RHS child count to an interval-list
  length; explicit `List.length_range'` and Boolean-list length fixed it.
  That failed compile's `sorryAx` print is error recovery, not an accepted proof.
- Full `es status` in this checkout crashes on a historical string-valued
  release detail. `es status --brief --full` works. The shared journal names
  primary fix `f397b708`; R9 does not edit the harness or primary sources.
- Final consumer job `20260930-093115-e67f81` failed before elaboration because
  the existing R6 module lacked a cached olean. Job `20260930-093539-394b00`
  successfully scratch-compiled unchanged R6 source in 12.78s, then its partial
  import overlay shadowed the existing R9 olean path. Those are infrastructure
  failures, not mathematical failures. Source-based consumer validation
  `20260930-093734-c64ab7` resolves the intended type/axiom check without any
  cache/source mutation outside R9 artifacts.

## Open questions and safest next action

There is no remaining R9 proof obligation. C1 and DelMono remain external
obligations. The coordinator can review this conditional reduction and later
combine proven hypotheses with it and R6's glue. Do not launch another trial,
merge, or push from R9.

Research deadline is fixed at `2026-09-30T21:08:02.442541Z`; consolidation starts
at `20:38:02.442541Z`. The native goal must remain active before that deadline
even if theorem work finishes early. Preserve all receipts on interruption.

Only the native goal's user-set time gate remains pending. Host job
`20260930-090758-d1f606` is verified running; no R9 compiler, check, or commit
job remains pending. Do not extend/reset the host deadline or start another trial.
The report can be finalized and goal marked complete only once the required
instant has passed and the completion audit still matches the committed state.

Claim released closed at 13:43 UTC, with this handoff linked. `es release`
automatically mirrored the handoff into primary `runs/r9-sol-20260930/`, as its
output announced. This is a harness evidence-preservation side effect, alongside
primary-resolved shared state; no primary source or branch was edited manually.
Do not clean up primary artifacts from R9. Monitoring is separately recorded
in `window-db64cc753d174d55` with an observational 10,000-output-token target.
