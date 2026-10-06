# R10 mathematical handoff

Status at 2026-09-30 15:59 UTC: the registered bridge is closed and committed
as `b58edc4cc368f92dbbf26a3aa0f3cbdfdbcbe745` on
`node/CtxBoundPartRunContractionOfOneLevelRoot`. The worktree is clean.
The targeted check and commit jobs are terminal with rc 0.

Exact obligation: prove
`ErdosSzekeres.ctx_bound_part_run_contraction_of_one_level_root`, with the
registered universal root-contraction premise `hroot`, for every well-formed
context `σ` with `σ.numRuns ≤ 1`, arbitrary `keep`, side `s`, and
`1 ≤ m ≤ σ.k - 2`, whenever the part word contains the displayed adjacent
child pair. The exact original statement and docstring are preserved.

The proof reconstructs the nonempty ancestor run as
`L ++ replicate N child ++ R`. A deleted kept child at `p = left.length`
gives `small.word = σ.word.eraseIdx p`, still a run of size `N - 1`.
The contracted part is `small.part kept s m`, where `kept` is the ordered
pullback of `keep` through `up p i = if i < p then i else i + 1`.

`ctx_single_run_descendant_bound_normalize` applies to both parts with
`D = 1`. Its hypotheses require positive labels and contiguous ancestor
children, and do not require well-formedness of the normalized raw context.
The two normalized contexts have identical parameters: ordered external
position transport preserves both limits at `up p b`, and
`ctx_point_limits_eq_of_child_interval` identifies that point with `b`
inside the original run. The normalized parameters are `capLimit b b + 1`
and `cupLimit b b + 1`, both between `1` and `k`.

The older letters in `L` and `R` shift to levels at least `2`, while the
normalized maxima list is `[m]`. An exact local fuel induction deletes an
inert letter at either word end. It transports child positions, active
external positions, side selectors, extension folds, bases, blocks and
parts. End deletion preserves run starts in every descendant, so it proves
equality for every fuel without isolated-child or well-formedness premises.
Repeated deletion strips the old prefix and suffix. Filtering by
`child ∨ level = 1` produces the displayed pair in the remaining word over
`{child, ext 1 s}`, allowing direct application of `hroot`.

Accepted inputs: the two imported normalization/point-limit nodes were
already closed with standard axioms. New scratch receipts:

- `20260930-113454-900ba6`: exact inert-end transport, rc 0.
- `20260930-114039-49c421`: assembled local helper checks, rc 0; outer
  conclusion `True`, so this is diagnostic helper evidence only.
- `20260930-114807-1296db`: the full exact-statement candidate, rc 0,
  19.9 seconds, 682 MiB peak, no missing outputs. Candidate SHA-256:
  `42d838fcee6d857b9e06f772fee58465e99d200ea898ae5d0b6cef37c379c899`.
- `20260930-115406-87ab9e`: targeted `es check` of the registered module,
  rc 0, 114.9 seconds, 2353 MiB peak, all outputs present, no OOM or budget
  event. Receipt
  `1de650ee0589affa54d452e27dea92de8232cb6e90707dc829ef09e76276b046`,
  copied to `TARGETED-CHECK.json`, reports `status=closed`, `sorry=false`,
  no uncovered axioms, exactly `propext`, `Classical.choice`, `Quot.sound`,
  and unchanged type hash `15a30a4e651354ba`. The module build took 22.49 s.
  Extraction was targeted and incremental; no full extraction ran.
- `20260930-115816-9fe979`: `es node commit`, rc 0. It committed exactly
  the node module plus generated `harness/nodes.json` and
  `harness/status.md`, with no files left uncommitted.

Failed attempts and infrastructure:

- `20260930-113359-21b5e2`: suffix predecessor rewrite affected both sides;
  fixed with `conv_lhs`.
- `20260930-113846-5792f7`: append associativity/lookup and middle-map
  congruence errors; fixed with explicit list identities.
- `20260930-114417-d65dc5`: uncached mathlib erase module, before elaboration;
  replaced by the core `Init.Data.List.Nat.Erase` import.
- `20260930-114455-8b1f66`: record indentation and erased-part length.
- `20260930-114613-5d6f72`: propositional part length, arithmetic,
  self-rewriting run-size simplification, and missing ext case equation.
- `20260930-114727-a2a2cc`: redundant `omega` after a solved length goal.
- A 4G admission request was refused at 29G live reservations; subsequent
  compiles were queued explicitly. Initial targeted-check queue entry
  `20260930-115042-a5d00c` chose a 20G fallback cap because the sandbox
  could not verify dependency freshness. It was cancelled while unstarted;
  no compile or coverage was interrupted. The identical targeted check
  succeeded inside the 6G worker job `20260930-115406-87ab9e`.

Artifacts: `EndpointTransport.lean`, `BridgeScratch.lean`,
`AssemblyTail.lean`, `BridgeCandidate.lean`, `NodeCandidate.lean`, and the
registered node module. All job logs are in the shared harness journal.
No auxiliary axioms, `native_decide`, or new `sorry` were introduced.

No mathematical obligation remains for R10. The root contraction theorem
itself remains an explicit premise and is not proved by this bridge. The
coordinator's review/integration is the safest next action; no second trial,
merge, push, or full extraction is authorized. No tracked scripts or new
workflow glue were introduced. R8/R9 local Lean transports were reused;
promoting the inert-end equality to an independently registered reusable
node is deferred because this trial is restricted to one node and module.

Research window: `window-873fe0c3430041b4` (ended, one accepted result).
Final mathematical review: `window-214a569e709d45d5`. Review checked the
exact premise, every normalization hypothesis, zero-capacity cases allowed
by `hroot`, ordered keep transport, fuel preservation under inert end
deletion, the source/lock identity, actual axiom receipt, and commit scope.
This review was performed by the configured Sol model; no model change or
delegation occurred. Maintenance review `window-d9dddfc11b634533` is also
ended. The coordinator subsequently verified `TARGETED-CHECK.json` and the
module and ended research early at 2026-09-30T16:00:47.382560Z. The user
made that instant the research deadline; this turn performs finalization
only, without new research or compilation.

The implicit usage reconciliation refused to move an already attributed
response into another explicit window. Reconciliation with the original
research window preserves that attribution; the single long response is
not split across the separately recorded review/maintenance windows. No
usage-savings claim is asserted. `HARNESS-HANDOFF.json` preserves the factual
operation and usage records. The claim is released closed with this handoff;
no job or mathematical work remains pending in R10.

The release command automatically preserved this handoff under the primary
checkout's `runs/r10-sol-20260930/`; no primary source file was edited.
