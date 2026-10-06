# R6 mathematical handoff

Agent: `codex:agent-run-f0f2579383bd4d30`, gpt-6.1-sol at xhigh; no delegation.
Branch: `node/CtxBoundAdditiveSingleRunOfRunContractionAndAlternating`.
Baseline: `5d58845b64c80c52f843290e31fa573398ebdd9f`.
Fixed research deadline: 2026-09-30 11:10:47.215813Z.

## Exact obligation and present state

Prove `ErdosSzekeres.ctx_bound_additive_single_run_of_run_contraction_and_alternating`
exactly as the second theorem in `GlueStatements.lean`: single-run additivity for both
orientations, arbitrary membership-based `keep`, and every admissible `d`, assuming explicit
C1 (adjacent child contraction when the child span contains only child/ext-1-side letters)
and C3 (alternating singleton partitions).

The exact theorem has a complete scratch proof, `GlueProof.lean`. Guarded job
`20260929-212539-aec410` passed with rc=0, 6.9 seconds, peak 592 MiB, and no missing outputs.
Lean printed precisely `propext`, `Classical.choice`, `Quot.sound` as its transitive axioms.
The statement bytes match the approved template. The certified source before review cleanup
is preserved as `GlueProof.accepted01.lean`, with its hash in `compiled-scratch-01.sha256`.
The cleaned version passed guarded check `20260929-212807-066210`, rc=0, again with
exactly those standard axioms. Evidence: `compile-12.log`, `receipt-scratch-clean.json`,
`compiled-scratch-clean.sha256`.

The first `es node add --targeted` attempt was refused because 20 GiB cannot fit the shared
30 GiB budget. It retained the exact node module stub and its root import, with no lock entry.
The exact retry arguments and thirteen memory refusals are in `REGISTRATION.json`.
No inadmissible 20 GiB job was queued. At 05:50Z shared solver job
`20260929-154930-35aca9` finished, rc=0, leaving only two 2 GiB hosts live. The direct retry
then met the sandbox's unreachable systemd bus. The same request was submitted as fitting
guarded worker job `20260930-015047-f6d4f9`, output `registration.log`.
Registration passed: rc=0, 203.5 seconds, peak2481MiB, no missing outputs;
`receipt-registration.json` and `NODE.registration.json` preserve the receipts. The node
was claimed and only its proof/imports/open/options were changed. The exact binder/type
bytes match the registered stub and approved scratch theorem.

Guarded targeted check `20260930-015830-a40734` closed the registered node: rc=0,
98.5 seconds, peak2344MiB, no missing outputs; the build phase was5.452 seconds.
`targeted-check.log`, `receipt-targeted-check.json` and `NODE.closed.json` certify
`sorry=false`, exactly `propext`, `Classical.choice`, `Quot.sound`, no nonstandard or
uncovered axioms, and `lock_ok=true`. The type hash remains `8a8e1b43f96a9e11`.
`module-before-check.sha256` still matches the accepted registered source.
Whole-source proof fixture: `1745cbdfcf863496af76be0374040f63440e00c4d2ddbf72ec0f34ddfa0c56bc`.
Proof commit: `0613cea1565ddb9ba7186c373ce37e2d05d755de`, on the authorized branch only.
Guarded commit job `20260930-020442-cd2bc6` passed, rc=0; `proof-commit.log` and
`receipt-proof-commit.json` preserve it. The commit contains the new node, root import and
generated node index/status/statement lock. Claims are released: new conditional node
closed, original unconditional consumer partial. Only evidence-bundle consolidation and
fixed-deadline reporting remain; the mathematics is complete.

## Proof argument

1. A nonempty context with at most one child run has child positions `range' off n`.
   Reconstruct its word as `L ++ replicate n child ++ R`, with no children in `L ++ R`.
2. Encode keep membership by a Boolean list `bs` of length `n`. The word of its part is
   `map shift L ++ paint side bs ++ map shift R`; the complement uses `map not bs`.
   Both identifications are exact context/list equalities.
3. Induct strongly on `bs.length`. If two neighboring labels agree, remove one.
   A kept double letter contracts by explicit C1; a discarded double letter contracts by
   the closed `ctx_bound_external_letter_contraction`. Each part has the C1 span shape
   because any position between its child endpoints lies in the parent's child interval.
   Apply the same transport to the complemented labels and both orientations.
4. Shortening the positive parent child run preserves its base by the closed
   `ctx_base_child_letter_contraction`. Both parents have at most one run, so their bounds
   are their bases. External-membership transport preserves well-formedness.
5. If no equal neighbors exist, the Boolean list is exactly `decide (i % 2 = r)` for an
   `r < 2`. The canonical keep list equals the one in C3; zeta-reduce C3's keep binder and
   rewrite its complement before applying the explicit C3 hypothesis.
6. Original `keep` duplicates cause no problem: `part_congr` uses membership only.
   Nonempty keep gives a true label. If no false label existed, the distinct child positions
   would all occur in keep; finite-cardinality bounds would give `n <= keep.length`,
   contradicting the original strict `hall` hypothesis. No new nodup assumption is used.

Source checkpoints in `ESBlueprint/B/CtxBoundAdditiveSingleRunOfRunContractionAndAlternating.lean`:

| Obligation | Local proof and line |
| --- | --- |
| Child interval and literal-word reconstruction | `hInterval` 54; `hReconstruct` 422 |
| Parent run count, bound/base and positive-run base invariance | `hRunCount` 257; `hRunBase` 284; `hBaseRun` 290 |
| Painted part, complement and exact relative-index parity keep | `hPartPaint` 355; `hComplement` 376; `hParityKeep` 400 |
| Adjacent-repeat/parity dichotomy | `hDichotomy` 475 |
| C1 span and paired contraction | `hSpan` 504; `hPaintContract` 520 |
| Strong induction and duplicate-keep bridge | `hAll` 554; `hmember` 637; `hf` 656 |

The local span statement needs only `childPositions = range' b n`; well-formedness and
the parameter range enter when applying contraction to the parts. C3's parity is on the
relative child index, and `hParityKeep` transports the word offset exactly. The final
complement-nonemptiness argument uses the nodup child list and finite cardinality, while
`keep` may have duplicates. These are accepted local proof steps within the closed glue
theorem, not separately registered helper nodes.

## Accepted helpers and receipts

- `Bookkeeping.lean`: Boolean adjacent-repeat/parity dichotomy and C1 span condition for
  interval parts; job `20260929-211359-4eefd2`, rc=0, `compile-02.log`.
- `Groundwork.lean`: interval/WF/base word transport, Boolean keep membership, painted part
  words, complemented keeps, exact parity keeps and word reconstruction; jobs
  `20260929-211636-a5d026` and `20260929-211732-2f1a21`, rc=0,
  `compile-06.log` and `compile-07.log`.
- Exact glue scratch theorem: job `20260929-212539-aec410`, rc=0,
  `compile-11.log`, `receipt-scratch.json`, `GlueProof.accepted01.lean`.

Scratch receipts certify their indicated sources. The separate targeted receipt above
certifies the registered-node closure.
C1 and C3 remain hypotheses. This run proves neither of them and does not establish
unconditional single-run additivity or the full happy-ending conjecture.

## Failed work and reusable diagnostics

- `compile-01.log`: parity arithmetic before Bool normalization; fixed by simplifying cases.
- `compile-03.log`–`compile-05.log`: GetD import/rewriting, append congruence and complement
  map length normal forms. Use explicit GetD rewrites and retain keepOf inside predicates.
- Job `20260929-211954-2f448d` was explicitly cancelled (rc=-15) after a live three-minute
  stall. Source `GlueProof.attempt01.lean`, log `compile-08.log`. Reused `simp_all` helpers
  saw the new universal C1/C3 hypotheses and could attempt broad recursive rewrites.
  Replacing them with local simplifications made the next compile finish under a minute.
- `compile-09.log`: explicit getElem case equations, toFinset cardinality argument lists,
  and recursive simp expansion of `childPositions = range' off childPositions.length`.
  Rewrite that equality once with `rw`; do not place it in a recursive simp set.
- `compile-10.log`: C3's let binder blocked complement rewriting; zeta reduction fixed it.
  Use current `List.length_eq_zero_iff` API.
- Installation validation caught a numeric proof-delimiter offset before any edit;
  using the delimiter's actual length repaired the source assembly. Exact statement/body
  comparison and the subsequent targeted compile certified the installed source.
- Thirteen memory refusals and one sandbox-bus refusal preceded guarded registration.
  No compiler failure or proof credit arose from them. All receipts are in `REGISTRATION.json`.
- An unqualified usage sync inherited an earlier explicit window and refused reassignment.
  Explicit-window sync reconciled the snapshot without changing prior allocations.
- Local git staging met read-only sandbox metadata. First guarded commit preflight
  `20260930-020359-3dbb96` failed rc127 because the worker lacks rg, before staging.
  `proof-commit.attempt01.log` and `receipt-proof-commit-failed.json` preserve it.
  Built-in branch/HEAD comparisons with `/usr/bin/git` passed in the successful job above.
- An artifact patch rejected delete/add operations on one report path before edits;
  a single update operation repaired the report assembly. The committed proof was untouched.

No mathematical conjecture was refuted and no structural bookkeeping obstruction remains.
All diagnostics and the plan change were recorded in the shared harness before follow-up.
Error-recovery `sorryAx` in failed compilations was never treated as theorem evidence.

## Review and library disposition

Reviewed the child-span bounds (including the default beyond-word letter), well-formedness,
both painted-word contractions, the unchanged parent base, induction decrease, parity
identification and the duplicate-keep argument. Removed a duplicated run-count proof and
one unused external-run helper. Proof body lines fit 100 columns; the exact supplied
statement was preserved.

Reused existing local proofs and `part_congr`; introduced no solver, evaluator or execution
workflow. One-off source assembly and source/receipt inspection commands are preserved in
the journal/client transcript. No recurring algorithm warrants promotion in this trial;
local Boolean/list facts can be considered for core-library extraction during later review.
Shared library edits are outside this run's authorized scope. Review usage is recorded
separately from research. No other agent/model was invoked; final mathematical and code
review was performed by this configured Sol model under the no-delegation contract.
The installed body is exactly the reviewed scratch body. Reviewed the two guarded
registration/check shell commands (only exact es calls and output redirection), bounded
read-only monitoring/retry orchestration, and generated metadata. No tracked script changed.
The statement lock adds only this node; existing theorem statements are untouched.

## Safe next action

Review proof commit `0613cea1565ddb9ba7186c373ce37e2d05d755de` and address C1/C3
separately. This trial proves the conditional reduction and does not prove either
hypothesis. The exact remaining mathematical obligations are C1 and C3 as quantified in
the theorem header; no list/position glue obligation remains. Within R6, preserve this
result for final consolidation at 10:40:47.215813Z and reporting at or after 11:10:47.215813Z.
Do not run a full extract, merge, push, edit other statements or start another trial.
