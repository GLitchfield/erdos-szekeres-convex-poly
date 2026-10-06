# Independent final review

This review concerns the single Sol/xhigh host job `20260928-132926-6df35b` and the target `ErdosSzekeres.ctx_two_actual_marker_small_history_internal_chosen_kept_cut_six_bound`. The harness interrupted research at the fixed `2026-09-29T05:31:24Z` deadline and entered bounded finalization. No second trial was started.

## Mathematical trust result

The target is **open**. The terminal guarded check `20260929-010130-71d5cc` passed compilation, but its detail receipt `d8cc704edf7ffb3cf4ec5c97e849c84b18f29a0ec0ee0fc4874d79e3775b7418` reports `sorry: true` and axioms `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The source contains exactly two explicit `sorry` terms, at lines 3605 and 4024 of `ESBlueprint/B/CtxTwoActualMarkerSmallHistoryInternalChosenKeptCutSixBound.lean`. The type hash remains `afc74d2efdb0115f`; the captured whole-declaration fixture is `82e1af28fe183aa37968dfd613a5cc9083f9809f978280a1c99a5da1fc6da54a`. This is a checked partial proof, with **zero accepted theorem credit**.

The first admission is a fixed-fuel endpoint exclusion in the middle two-arm cut: the checked outer envelopes are `C ≤ 10`, `D ≤ 2` and the checked inner envelopes are `C ≤ 9`, `D ≤ 3`; one must exclude simultaneous `(10,2)` or `(9,3)`. The second admission is `boundFuel g (B.part R t 1) ≤ 10` in the swapped extreme two-arm cut after all-active and all-small cases have closed. Its remaining context has actual markers and separated mixed-capacity witnesses on both axes. Exact hypotheses and evidence paths are in `MATHEMATICAL-HANDOFF.md`.

The finite evaluator probes are diagnostic. In particular, the witnessed `C = 9, D = 1` case rules out a standalone `C ≤ 8` strengthening while preserving the desired sum; a separate outer witness rules out `D ≤ 1`. Neither is a Lean-certified counterexample to the target.

## Code and command review

I inspected the immutable run-review inventory `f16b94b3710edd78232ee901698b98ab2ad8e5bd5fe5e28006f8fd722fc8a2f2`, the run's eight Python probe scripts, and the four sanitized inline commands it lists. The scripts import the registered `harness.research.recursive.evaluator` and shared `part`/`extension` primitives; their only file writes are the declared JSON outputs. They contain no process spawning, shell invocation, network access, certificate generation, or tracked workflow edit. The inline commands are three evaluator probes and one `py_compile` plus probe invocation, all directed to the run directory. The review inventory reports 135 jobs and no pending or unknown jobs at its snapshot. Its hashes and command inventory are evidence of execution and scope, not proof credit.

The diagnostic drivers have task-specific enumeration, pruning, and rectangle-partition code without a Lean-equivalence certificate or stable regression fixture. There is no recurring, validated API to promote to `harness/research/` or `tools/es/es/` from this trial. Promotion is deferred. The sole tracked delta is the target Lean module. This review does not treat its local helper facts as accepted standalone theorems because the enclosing declaration still depends on `sorryAx`.

The terminal run review artifact is `c0fb35e35d1513e553735b35f2c6cff1cdc4caf55bfd367167672f2fb98292be`. It reports 135 jobs, no pending or unknown jobs, 93 validation-evidence records, and no explicit accepted proof receipts. Reconciled native usage is 2,994 responses (89 late): 426,050,909 input tokens (416,648,320 cached), 1,318,477 output tokens, and 588,559 reasoning-output tokens. Coordinator monitoring and review usage are separate. A mistaken coordinator usage import into Sol's window was backed up and corrected by session ID and timestamps; the shared journal records the repair, and Sol's research window again contains only its 2,905 in-window responses.

The coordinator monitoring window `window-914f7c04b77e4f94` ended complete with 1,286 responses, 155,971,905 input and 195,704 output tokens. The independent review window `window-d42940ca3c1d4369` ended complete with 78 responses, 16,574,982 input and 22,264 output tokens after a final usage sync. These windows are reported separately from the native Sol total; imports cover recorded responses and later reporting can still add outside-window records.

## Repository disposition

Preserve `MATHEMATICAL-HANDOFF.md`, `REPORT.sol.md`, JSON probes, and the checked partial proof. Release the coordinator-owned claim as partial after terminal host finalization. Commit and push the reviewed Lean delta to `main` under the user's earlier authorization, using the separate integration worktree so the primary checkout's unrelated edits remain untouched. Record the final commit and CI result in a follow-up journal entry.

Completed: the claim was released as partial. Node commit `089bdd46` was cherry-picked as integration commit `21cdd7ad1bebffa777deb1e666642ae6d5bb7796`, then normally pushed to `origin/main`; local `main`, `origin/main`, and integration `HEAD` agree. Guarded targeted check job `20260929-013801-279eac` passed on the integrated source and still reported `sorryAx`. The primary checkout's modified `ESBlueprint.lean` and untracked `harness/dataset/ctx_end_cut_normal_form/` were untouched. The shared journal records the push and check.

CI was later checked: [run 36527336768](https://github.com/GLitchfield/erdos-szekeres-convex-poly/actions/runs/36527336768) completed successfully on `21cdd7ad`; `harness-tests` and `layers` passed. The workflow skipped `lean` and `pr-shape` on this push. The local guarded targeted check remains the compiler evidence for the target and does not remove `sorryAx`.
