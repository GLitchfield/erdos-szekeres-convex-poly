# Exact older-exterior companion, one fixed 12-hour trial

## Identity, scope, and starting state

Coordinator thread: `01a0e90e-755d-75d0-a9d8-15eadb32fd28`.
Use this checkout, `runs/worktrees/sol-12h-20260916`, branch
`node/CtxTwoActualMarkerSmallHistoryInternalChosenKeptCutSixBound`, starting HEAD
`322f1c38`. Preserve the existing uncommitted edit in
`ESBlueprint/B/CtxTwoActualMarkerSmallHistoryInternalChosenKeptCutSixBound.lean`.
The primary checkout has unrelated changes; leave them alone. This is the only
research trial. The host fixes its twelve-hour deadline on pickup; never reset it
on recovery. Do not start a second trial.

Target:
`ErdosSzekeres.ctx_two_actual_marker_small_history_internal_chosen_kept_cut_six_bound`.
Read the complete exact declaration at line 18 of the target file before editing.
The only literal `sorry` is the final older-exterior, chosen-global-five,
opposite-global-five branch at line 187. The theorem assumes actual indexed
chosen markers `x ∈ σ.extPositions N`, `y ∈ σ.extPositions M`, `N < M`,
distinct sides `s ≠ t`, positive external levels, exactly the chosen-side
markers `x,y`, their maxima at most one, an internally bracketed nonempty
convex child interval `keep`, `m+2=σ.k=6`, `1≤n`, and `m+n=σ.k-1`.
Consequently `m=4`, `n=1`, `A=σ.part keep s 4`, and
`B=σ.part (σ.childPositions.filter (· ∉ keep)) t 1`.
The checked proof already gives `∀f, boundFuel f A≤1` and `A.bound≤1`.
Prove `∀g, boundFuel g B≤11` and `B.bound≤11` under the **actual marker,
cut, and transport hypotheses**, then discharge the sum bound 12.

## Existing mathematical evidence

Read `runs/older-exterior-truth-20260924/obstruction.md` first, plus the
node-filtered journal since September 16 and the latest handoff. The checked
`ctx_two_marker_older_exterior_internal_interval_cut_potential_bound` has
type hash `3ba83b22399bb37f`, sorry false, standard axioms only. It bounds
the companion by 12 at opposite global five: far group ≤3 and near group ≤9
are separate charges. Splitting at retained opposite marker gives weaker
original-history charges 8 and 6 for the clean three-child witness.
The checked `ctx_two_actual_marker_companion_maximum_bound` has type hash
`48fd722ebea4ebd3`, sorry false, standard axioms. In the relevant recursive
opposite parts, sibling maximum 2, 3, 4 yields bounds 8, 4, 1.
The first maximum-2 case can pair an 8 charge with a chosen-side straddling
part charged 4. Investigate the coupled claim that an opposite recursive
part actually reaching eight forces the chosen straddling part to ≤3;
handle the analogous other maximum cases. This one-unit incompatibility is
the conjectured missing step, not a proved lemma. Preserve the synthetic
opposite-axis marker and its endpoint effects in every recursive transport.
The checked younger-exterior companion-eleven theorem has type hash
`659c2ef5b137dd59`, sorry false. Between-marker eleven is also compiled.
Their proofs may offer reusable transport tactics.

The registered `context-bound-zero-children-v1` Python evaluator ran on
`[S,S,2L,3L,S,S,1U,S,S]`, child maxima `[1,1,1]`, in job
`20260924-182140-c135a6`; it returned `B=11`, `A=1` after 820.4 s,
195 MiB peak. See `runs/older-exterior-truth-20260924/exact_222.json` and
`exact_222.py`. Other diagnostic finite probes there cover zero maxima,
an unindexed barrier, and selected larger patterns. They have no Lean
equivalence certificate. Witness compression is unproved: deleting children
may invalidate a `numRuns>1` cut, while retaining a run witness may change a
positive part. No finite negative sweep is theorem credit.

The prior source passed targeted `es check` on September 24 while still
reporting `sorryAx`; journal entries at 20:24 and 21:31 record the checks.
`es node show` still reports target type hash `afc74d2efdb0115f`,
`sorry: True`, `sorryAx`. The uncommitted edit closes only the
opposite-global-at-most-four branch; preserve it.

Before any new lemma, run `es search` for the exact statement and record the
result. Coordinator startup searches for the coupled bound and older-exterior
eleven gave no exact result; a transport search found boundary and between
companion lemmas. Read their precise hypotheses before use.

## Workflow and evidence contract

Set `ES_AGENT` to the host's supplied researcher id. The coordinator claimed
the target after the previous claim expired. Renew the same claim before its
eight-hour lease expires if needed. Use `es status`, `es ready`, and extract if
stale. Follow `AGENTS.md` on this checkout. Use `es build`/`es check`,
`es proof capture/check/prove`, and guarded `es job run` for commands over a
minute. Search the library with `es lib search` and inspect `es lib show`
before writing Python or workflow glue. Keep all outputs and receipts under
this run directory.

Every substantive finding, proposed bound, failed conjecture, compiler
failure, diagnostic probe, correction, and plan change must be logged with
`es log` **before the next substantive attempt**. State the exact hypotheses
or probe semantics, observed result, why it works or fails, and durable job,
proof, or file evidence. Explicitly label diagnostic evidence. Never silently
retry an undocumented failure. Keep compact progress and a mathematical
handoff in this directory. Preserve uncommitted work and avoid unrelated
changes. No axioms, `native_decide`, or unauthorized `sorry` additions.

At the fixed deadline stop research and complete the host's bounded
finalization. Inspect actual Lean proof receipts and axioms; a successful
process exit or review inventory is not theorem credit. If closure succeeds,
follow `es node finish` and one-node branch rules. Otherwise release honestly
as partial or blocked, naming the exact obstruction. Review any new ad hoc
run code, changed tracked scripts, and inline job commands; record reuse,
promotion, or deferral. Write `MATHEMATICAL-HANDOFF.md` and
`REPORT.sol.md` with receipt paths and `es log` the handoff. Astra will
perform independent final review and reconcile usage after the terminal event.
