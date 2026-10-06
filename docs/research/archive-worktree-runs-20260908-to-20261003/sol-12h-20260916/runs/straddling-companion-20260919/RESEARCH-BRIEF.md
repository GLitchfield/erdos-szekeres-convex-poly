# Close the straddling companion bound

The user authorizes one focused attempt to close the straddling companion bound,
stopping within twelve hours. This is a new allowance after completion of the
September 18 trial and Astra's final review, not a resume or extension of its
expired native goal.

## Clock and scope

Coordinator start: 2026-09-19T14:23:57Z. Absolute user stop:
**2026-09-20T02:23:57Z** (September 19, 10:23:57 p.m. EDT).
The native host will receive a shorter research duration so its existing
30-minute finalization allowance and coordinator review fit inside this limit.
Honor the earlier native research cutoff as well. Do not extend either clock,
reset a quota, resubmit an uncertain operation or begin another trial. Child-job
budgets must fit the time remaining; cancel and inspect any unfinished job before
the applicable cutoff. No new mathematics during finalization.

Work only toward the actual straddling companion estimate. A compiling theorem
removing that obstruction is the success criterion. Supporting lemmas are useful
when they have a concrete proof dependency toward it. Additional classifications,
conditional wrappers assuming the missing estimate and theorem counts are not
substitutes. If it closes early, verify and prepare the handoff; do not broaden
the research agenda. The coordinator will review the completed result.

## Absolute locations and baseline

- Research checkout: `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916`.
- Clean reviewed baseline: `668e390e22c6d7ce769e19c2913ee15cb8a65d13`.
- Last prior proof commit: `eb421ac30725bf7b2b1155ac21dc745e2f9d994b`.
- New artifact directory: `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916/runs/straddling-companion-20260919`.
- Native host: that directory's `host/`.
- This brief: that directory's `RESEARCH-BRIEF.md`.
- Sol reports: that directory's `REPORT.sol.md`, `checkpoint.md`,
  `mathematical-analysis.md`, `verified-results.json`, and `code-inventory.md`.
- Astra reports: `/home/gavin/git/erdos-szekeres-convex-poly/runs/straddling-companion-20260919`.

Baseline `es status` is fresh: 305 closed, 12 open, one refuted, zero stale or
problems, eleven ready nodes. Check it yourself and extract if stale before
selecting work. The umbrella node is
`ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end`.

First read AGENTS.md and the reviewed prior mathematical and code reports:
`/home/gavin/git/erdos-szekeres-convex-poly/runs/sol-12h-20260918/MATHEMATICAL-REVIEW.md`,
`REPORT.md`, `review/RECEIPT-AUDIT.sol.md`,
`review/verified-results-reviewed.json`, and `review/CODE-LIBRARY-REVIEW.md`.
Their source/receipt corrections supersede the incomplete native checkpoint and
analysis from that run. Its 22 accepted supporting declarations are baseline.

## Exact mathematical target

For the actual chosen-kept extreme at `k=6,m=4,n=1`, write
`rest := σ.childPositions.filter (· ∉ keep)`,
`A := σ.part keep s m`, and `B := σ.part rest t n`.
The other component already has an every-fuel/full bound of one. Seek a compiling
every-fuel/full **B <= 11** theorem for the remaining straddling companion, giving
the missing numerical slack for `A+B <= 12`.

Reconstruct exact declarations and hypotheses, starting from:

- `ctx_two_actual_marker_opposite_between_intersection_three_and_oriented_high_support`;
- `ctx_extreme_cut_six_pair_intersection_three_residual_classification`;
- `ctx_actual_marker_opposite_rank_interval_endpoint_exclusion`;
- `ctx_two_actual_marker_opposite_between_active_separated_companion_eleven_bound`;
- `ctx_two_actual_marker_opposite_between_pair_card_sum_eleven_bound`.

The between-marker residual has both axis globals equal to five, active children
of the canonical low-capacity pruning on both sides of physical marker p, and
canonical low/high ordered-rank-pair overlap at least three. The actual transport
retains `p ∈ B.extPositions 1`, opposite side t and `B.maximumAt 1 = 1`, together
with ordered chosen levels `N<M`, actual positions x,y and `x<p<y` or `y<p<x`.
The high pair support lies in `Q([2,4])` or `Q([1,3])` according to orientation.
Preserve the actual cut construction, positive external labels, exact chosen
marker support, high-capacity child witness and the hypotheses of the consumer.
The synthetic level can have multiple physical occurrences. Additional history,
inactive children, arbitrary child counts and independent fuels cannot simply
be discarded without proof.

Do not conflate the older extreme classifier's hypotheses with legal coupling:
the classifier alone does not assert n=1. The new between-marker wrapper takes
n=1 explicitly. Decide and write down the exact statement you intend to prove
before formalization. If a broader abstract statement fails, retain the actual
legal-cut hypotheses needed by the original obstruction, explain the distinction
and test them. Do not add an arbitrary numerical assumption equivalent to the goal.

Already solved: all prior internal-complement k=6 cuts, opposite-kept block cuts,
the exterior-marker companion bound of nine, active-separated companion bound of
eleven, overlap at most one, and geometric exclusion of overlap exactly two.
Reuse these and do not recount them as new progress.

The final prior theorem assumes
`hPairCard : (pairs 0).card + (pairs 1).card <= 11`.
It does not derive this inequality. The nine-pair union bound does not control
duplicated group charges. The principal research direction is a coupled recurrence
or invariant using the synthetic maximum-one marker and endpoint losses to supply
the missing slack. This direction is a proposal, not an established estimate.

## Focused research discipline

Begin with a short, faithful diagnostic/reconstruction pass, then attack the
coupled estimate. Search the existing library and source before writing any new
lemma or Python/workflow glue. Log a change of mathematical plan before acting.
Keep small counterexample searches faithful to the actual companion and preserve
their domain, semantics and exact script hash. A finite failure of a stronger
pair-count route is not automatically a refutation of B<=11. A Python witness
is diagnostic until an appropriate Lean theorem certifies it.

The reviewed corrected probe is
`/home/gavin/git/erdos-szekeres-convex-poly/runs/sol-12h-20260918/review/probe_companion_group_charges_corrected.py`.
Reuse it or the catalogued context limits, extension and recursive evaluator where
their contracts fit. Its replacement barrier is `len(maxima)+1`; literal level
four is wrong with four indexed levels. The existing probe covers a finite,
one-marker-per-level domain and is not equivalent to unrestricted Lean contexts.
Its `--all-chosen-maxima` actually varies every tail maximum. Correctly record
these limits. Do not overwrite outputs or modify a script while its jobs are live;
preserve per-execution source snapshots/hashes and use distinct result paths.

If several hours produce no useful coupled mechanism, explicitly reassess the
mathematics, inspect faithful smallest obstructions and change method as warranted.
Do not fill the remainder with cosmetic classifications. Keep the live handoff
current after every accepted result or significant dead end; the previous run's
quota stop left its narrative far behind its actual commits.

## Claims, checks, storage and commits

Use inherited registered researcher `ES_AGENT` and `ES_WINDOW_ID`; do not replace
them with the coordinator identity. Claim the ready umbrella before research and
use fresh `node/<Name>` branches and explicit claims for new nodes. Read command
help; use `es node add/restate`, `es search`, proof capture/check/prove, node finish,
probe replay, context and handoff primitives as appropriate. Preserve statement
contracts and all prior sources, compiled proof bodies and receipts. No axioms,
native_decide or sorry outside the existing allowlist policy.

All long commands use guarded jobs. Enclosing reservations must cover every
configured stage. Do not repeat the prior 20G check wrapper that refused a 28G
full extraction. The normal native host reserves 2G inside a 30G shared budget;
inspect the actual command/stage requirements and use a valid fitting reservation.
The reviewed ordinary path is an OUTER `es job run --mem 28G ... -- es check NODE`
(or a shell wrapper that captures its JSON): the 20G node build and 28G extractor
run sequentially inside that one 28G scope, fitting beside the 2G host. Do not use
`es check --async`, whose default enclosing check job is only 20G. A normal warm
full extraction can likewise use the matching 28G enclosing reservation. Read the
new preflight report for exact commands; no global resource changes are needed.
If a final stage genuinely needs 30G, record that and defer its full-environment
check until the host has stopped, inside the overall deadline. Do not reduce safety
limits silently, modify global resource configuration, or wait forever for an
impossible 30G child alongside a 2G host. Keep genuine targeted check receipts
distinct from full extraction and do not claim a stale index is current.

Keep guarded setup-metadata cleanup and native immutable artifact caching enabled.
Reuse this checkout and shared artifacts. No cache duplication, mutable build
sharing, destructive cache cleanup or new checkout. The primary checkout's
unrelated ESBlueprint.lean and context-end-cut datasets must stay untouched.

Make focused local commits after compiling/reviewing each accepted node and
record exact hashes. No push, merge or publication is requested. On exit release
all owned claims with accurate outcomes; the parent is partial unless actually
proved. Maintain a current result ledger with theorem, full hypotheses, source and
type hashes, checks/proof fixtures, commits and mathematical obstruction removed.

## Final handoff

Leave enough time for full checks and a truthful report before the fixed cutoff.
Report precisely whether the straddling estimate is closed, what hypotheses were
needed, exact theorem/check/commit receipts, any uncertified diagnostic evidence,
failed approaches, remaining cases, and pending jobs. Inventory run-local scripts,
changed tracked scripts and inline job commands, with reuse and promotion candidates.
Sync usage including failed attempts and late reporting. Never infer theorem credit
from host exit status. Astra performs separate final mathematical and code/library
review and records physical disk growth and usage by role.
