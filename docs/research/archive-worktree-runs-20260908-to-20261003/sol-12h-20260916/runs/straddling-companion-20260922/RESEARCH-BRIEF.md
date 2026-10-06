# Close the actual-cut straddling companion bound

This is a fresh Sol research attempt authorized after the September 19 run ended
at its usage limit. It is not a resume of that frozen native thread, whose
deadline expired on September 20. Use a new host, native thread, research window,
and absolute deadlines. The root coordinator must fill the clock fields below at
launch time so setup, native research, finalization, review, and reporting all fit
inside one new twelve-hour overall cap.

- Overall start: `2026-09-22T18:59:28Z` (first resumed-work clock, including setup)
- Overall stop: `2026-09-23T06:59:28Z` (absolute twelve-hour cap)
- Native research cutoff: no later than `2026-09-23T05:55:00Z`; the host's `--hours 10.75` may end research earlier after pickup
- Native finalization hard stop: no later than `2026-09-23T06:25:00Z`, leaving over 34 minutes for review and reporting
- Model and effort: `gpt-5.6-sol`, `xhigh`

Do not reuse, reset, or extend observer
`run-monitor:e573555bdd95f15161aabaf6`, host job
`20260919-102946-bb2e14`, or its native thread. Do not submit twice after an
uncertain response. The root coordinator handles exact-thread delivery
verification and confirms worker pickup before yielding.

## Baseline and scope

Work only in
`/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916`.
The reviewed, clean baseline is
`668e390e22c6d7ce769e19c2913ee15cb8a65d13`, tree
`6f96afcf8ccbcf22c50166c390ae57d64da53ae1`. The last proof commit is
`eb421ac30725bf7b2b1155ac21dc745e2f9d994b`. At setup, the checkout has no
tracked or untracked changes and is on
`node/CtxTwoActualMarkerOppositeBetweenPairCardSumElevenBound`. The fresh index
has 305 closed nodes, 12 open nodes, one refuted node, no stale entries or
problems, and eleven ready nodes.

Read `AGENTS.md` and the final reviewed September 18 evidence before changing
mathematics:

- primary `runs/sol-12h-20260918/MATHEMATICAL-REVIEW.md`;
- primary `runs/sol-12h-20260918/REPORT.md`;
- primary `runs/sol-12h-20260918/review/RECEIPT-AUDIT.sol.md`;
- primary `runs/sol-12h-20260918/review/verified-results-reviewed.json`;
- primary `runs/sol-12h-20260918/review/CODE-LIBRARY-REVIEW.md`.

The September 19 host is terminal with `goal_usageLimited`. A fresh compact
review on September 22 reports 57 responses, zero research jobs, zero explicit
proof receipts, zero validation evidence, zero changed tracked scripts, and no
inferred theorem credit. Unless the separate final audit finds stronger source
and receipt evidence, there is no new mathematical baseline after `668e390e`.

The only objective is a compiling theorem that removes the actual
between-marker, active-low-straddling companion obstruction and proves the
companion context is at most eleven for every fuel and in the full bound.
Supporting lemmas count only when they are concrete dependencies of that result.
Further residual classifications, wrappers that assume the missing numerical
bound, and unrelated theorem counts do not satisfy the objective.

## Exact actual-cut target

For the legal chosen-kept extreme, define

```lean
let rest := σ.childPositions.filter (· ∉ keep)
let A := σ.part keep s m
let B := σ.part rest t n
```

The intended consumer has `k = 6`, `m = 4`, and `n = 1`. The other component
already has the every-fuel and full bound `A <= 1`; closing `B <= 11` supplies
the needed `A + B <= 12`. Preserve the actual part construction and the legal
consumer hypotheses rather than replacing them with an abstract context that
forgets why its synthetic marker exists.

Start from the exact compiled interfaces:

- `ctx_two_actual_marker_opposite_between_intersection_three_and_oriented_high_support`;
- `ctx_two_actual_marker_opposite_between_eleven_or_active_low_straddles`;
- `ctx_extreme_cut_six_pair_intersection_three_residual_classification`;
- `ctx_actual_marker_opposite_rank_interval_endpoint_exclusion`;
- `ctx_actual_marker_rank_pair_union_nine_bound` and its binary-pruning transport;
- `ctx_two_marker_mixed_capacity_pair_card_sum_bound`;
- `ctx_two_actual_marker_opposite_between_active_separated_companion_eleven_bound`;
- `ctx_two_actual_marker_opposite_between_pair_card_sum_eleven_bound`.

The unsolved residual is under the explicit hypothesis
`(x < p ∧ p < y) ∨ (y < p ∧ p < x)`. It retains:

- positive external labels and distinct axes `s != t`;
- chosen levels `N < M`, actual positions `x,y`, both on axis `s`;
- every indexed chosen-axis occurrence at `x` or `y`;
- both relevant global parameters equal to five in the residual;
- `n = 1`, `p ∈ A.childPositions`, and after transport
  `p ∈ B.extPositions 1` with side `t` and `B.maximumAt 1 = 1`;
- a child `high ∈ B.childPositions` with chosen-axis diagonal capacity at
  least three;
- active capacity-at-most-two children of the canonical low pruning on both
  sides of `p`;
- canonical low/high rank-pair intersection cardinality at least three;
- high-pair support inside `Q([2,4])` when `x < p < y`, or inside `Q([1,3])`
  when `y < p < x`.

`B.maximumAt 1 = 1` is the synthetic marker constraint that remains materially
unused. It does not assert that level one has exactly one physical occurrence.
Do not add such an occurrence hypothesis. Retain arbitrary child counts,
additional opposite history, inactive children, unused levels, and independent
fuel unless a proved reduction removes them.

The result under `hbetween` closes this exact straddling residual. It does not
by itself prove that every remaining cut has a between-marker point. Keep that
scope explicit so subsequent consumer case analysis does not silently acquire a
false premise.

## Coupled estimate to investigate

The current decomposition proves

```text
boundFuel fuel B <= |pairs 0| + |pairs 1|
B.bound          <= |pairs 0| + |pairs 1|.
```

The actual-marker endpoint theorem gives a common union envelope of at most nine
rank pairs. Separate pruning charges can count an intersection pair twice, so
the union bound alone does not prove eleven. In the residual, the overlap is at
least three; that is evidence of duplicated charges, not numerical slack by
itself. The existing final wrapper assumes
`hPairCard : |pairs 0| + |pairs 1| <= 11`; deriving no such fact is the present
obstruction.

Attack the recurrence before or while it is split into independent low/high
groups. A precise candidate interface is a direct coupled estimate of the form

```text
boundFuel fuel B <= |pairs 0 ∪ pairs 1| + 2
B.bound          <= |pairs 0 ∪ pairs 1| + 2,
```

under the actual-cut hypotheses above. The union-nine theorem would then close
eleven. An equivalent theorem may instead show that at most two common pair
charges survive after coupling, or that at least one duplicated residual charge
must be paid by the maximum-one level and cannot appear independently in both
pruning recurrences. This is a research direction, not an available lemma: test
the recurrence semantics before formalizing it.

Use all three pieces of geometry together:

1. active low support genuinely crosses `p`;
2. high support is confined to the oriented three-rank triangle;
3. the actual opposite-axis marker has maximum one and excludes the appropriate
   endpoint from every active interval.

A proof based only on the separate cardinalities repeats the known gap. A proof
based only on `hbetween` misses the marker maximum. Do not postulate
`hPairCard`, an equivalent charge inequality, a chosen classification, or an
arbitrary finite case split as a hypothesis. If the direct union-plus-two
candidate fails, preserve a faithful smallest witness and switch to a different
coupled invariant rather than weakening the goal into another conditional
wrapper.

## Diagnostic contract

The reviewed corrected finite diagnostic is
`/home/gavin/git/erdos-szekeres-convex-poly/runs/sol-12h-20260918/review/probe_companion_group_charges_corrected.py`,
SHA-256
`ab793ce2dbcc3976cf2b40d83d91629de6b57ff8818353141fee8bf826fb777f`.
It uses the canonical fresh pruning barrier `len(maxima) + 1`. The preserved
older script's literal level four is invalid when four indexed levels are
present. Reuse or snapshot the corrected source; never reintroduce the literal
barrier.

The diagnostic has fixed `(a,u,k) = (5,5,6)`, exactly one marker per level, two
chosen levels above actual level one, finite child counts, and the explicit
`context-bound-zero-children-v1` evaluator. `--all-chosen-maxima` varies every
tail maximum. It is not equivalent to unrestricted Lean contexts, and it does
not certify the actual-cut transport. Filter and report the exact residual
conditions, including between placement, active low straddle, mixed active
capacity classes, oriented high support, pair overlap at least three, and
maximum one. Preserve each execution's source snapshot, hash, arguments,
semantics, and distinct output path. A finite result is diagnostic only until a
Lean theorem proves the corresponding reduction.

Before writing any new diagnostic or workflow code, use `es lib search` and
`es lib show`. The existing reviewed APIs are `decomposable.context-limits`,
`research.context-extension`, and `research.recursive-bounds`. Do not create an
arbitrary classifier when a direct recurrence or invariant can be tested.

## Research and formalization workflow

Run `es status`, `es ready`, and `es search` from the mathematical checkout.
The September 22 search for an existing actual straddling maximum-one eleven
theorem returned no result. Claim
`ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end` before research.
Use one fresh `node/<Name>` branch per new theorem and `es node add` for every new
statement; never edit a statement by hand. Log any decision that changes the
mathematical plan before acting on it.

First reconstruct the exact recurrence and state the coupled lemma on paper.
Then perform a small faithful diagnostic pass if it can distinguish plausible
couplings. Formalize only a statement that removes a real step of the
obstruction. Search the library before every lemma. Keep proof receipts and the
live handoff current after each accepted result or important failure. Do not add
axioms, `native_decide`, or `sorry` outside the allowlist.

Use `es proof capture/check/prove`, `es node finish`, `es probe run/replay`,
`es context`, and `es run handoff` where their contracts fit. All commands over
one minute go through `es job run` and write under this run directory. Preserve
failed jobs and exact inline commands. Compile incrementally, then run the
targeted node check and final extraction only when they resolve a remaining
risk.

If several hours fail to produce a credible coupled mechanism, inspect faithful
minimal residuals and make one explicit method change. Do not spend the rest of
the window accumulating classifications. Stop research early when the theorem
is compiled and checked, leaving time for finalization and review.

## Resource and launch facts

At setup on 2026-09-22, `es doctor` passed: Lean 4.29.1, Lake 5.0.0, all 9,857
certificate oleans and 319 root-closure core oleans present, 46 GiB available,
zero Lean compilers running, and guard enabled. The job database had no queued,
starting, or running jobs. Physical free space was 449,436,086,272 bytes with
65,194,264 free inodes. The checkout occupied 134,543,419,113 bytes.

`harness/config.toml` has SHA-256
`24c80777fb32c0fea031cbc39173f3b11911c7df8c76acff3e3dcc1c661d3029`.
The shared job budget is 30G, a native host reserves 2G, normal builds use 20G,
and extraction uses 28G. The reviewed route for a node check requiring final
extraction is one explicit outer 28G guarded job around `es check NODE`, whose
20G build and 28G extraction stages are sequential. Do not use the default 20G
asynchronous check wrapper for a 28G extraction. If admission refuses the 28G
stage beside the host, stop the host after native finalization and run the check
within the overall deadline; do not silently lower a genuine memory cap.

Fresh guarded worker probe `20260922-150637-72f35e` was picked up through the
ordinary queue and finished exit zero in 0.2 seconds at 126 MiB under its 128M
cap and one-minute budget. Host-side evidence shows the same worker
`MainPID=492743`, start time September 18 at 16:26:52 EDT, working directory,
PATH, Codex 0.155.1, and Node 24.14.0 as the worker that passed the earlier
completion canary and delivered three callbacks. No queued, starting, or running
jobs remained afterward. Root separately confirmed the exact delivery binding
as `already_verified`, ready with zero reconciliation. The prior canary is
reusable; no model canary or service restart is needed.

Suggested launch after root fills the clock and verifies the exact callback:

```text
es run agent --out runs/straddling-companion-20260922/host \
  --prompt /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916/runs/straddling-companion-20260922/native-goal.md \
  --model gpt-5.6-sol --effort xhigh --hours 10.75
```

The overall twelve hours include pickup, setup attributable to the attempt,
failed work, native finalization, root review, and reporting. Record the exact
host job, native thread, native window, observer, deadlines, worker pickup, and
callback state once. Never revive the old host or extend either the native or
overall deadline.

## Final handoff

Release all owned claims accurately. Report whether the actual straddling
companion estimate is compiled; its full hypotheses; theorem, source/type hash,
check, proof fixture, extraction, and commit receipts; every diagnostic's finite
domain; failed coupled mechanisms; remaining placement cases; and every pending
job. Inventory changed tracked scripts, run-local code, and inline job commands.
Sync usage by setup, Sol research/finalization, root monitoring, final
mathematical review, and code/library maintenance. A terminal host status or a
review inventory alone grants no theorem credit.
