# R16 final report — 2026-10-01 17:06Z

**Stuck on the full target. Part 1 is done. Thirty helper theorems are closed and
committed independently; N_ends and N_root remain open.** This is the same single
Sol/xhigh trial, without delegation, integration, merge, push, existing statement
edits, primary source edits or full extraction.

Part 1 registered
`ctx_one_level_root_bound_attained_by_extreme_run_end_singleton_cut`
(N_ends), locked type `32c6d22aba01da18`, commit
`22d8137334ce31f2175aee57f29ff79d92fc1f36`, targeted check
`20261001-013617-679625`. That check accepts its registration as an **open
conjecture containing sorry**, not a closed theorem. Falsifier
`20261001-013208-804918` completed 5,976 roots, 127,472 explicit leaf-T audits
and 98,688 cut queries with zero violations; this is diagnostic evidence.
The closed weakening from an explicit selector premise to N_root is commit
`cd1e05ce4528237b2cae5d120e310f044bcacdaf`, targeted check
`20261001-020205-1f077b`, locked type `6ecc666112a7ba4e`.
It uses neither open conjecture as an axiom. Exact account: [PART1-HANDOFF.md](PART1-HANDOFF.md).

All thirty accepted results, exact commits, checks, locked types and handoffs
are in [ACCEPTED-INVENTORY.md](ACCEPTED-INVENTORY.md). Each commit is a direct
child of approved base `5847e155fa613d4d2311eaee86b4b094f630e9a4`,
with one node, unchanged statement, targeted compiled receipt, no proof holes
and standard axioms. These are separate branches; the current environment
contains the base plus its own node. The [scope map](CERTIFIED-SCOPE-MAP.md)
distinguishes actual selector cases from upper bounds and geometric tools.

The latest accepted theorem is raw indexed chosen-global-at-most-three zero
when two actual markers of that level bracket every child. It has no positive
label, WF, opposite-global, k, run-count or history-legality premise.
Commit `aab5395c45d32470b40458039b26b9a79fcbc0e0`, locked type
`ca893a8c2e474cd0`, check `20261001-123039-b16343`,
4.576639 compiler seconds, 576 MiB peak, 4 GiB guard.
[HANDOFF.bracketed-three.md](HANDOFF.bracketed-three.md) preserves the exact
statement, inline receipt, frozen proof SHA, successful commit and the preceding
missing-import compiler failure. Its consumer into a root selector is unproved.

The exact larger-axis obstruction is the raw positive-physical-label,
legal-global, empty-indexed-history inequality
`σ.bound ≤ T(σ.a, σ.u, σ.k)` for arbitrary runs and positive inert barriers.
Axis at most four is closed; axis at most five below saturation is closed.
Remaining scope: minimum axis five with `a+u ≥ k+4`, or both axes at least six.
Two consecutive routes to that same inequality failed:

- Rank-triple charging: at chosen five/opposite seven/k seven the support is
  56 while T is 26. Job `20261001-061913-2ecdcc`.
- Scalar split charging: legal split m=4,n=2 gives 4+26=30 > 26;
  m=5,n=1 gives 1+26=27 > 26. Job `20261001-062036-f1475c`.

The same tested 36-root family has actual bound 26 and no upper-bound
violation. These failures refute intermediate estimates, not N_ends or N_root.
[HANDOFF.larger-axis-upper-stuck.md](HANDOFF.larger-axis-upper-stuck.md)
contains exact inequalities, probe semantics, witnesses and durable outputs.
General neither-marked exchange and complete unit/degenerate selector edges
also remain open. Even the missing upper theorem alone would not finish N_ends.

A separate kernel-certified counterexample refutes a **global-ends-only**
selector: SSLSS, chosen global 3/opposite 2/k4/m1 has source bound 1 and all
eight legal global-end cuts 0; inner first-run end p=1 attains 1.
Commit `aad0cd4939df89e219189c4372b9e629a5f2950e`, check
`20261001-094654-b4d99d`. This does not refute N_ends or N_root.
[Exact handoff](HANDOFF.global-end-counterexample.md) includes the earlier
ordinary-decide OOM and successful trusted-kernel proof; no native_decide or
new axiom was used.

Infrastructure and accounting limits are recorded, not mathematical results.
Registration `20261001-120130-152844` completed in 140.7 s/2319 MiB under 5 GiB
after a confirmed-unstarted 8 GiB registration was cancelled and the exact
argv resubmitted. Guard requests/retries remained enforced. Shared DB access
failed around 16:06–16:17Z, recovered without database/config/worker mutation,
and deferred findings were logged before another proof attempt.
[OFFLINE-LOG.pending-1608.md](OFFLINE-LOG.pending-1608.md) and
[CODE-REVIEW.infrastructure-offline.md](CODE-REVIEW.infrastructure-offline.md)
preserve the errors, uncertain admission cause and read-only diagnostics.
No owned job is queued or running at this checkpoint.
Both full-target research claims were released partial at16:56Z after the
[immutable Stuck handoff](HANDOFF.full-target-STUCK-1655.md) was linked in es.
Administrative checkout/restore jobs20261001-125548-1dd609 and
20261001-125647-78fb16 both finished0.1s under1GiB; no missing output or refusal.
The latest accepted30 branch is restored at aab5395c45d32470b40458039b26b9a79fcbc0e0,
clean, stale0/problems0. [Exact administrative receipts](ADMIN.final-claim-releases-1657.json).

Consolidation was first recorded at 16:35:28Z, about 42 seconds after the
scheduled 16:34:46Z start, while the last theorem's review/commit follow-up
finished. Research deadline remains 17:04:46.416915Z; hard finalization remains
17:34:46.416915Z. The native goal was held active until the research deadline,
then paused by the host. This single finalization turn starts no new research.
The report and its Stuck criterion are supported by existing receipts; completion
of the authorized trial/report does not certify either mathematical target.

Whole-thread usage reconciled through 17:05:09Z: 1,569 requests, 219,868,821 input,
214,304,000 cached input, 1,642,880 output and 767,772 reasoning tokens.
[Exact usage snapshot](USAGE.final-snapshot-1705.json), reconciliation delta0.
Active requests and later final reporting may not yet be included.
Historical explicit-window assignments were preserved by syncing with
ES_WINDOW_ID unset; overlapping/late/offline windows and direct-job attribution
have gaps. These are whole-thread totals, not this window's cost or evidence of
savings. Sol self-review is documented separately; an independent Astra review
was unavailable under the host's no-delegation rule.

Safest next research action: review the exact committed scope and failed
inequalities, then pursue a cut-aware larger-axis upper estimate that preserves
geometric correlations discarded by the failed scalar charge. Treat general
neither-marked exchange and degenerate edges as separate open obligations.
Prospective crossed-level/protected-child/two-run/higher-chosen routes remain
unproved in [PROSPECTIVE-DEGENERATE.md](PROSPECTIVE-DEGENERATE.md).

The complete current mathematical account is
[MATHEMATICAL-HANDOFF.md](MATHEMATICAL-HANDOFF.md).
Final read-only [receipt and commit audit](ACCEPTED-RECEIPTS.final-audit-1646.json)
passes all thirty results. Guarded proof-span audit
`20261001-124906-638eb3` finished 17.5 s/20 MiB/1 GiB, no missing output:
all thirty committed bodies match frozen candidates;28 full modules match,
two differ only by a final blank line. Exact
[proof audit](AUDIT.committed-proof-spans-1649.json) and
[diffs](AUDIT.committed-proof-nonbody-diffs-1649.json) are preserved.
Earlier checkpoint prose is preserved in REPORT.history-preconsolidation.md,
MATHEMATICAL-HANDOFF.history-preconsolidation.md and
PROGRESS.history-preconsolidation.md; their historical counts and queued states
are superseded here. Frozen individual proof receipts and handoffs are unchanged.
