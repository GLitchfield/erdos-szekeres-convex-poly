# R8 progress

Agent: `codex:agent-run-ea2920bdae864f85`; thread `01a0f269-88d8-7053-906d-e9fc42afa312`.
Research window: `window-65885abecb2d4f22`.
Original claim expiration was 2026-09-30 21:04 UTC; released closed before expiry.
Branch: `node/CtxBoundExtLetterDeletionMonoOfIsolatedChildren`; baseline `73675e50874881119df95f689c907e729400f008`.

2026-09-30 13:06 UTC: startup inspected brief, state, journal, existing proofs. Node open;
no earlier R8 attempts. `es status` fails in burn-down formatting (`detail` is a string);
`es status --brief --full` and scoped commands work. No full extraction needed.

Initial proof obligation: formalize inert insertion/deletion transport, with deleted context
WellFormed and source child positions isolated. Source inert context need not be WellFormed.
Reuse the closed external contraction's order-map, extension-fold and block transport proof
patterns; replace its run equality by isolated-run/merge bookkeeping.

2026-09-30 13:19 UTC: complete exact-statement scratch proof passed guarded job
`20260930-091430-8e8366` (12.42s, no warnings). It is installed in the node module;
statement and docstring preserved. Inert fuel comparison proves each source approximation
is bounded by the target full bound, using closed target cut domination and prefix/suffix
additivity for the two-child merge.

At 13:19 UTC, targeted audit was **running**: `20260930-091640-28f1ec`, explicit 5G guarded job wrapping
`es check ... --targeted --force --full`. New module build passed (~10s); targeted extractor
finished 5451 modules (5450 cache hits, one scanned module). Reviewed at the 2-minute
checkpoint: leave running, expected report completion shortly. No theorem closure claimed
until the final axiom receipt is inspected. Generic async check `20260930-091532-856030`
reserved 20G and was cancelled while queued (no compiler/log); exact same audit rerouted.

Scratch jobs: `20260930-090606-227b90` failed, `20260930-090701-0adef9` passed,
`20260930-090825-f93ba0` passed, `20260930-091011-5b4118` passed,
`20260930-091128-f0d031` passed, `20260930-091341-108093` failed,
`20260930-091430-8e8366` passed. Every failure/findings logged; failures were elaboration
bookkeeping, not false mathematical subclaims. Source snapshots are in this directory.

Pre-edit proof fixture: `3af69c983fb8177baf625a0a7ef9f604978d77f1f1c5e1d4ef2015eb230b40ac`
(captures original `sorry` source; freeze record only, not an acceptance receipt).
2026-09-30 13:23 UTC: **node CLOSED and committed**.
Targeted audit `20260930-091640-28f1ec` terminal rc=0: standard axioms only, no sorry,
unchanged type hash `41d377ff917bd9a1`, lock matches. Saved `TARGETED-CHECK.json` and
`NODE-CLOSED.json`. Commit job `20260930-092220-63abf4` terminal rc=0 created
`bf243a393c9a220ffc1ea0d4e5f387fd0c52d70a`; exact node module plus generated nodes/status
records only, tracked tree clean. Commit receipt `COMMIT-JOB.json`.
Final checked-source fixture `8b29c702a5cce327954a43b84afe9b8939bdc66bead43b3e66422ef4a687e6ea`.
Research window complete (one checked theorem); separate solo review window
`window-f8a58ff3ec1b4424`. Final mathematical handoff and REPORT.sol.md written.
Claim released with outcome closed. No further research trial; native timing gate
remains until the required completion instant.
Deadline 23:03:18.554193 UTC; consolidation starts 22:33:18.554193 UTC. One trial only.

Remaining native-goal requirement is temporal, not mathematical. At consolidation,
revalidate current commit/node/receipts and handoffs. At/after the deadline, audit and
truthfully complete the native goal if the accepted result still holds. All submitted
R8 compiler/check/commit jobs are terminal; the timing host remains running. No callback
or notification while the client is closed is promised.

2026-09-30 13:28 UTC: preliminary requirement audit recorded in COMPLETION-AUDIT.md.
Current source, HEAD source, saved candidate and final captured source fixture share
SHA-256 `79b52551338ef52ac68390becf8492626c0da274b76370edf6c03fa07717ae11`.
Verified existing native host job `20260930-090312-6e9550` running with fresh heartbeat;
it enforces the fixed timing gates. No new compiler admission or theorem trial.

2026-09-30 14:29 UTC: host checkpoint inspected. Fresh heartbeat, unchanged 2G cap,
running; fixed research deadline about 8h33m away. All proof jobs remain terminal.
Review left the host running and set the next checkpoint in 60 minutes; no deadline,
quota or cap changed. Timing-only monitoring window `window-5eb6954327604c0c` has an
observational 10,000-output-token target. Pending gates and accepted evidence remain
as listed in COMPLETION-AUDIT.md. Native goal active; no new trial authorized.
