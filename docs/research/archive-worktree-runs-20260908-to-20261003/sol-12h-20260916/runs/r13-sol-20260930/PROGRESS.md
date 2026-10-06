# R13 — STUCK; reviewed and finalized, 2026-10-01

**Done is not met. C1r is unchanged and open.** New research stopped at
23:13Z under the brief's two-failed-attempt rule. The missing root singleton
reduction N remains unproved. Registered/tested exchange X is still sorry;
no full closed C1r-from-X-alone conditional was produced.

Five reusable helper theorems are committed with standard-axiom/no-sorry,
unchanged-lock targeted receipts on independent branches from main41cc0e4b:

| Helper | Commit | Targeted check job |
| --- | --- | --- |
| singleton part = explicit T | 6d49410067fbc677ae64cc252d4774698985c353 | 20260930-165717-642558 |
| adjacent deletion preserves run count | 5bfb2e085e2999b10be2bf31fedfd645eb1fb152 | 20260930-173003-dade47 |
| unit global axis gives zero at every fuel | dd4291f419eef48178c2c75d9e839b6de18defa3 | 20260930-175052-dd087d |
| singleton attainment with <=3 children | 59809ac4e015f79f8acd2b58ccf07bd60d7257f1 | 20260930-183003-64cb4c |
| exact one-indexed-level capacities | 95559e090ff7044040348aec1c00ac7094fbd6af | 20260930-194307-536ecb |

Open X commit: eb65ce22ba759254ff4db4a06a159c5e70bd6f78.
Reviewed singleton library commit:8fd0a9b8efa3325f492cfb952f810ed9b1b200a4;
ten guarded tests and the catalog example passed. Sol self-review is in
CODE-REVIEW.md. The coordinator accepted all five helpers and registered X.
Main 7d9c2fed contains the first four closed helpers and open X, verified
read-only. Accepted ctx_single_level_limits_exact at 95559e09 still awaits
coordinator integration. Follow-up R14 is prepared, not started here.

All authorized helper/compiler/probe/library jobs are terminal. Last
probe184927-794b43 completed95232/95232rows,31distinct placements,
complete=true,zero failures,3935.7s/334MiB. General five-child probe
170246-ccbdbe completed3889rows with zero failures. Probes are diagnostic
arithmetic only; exact restricted families and witnesses are in the handoff.

All five helper claims are closed; C1r claim is released partial. Final
account: MATHEMATICAL-HANDOFF.md; compact report: REPORT.sol.md;
receipts: focused helper handoffs and RECEIPT files. Earlier progress is
preserved in PROGRESS.history-2332Z.md and the shared journal. No new trial,
merge/push, primary-source edit, existing-statement edit, full extraction,
axiom or native_decide. Only the fresh passing C1r falsifier receipt remains
tracked/uncommitted, intentionally excluded from other nodes' commits.

Model gpt-6.1-sol,xhigh; researcher codex:agent-run-65158fed3cd841d2;
no delegation. Research/review usage windows ended with4+1 accepted results.
USAGE.finalization-sync.json gives all-in recorded thread usage including failures
and setup, with active/later-request caveats. No savings comparison is claimed.
The coordinator ended research at 2026-10-01T00:00:34.307053Z; finalization
ends before 2026-10-01T00:30:34.307053Z. This single finalization turn
inspected existing receipts and updated reports/accounting only. No new
research or checks were launched. The native goal remains paused because
its mathematical Done criterion is unmet. Safest next action: coordinator
integration of accepted 95559e09, then the separate R14 obligation.
