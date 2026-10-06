# R15 k4 diagnostic self-review — 2026-10-01 08:58Z

Configured Sol at xhigh reviewed in separate observational window
window-1928a23cb9bc4dd6; no delegation or Astra review claimed. Diagnostic
research window-435d00672d1b4941 ended with zero accepted Lean results.

Complete inventory89ff7f48ce0b4ef5e2bf893347279884cbfc249bd95faf0abf86beab8cba3cb3
contains17 artifact scripts and22 tracked scripts. Every hash equals the
0841 inventory. The already-reviewed k4 generator/profile is unchanged.
Host identity association still omits this thread's jobs and usage; those
empty arrays are unavailable evidence, not proof of no work. Initial review
used the artifact root instead of host directory and returned exit2; corrected
host review succeeded. Unsupported job-show invocation ran no job.

Timing796ff9 measured2 rows in0.1694s algorithm/0.4s outer before576-row
sampleeae2c6. Sample finished44.8s/151MiB/OOM0, rc2 because end-only exchange
failed, not because execution failed:2880 classes all pass full exchange,
2259 zero/621 positive; first-end misses2, last-end misses10, both-end misses1.
All rows and individual witnesses remain in k4-end-sample.json SHA
78e0334097338c4773e800f6da53a82bf843a9a282e53badb85119e876e8d4db.

Reviewed complete inline commands for extraction0ea5f8, exact replay7a5b7a,
limitsd2c95d and saved-witness query6b0094. Extraction reads JSON and asserts
the both-end count. Replay pins frozen profileb761f2c3, computes full maxima
without a threshold for the original keep and every maximal segment, writes
progress and closes the shared evaluator. It confirms old2 and maxima
[1,2,2,2,1] on WF4/3/4 wordS1LSSS1LS/max1/keep0,3,6. Saved query compares
interior witness segments against both endpoint lists:621 positive classes,
zero misses, no new bound calls. Shared limits API uses lean=True and reports
source cup1/cap3, nonsingleton part cup/cap1/1. Existing fixed C CLI9c019a
reports that part's full bound0. These are finite diagnostics, no kernel credit.

Reuse: frozen exact/threshold-separated profile, shared persistent evaluator,
existing part constructor and legacy limits API. No new reusable runtime
algorithm was introduced; JSON extraction/query are one-off analysis and
promotion is deferred. Keep the full any-length exchange obligation open;
end-only and arbitrary-keep point-positivity shortcuts are rejected. Next
register and certify the finite end-gap witness in Lean on its own branch.

Explicit research usage sync:1071 responses, input151571566/cached147155584/
output1217847/reasoning582584 through08:55:37Z, reconciliation deltas0.
No all-in savings or theorem credit inferred from process exits/inventory.
