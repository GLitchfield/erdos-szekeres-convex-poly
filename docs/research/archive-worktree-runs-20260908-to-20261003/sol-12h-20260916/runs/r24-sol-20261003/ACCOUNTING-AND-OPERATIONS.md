# R24 accounting and operational evidence

Snapshot 2026-10-04 01:48 UTC. The native goal remains active until the
fixed research deadline, 2026-10-04T01:52:46.857271Z. The source/code
review window is complete; final mathematical review is separate.
The actual recorded final window `window-6bbdcf6e5e3d4ae7` began at
01:23:16.400671 UTC and ended COMPLETE, accepted=0, at 01:47:27.607699 UTC.
`FINAL-MATHEMATICAL-REVIEW.md` records its mathematical scope checks.

Latest accepted research window `window-164c4bd3540947a3` ended accepted=1.
Separate fixed-Sol review `window-ee09196b77584580` ended accepted=0.
Their actual end receipts and usage imports are
`assigned-transfer-window-end.json`, `assigned-transfer-usage-final.json`,
`assigned-transfer-review-window-end.json` and
`assigned-transfer-review-usage-final.json`. These windows do not create or
end the native research goal. Observational targets are not admission limits.

The latest usage import covers 1362 recorded responses through
2026-10-04T01:48:00.254Z: input 193006392, cached input 187028480, output
1791386 and reasoning output 870394, with reconciliation deltas zero.
Its receipt is `final-mathematical-review-usage-final.json`.
Imports are thread cumulative and
must not be summed across windows or described as exclusive window cost.
Active requests and subsequent reporting are not yet included. A final
late-usage reconciliation remains required. All-in work includes setup,
failed conjectures, failed compiler attempts, recovery, monitoring and review.
There is no matched baseline or savings claim.

`final-mathematical-review-window-end.json` and
`final-mathematical-review-factual-handoff.json` record the completed
window. The factual report has no operations or pending decisions. It
associates 42 responses and 63017 output tokens with the window, exceeding
the observational 10000 target; that target does not control admission.
This association is not a causal allocation of all reasoning. Its job/tool
counts cover only explicitly linked work. The all-in cumulative import,
rather than this window alone, includes later final reporting.

Supported inventory `20261003-211031-652d9b` completed rc0/0.8 seconds/
37 MiB. Its immutable artifact and exact source boundaries are reviewed in
`SUPPORTED-INVENTORY-REVIEW.md`. It includes 243 researcher jobs, maximum
measured peak 6556 MiB and aggregate worker time 54949.1 seconds. These are
resource measurements, not mathematical progress or elapsed model time.
The snapshot's only pending job was itself; its later terminal receipt and
the current own-job list show no pending jobs. Other agents' jobs were not
touched. Failed/killed job records and replacement coverage are preserved.

`accepted-environment-final-summary.json` records the accepted compiled
types at the last full extraction: they match their locks, sorry=false,
only propext/Classical.choice/Quot.sound, stale=[] and problems=[]. Its
cached extraction was generated at 01:04:10 UTC with precommit Git SHA
aebb6505. The actual Git HEAD is independently verified as e0e31525;
committing did not change the checked Lean source. Do not present the
cached Git field as a new postcommit extraction.

The final context artifact
`c10d301a7295e668611012da5c3d3047eb88d71359c87210917f7587042f8ff1`
was read completely (28462 bytes, next_offset=null). It reports
frontier_fresh=false while pinning the same accepted source/type. Source
review found an incompatible comparison: bundles.py uses the bare
tree_hash(state_dirs), whereas the extractor stores extract_key, including
toolchain inputs and an extractor digest suffix. This boolean therefore
does not establish source staleness. Neither does this review assert a
newly verified postcommit extract key. Repair or meaningful fingerprint
verification is deferred before the next research admission; no source
proof changed and no unnecessary compiler rerun was launched.

`commits-final.txt`, `preserved-refs-final.txt` and `tracked-status-final.txt`
record the local commit chain, preserved R18/R19 and R24 starting refs,
and clean tracked state. No merge, push or publication was performed.
The mathematical handoff and acceptance notes link exact type, source,
body, proof, full-check, audit and review receipts. No operation inventory
or process exit grants theorem credit by itself.
The final live-claim projection is `final-operational-status-summary.json`;
owned_claims=[] and stale=[] have their distinct meanings above. The named
protected refs were rechecked in `preserved-refs-named-final.txt`.
