# Offline infrastructure code review — R16 Sol self-review

Review checkpoint16:18Z. The sharedStore is locked; an es reviewwindow/usage
import cannot yet be recorded. This is separate offline maintenance work and
must be linked/reconciled once writable. IndependentAstra forbidden by user.
No new formal result credit.

Reviewed new resource-admission-diagnostic-v4.py: exact sharedAPI reuse
load_config/job_memory_gib/budget_problem/available_gib and mode=ro SQLite.
No compiler, subprocess, DBwrite or admission decision. Fixed requested5G,
currentcfgbudget40G and livecaps/leases are observational snapshots. Actual
reserve_job also checks locks/owners/unknownexecution; snapshot has leases0 and
unknown0, but it does not expose old worker's live configuration or provefit
at anotherinstant. frozenJSON/source hashes recorded in OFFLINE-LOG.pending-1608.
Read-only query ran0.0388s; resultjobnull, not a guarded jobreceipt.
No rerun/overwrite of v1/v2/v3/v4 frozen snapshots.

Reviewed DB-READONLY-1615.py: constant mode=ro path and parameterized exactjobid,
no DBwrite/subprocess/compiler. SQLite busytimeout1 is metadata I/O contention,
not a research-test deadline. Emits explicit okfalse whenlocked; doesnotinfer
queued/running/terminalstate. Infailedbranch connection closes onprocess exit;
no longlived observer/unknownjob execution created. Repeated same frozenwrapper
reuses the code; subsequentstdout snapshots do not overwrite firstfrozenJSON.
SourceSHA7353b301b7a58f3db5ccd1c69d8cae05feffd6153c9c3f6b0e0d30c123664c07,
firstJSONSHA8fc776d95aec9a24758847a39da3cc00dbcda8d8ecdbfa3e3991a67619bf2a37.
No tests warranted for these reversible tiny metadata adapters; observed errors
and semantics are captured, not mirrored implementation tests.

Allinlinecommands reviewed: short config/source reads, diskfree, optionalDB
journalmetadata ls (wal/shm absent causesexit2, not lost DB data), /proc/locks
no visiblematches (noowner/liveness inference), ALL_TOOLS esMCP capability
search no match. No forced DB recovery, worker manipulation, override or approval.
Allcompiler/proof work remains inside esguards; metadata probes measured<1s.

Repeated tiny resourcewrappers use existingsharedAPIs, no newresearch algorithm.
Generic metadata CLI promotion deferred: existingharnessimplementations own
admission semantics; current one-node trial forbids unrelatedprimary/integration
changes. Preserve exact original artifacts rather than generalize an unconfirmed
infrastructure issue. Useful followup outside thistrial: expose a readonlyresource
snapshot and readonlyStore healthpath through existing escommands, after review.
No genericworkflow implementation has been changed.

Pending journal linkage, retrospective reviewwindow and lateusage reconciliation
are explicit gaps, not completed operations. RetryStore calls onlysequentially
and do notblindlyresubmit currentregistration120130-152844.
