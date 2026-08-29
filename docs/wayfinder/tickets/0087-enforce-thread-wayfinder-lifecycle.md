---
title: Enforce the Wayfinder lifecycle around persistent worker threads
type: research
mode: HITL
status: open
claim: persistent-thread-wayfinder-lifecycle-v1-2026-08-27
blocked_by: none
---

# Ticket 0087: enforce the Wayfinder lifecycle around persistent worker threads

## Question

Can the persistent scheduler maintain real worker occupancy while ensuring that
every terminal passes through independent evidence admission, serial canonical
reconciliation, a checked Wayfinder transition, and a fresh reconciled snapshot
before any result-dependent successor becomes eligible?

## Admitted defect

Scheduler v2 separates process lanes from its terminal inbox, but its
`reconcile` command currently accepts free-form disposition, reference, and
ledger-edge strings.  It does not authenticate a completed ticket/portfolio/map
transition or a post-reconciliation snapshot.  The daemon is therefore an
execution plane, not the complete rolling research pipeline.  Its deterministic
tests also replace the real worker launcher with a fake runner, so four database
rows have never established four production worker processes.

This is an `operational-only` process gap under `FP-14`.  It is not mathematical
evidence and changes no load-bearing destination dependency.

## Resolution

Keep immutable tasks, exact waves and reserves, SQLite process lanes,
resource/family/write-set gates, independently authenticated terminals, and
root-only canonical integration.  Do not make workers edit the Wayfinder or
trust their proof-distance self-assessment.

Add one serialized control-plane contract around each terminal:

1. create an immutable lifecycle-inbox item when the scheduler admits a
   terminal;
2. require a sealed lifecycle receipt binding the exact task, terminal, result,
   adjudication, pre/post canonical file receipts, required failure-genome
   anchor, Wayfinder checks, and fresh context snapshot;
3. refuse scheduler reconciliation until that receipt authenticates and its
   post-state still equals the live canonical state; and
4. allow immediate backfill only from already approved result-independent
   reserve work.  A result-dependent successor must bind the sealed lifecycle
   receipt and post-reconciliation snapshot in a newly approved packet.

Use one service-manager transport for daemon and worker supervision.  The
first acceptance envelope disables web search, builders, shared writes, and
same-thread retry.  No route selection, proof-movement assignment, canonical
edit, or user approval is delegated to a mathematical worker.

## Decision criteria

The repair is not live merely because unit tests or an observer daemon pass.
It requires all of the following:

- malformed, stale, incomplete, self-authored, or operationally inconsistent
  lifecycle receipts reject;
- mathematical negatives require one existing-record failure-genome anchor,
  while purely operational stops forbid a mathematical genome;
- a terminal cannot be marked reconciled until ticket, affected portfolio
  entry, map/ledger statement, validators, and fresh snapshot authenticate;
- deterministic full-path canaries start four actual supervised worker
  processes with a fifth queued, survive a scheduler-service restart without
  duplication, backfill the fifth within two polling intervals after one
  terminal, and retain the first terminal in the reconciliation inbox;
- an independent checker compares raw SQLite rows, process identities,
  service-manager state, event order, and immutable receipts rather than
  trusting scheduler `status`; and
- a separately approved five-task real Codex canary later passes the same
  production path.  No live research wave is eligible before that gate.

## Authorization inventory

The user's 2026-08-27 instruction to perform this work authorizes repository
implementation, this ticket and affected process documentation, stopping the
empty observer-only scheduler, isolated deterministic local canaries, focused
tests, Wayfinder checks, and the full repository gate.  It does not authorize a
Codex/provider call, web/network mode, mathematical reserve, route admission,
automatic canonical edits, software installation, destructive operation,
commit, or push.  The five-task live provider canary requires a later literal
decision binding its exact authorization, wave, reserve, packets, settings,
limits, and retry policy.

## Predeclared outcomes

- `THREAD-LIFECYCLE-LOCAL-READY`: lifecycle enforcement and independent local
  end-to-end canary pass; live provider acceptance remains the only process
  gate.
- `THREAD-LIFECYCLE-LIVE`: the separately approved five-task real Codex canary
  also passes four-worker, restart, backfill, terminal, and reconciliation
  checks.
- `THREAD-LIFECYCLE-DEFECT`: a lifecycle authority, canonical-state,
  supervision, restart, backfill, or independent-observer invariant fails.
- `THREAD-LIFECYCLE-OPERATIONAL-STOP`: implementation checks pass but the local
  user service manager cannot execute the isolated canary.  Do not substitute a
  chat-bound background process.

## Evidence

### Local acceptance lifecycle reconciliation

#### Worker 1

Terminal SHA-256
`b5b9ab3a9b60c0ecc4991dac8c074dcd0acef925441e5b925ebf6e78d58258fc`
is independently admitted as one process-only canary result.

- **Net proof movement:** `neutral`.
- **Evidence:** `proposal`.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** No mathematical destination obligation became smaller; only the local scheduler process path was exercised.
- **Counterfactual test:** Earlier knowledge would have exposed unit-name and asynchronous-stop defects before any research dispatch.
- **Planning consequence:** `retain`.
- **Load-bearing ledger edge:** `NONE`.
- **Failure genome:** none; this is not a mathematical negative.

#### Worker 2

Terminal SHA-256
`2edf3eb6a7fb81635d979463db10102d88ed78fd3a5a5fdb5c33c2077af6bcde`
is independently admitted as one process-only canary result.

- **Net proof movement:** `neutral`.
- **Evidence:** `proposal`.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** No mathematical destination obligation became smaller; only the local scheduler process path was exercised.
- **Counterfactual test:** Earlier knowledge would have exposed unit-name and asynchronous-stop defects before any research dispatch.
- **Planning consequence:** `retain`.
- **Load-bearing ledger edge:** `NONE`.
- **Failure genome:** none; this is not a mathematical negative.

#### Worker 3

Terminal SHA-256
`849b5ba3dfaed7b1547efe0dace4354160f9dbbf7c3a68f5b5c728cfc2223a09`
is independently admitted as one process-only canary result.

- **Net proof movement:** `neutral`.
- **Evidence:** `proposal`.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** No mathematical destination obligation became smaller; only the local scheduler process path was exercised.
- **Counterfactual test:** Earlier knowledge would have exposed unit-name and asynchronous-stop defects before any research dispatch.
- **Planning consequence:** `retain`.
- **Load-bearing ledger edge:** `NONE`.
- **Failure genome:** none; this is not a mathematical negative.

#### Worker 4

Terminal SHA-256
`3143403917465cfeef462f0aaccbbb92c4c91a346e7b9de7abba32eef1cd01cc`
is independently admitted as one process-only canary result.

- **Net proof movement:** `neutral`.
- **Evidence:** `proposal`.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** No mathematical destination obligation became smaller; only the local scheduler process path was exercised.
- **Counterfactual test:** Earlier knowledge would have exposed unit-name and asynchronous-stop defects before any research dispatch.
- **Planning consequence:** `retain`.
- **Load-bearing ledger edge:** `NONE`.
- **Failure genome:** none; this is not a mathematical negative.

#### Worker 5

Terminal SHA-256
`0161889fd37c06295c9da9c0bb186bc1abef8d0762887df76b703b1901665edb`
is independently admitted as one process-only canary result.

- **Net proof movement:** `neutral`.
- **Evidence:** `proposal`.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** No mathematical destination obligation became smaller; only the local scheduler process path was exercised.
- **Counterfactual test:** Earlier knowledge would have exposed unit-name and asynchronous-stop defects before any research dispatch.
- **Planning consequence:** `retain`.
- **Load-bearing ledger edge:** `NONE`.
- **Failure genome:** none; this is not a mathematical negative.

### Aggregate local process acceptance

The corrected immutable process-boundary run
`20260827-ticket0087-local-acceptance-v6` has result SHA-256
`908cb3ea775d78e70055e6ba42e5a199749b4f4515a7ca64f894ff408d16700d`.
Its independent raw-state checker authenticates four initially concurrent
systemd-supervised worker processes, a scheduler restart with distinct service
identity and no duplicate attempts, a fifth-worker backfill after 0.018032
seconds, five valid terminal lifecycle inboxes, and zero provider calls.  The
checker reads immutable SQLite snapshot SHA-256
`a74bb99f1269a568603e4688ebb72a2f32ddf38ce465ea6f42aa1712d4828ca8`,
so later legitimate lifecycle reconciliation cannot erase the process evidence.
All five v6 terminal receipts have now been independently sealed and accepted
by the scheduler's authenticated reconciliation transition. V6 ends with five
reconciled jobs, zero pending terminals, and four free lanes. The local outcome
is `THREAD-LIFECYCLE-LOCAL-READY`; the real-provider gate remains unrun and
separately authorized.

#### Immutable-snapshot rerun — Worker 1

Terminal SHA-256
`a39cda2fe5cc3db87eab356eeb049bb005ae47eb811fdc2c52524bed03a177d8`
is independently admitted as one process-only canary result.

- **Net proof movement:** `neutral`.
- **Evidence:** `proposal`.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** No mathematical destination obligation became smaller; only the local scheduler process path was exercised.
- **Counterfactual test:** Earlier knowledge would have exposed unit-name and asynchronous-stop defects before any research dispatch.
- **Planning consequence:** `retain`.
- **Load-bearing ledger edge:** `NONE`.
- **Failure genome:** none; this is not a mathematical negative.

#### Immutable-snapshot rerun — Worker 2

Terminal SHA-256
`e33a8478a833932927cd19657fb216e3081976a064e4749ce4ccf0bfd2404b34`
is independently admitted as one process-only canary result.

- **Net proof movement:** `neutral`.
- **Evidence:** `proposal`.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** No mathematical destination obligation became smaller; only the local scheduler process path was exercised.
- **Counterfactual test:** Earlier knowledge would have exposed unit-name and asynchronous-stop defects before any research dispatch.
- **Planning consequence:** `retain`.
- **Load-bearing ledger edge:** `NONE`.
- **Failure genome:** none; this is not a mathematical negative.

#### Immutable-snapshot rerun — Worker 3

Terminal SHA-256
`4cc66aad565497851f3eabefbbd756e64a1daa9b82521b93a2c2bc3d8a115a3c`
is independently admitted as one process-only canary result.

- **Net proof movement:** `neutral`.
- **Evidence:** `proposal`.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** No mathematical destination obligation became smaller; only the local scheduler process path was exercised.
- **Counterfactual test:** Earlier knowledge would have exposed unit-name and asynchronous-stop defects before any research dispatch.
- **Planning consequence:** `retain`.
- **Load-bearing ledger edge:** `NONE`.
- **Failure genome:** none; this is not a mathematical negative.

#### Immutable-snapshot rerun — Worker 4

Terminal SHA-256
`6c107b09f55329a649486c98b8af2f739720080518f3b33ce8b0b565fe4abf5d`
is independently admitted as one process-only canary result.

- **Net proof movement:** `neutral`.
- **Evidence:** `proposal`.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** No mathematical destination obligation became smaller; only the local scheduler process path was exercised.
- **Counterfactual test:** Earlier knowledge would have exposed unit-name and asynchronous-stop defects before any research dispatch.
- **Planning consequence:** `retain`.
- **Load-bearing ledger edge:** `NONE`.
- **Failure genome:** none; this is not a mathematical negative.

#### Immutable-snapshot rerun — Worker 5

Terminal SHA-256
`63073ae2ee58c5b36978e74f95fd3d5e97fdb9eb0d546d89181cfd7a48ba3c4c`
is independently admitted as one process-only canary result.

- **Net proof movement:** `neutral`.
- **Evidence:** `proposal`.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** No mathematical destination obligation became smaller; only the local scheduler process path was exercised.
- **Counterfactual test:** Earlier knowledge would have exposed unit-name and asynchronous-stop defects before any research dispatch.
- **Planning consequence:** `retain`.
- **Load-bearing ledger edge:** `NONE`.
- **Failure genome:** none; this is not a mathematical negative.

This fifth lifecycle receipt has SHA-256
`2ec9ad144936c84a6077163a0a25e65b8cc1074e984a5e69cbb2555fcfed9741`.
The scheduler accepted it in reconciliation SHA-256
`852a762aba4aeef8e6d3d7a766a6d688f53e148316423fe4e7f133600fe92486`,
completing the local lifecycle sequence.

### Local outcome

`THREAD-LIFECYCLE-LOCAL-READY` is admitted. This is a process result only.
Production research dispatch remains stopped, and `THREAD-LIFECYCLE-LIVE`
still requires the separately approved exact five-task real Codex canary.

Validation at this boundary:

- the independent v6 acceptance checker passes again after all five scheduler
  reconciliations, proving that the process receipt is immutable rather than a
  hash of mutable live state;
- 24 focused scheduler and lifecycle tests pass;
- agent orchestration, Wayfinder status, and all 19 frontier-portfolio records
  validate; and
- the full `make test` gate exits zero, including the 11,746-job Lean build and
  all 348 Python tests.

## Proof-distance accounting

- **Net proof movement:** `neutral` by construction.
- **Evidence:** operational implementation and checked process behavior only.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** no mathematical obligation; only the gap between a
  worker terminal and an authenticated, current Wayfinder state can shrink.
- **Counterfactual test:** a passing implementation would prevent unintegrated
  terminals, stale successor selection, and simulated occupancy from being
  reported as a functioning rolling pipeline, but would not shorten the exact
  Erdős--Szekeres proof.
- **Planning consequence:** retain `FP-14` gated until live acceptance; do not
  schedule another scheduler feature or mathematical reserve first.
- **Load-bearing ledger:** no mathematical edge changes.

## Frozen live-provider canary v1

The next process gate is now concrete but unapproved. Five validator-clean,
proposal-only `research_card_auditor` packets use disjoint result/ready paths,
one immutable barrier control each, 10 minutes, one CPU, 2 GiB memory, 0.01 GiB
output, `gpt-5.6-sol` at low effort, disabled web search, and zero retry. Their
task SHA-256 values in priority order are:

1. `b522b2421e8487ecb9880ec19d34de3119565a0b9267d3ef46bb6089d01b1ede`;
2. `92ee1bad607d0ff9496421242f6a7e7e53816ad4ee348e444761a10280d5ce48`;
3. `758bc14bfcd57ec4a458da0ad067711c6fa6ca2daebadcad831a4125fae372c6`;
4. `cbdc8fe77bebabdd1d8935692b5aef82e33d2c751e1efbfd06356c35a9e5c3b1`;
5. `d609a88ccf0403b3415ee7502be9b02ce312b19f6637565d38ad7b27742acfe6`.

Candidate operational-wave SHA-256 is
`c1d28b9ad59b6ea776321dc1cb530ce200f9ecb59ef21cdfca7372b6cdbafd81`.
The first four workers must create exact ready markers before root restarts the
scheduler service; only then is worker one released. Worker five must move from
queued to supervised, create its own ready marker, and backfill within two
five-second poll intervals after the first terminal. Root then releases the
other four. No task assesses mathematics or edits a canonical file.

The live runner and independent raw-state checker have SHA-256 values
`3e8f91df66e80d7d13f99badd268b01cd089f2def4b01dcf72b251d59fadb5e1`
and
`38d40ae5a4e20c34468ed2035d0558c33d59090cc923355d61415890faf156dc`.
They verify exact provider commands, four initial systemd units, service
identity change without worker loss or duplicate attempts, one fifth-worker
backfill, five distinct thread IDs, five byte-identical structured
result/last-message pairs, five lifecycle inboxes, disabled network, and zero
resume. Both scripts compile; the 24 focused scheduler/lifecycle tests and all
Wayfinder/orchestration checks pass.

An isolated current-code static preflight then created no service and made no
provider call, but authenticated the complete five-task wave, barrier controls,
provider metadata, budgets, write sets, and output absence; reserve SHA-256
`24cf4f5ff1e7201288c7b6f175e380027ffbb387246778def44e609c8def7261`
imported all five jobs with `--no-backfill`. Import receipt SHA-256 is
`57453076450da7dbc57dfef128c5d2ac6db712cf4480da1efb62c49e4b3687a7`.
Raw isolated state shows five queued support jobs, four free lanes, zero
attempts, and exactly the highest-priority worker as the next compatible
candidate. This preflight is not the future successor-bound production
reserve and carries no launch authority.

Dispatch activation contract v2 has SHA-256
`40f8bda0a9ebc85d643fd90992cd9e492aaa1c402add51f6fa77e3b72d708c11`.
It is necessary because the current observer receipt predates the admitted
lifecycle implementation and therefore rejects fail-closed. The raw production
database is empty with four free lanes and no events. The current sandbox could
not connect to the user-systemd bus, so the contract makes a reachable
supervising user manager a mandatory activation-time stop gate; no chat-bound
fallback exists.

No reserve can be frozen until an approved activation prints the exact
successor authorization path and hash. Activation itself launches no provider.
The later live-canary reserve and provider launch require a second literal
decision binding that successor, all five packets, the wave, runner/checker,
provider settings, zero retry, and exact reserve hash.

**Net proof movement:** neutral. **Evidence:** authenticated immutable process
plans and static/focused implementation checks only. **Damage scope:**
`operational-only`. **Difficulty displaced:** no mathematical obligation and
not yet the live-provider process gap. **Counterfactual test:** the barrier
design removes timing-dependent sleeps and makes restart/backfill failure
observable, but no proof work becomes smaller before a passing live terminal.
**Planning consequence:** obtain the exact route-review and activation
decisions, create the successor-bound reserve only after successful empty
activation, then seek the separate live launch decision. **Load-bearing ledger
edge:** none.
