---
title: Build a persistent approved-packet research scheduler
type: research
mode: HITL
status: closed
claim: persistent-approved-packet-scheduler-v1-2026-08-26
blocked_by: none
---

# Ticket 0084: build a persistent approved-packet research scheduler

## Question

Can the rolling pipeline move worker dispatch, process monitoring, resource
enforcement, crash recovery, and ready-queue backfill out of chat while
preserving exact packet approval, no-padding, root-only evidence admission,
mechanism-family diversity, and serialized builder/integration boundaries?

## Decision criteria

Accept v1 only if the scheduler can fill four lanes from four exact approved
packets in a deterministic test; refuses stale, duplicate, historical-control,
or pre-populated packets; enforces family, builder, resource, and write-set
limits; independently rejects a forged terminal; blocks completed lanes until
root reconciliation; preserves a resumable same-thread checkpoint; survives
chat termination under an enabled user service; and reports an empty approved
queue without padding. No live provider call is part of this ticket.

## Resolution

On 2026-08-26 the user identified that neither four mathematical lanes nor the
continuous proposal loop was actually running and then explicitly directed
root to build the scheduler. Build v1 as a separately authorized user-systemd
service. This decision authorizes repository implementation, focused tests,
ignored dry-run receipts, and an observer-only persistent configuration. It
does not by itself approve any mathematical packet, a provider call, live web
search, automatic reconciliation, route mutation, canonical edit, model or
resource widening, or reuse of an old approved wave.

## Frozen v1 contract

- durable SQLite WAL state for lanes, jobs, attempts, and events, plus
  immutable human-auditable JSON receipts;
- four-worker mathematical occupancy target, mathematical-first queue order,
  no padding, maximum two active lanes from one mechanism family, and one
  builder at a time;
- exact authentication of the task packet, all direct inputs, registered
  profile, base revision, output absence, approved operational wave, standing
  authorization, generated worker prompt, Codex executable/version, and final
  result;
- one transient user-systemd unit per worker with the task's CPU, memory,
  wall-time, task-count, file-size, and output ceilings;
- Codex noninteractive JSONL execution with approval policy `never`, no
  subagents, no danger-full-access, and the ordinary result JSON schema;
- web search disabled unless the exact dispatch opts into `live` under its
  approval reference;
- optional single same-thread recovery only when the first attempt published
  an authenticated thread ID and the dispatch explicitly set a resume limit of
  one;
- independent comparison of owned `result.json`, structured last message, and
  ordinary task/result validation before recognizing a valid terminal; and
- every terminal lane blocks pending root reconciliation. Only a receipt bound
  to the terminal hash, canonical reconciliation reference, disposition, and
  ledger edge releases the lane and triggers backfill.

## Authority firewall

The scheduler cannot generate or approve a task, infer a successor, consume an
idea batch, admit evidence, assign damage scope or proof movement, create a
failure genome, edit the Wayfinder, change a theorem, commit, push, install
software, widen resources, or terminate unrelated processes. The historical
Factory v3 control is explicitly non-dispatchable. The idea generator and
research scheduler have separate receipts and no cross-service authority.

## Predeclared outcomes

- `RESEARCH-SCHEDULER-V1-LIVE`: focused tests and repository workflow gates
  pass, an observer-only authorization authenticates, and an enabled persistent
  service reports a fresh heartbeat and an honest empty queue without launching
  a provider.
- `RESEARCH-SCHEDULER-V1-CODE-READY`: code, schema, tests, docs, dry-run state,
  and unit file pass, but this execution namespace cannot access the already
  running user service manager; preserve the exact activation command and do
  not fall back to a chat-bound background process.
- `RESEARCH-SCHEDULER-V1-DEFECT`: packet, authority, queue, resource, terminal,
  resume, or reconciliation tests expose a contract defect; repair under the
  same scope before configuration.
- `RESEARCH-SCHEDULER-V1-TEST-STOP`: repository or environment gates fail for
  an unrelated pre-existing reason; report the exact boundary without claiming
  scheduler acceptance.

## Approval inventory

- already authorized: repository code, schema, documentation, ticket, focused
  test, workflow validation, ignored observer-state creation, and an attempted
  persistent observer-only service start;
- not authorized: dispatch-enabled standing authority, any provider/network
  call, any mathematical packet enqueue, automatic evidence reconciliation,
  process termination, software installation, resource increases, external
  repository mutation, commit, or push;
- platform prompt: none is available in this managed session. The start command
  may fail if its user-systemd bus is outside this namespace; v1 must refuse an
  unsupervised fallback; and
- future exact mathematical waves require their own packet hashes, approved
  wave receipt, dispatch labels, mechanism families, provider settings, and
  user decision.

## Evidence gate

Run the scheduler unit tests and Python compilation; ordinary agent,
campaign, rolling-pipeline, Wayfinder, and portfolio validators; `git diff
--check`; then the full repository gate if the existing dirty proof tree fits
the declared local resource ceiling. Configure observer-only authority, run
`doctor`, attempt the persistent start, and inspect process-backed status. No
provider worker may launch during this ticket.

## Live evidence

The predeclared terminal is `RESEARCH-SCHEDULER-V1-LIVE`.  Eleven focused
scheduler tests pass, including deterministic four-lane fill, honest empty
undercapacity, exact packet/wave/prompt binding, stale-output and historical
control rejection, family/builder/resource/write-set exclusion, forged
terminal rejection, lane blocking before reconciliation, one authenticated
same-thread resume, and refusal to reconcile a result changed after terminal
publication.  The complete Python suite passes 330 tests, the campaign,
orchestration, rolling-pipeline, Wayfinder, and portfolio validators pass,
`git diff --check` passes, and `make test` exits zero after the full Lean build
and repository workflow checks.

The enabled user-systemd unit is active with a fresh process-backed heartbeat.
Its observer authorization SHA-256 is
`1b7647096ba182596f99124a1a44a3c77ee04dcdb8ee33c6f4c6ffbb7f4f11f3`,
service identity is `a9a0dcb3-8fd1-4e3c-b518-270c935a2c90`, and authenticated
implementation SHA-256 is
`0ec267989f961af92d7f81c45027b3fe6cf5884ca54dc4abd7ce8ee8b24b4bfe`.
Status truthfully reports four free lanes, zero jobs, zero mathematical
workers, an empty approved reserve, and dispatch disabled by observer-only
authority.  No provider call or mathematical dispatch occurred.  The first
`systemctl --user` frontend attempt stopped with an environment-level `No data
available`; direct authenticated user-systemd D-Bus activation replaced that
frontend and passed `doctor`.  The initial stop is `operational-only` and does
not alter the accepted terminal.

## Proof-distance accounting

- **Net proof movement:** `neutral` by construction.
- **Evidence:** operational implementation and tests only.
- **Damage scope:** `operational-only` for a code, supervisor, activation, or
  environment stop; no mathematical failure genome.
- **Difficulty displaced:** no mathematical obligation. The service displaces
  chat-bound dispatch, telemetry, resource, crash, and queue bookkeeping, but
  root reconciliation and the production of honest approved packets remain.
- **Counterfactual test:** the service would have exposed zero active workers
  and an empty reserve immediately after the last wave instead of allowing a
  stale board to imply activity. It would not have produced a theorem or an
  approved replacement packet.
- **Planning consequence:** retain as `FP-14` process infrastructure; enable
  dispatch only after a separate exact standing decision and populate it only
  with current approved packets.
- **Load-bearing ledger:** no edge changes.
