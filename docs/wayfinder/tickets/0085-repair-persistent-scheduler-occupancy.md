---
title: Repair persistent scheduler occupancy and reserve continuity
type: research
mode: HITL
status: closed
claim: persistent-approved-reserve-scheduler-v2-2026-08-26
blocked_by: none
---

# Ticket 0085: repair persistent scheduler occupancy and reserve continuity

## Question

Can the persistent scheduler actually backfill completed process slots from an
approved reserve without allowing unreconciled agent output to influence route
selection, proof movement, or canonical state?

## Admitted diagnosis

The live Ticket-0084 service was operational but incapable of meeting the
user's intended occupancy semantics. Its active receipt was observer-only, its
queue was empty, and its v1 state machine kept an exited worker's process lane
occupied until chat-side reconciliation. Even a dispatch-enabled v1 instance
would therefore drain a finite manually enqueued queue and stall. This is an
architecture-level process defect under `FP-14`, not mathematical evidence.

## Decision criteria

Accept v2 only if all of the following hold under deterministic tests:

- one immutable approved reserve plan exactly covers one authenticated
  operational wave, binds the active standing authorization and literal user
  approval, and preflights every task before any job is admitted;
- an interrupted reserve import is idempotent only for byte-identical remnants
  and can neither duplicate nor silently change a job;
- four compatible mathematical jobs launch while an additional approved
  mathematical reserve remains queued;
- a valid or operational terminal immediately frees its process lane and the
  same tick can backfill an independent approved job;
- the terminal remains pending for root reconciliation and cannot influence a
  successor;
- late reconciliation cannot free or mutate a lane already reused by another
  job;
- resource, builder, mechanism-family, write-set, output-absence, forbidden
  control, terminal-authentication, and same-thread-resume gates remain intact;
- status separately reports active mathematics, mathematical reserve, pending
  reconciliation, and whether the occupancy invariant is healthy; and
- daemon liveness authenticates boot/start process identity rather than PID
  existence alone.

## Resolution

Implement scheduler v2 in a new preserved service directory and protocol.
Separate process-lane release from evidence reconciliation, add an exact
approved-reserve import contract, and refuse live dispatch until the new code,
standing receipt, operational wave, reserve plan, and literal user decision all
authenticate together. Ticket 0084 and its observer state remain historical;
no v1 receipt is rewritten or reused.

## Frozen v2 boundary

The scheduler remains an executor. It cannot generate or approve packets,
select routes, interpret a terminal to choose a successor, reconcile evidence,
assign proof movement, edit canonical files, spawn subagents, or dispatch a
provider without a new dispatch-enabled standing receipt and exact approved
reserve. Four is still an occupancy target rather than permission to pad the
queue with correlated or non-mathematical work.

Process occupancy is separated from evidence admission. A worker's process
lane ends when its supervised process ends. Its immutable terminal then lives
in a root-only reconciliation inbox; root authentication and all proof-distance
accounting remain mandatory before the result can affect planning.

## Authorization inventory

On 2026-08-26 the user explicitly directed root to fix the scheduler after the
current mathematical work closed. This authorizes stopping only the idle v1
observer service, repository implementation, new schemas and documentation,
ignored dry-run state, deterministic fake-runner simulations, and repository
tests. It does not yet authorize a provider call, a mathematical task packet,
live web search, a dispatch-enabled standing receipt, automatic evidence
reconciliation, external mutation, commit, or push. Those require one later
exact decision binding the new authorization and reserve hashes.

## Predeclared outcomes

- `RESEARCH-SCHEDULER-V2-READY`: focused and workflow tests pass, v2 observer
  authority authenticates, and the preserved v1 service remains stopped; live
  dispatch waits only for an exact approved reserve decision.
- `RESEARCH-SCHEDULER-V2-LIVE`: in addition, a separately approved standing
  receipt and current reserve import successfully start real workers.
- `RESEARCH-SCHEDULER-V2-DEFECT`: any admission, lane-reuse, crash-recovery, or
  authority test fails; repair before activation.
- `RESEARCH-SCHEDULER-V2-OPERATIONAL-STOP`: the code passes but the user service
  manager cannot activate the authenticated observer service; retain exact
  commands and do not use a chat-bound fallback.

## Evidence

The predeclared terminal is `RESEARCH-SCHEDULER-V2-READY`. Eighteen focused
tests pass. They cover complete eight-job reserve import, byte-identical crash
recovery and corrupt-remnant rejection, exact wave coverage, all-batch
preflight failure, four-active-plus-four-reserve occupancy, immediate terminal
backfill, lane-reuse safety under late reconciliation, forged-terminal
downgrade, result drift, authorization capability/limit widening, authenticated
same-thread resume, and boot/start process identity. The complete Python suite
passes 342 tests. `make test` exits zero after the 11,744-job Lean build and all
repository certificate and workflow checks.

The historical v1 observer was stopped without touching worker units; it had no
workers. The separately preserved v2 observer is enabled and live under
authorization SHA-256
`98c1d645d7df1e55d8acbb86da8d2b2118b603f26b87c8811de1460786b50f34`,
implementation SHA-256
`f3833688f8d3ff91a94ef5e544fe0a0094df5239b7653f528a6916ff86ffe88c`,
and service identity `4ee04456-661c-4881-88d4-b5c4eac65af5`. `doctor` passes
against Codex CLI `0.150.0` and the user-systemd manager. Status authenticates
the daemon's boot/start identity and truthfully reports four free lanes, zero
active or queued jobs, zero pending reconciliations, occupancy unhealthy, and
dispatch disabled. No provider call occurred.

Live mathematical occupancy is deliberately not claimed. It requires a new
dispatch-enabled standing receipt plus one current exact approved reserve; old
waves cannot be reused.

## Proof-distance accounting

- **Net proof movement:** `neutral` by construction.
- **Evidence:** operational implementation and deterministic tests only.
- **Damage scope:** `architecture-level` for the admitted v1 occupancy defect;
  any activation or supervisor failure is `operational-only`.
- **Difficulty displaced:** no mathematical obligation. The intended reduction
  is from terminal-to-backfill latency and manual per-packet queue handling to
  an approved reserve transaction; producing honest executable mathematics and
  reconciling its results remain with root.
- **Counterfactual test:** if v2 had existed before the last run, an exited
  worker would not have held a compute lane and a preapproved independent
  reserve would have backfilled automatically. With no approved reserve, it
  would still have reported an honest stop rather than manufacturing work.
- **Planning consequence:** retain under `FP-14` only if the invariant tests
  pass; activation remains gated on exact current packets and a new user
  decision.
- **Load-bearing ledger:** no mathematical edge changes.
