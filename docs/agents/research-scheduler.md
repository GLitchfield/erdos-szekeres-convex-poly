# Persistent research scheduler

The research scheduler v2 is the chat-independent execution layer for the
rolling pipeline. It maintains process-backed telemetry, a durable queue of
exact approved task packets, and a separate root-only reconciliation inbox. It
is not a research director, evidence referee, route selector, or substitute for
the Wayfinder.

The scheduler uses the installed Codex non-interactive interface with JSONL
events and a structured final-result schema. This follows the official Codex
automation interface documented at
<https://learn.chatgpt.com/docs/non-interactive-mode>. A future SDK backend may
replace the process launcher without changing the queue or authority contract.

## What it fixes

The old rolling board was a declaration checked after manual dispatch. It did
not own workers, observe their processes, survive a chat turn, or refill a
vacancy. The scheduler now owns those operational responsibilities:

- an SQLite write-ahead-log database records jobs, lanes, attempts, and events;
- immutable JSON receipts bind every task, approval wave, profile, provider,
  prompt, resource budget, and standing authorization;
- a user-systemd service survives chat termination and WSL restarts;
- each worker runs in its own transient systemd control group with explicit
  CPU, memory, task-count, wall-time, file-size, and output limits;
- the daemon prefers mathematical jobs, enforces one builder at a time,
  prevents overlapping write sets, and caps correlated mechanism-family
  concentration;
- one authenticated reserve plan imports every exact task in one approved wave
  after preflighting the complete batch, and an interrupted import can resume
  only when every surviving byte is identical;
- Codex JSONL output supplies process telemetry and a resumable thread ID;
- a packet may opt into at most one same-thread crash resume; and
- a terminal worker releases its process lane immediately while its immutable
  result remains pending in the reconciliation inbox; and
- status reports actual queue/process state and explicit under-capacity reasons
  rather than copying agent names from a board.

Four mathematical investigations is the target, not a padding rule. An empty
approved queue is reported as empty. Seed generation, source grounding, and
route review may use otherwise idle capacity only when they have their own
approved packets and are labeled as support.

Ticket 0103 currently overrides automatic support backfill and the default
four-packet reserve floor. While no `advancing` entry and no theorem-ready
producer exist, an honest approved reserve may contain zero to three packets;
do not manufacture support work to restore occupancy. The scheduler remains
intentionally paused/stopped. The commands below document the implementation
but provide no current restart authority. Before any restart, diagnose and
report the stopped implementation and receipt state, identify a theorem-first
workload satisfying Ticket 0103, obtain a valid current implementation and
receipt, and receive a new explicit user decision.

## Authority boundary

Three independently authenticated layers govern a bulk-dispatched provider
process.

1. A standing scheduler authorization binds the implementation hashes, Codex
   executable and version, allowed models, capacity, aggregate resources,
   builder and family limits, and whether dispatch is enabled.
2. An approved reserve plan binds that standing authorization, a literal user
   decision, an authenticated `approved-operational-wave`, and the complete
   per-job dispatch metadata. Its task set must equal the wave task set.
3. Every queued job binds one schema-valid immutable task packet to its exact
   wave, reserve plan, generated prompt, profile, resources, and provider
   settings. The single-job command retains the same exact packet/wave/user
   boundary without a reserve plan.

The service refuses danger-full-access, automatic approvals, subagents,
canonical edits, route admission, proof-movement assignment, and automatic
reconciliation. The historical
`sol-factory-refresh-014-current-state-v3` control is hard-blocked in addition
to its repository disposition.

A worker final is checked three ways: Codex must satisfy the result output
schema, the owned `result.json` must be byte-for-byte the same JSON object as
the structured last message, and the ordinary task/result validator must
accept the pair. The scheduler independently repeats those checks before
changing lane state. A forged `valid_result` terminal is downgraded to an
operational stop.

## Process lanes and reconciliation inbox

The state machine is:

```text
queued -> dispatching -> running -> terminal inbox + lane free -> immediate backfill
                                      |
                                      +--root receipt--> reconciled/rejected
```

Process occupancy and evidence admission are different resources. Once the
worker process ends, its lane is free and may be filled from the approved
reserve in the same scheduler transaction. The terminal remains pending in a
separate inbox. Root must still authenticate the evidence, perform the
failure-genome and proof-distance accounting, update the canonical record, and
bind the exact terminal hash in a reconciliation receipt before any result can
affect research direction. Reconciliation never frees a lane, so a late receipt
cannot clobber a replacement worker already using that lane.

The scheduler therefore continues only already approved, result-independent
work through a reconciliation backlog. It still cannot infer a successor from
an unreconciled result or manufacture work when the approved reserve is empty.
Every admitted terminal receives an immutable `lifecycle-inbox` item binding
its exact task, dispatch, terminal, result (when valid), and owning Wayfinder
ticket.

## Serialized Wayfinder control plane

A worker result cannot close its scheduler job directly. Root first prepares a
serial integration draft and pre-state snapshot:

```text
python3 scripts/check_wayfinder_thread_lifecycle.py prepare \
  --service-dir runs/agents/research-scheduler-v2 \
  --job-id <job-id> \
  --output runs/agents/<run>/lifecycle/<job-id>/draft.json \
  --pre-snapshot runs/agents/<run>/lifecycle/<job-id>/pre-snapshot.json
```

Root independently adjudicates the evidence, updates the owning ticket,
affected portfolio entry, and map/ledger statement, adds one existing-record
failure-genome anchor when required, runs the Wayfinder checks, and freezes a
post-state context snapshot. The checker then seals a receipt:

```text
python3 scripts/check_wayfinder_thread_lifecycle.py seal \
  --service-dir runs/agents/research-scheduler-v2 \
  --job-id <job-id> \
  --draft <draft.json> \
  --adjudication <root-adjudication.json> \
  --post-snapshot <post-snapshot.json> \
  --approval-ref <root-reconciliation-reference> \
  --output <lifecycle-receipt.json>
```

The receipt binds proof movement, evidence, damage scope, displaced difficulty,
counterfactual, planning consequence, ledger edge, affected `FP-NN` entries,
pre/post canonical hashes, snapshots, and check outputs. Operational stops
forbid mathematical genomes; admitted mathematical negatives require exactly
one genome anchor in an existing route record. Workers cannot create this
receipt because their packets cannot own canonical Wayfinder paths.

## Standing authorization

V2 uses the preserved, separate state directory
`runs/agents/research-scheduler-v2`; the v1 directory remains historical.

The following configuration examples are inactive while the Ticket 0103 hold
is in force. Historical or observer receipts grant no dispatch authority, and
the shown reserve floor is not the current planning requirement.

An observer-only receipt is safe to start without provider authority:

```text
python3 scripts/research_scheduler.py configure \
  --approval-ref <literal-user-decision>
```

Dispatch requires a new receipt created while the service is stopped:

```text
python3 scripts/research_scheduler.py configure \
  --approval-ref <literal-user-decision> \
  --dispatch-enabled \
  --capacity 4 \
  --mathematical-target 4 \
  --reserve-floor 4 \
  --max-builders 1 \
  --max-same-family 2 \
  --total-cpu-cores 8 \
  --total-memory-gib 32 \
  --total-output-gib 5
```

Configuration prints the immutable authorization path and SHA-256. Start only
that receipt:

```text
python3 scripts/research_scheduler.py start \
  --authorization <printed-path> \
  --authorization-sha256 <printed-sha256>
```

Changing scheduler code, schemas, the agent manifest, Codex version, model
set, limits, or authority invalidates the active receipt. Stop, obtain the
needed decision, and rotate to a new immutable authorization; never edit an
old authorization.

## Queue one approved task

The packet must still authenticate, freeze its registered profile, have no
pre-existing deliverable, and appear with its exact hash in the named approved
wave:

```text
python3 scripts/research_scheduler.py enqueue \
  --task-packet runs/agents/<run>/ready/<task>.json \
  --task-sha256 <sha256> \
  --operational-wave runs/agents/<run>/approved-operational-wave.json \
  --wave-sha256 <sha256> \
  --approval-ref <literal-user-decision> \
  --slot-label proof-producing \
  --occupancy-class mathematical \
  --mechanism-family <stable-family>
```

Web search is disabled unless `--web-search live` is explicitly included in
the approved dispatch. `--resume-limit 1` permits one continuation of the same
authenticated Codex thread after an operational interruption; it does not
authorize a fresh attempt or a changed packet.

## Import an approved reserve

For sustained occupancy, freeze one reserve-plan JSON object conforming to
`docs/agents/schemas/research-scheduler-reserve.schema.json`. It must bind the
active standing authorization, literal approval reference, exact approved wave,
and one dispatch specification for every task in that wave. Preflight and stage
it without launching providers:

```text
python3 scripts/research_scheduler.py import-reserve \
  --reserve-plan runs/agents/<run>/approved-scheduler-reserve.json \
  --reserve-sha256 <sha256> \
  --approval-ref <literal-user-decision> \
  --no-backfill
```

Omit `--no-backfill` only when the exact plan is approved for immediate live
dispatch. The importer preflights the entire batch before admitting any job.
Filesystem remnants from an interrupted import are accepted only byte-for-byte,
making the exact import safely repeatable without duplicating jobs.

## Observe and reconcile

```text
python3 scripts/research_scheduler.py status
python3 scripts/research_scheduler.py doctor
```

After root completes canonical reconciliation and seals that lifecycle receipt:

```text
python3 scripts/research_scheduler.py reconcile \
  --job-id <job-id> \
  --terminal-sha256 <sha256> \
  --lifecycle-receipt <lifecycle-receipt.json> \
  --lifecycle-sha256 <sha256>
```

The independent lifecycle checker reruns task/result, Wayfinder-status, and
portfolio validation and requires the live canonical bytes to equal the sealed
post-state. Reconciliation writes a separate immutable receipt. The process
lane was already released at terminal, and the command cannot mutate any
currently occupied lane. It does not itself edit the Wayfinder.

Stopping the scheduler leaves independently supervised live worker units
untouched:

```text
python3 scripts/research_scheduler.py stop --reason <reason>
```

## Validation

Run the focused gates with:

```text
python3 -m unittest scripts.test_research_scheduler
python3 -m unittest scripts.test_check_wayfinder_thread_lifecycle
python3 -m py_compile scripts/research_scheduler.py
python3 scripts/check_agent_orchestration.py
```

The local process acceptance gate is deliberately separate from unit tests:

```text
python3 scripts/run_research_scheduler_acceptance.py --run-id <fresh-run-id>
python3 scripts/check_research_scheduler_acceptance.py \
  --result runs/agents/<fresh-run-id>/acceptance-result.json \
  --result-sha256 <sha256>
```

It uses a frozen no-network fake Codex executable to prove four real supervised
workers, one queued reserve, scheduler-service restart without worker loss or
duplicate attempts, fifth-worker backfill within two poll intervals, and five
immutable lifecycle inboxes. It is not provider acceptance. A separately
approved five-task real Codex canary remains mandatory before live research
dispatch is claimed.

The full repository gate remains `make test`. Scheduler state and transcripts
belong under ignored `runs/agents/research-scheduler-v2/`; durable mathematical
conclusions still belong only in the existing Wayfinder, experiment, source,
or Lean artifacts.
