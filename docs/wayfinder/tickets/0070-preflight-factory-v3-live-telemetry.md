---
title: Preflight Factory v3 live telemetry and isolation
type: research
mode: HITL
status: closed
claim: codex-factory-v3-live-telemetry-preflight-2026-08-22
blocked_by: none
---

# Ticket 0070: preflight Factory v3 live telemetry and isolation

## Question

Can the admitted synthetic Factory-v3 canary be connected to a live Codex
runtime in a way that makes invocation provenance, exact input isolation,
source-event timing, and skeleton-before-source ordering harness-attested
rather than provider-authored assertions, before requesting authority for even
one nonresearch provider call?

## Decision criteria

- `V3-LIVE-CANARY-PACKET-READY`: a local checker, exact nonresearch task,
  isolated runtime layout, output schema, event-receipt contract, corruption
  controls, and one-call command/approval inventory are frozen.  Every field
  required from the live platform has a named trusted producer.  The packet
  authorizes no call.
- `V3-LIVE-TELEMETRY-ARCHITECTURE-GAP`: the available Codex CLI, app-server,
  collaboration, or Responses interfaces cannot expose a stable event needed
  by the pilot without a materially different runtime architecture.
- `V3-LIVE-INPUT-ISOLATION-GAP`: no technically enforced runtime can limit a
  call to its frozen visible input set and permitted source tool while
  withholding the rest of the shared repository and pilot-private tree.
- `V3-LIVE-SKELETON-GATE-GAP`: native source access cannot be disabled until a
  harness-sealed skeleton exists.  A task instruction or post-hoc provider
  statement does not close this outcome.
- `V3-LIVE-PREFLIGHT-OPERATIONAL-STOP`: the local protocol or checker cannot be
  completed inside the bounded work packet without unplanned authority.

More than one gap label may hold.  A gap may motivate a separately reviewed
architecture mutation, but does not authorize that mutation or the live call.

## Resolution

Run one local-only preflight before asking for the Ticket-0069 real-call
telemetry canary.  The preflight has three independent read-only audits and one
root-owned integration lane:

1. audit the actual Codex 0.149.0 CLI/app-server event and sandbox surfaces
   against the official OpenAI documentation and generated local protocol
   schema;
2. audit the admitted pilot checker for every field that is still synthetic,
   self-authored, or semantically under-adjudicated;
3. freeze the smallest one-call, nonresearch telemetry canary and adversarially
   enumerate what a passing transcript would and would not establish; and
4. implement only the deterministic receipt validator and corruption tests
   justified by those audits.

No provider, collaboration subagent used as the canary, primary-source search,
networked source proxy, MCP server, external Responses request, or ten-call
pilot runs in this ticket without a later exact user authorization and the
corresponding platform prompt.

## Evidence at launch

- Ticket 0069 closes on `V3-CANARY-READY` only at synthetic scope, with the
  final checker and context audits independently admitted;
- its conditional pilot-plan audit requires authentic platform receipts,
  enforced exact input isolation, trusted source intervals, a sealed
  skeleton-before-source event, and dual agreement on every counted semantic
  field;
- the official Codex non-interactive documentation states that `codex exec
  --json` emits JSONL lifecycle events including `thread.started`,
  `turn.started`, `turn.completed`, and `item.*`;
- the locally generated Codex 0.149.0 app-server schema gives thread and turn
  identifiers, turn start/completion times, and item start/completion times;
- the official hook documentation states that `PreToolUse` and `PostToolUse`
  do not observe hosted tools such as `WebSearch`, so native hosted search
  cannot itself be the enforcement point for skeleton-before-source; and
- the current synthetic checker authenticates internally consistent invocation
  JSON, but the JSON is not yet bound to an external runtime receipt, while
  its auditors currently return only `status` rather than every semantic field
  used in public counts.

Official interface references:

- <https://developers.openai.com/codex/noninteractive>
- <https://developers.openai.com/codex/hooks>
- <https://developers.openai.com/codex/sandboxing>
- <https://developers.openai.com/api/reference/cli/resources/responses/methods/create>

## Exact local execution packet

| stream | class | owner | ceiling | write set |
| --- | --- | --- | ---: | --- |
| platform capability audit | read-only process audit | delegated reviewer | 25 min | one ignored report and standard result under the Ticket-0070 run root |
| checker/semantic audit | read-only process audit | delegated reviewer | 25 min | one ignored report and standard result under the Ticket-0070 run root |
| canary contract audit | read-only process design | delegated reviewer | 25 min | one ignored report and standard result under the Ticket-0070 run root |
| validator, controls, integration | local process implementation | root | 60 min | one new checker and test module, this ticket, and ignored Ticket-0070 artifacts |

This is zero proof-producing and zero information-gathering mathematical
threads.  The three delegated lanes are operational review, not a mathematical
execution slate.  The forecast is 45--90 minutes with a 120-minute local hard
wall, one builder, at most four active agents, two CPU cores, 4 GiB RAM, and
0.10 GiB under the ignored run root.

## Authority inventory

The user's instruction to proceed authorizes the bounded local work above,
including read-only inspection of installed Codex interfaces and official
OpenAI documentation already opened for this preflight.  It does not authorize
the nonresearch canary itself.

No provider call, new general web research, software installation, resource
increase, process termination, destructive operation, git staging/commit/push,
issue or PR mutation, publication, login change, GUI, Lean/Lake, SAT/SMT, or
external repository mutation is planned.  If the preflight reaches
`V3-LIVE-CANARY-PACKET-READY`, root must present one separate exact request for
the single Codex/provider call, its model and effort, command, sandbox, source
authority, 15-minute wall, output paths, and conditional interruption target.

## One-call scope ceiling

The later canary contains no Erdős--Szekeres question, candidate, prior idea,
source query, or private pilot text.  It can at most show that one chosen
runtime emits a unique invocation/thread/turn identity, binds an exact task and
input fingerprint, emits usable start/end and item events, and authenticates a
schema-conforming output digest.  It cannot by itself establish ten-call
independence, research quality, source isolation, skeleton gating, privacy of a
different runtime, or any policy effect.

## Proof-distance accounting at launch

- **Net proof movement:** `neutral`.
- **Evidence:** checked local interface/schema evidence and an admitted
  synthetic process canary; no live receipt or mathematical theorem.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** no mathematical producer.  This ticket can only
  decide whether the proposed factory experiment has an executable trust
  boundary.
- **Counterfactual test:** a correct preflight can prevent invalid provider
  spend and false process conclusions, but does not reduce the remaining exact
  Erdős--Szekeres proof work.
- **Planning consequence:** freeze the smallest honest canary or stop on the
  exact runtime gap; never weaken a missing attestation into a provider
  self-report.
- **Failure genome:** none for operational-only outcomes.
- **Frontier portfolio:** unchanged at launch.
- **Load-bearing ledger:** no node or edge changes.

## Final outcome

Ticket 0070 closes on the two jointly supported terminals
`V3-LIVE-INPUT-ISOLATION-GAP`, narrowed to the current native execution
binding obligation `BIND-01-NATIVE-EXEC`, and
`V3-LIVE-PREFLIGHT-OPERATIONAL-STOP`.  It does **not** close on
`V3-LIVE-CANARY-PACKET-READY`.  No provider, model, network, MCP, or live
canary call ran or is authorized by this ticket.

The installed Codex 0.149.0 permission engine accepts and enforces the tested
custom profile when it is selected explicitly for a local `codex sandbox`
fixture.  The documented `default_permissions` key also identifies a plausible
static selector for `codex exec`.  The admitted evidence does not authenticate
that the actual `codex exec` command-spawn path applies that profile before
every generated command, binds the command item to the resulting child and
profile, or prevents an unwrapped alternate spawn.  This is an
architecture-local admission and implementation gap, not evidence that no
future technically enforced runtime can provide the required isolation.

Runtime-checker v6 is separately admitted at bounded synthetic-verifier scope.
Its 55-test frozen suite, fresh cross-class precedence controls, positive
event-chain witness, completion digest, and run digest all pass independent
boundary review.  The checker authenticates the frozen descriptor, launch,
event, output, process, closure, completion, and run-digest representation; it
does not produce native process/profile binding, launcher ownership, OS
enforcement, live event compatibility, or source/skeleton ordering evidence.

Admitted implementation and review artifacts are:

- checker SHA-256
  `c8b593bf5d2d2b0c095f32f5c52984c84204ef2fdccaf2256df73a6e1e47a2fb`;
- test-suite SHA-256
  `a7dd1af053b8e0adb800463aa49a005319ef239f093e192dc39dabf00fffe62c`;
- v6 repair-contract SHA-256
  `26225a87b8020973c80666d0a24baa16d6297a1f955b3359a0eedae9cb86aced`;
- v6 independent boundary-review SHA-256
  `4cf61f47d09a01c16fd7bfab1edcff89d49747ec145e0308787a49e935a8e349`;
- native-selector reconciliation SHA-256
  `b6dbae28e7d82b7df92a95d2825bd1160c8741b5a86a05fa24e587b2a50acfe1`;
  and
- final ticket-reconciliation review SHA-256
  `f9601ba91fde4e48a582a50318527d865756ed18259ce4de42014bb67111a779`.

Earlier checker versions were not silently promoted.  Independent reviews
rejected v2 for an incomplete/incorrect digest and pathname boundary, v3 for
strict-numeric alias defects, v4 for lifecycle error classification, and v5
for terminal-usage validation precedence.  The admitted v6 suite contains the
prospectively frozen repairs and regression controls for those defects.

## Remaining live producers

A later local-only packet must implement and independently falsify the exact
launcher-owned `L -> C -> B -> T` topology before any provider request.  It
must freeze and hash both permission profiles and their normalized expansions;
authenticate the installed runner's profile-before-exec binding and denial of
alternate spawn paths; correlate the command item, child, argv, profile,
environment, descriptors, and clocks; remove `codex exec -o`; make the launcher
the only receipt and final-output writer; and pass the repository, credential,
alias, socket, process-group, resource, termination, ownership, and digest
corruption controls.  Live event compatibility, provider transport, and one
run-specific receipt may remain for a later separately authorized canary, but
the live call may not be the first test of these local producers.

That packet is not scheduled by this resolution.  It is operational work and
must not delay mathematical route acquisition or be reported as proof
movement.

## Final proof-distance accounting

- **Net proof movement:** `neutral`.
- **Evidence:** authenticated checked local computation and static independent
  audits; no mathematical theorem and no live receipt.
- **Damage scope:** `operational-only`, specifically the current native
  `codex exec` binding and ownership architecture.
- **Difficulty displaced:** no mathematical obligation.  Selector-family
  uncertainty was narrowed, but actual command/profile binding, bypass denial,
  launcher-owned extraction, and local containment controls remain.
- **Counterfactual test:** knowing this result earlier would prevent an unsafe
  provider spend and avoid treating a self-consistent receipt as runtime
  attestation; it would not improve the remaining exact-proof estimate.
- **Planning consequence:** close the preflight, prohibit the live canary, and
  return primary capacity to mathematical route acquisition.  Any later
  launcher implementation is a separately frozen operational packet.
- **Failure genome:** none, because every admitted stop is
  `operational-only`.
- **Frontier portfolio:** byte-unchanged; no `FP-NN` evidence, state, or gate
  changes.
- **Load-bearing ledger:** no edge changes.  `D-UPPER`, `D-HALF`,
  `D-DECOMP`, and `D-NORMALIZE` remain open, while `D-ASSEMBLE` remains gated.

The durable run artifacts span approximately 2 hours 41 minutes from the
first recorded capability snapshot to the final v6 result, including the
serial repair/audit cycles.  The run used one root builder and at most three
concurrent read-only reviewers and occupies 764 KiB under the ignored run
root.  CPU and peak RAM were bounded by the packet but were not independently
metered, so no stronger actual-resource claim is made.
