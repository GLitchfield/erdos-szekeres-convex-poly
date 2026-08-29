---
title: Make the idea generator continuously self-refilling
type: research
mode: HITL
status: closed
claim: bounded-continuous-idea-loop-v2-2026-08-24
blocked_by: none
---

# Ticket 0083: make the idea generator continuously self-refilling

## Question

Can the chat-independent seed service continuously rebuild current context and
generate new proposal batches without requiring this chat to authorize every
call, while retaining finite resource, rate, duplicate, retry, and route-
authority boundaries?

## Decision criteria

Accept v2 only if its checked implementation authenticates one finite standing
envelope, automatically prepares a fresh immutable packet when capacity is
available, launches each packet at most once, pauses at every declared bound,
survives chat and WSL restarts through an enabled supervisor, and leaves all
mathematical admission and project mutation with root.

## Resolution

On 2026-08-24 the user observed that Ticket 0079's live daemon was idle after
one consumed batch and directed root to do what is needed to make the idea loop
run continuously. This supersedes only Ticket 0079's one-reserve and per-call
approval clauses. It does not weaken root-only evidence admission, immutable
attempt receipts, no-padding, model-tier discipline, failure-genome scope, or
the prohibition on autonomous experiments and portfolio changes.

The user's direction is the standing mathematical/operational authorization
for the exact v2 envelope below. Platform approval remains required for the
single command which links, enables, and starts the persistent user-systemd
service and thereby permits its bounded external provider calls.

## Frozen v2 envelope

- one `gpt-5.6-sol` call at `max` effort at a time, read-only, ephemeral, live
  web search, no subagents, and provider approval policy `never`;
- per call: at most 90 minutes, 2 local CPU cores, 4 GiB local process-tree RSS,
  and 0.05 GiB captured output;
- cadence: at most six calls in a rolling 24 hours and at least 30 minutes
  between completed calls;
- standing cap: 100 calls;
- proposal inbox: at most ten unreconciled batches or fifty seeds;
- circuit breakers: two consecutive provider stops or two consecutive
  zero-seed novelty stops;
- generation-mode rotation: context-rich, failure-dual, recombination;
- no attempted packet is retried; every later call receives a new campaign,
  snapshot, prompt, schema, task, packet, queue, and attempt receipt; and
- changing code, CLI version, model, effort, modes, ceilings, or authority
  invalidates the standing receipt.

The implementation binding covers the daemon, packet builder, campaign
validator, and seed schema. Configuration may tighten but cannot weaken the
declared ceilings. Authorizations are versioned immutable files behind an
active pointer, so rotation never mutates a historical packet input.

The daemon may self-prepare and invoke only proposal-generation packets inside
that envelope. It cannot run first tests, edit project or canonical files,
consume or reconcile batches, admit or schedule routes, assign proof movement,
spawn subagents, or mutate Git.

## Continuous duplicate memory

The whole-project packet builder must add every prior validated continuous
seed, including unreconciled inbox seeds, to the duplicate registry. A second
deterministic filter may remove only normalized literal semantic-core repeats
from provider output and must preserve a `dedup-report.json`. Semantic target
equivalence and failure-family scope remain root judgments. Prior proposal
presence is never positive evidence.

## Persistence contract

The supervisor is a linked and enabled user-systemd unit rather than a
chat-owned or transient process. It restarts after process failure and at the
next user service-manager startup after WSL restart. The unit owns its provider
control group and enforces 5 GiB cgroup memory, two-core CPU, and bounded-task
ceilings. A clean operator stop disables the unit. The daemon's first action
after any restart is to reauthenticate the standing implementation receipt; an
existing `attempt.json` forbids a duplicate provider launch. Recovery follows
a live provider only when its PID, process group, Linux boot identifier, and
process-start ticks all match the frozen start receipt, and it reapplies the
original wall, RSS, and output ceilings.

## Predeclared outcomes

- `CONTINUOUS-IDEA-LOOP-LIVE`: focused tests and workflow gates pass, the
  persistent daemon reauthenticates the standing receipt, and it automatically
  freezes a new cycle and reaches a provider attempt or validated terminal
  without a per-batch chat action.
- `CONTINUOUS-IDEA-LOOP-CIRCUIT-OPEN`: a declared rate, inbox, total-call,
  provider-stop, or zero-seed boundary pauses generation while keeping status
  fresh and existing evidence intact.
- `CONTINUOUS-IDEA-LOOP-MIGRATION-STOP`: implementation, systemd persistence,
  packet authentication, or regression testing fails before autonomous launch.
- `CONTINUOUS-IDEA-LOOP-PROVIDER-STOP`: the first v2 packet launches once but
  reaches a bounded provider or validator terminal; preserve it and let only
  the declared circuit/cooldown policy decide whether a new packet is allowed.

## Approval and mutation inventory

- authorized in the user's direction: implementation and documentation edits,
  ignored run receipts, stopping the idle v1 daemon, creation of the exact
  standing authorization, and the bounded repeated provider envelope above;
- requires one platform escalation: the exact v2 `start` command, because it
  links/enables a persistent user-systemd unit and its children use OpenAI and
  live web search;
- no installation, resource-limit increase, destructive deletion, external
  repository mutation, commit, push, credential inspection, Lean build, or
  solver call is planned; and
- any future widening beyond the frozen envelope requires a new user decision
  and standing receipt.

## Evidence gate

Run the focused service tests, Python compilation, campaign template validator,
agent orchestration validator, frontier-portfolio checker, Wayfinder status,
and `git diff --check`. Then create and authenticate the standing receipt,
start the service through its persistent supervisor, and observe a fresh
heartbeat plus an automatically created cycle and attempt/terminal receipt.
Provider proposals remain unadmitted until ordinary root review.

## Live evidence

The predeclared terminal is `CONTINUOUS-IDEA-LOOP-LIVE`. Python compilation
passes, all 35 focused continuous-generator and campaign tests pass, and the
campaign-template, agent-orchestration, frontier-portfolio, Wayfinder, and
diff-whitespace gates pass.

The enabled user unit
`erdos-szekeres-continuous-idea-generator.service` first proved the complete
cycle under standing receipt
`421b1d53f90af2a0f527d86667b215cbf9fa93775e0b8251babc8aa8625756c2`.
Without any packet-specific user action, daemon service
`c12dc1f5-d00c-4e43-9794-3cae04bd15dc` rebuilt the reconciled packet, froze
`20260825-continuous-seeds-007` in `context_rich` mode, authenticated its task,
and launched its one authorized provider attempt. That attempt subsequently
reached `SEED-BATCH-COMPLETE` with five schema-valid proposal seeds and no
literal cross-batch duplicate removed. The packet, task, prompt, attempt, and
provider-start hashes are respectively
`c74bc47abc219ff2b1a655f3438df4efbabc008e403c309674f0eaa35ae2a5d4`,
`fb415329ff831f0069a4fc661585429dbe0f16cc90b4ff639127ad4cd316780f`,
`fbb330a45d06e52ed73854117026e53992acf901b7716d464d579bd8b0d242ca`,
`ea76b432b7cd085de938a17da5028c077ee8917e959d6e4134405f14eb304a33`,
and `3dd242c77de94383718643425d08c4332819cf1602abb617b9071e8c9523d717`.
The validated seed-batch, result, and deterministic dedup-report hashes are
`6b74fa0d3cc5fffc426798b5009c535c19a2ade468c4a962828e0f8cbdbb8e90`,
`8bd179085d131aa8b4bdfaef295cf067c827fbbc6d8d8efb3368fb8e0432e40e`,
and `4ff61ece9a7a3b9d04914b263e9afc0db12a6ab2cbc60c998c08ee37d74be39d`.
The post-terminal audit then found three operational gaps before unattended
handoff: helper/schema bytes were not in the standing receipt, configuration
could weaken some nominal ceilings, and provider recovery used a bare PID.
The service was cleanly stopped. V2.1 binds the daemon, builder, validator,
schema, Codex executable bytes/version, and exact authority; rejects weakened
limits; keeps authorizations at immutable versioned paths; carries rate and
cooldown accounting across receipt rotations; and authenticates boot/start
process identity while reapplying recovery ceilings. Its first restart exposed
one `operational-only` PATH-namespace stop: systemd did not expose the NVM
launcher through `PATH`. No provider was launched. The verifier now binds the
absolute executable by SHA-256 and CLI version, and failed-unit cleanup plus
`reset-failed` are tested.

The final active pointer and standing receipts are
`63dd15ea435778e187c2c652d4755e795c273bb564e103109c89131e13f6f791` and
`5c49535106b4c10e157a57538ab5d52cab6b2c7c4f18dae18473ffe9e6e4625b`;
the bound daemon implementation is
`7e71be97151539a3e908005f15966d0b0e0afc9cb1af8440674d96f6d6f8cba3`.
The enabled unit is active with `Restart=on-failure`, no restarts, two-core CPU
quota, 5-GiB cgroup memory ceiling, and `TasksMax=128`. It preserved Batch
007's one-call/five-seed accounting and waited through the original cooldown.
At eligibility, without chat action, service
`100a74c4-0c81-425d-9077-4d9d16a7acdb` froze Batch 008 in `failure_dual` mode
and launched its single provider attempt. Its packet, task, prompt, attempt,
and identity-bearing provider-start hashes are respectively
`e672106a5687ca0f1577c7a76f67c9787eb238acfff712e90785f8f31c6750e0`,
`cf785bd06ab7219f6694caaf1d4a83be5d5e91ef78b054d8e8d9a2a70ca75496`,
`21833c919a7f7a37f4632bb130cb1514960c41f7f758350c5798feedc748b70b`,
`85a34a009607bba2029c75176e116fc1c9008874a41fd3e47ef1399eae62d947`,
and `0d2eb43c8f3c339a62f1dbd632f4362c0e974c26201bd0c42179a49ce312c7c7`.
Batch 008 remains bounded provider work at ticket closure. Batch 007's five
seeds and any later terminal remain unadmitted search information pending root
review.

## Proof-distance accounting

- **Net proof movement:** `neutral` by construction.
- **Evidence:** operational code/tests and proposal-level provider output only.
- **Damage scope:** `operational-only` for any migration, supervisor, provider,
  validation, rate, or circuit stop.
- **Difficulty displaced:** no mathematical obligation; the change reduces
  idea-generation latency and chat dependence only.
- **Counterfactual test:** if v2 had existed before Packet 006, a reconciled
  result would have refreshed later idea batches automatically, but no
  destination theorem would have become easier merely from daemon uptime.
- **Planning consequence:** keep v2 running beside mathematical lanes and
  review its inbox serially without counting it as proof work.
- **Load-bearing ledger:** no edge changes.
