---
title: Build and launch the continuous idea generator
type: research
mode: HITL
status: closed
claim: continuous-evidence-first-seed-reserve-2026-08-24
blocked_by: none
---

# Ticket 0079: build and launch the continuous idea generator

## Question

Can the evidence-first campaign's seed stage run independently of this chat as
one specific bounded service, while preserving exact packet approval, no-padding,
root-only route admission, and provider/resource limits?

## User decision

On 2026-08-24 the user directed root to build the proposed continuous idea
generator and start it running. The approved function is narrow: keep one
five-seed reserve ready, so mathematical lanes need not wait for idea generation.
This does not authorize autonomous route decisions, proof experiments, Lean
work, portfolio edits, unbounded provider looping, commits, pushes, software
installation, destructive actions, or future provider calls whose immutable
packets have not received exact approval.

## Frozen architecture

The service is documented in `docs/agents/continuous-idea-generator.md` and
implemented by `scripts/continuous_idea_generator.py`. It uses a durable ignored
queue under `runs/agents/continuous-idea-generator/`. Each queue entry binds one
coordinator snapshot, prompt, task packet, output schema, model, reasoning
effort, resource envelope, and one-invocation approval receipt by SHA-256.

The daemon performs only:

```text
approved packet -> authenticate -> one read-only Sol seed pass -> deterministic
campaign validation -> one reserve batch -> idle
```

It cannot consume its own output. Root must reconcile a batch and explicitly
release it before another separately approved packet can run. An attempt receipt
is written before launch and forbids automatic retry after interruption.

## First-call resource and approval inventory

- already authorized by the user: local implementation, tests, ignored run
  artifacts, one bounded first seed-generation launch, and persistent idle
  monitoring;
- requires a platform prompt after the exact packet is frozen: the single
  out-of-sandbox `python3 scripts/continuous_idea_generator.py start ...`
  command, because its detached child authenticates to OpenAI and may use live
  primary-source web search;
- active call ceiling: 90 minutes, 2 local CPU cores, 4 GiB local process-tree
  RSS, 0.05 GiB output, one `gpt-5.6-sol` invocation at `max`, and no subagents;
- no new approval anticipated: dependency installation, resource-limit change,
  process termination outside the service's own child group, destructive file
  operation, external repository mutation, commit, or push; and
- conditional future action: every later provider packet requires a new exact
  user/platform approval. A consumption receipt requires prior root evidence
  admission and reconciliation.

## Predeclared outcomes

- `CONTINUOUS-SEED-RESERVE-LIVE`: implementation checks pass, the daemon is
  alive, one exact provider attempt is running or has filled the reserve, and
  status is independently readable.
- `CONTINUOUS-SEED-RESERVE-NOVELTY-STOP`: the daemon is live and the exact pass
  returns zero to four honest seeds; preserve the batch without padding.
- `CONTINUOUS-SEED-RESERVE-PROVIDER-STOP`: provider, timeout, local resource, or
  structured-output failure ends the single attempt; preserve receipts and do
  not retry automatically.
- `CONTINUOUS-SEED-RESERVE-PACKET-MISMATCH`: an immutable receipt fails before
  launch; do not call the provider.
- `CONTINUOUS-SEED-SERVICE-REVISE`: local regression or orchestration review
  finds that the daemon can exceed its authority, duplicate a call, or hide its
  terminal state; do not launch until repaired.

## Decision criteria

Resolve only after regression tests cover hash binding, read-only single-agent
provider configuration, reserve blocking, immutable receipt drift, and path
containment; the ordinary campaign and orchestration validators pass; the first
packet is frozen after this ticket and its documentation enter the snapshot;
the exact platform approval is obtained; and a detached PID, heartbeat, packet
receipts, and provider attempt or validated terminal can be checked from a
fresh command.

## Evidence

The implementation is admitted only through local regression, campaign,
orchestration, Wayfinder, and packet-authentication checks. A live provider
response remains proposal evidence even when its JSON contract validates.

## Proof-distance accounting

- **Net proof movement:** `neutral`.
- **Evidence:** operational implementation/tests and, after launch, provider
  proposal-level search information only.
- **Damage scope:** `operational-only` for any service or provider stop.
- **Difficulty displaced:** none. A reserve reduces scheduling latency but does
  not close `D-HALF`, `D-DECOMP`, `D-UPPER`, or `D-NORMALIZE`.
- **Counterfactual test:** earlier availability could have reduced idle time and
  stale factory work, but would not itself reduce remaining proof obligations.
- **Planning consequence:** run the bounded service beside mathematical work;
  validate and route-review each batch before any seed becomes executable.
- **Load-bearing ledger:** no edge changes.

## Resolution

Implementation checks passed and packet 001 was frozen with packet, prompt,
task, and snapshot hashes respectively
`10e12a399cc418da06b4b1dac942a2d63621dfa81980f997520161d14d2cdf0b`,
`7d574e9c86b3e1b2caea0192fb821424ea58bf844c6ce198996158fcc74573d3`,
`b70781da80295c3445e2244dcd0bb0f4726fc0a2e6a41e2d231ca0384f440b4d`,
and `e2f73de25e4006ad2e30575f51caa44f680e1b3e3c77a6ed7042f8fae58ac6b7`.
Exact platform approval was granted and the attempt receipt proves one launch.

Packet 001 reached `CONTINUOUS-SEED-RESERVE-PROVIDER-STOP` before any model
response: Codex exited status 1 because the managed checkout required
`--skip-git-repo-check`. The admitted result-receipt hash is
`11ebffdf1f78725863fcd2fac0c86bebe53d7a418942f78db07cdc94a91ce74f`;
the provider log hash is
`dd701e712037bba81445e9a92376e3d3af69acac5f0187ec904e9ed3c401324d`.
This is an `operational-only` stop, not mathematical evidence, and receives no
failure genome. The no-retry barrier held: packet 001 was not relaunched.

The first daemon was invisible from the chat sandbox but remained live outside
it. Packet 002 was separately frozen and approved, then that already-loaded
daemon consumed its queue entry with the old command constructor and reached
the same pre-model provider stop. Its result-receipt and attempt hashes are
`56417f9aeca652b20041ad5c20b4906247f78e34e24525dc092d03cc226562c3`
and `a72d345d48d9198e6b50d2ab23f071eed265ec5973436a004aeb79205a46171e`.
Root gracefully stopped PID 302907 with no provider child active. This second
outcome is also `operational-only`, creates no mathematical genome, and did not
retry packet 002.

The corrected service now uses a user-systemd transient unit and binds both its
implementation SHA-256 and supervisor kind in the PID receipt. It refuses to
consume approved work through stale daemon code. Packet 003 is the first packet
eligible for this exact implementation and requires a new exact approval. The
ticket remains open pending its live daemon and provider-attempt receipt.

Packet 003 ran under the corrected implementation and user-systemd supervisor.
The daemon heartbeat, implementation receipt, cgroup ownership, attempt barrier,
and managed-checkout bypass all worked. The provider created a thread but
rejected the structured-output schema before sampling because inherited
`const` declarations did not carry explicit JSON `type` keys. The admitted
result, event, and attempt hashes are
`dd9e3b825f3779043a4ab2e238567bc7ed0b270b43c43b9622754e0eb95b3d45`,
`6279e4147c06d15062c519ac047cdd43f8ac1b723b557d49405fc708995eae6c`,
and `6756ea65dfab09e672f35efb4ffcc5e8b4ce5a54bd37d58ab727c019c18761fd`.
This is a third `operational-only` stop with no model response, mathematical
evidence, or failure genome. Root stopped only the idle systemd service. The
provider-schema adapter now assigns explicit types to every `const` and
single-type `enum`; packet 004 requires a fresh snapshot and exact approval.

Outcome `CONTINUOUS-SEED-RESERVE-LIVE` now holds. Packet 004 was frozen and
separately approved with implementation, packet, prompt, task, and snapshot
hashes
`bb5878db52d44173dd6d70b74ab662273a822bfa46da11e081db505121b8c34e`,
`3a622b27ba83a1721c0b1b4ac0e3a0e349c301cf60eb9a9f51d8734d0c25107d`,
`0cf53c154960ca26ed66d471e2a17655ac5c8528cb492b047202f303ab3a09a8`,
`3797d848e7ec05832bfd8ecf344c71429b6e37e8993bcecb3159467ba0dba9e3`,
and `dd5315fb302bda4ae85a4d57f2ec151622782eebb34923e17ee47d23fc702770`.
The immutable queue, service-PID, and attempt receipt hashes are respectively
`4103aaee603a23a43ada585fcb979157044edbb56c45e3129a57e6cac04c7b27`,
`13b73f24aad515d575afacc6a15e329c3af633fc357385211a3750d003937637`,
and `c988d8f9ae6e6f6650a716bdeabfc64b55ee5c98755f6ebb48bdf3f06407e67b`.

At admission, user-systemd service
`erdos-szekeres-idea-generator-63ac8f17.service` had PID 306932 and the single
Codex child had PID 306949. The captured stream contained `thread.started` and
`turn.started`, proving the managed-checkout and strict-schema preflight gates
were cleared. No result was claimed early: Sol remains bounded by the frozen
90-minute/resource envelope, and its eventual complete, novelty-stop, or
provider-stop batch still requires deterministic validation and root
reconciliation. The daemon cannot run another call after that terminal without
a new exact packet and approval. No load-bearing edge or portfolio state
changed.

Packet 004 subsequently reached `SEED-BATCH-PROVIDER-STOP` after one successful
Sol invocation. The provider returned five structurally well-formed proposal
objects, but the second used `transfer_status = same_tier` with textually
different working and target tier strings. The deterministic campaign
validator therefore rejected the whole response and the daemon correctly
reserved zero seeds, issued no retry, and returned to
`waiting-for-approved-packet`. The result receipt, raw response, and admitted
zero-seed terminal have SHA-256 values
`34c5fafd1d8ac637920f8c94bd56969bcf26513cdbdcefe636539e636c25e4fa`,
`d5b7ea2cbeb99f814f9c8c9ddf9d9738d609f9728b316722d47065763018bd60`,
and `1db06bd76085f954819e7b8c5dc8794f064a10e5ad5386994d1fc387954ec122`.
Root replayed the seed-batch and task validators. The provider ran for about
24 minutes 51 seconds and its event receipt reports 5,261,898 input tokens,
4,994,048 cached input tokens, 54,970 output tokens, and 37,299 reasoning
tokens; captured output was 1,707,499 bytes. No exact provider peak RSS was
recorded.

The malformed response remains immutable operational evidence, not a seed
batch, route, or mathematical result. For duplicate avoidance only, its five
unadmitted mechanism signatures were projection-rank parity, hull-edge
incidence parity, reflex-vertex polygon exchange, proxy-conditioned bowtie
polynomials, and minimum-triangle six-cell supports. These names convey no
positive evidence and authorize no first test. The prompt now states the
validator's conditional model-tier rules explicitly and has a regression test;
any successor call requires a newly frozen packet and exact approval.

**Packet-004 accounting:** net proof movement `neutral`; evidence is an
authenticated provider/validator operational stop; damage scope
`operational-only`; difficulty displaced none; counterfactually, the explicit
cross-field prompt rule avoids wasting a later batch but does not reduce proof
work; planning consequence is one fresh nonduplicate seed packet after exact
approval. No load-bearing dependency or frontier state changed, and no
mathematical failure genome applies.

Packet 005 is now frozen in `failure_dual` mode after the prompt regression
passed all nine service tests. Its implementation, packet, prompt, task,
snapshot, and provider-schema SHA-256 values are
`7bb39b0559d9b2c48a88121a1174b1a955018cf8396b053b9d26eed6a0450a16`,
`1b57ea6f806bea2d7793999314fc79319c2a1a56d50f653364183349a9e6a7da`,
`e3e19d30ee933e2f2d8e45a7c991b89c1d3d264b9f558a485450d29b747eccfb`,
`87ea1869dff7d7d495b73243a8138eb52994c90854226814f9b55aee04d63c8e`,
`f889495ac9784a8c2ced2168e91c47c2b4f824e98e2b33e917272bc4ec39e0ab`,
and `3faaadb4cb8cbf160c79d7f75cb8e82ac4d2e5e845d2ad439cb2d510930c66f6`.
Its 12 direct inputs and task packet validate. The user and platform approved
that exact packet under the unchanged 90-minute, one-Sol-invocation, read-only
envelope.

The start command detected an old loaded daemon implementation. Because the
then-current launcher wrote the queue entry before checking the daemon version,
the old daemon had already consumed Packet 005 when the command reported the
version mismatch. Root stopped the service after its one bounded provider child
completed; no second call or retry occurred. A byte-level compatibility audit
proves that the loaded implementation differs from the approved implementation
only by the nine-line prompt paragraph that had already been materialized in
Packet 005's frozen prompt. Packet parsing, provider command construction,
resource enforcement, output validation, and reserve semantics are identical.
The compatibility audit and result have SHA-256 values
`df758aae79142a5f87199dcf1ca87354d0d6aa4e4f99562dd01d78bfb052c7fe`
and
`50e8678ec39a158accd17c41787c84de9418760c0a0de4158ddf49d04f1e27b6`.
This admits the output under the exact user authority; it does not admit any
mathematical proposal as a route.

Packet 005 reached `SEED-BATCH-COMPLETE` with five schema-valid proposal-level
seeds: `FD005-LOR-FREE`, `FD005-RADIAL-M2`, `FD005-DECK-QUARTET`,
`FD005-HELLY-MAT2`, and `FD005-JUMP-PROFILE`. The seed batch, result receipt,
and raw response have SHA-256 values
`69b34ad56c6055b3048fcafe9aaf83a389e0a0a1fbee97c32a6bbe8620bd84f3`,
`c312540943b1391f10607d36abef8bf1e1695f3f7d63ee06a19a3d58ed689af0`,
and
`9abdf1f91d3d09a310479351ad4b80f95dec4192dd22d85090ae6302e3b4bee5`.
The provider ran for about 30 minutes 6 seconds; the event receipt reports
7,388,760 input tokens, 7,058,944 cached input tokens, 66,339 output tokens,
43,782 reasoning tokens, and 1,110,612 captured output bytes. These are process
measurements, not mathematical evidence.

The launcher now authenticates or starts the daemon before queue publication,
and regression `test_start_rejects_stale_daemon_before_queue_write` prevents a
repeat. All ten focused service tests pass. The current implementation and test
hashes are
`f0b22c7cdefdb6530561aae97f9fe079338783e065dc0adbe243e2b96773b390`
and
`22a3be9e6839210e6fe9f8f6682cdb7ab545b441eba5ab89a9afd6818708865e`.
The service is stopped. After Ticket 0080 reconciled all five proposals, root
released the reserve with exact consumption receipt SHA-256
`15f3d12ea4e0fb4a9201dbece7dcb0b5b8bcbf040ceaa412405a8e7a1cdd6286`.
The receipt admits or schedules no seed. There is now no active reserve or
pending queue; any future provider call still requires a newly frozen packet
and exact approval.

**Packet-005 accounting:** net proof movement `neutral`; evidence is an
authenticated provider proposal batch plus a byte-exact operational
compatibility audit; damage scope `operational-only`; difficulty displaced
none; counterfactually, the completed reserve reduces idea-generation latency
but not proof work; planning consequence is route-review all five seeds before
any first test, then consume the reserve only from the canonical reconciliation
reference. No load-bearing dependency or mathematical portfolio state changed,
and no mathematical failure genome applies.

## Later supersession

Ticket 0083 supersedes this ticket's one-reserve and per-provider-call approval
clauses after the user explicitly required a genuinely continuous loop. All v1
packets, attempts, failures, batches, and consumption receipts remain immutable
historical evidence. Their proposal and proof-distance classifications do not
change. The v2 standing authorization is a new operational contract and cannot
retroactively authorize, retry, or mutate any v1 packet.
