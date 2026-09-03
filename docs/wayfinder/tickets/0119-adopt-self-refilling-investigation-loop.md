---
title: Adopt the self-refilling investigation loop
type: research
mode: HITL
status: open
claim: self-refilling-ten-seed-investigation-loop-authorized-2026-08-31
blocked_by: none
---

# Ticket 0119: adopt the self-refilling investigation loop

## Question

After pausing the empty post-Cycle-010 frontier slate, should the project keep a
ten-item proposal queue, investigate its ideas in a rolling loop, generate
root-origin replacements when the provider cannot do so, and continue until a
candidate survives a predeclared evidence-first “has legs” gate?

## Decision criteria

1. Preserve proposal/evidence separation and all mathematical proof-distance
   gates while changing queue throughput.
2. Count individual ready ideas, not transport batches, and prevent overfill by
   reserving the exact deficit before provider launch.
3. Remove the user-revoked daily cap without weakening per-call, lifetime,
   circuit, concurrency, or retry safety.
4. Make every admitted investigation outcome available to both future
   generation and root selection with explicit epistemic tags.
5. Define “has legs” by authenticated hostile evidence and a consumer path, not
   by provider enthusiasm or finite survival alone.
6. Keep the independently paused scheduler stopped.

## Evidence

### Diagnosis before restart

The continuous idea generator was failed/stopped.  A fresh read-only status
check found no daemon, no pending packet, and no active reserve.  Its historical
v2.1 state stopped because the installed Codex CLI version drifted after the
standing authorization was frozen.  The last recorded rate gate also reflected
the former six-call rolling-day ceiling, but that was not the service failure.
The scheduler is independently paused/stopped and is not diagnosed, repaired,
or restarted by this ticket.

Wave-4 hostile state, learning, evidence, and execution-envelope audits found
additional v3 release blockers.  The accounting/context, root-import commit,
validated-learning-export, full-feedback, exact-verifier, and first-test-guard
repairs are now implemented.  A later independent queue audit exposed one
additional fail-closed availability defect: an exact durable outcome event
written immediately before a crash could be validated by the recovery helper,
but both restart paths reached a strict accounting reader first.  The repaired
implementation now runs one shared locked transition preflight before those
readers, advances the head only for the single object-exact canonical outcome
tail, and rejects altered or multiple tails.  The final v3 suite passes `24/24`,
and all seven repaired base-generator cases pass focused reruns.  The final
aggregate rerun was interrupted at the user deadline and is not claimed
complete; the remaining guarded aggregate gate is still part of the release
gate.

The 2026-08-31 scout reconciliation was also corrected before snapshot use.
The independently reproduced seven-point fixed-anchor Orchard census remains
ordinary `checked computation` at `candidate-local` scope.  Five one-agent
Orchard-cocycle, Radon, Pascal-rank, normalization-commutation, and HMPT
observations are retained only as `proposal` route-design input; their five
unearned failure genomes were removed.  The resulting portfolio audit is
`CLEAN`, all affected route states are unchanged, and no load-bearing edge
changed.  A root novelty refill honestly produced zero materially new seeds;
it remains a proposal-level `NOVELTY-STOP` and is not generator learning.

The strict six-case Orchard-XOR panel, exact worker, root-owned freeze builder,
and guarded verifier handoff have passed their synthetic and independent
preflight checks, but the real panel remains unopened and has no mathematical
outcome.  No current authorization exists and no provider call or first
investigation is authorized to start yet.  Release still requires the final
post-repair guarded `make test`, final-byte state/learning/evidence/guard
reviews, and only then one fresh authorization.  The generator remains stopped
and the scheduler remains stopped throughout and afterward.

This is an `operational-only` stop.  It supplies no mathematical negative and
receives no failure genome.  The old authorization cannot be reused: it binds
the former CLI bytes/version, v2.1 implementation, batch-level queue semantics,
daily cap, cooldown, and high-water limits.

## Resolution

Adopt a v3 self-refilling investigation loop.  This ticket supersedes Ticket
0103's `40/30/20/10` discretionary allocation and its prohibition on automatic
campaign backfill while this temporary policy is in force; actual generation
and investigation remain gated by the release conditions below. It does not
supersede theorem-
entry, semantic-readiness, evidence-admission, model-tier, failure-genome,
mechanism-correlation, no-padding, or proof-distance rules.  It does not restart
or authorize the scheduler.

### Queue contract

- The queue target is exactly ten authenticated, ready, not-yet-assigned
  proposal items.  Queue membership is not route admission or proof evidence.
- A seed identity is `(campaign_id, seed_id, seed-batch SHA-256)`.  Transport
  batches do not control individual state.
- Per-seed states are `ready`, `investigating`, and `investigated`.  Claiming one
  seed removes only that seed from ready depth; its siblings remain ready.
- Every provider packet freezes
  `requested_seed_count = min(5, 10 - ready - pending reservations)`.  A result
  exceeding or disagreeing with that request is rejected.  Ready plus reserved
  capacity may never exceed ten.
- A learning-epoch hash commits every authenticated in-flight claim, all
  root-admitted terminal feedback, and every canonical route/failure-memory
  record available at packet freeze. The generator first derives one immutable
  validated-learning export from the current authorization/accounting view,
  closed batch/results, exact claims and tasks, fully validated feedback/root
  reconciliation, and canonical failure-memory receipts. The builder consumes
  only that export, materializes the exact list, and writes a closed snapshot-
  build receipt; it never scans raw service directories or decides evidence
  admission. An unattempted stale packet is not launched; results from
  an attempted packet whose epoch becomes stale expose no ready seeds and are
  replaced under a new identity.
- Snapshot validation has two time modes. Current admission regenerates the
  validated export, cold-rebuilds and byte-compares every deterministic output,
  checks the post-replay campaign-excluded learning epoch/workspace aggregate
  and current components, and writes one immutable snapshot-admission receipt.
  Historical attestation authenticates those frozen outputs and cross-bindings
  without consulting a later builder or mutable learning state; it does not
  claim reproducibility under today's implementation. Launch and ready exposure
  separately require current currency.
- Authoritative v3 ready, pending, and reserved counts derive from one current
  active authorization and authenticated hash-linked accounting view. A
  provider campaign contributes inventory only after its exact attempt,
  outcome, result, and seed-batch receipts close in the current head. A missing
  head, chain gap, unresolved attempt, or receipt mismatch fails closed even if
  queue directories are empty.
- Legacy batch-consumed seeds remain duplicate memory with status
  `legacy_reconciled_investigation_unknown`; no individual investigation is
  inferred from batch release.

### Standing provider envelope

- Provider: `gpt-5.6-sol`, maximum reasoning effort, live web, read-only,
  noninteractive, ephemeral, and subagents disabled.
- Concurrency: one provider invocation at a time; an attempted packet is never
  retried.
- Per call: at most 90 minutes, 2 local CPU cores, 4 GiB local process-tree RSS,
  and 0.05 GiB captured output.  The linked user service retains its 5-GiB
  cgroup ceiling.
- Cadence: no rolling daily call limit and no post-completion cooldown.  The
  service refills immediately while a positive exact deficit remains.
- Retained safety: 100 provider invocations total across v2, v2.1, and v3
  accounting; two consecutive provider stops or two consecutive zero-seed
  batches open their circuits.  The 30 historical v2/v2.1 attempts remain
  charged, leaving at most 70 provider attempts under this authorization.  The
  six pre-standing v1 calls are authenticated in the migration baseline but
  remain explicitly outside the Ticket-0083/0119 lifetime count.
- The active authorization binds that immutable migration baseline.  Before
  process creation every new charged attempt and its batch receipt enter a
  hash-linked ledger and durably advance the accounting head. After process
  creation, a provider-start receipt binds PID, boot, start ticks, process
  group, prompt, and attempt event and is durably committed before prompt
  delivery. A charged attempt lacking that acknowledgement is an operator-
  diagnosis stop, never an automatic retry or fabricated terminal. The exact
  outcome then closes only its immediately unresolved attempt.
  Missing or corrupted artifacts, an unknown or partial v3 result, a chain/head
  disagreement, or any unresolved attempt opens the circuit before fresh
  spending.  Partial finalization never exposes ready seeds and may recover
  only the exact immutable outcome.  A local hash chain cannot detect a
  coordinated rollback of its head and every removed tail; preventing that
  stronger threat requires an external monotonic anchor.
- Whenever the authenticated ready count is zero and no provider reservation
  is pending, root freezes its own compact seeds under the same schema,
  identity, current learning snapshot, duplicate-memory, claim, and feedback
  rules. The batch must bind the generator-produced validated-learning export,
  current closed snapshot-build and immutable snapshot-admission receipts, and
  a JSON semantic screen that covers every exact seed hash and the schema,
  identity, snapshot, proposal, first-test budget, semantic-duplicate,
  target-equivalence, model/return, failure-memory, source/novelty, family-
  correlation, and no-padding checks.  Provider failure never authorizes more
  provider spending. Same-run containment requires the source batch, snapshot,
  derived admission, and screen to resolve inside one ignored root run and
  outside the service directory.
  Current authorization/accounting and snapshot currency are checked before
  the first service-directory write and again after all non-commit writes;
  `result-receipt.json` is written last as the only inventory-visibility commit
  marker. An incomplete import is retained for operator diagnosis, exposes no
  ready seed, and is never silently deleted or retried.

### Investigation and learning loop

Root may keep up to four mathematically distinct bounded investigations active,
normally three delegated and one root-owned.  No more than half the active
lanes use one mechanism family without an explicit mathematical justification.
Each assignment has an immutable development brief, an exact first hostile
test of at most thirty minutes, outcome branches, and an evidence gate.

Every completed investigation receives a per-seed, hash-bound root feedback
receipt before the result can be treated as learned.  It records the exact
terminal and evidence event, model and scope ceiling, damage scope, proof-
distance account, individually tagged verified/inferred/not-established
learning, anti-duplication warning, and next mathematically different test.
The canonical feedback-core digest covers every field except
`root_admission`; root admission and `research-root-reconciliation-v2` both
bind that full core plus the exact claim, development receipt, standing
authority, and timestamp. Before projection, the generator independently
validates the exact task, trusted execution envelope, terminal event, guarded
verifier result, evidence level, scope, proof-distance account, learning tags,
next discriminator, failure-memory reference, claim-candidate disposition, and
queue disposition. Root reconciliation is a checked cross-binding, not an
evidence oracle. Only a normalized verifier result which explicitly establishes
the exact learning statement may support a `verified` tag; suggestions and
context remain `inferred` or `not-established`.
Mathematical negatives point to exactly one existing canonical failure-genome
home and heading through one unique marker-bounded JSON core and canonical core
hash, plus the selected exact falsifier artifact/hash. Later review can append
outside the immutable core; changing, moving, or duplicating that core fails
authentication. A per-seed positive or no-signal
terminal is candidate-local.  A per-seed falsifier reaches at most subfamily,
and only when its immutable brief predeclared the shared premise and subfamily.
Architecture- or mechanism-wide scope requires a separate authenticated
shared-cause/adversarial review in the same canonical genome home and does not
mutate the original feedback.  The ignored feedback receipt is an index/projection for queue learning,
not a second strategic tracker.  Every packet frozen after reconciliation
contains that feedback; in-flight investigations are marked so they are not
regenerated.

Provider output, worker prose, finite survival, source analogy, and unchecked
computation remain proposal or search information.  Root performs semantic
duplicate, stale-snapshot, model-tier, failure-memory, and family-correlation
review before assignment.

### “Has legs” stopping gate

The loop reports a candidate as having legs only after all of the following are
authenticated:

1. its exact predeclared first hostile test produces the live signal;
2. an independent hostile referee or cold re-deriver reproduces the gate-
   critical claim;
3. working and target model tiers, information at risk, and any return bridge
   are explicit;
4. a five-field theorem-entry memo and a short consumer ladder identify the
   named load-bearing consumer;
5. the candidate's mathematical delta from the nearest admitted controls is
   explicit; and
6. one bounded next theorem or falsifier has outcome branches that change
   allocation.

Passing this gate is search information and normally net proof movement
`neutral`.  It becomes forward proof movement only when a compiling theorem
strictly reduces or closes a named load-bearing dependency under the ordinary
rules. At this terminal, stop new claims and further loop spending/work until
the user makes a separate post-gate decision. A full ten-item queue is not
evidence that a candidate has legs. Route admission or redirection still
receives normal root review.

## Approval and operational inventory

The user's 2026-08-31 instruction is the explicit decision authorizing this
policy and the bounded standing provider envelope above.  Foreseeable external
actions are the remaining provider calls under that envelope and one user-
systemd start using the exact versioned authorization path/hash produced after
tests.  No software installation, repository deletion, scheduler start,
resource increase, external Git mutation, or unbounded search is authorized.
Stopping the service later may terminate only its authenticated provider
process/control group.

The same instruction is standing approval for future pre-admission first-test
packets within this loop, despite their seed identities not yet existing. Root
must first freeze the seed-specific immutable claim, development brief, exact
task, and root-owned first-test guard contract. Each standing test is a
noninteractive guarded deterministic Python check, not ordinary collaboration-
agent execution. Agent reasoning may be frozen as proposal-only input; it may
not author admitted checked evidence. The trusted guard authenticates the exact
checker and raw inputs, permits only declared artifact outputs, denies network,
services, scheduler, providers, canonical/external writes, installation,
destruction, delegation, and child processes, enforces at most 30 minutes, 2
CPU cores, 4 GiB aggregate RSS, and 0.1 GiB total output, and emits a root-owned
execution-envelope receipt.

Root independently replays the same exact artifact-consuming checker under the
guard and admits only its normalized result. Missing or violated execution or
verifier envelopes force `OPERATIONAL_STOP / operational-only`, with no
selected mathematical event, verified learning, or claim candidate. The
standing first-test feedback may have net proof movement `neutral` or
`backward`; this authority cannot support a forward claim. The
standing branch rejects manual reasoning, source reading, Lean,
`fixed_statement_in_loop`, theorem contracts, `file_compiles`, and all Lean
verification engines. At most four tests may run concurrently under family
diversity. Canonical Lean/documentation edits, installation, destructive or
external writes, scheduler changes, added provider authority, resource
increases, work past the “has legs” terminal, and any action outside that closed
envelope still require their ordinary later decision. Later Lean uses a
separately approved canonical theorem packet and the guarded Makefile path;
`native_decide` remains computational evidence, is never `file_compiles`, and
may never be replaced with kernel `decide`. This clause supersedes only the
exact-future-packet chat-approval requirement for those bounded guarded tests.

Restart order is fail-closed: finish v3 code and documentation; run focused
campaign/generator/guard regressions, Wayfinder and portfolio checks, and
guarded `make test` while both services remain stopped; freeze final hashes and
obtain an independent CLEAN state/learning/evidence/guard review; only then
freeze a new authorization against final implementation/helper/schema/policy
and current CLI bytes/version; independently confirm 30 charged calls and at
most 70 remaining; start the generator only with that exact receipt; and verify
accounting-backed queue, process, limit, and stopped-scheduler states before a
provider launch or first investigation. Historical receipts grant no current
authority.

## Proof-distance accounting

- **Net proof movement:** `neutral`.
- **Evidence:** explicit user operating decision, read-only service diagnosis,
  and bounded implementation/feedback/adversarial audits.  No mathematical
  investigation result is admitted by adopting the loop.
- **Damage scope:** `operational-only` for the stopped v2.1 service and policy
  migration.
- **Difficulty displaced:** none.  The exact upper-bound producers and return
  bridges recorded in the load-bearing ledger remain open and are not smaller.
- **Counterfactual test:** knowing the diagnosis and queue defects earlier
  would prevent unsafe restart, batch-level loss, overfill, stale learning, and
  repeated proposals; it would not reduce the mathematical destination.
- **Planning consequence:** replace the empty theorem-first slate with the
  bounded learning loop, retain all mathematical route states, and keep the
  scheduler stopped.
- **Load-bearing ledger edge changed:** none.

## Completion gate

Close this ticket only after canonical rules and implementation agree, all
focused and guarded tests pass, a final-byte independent CLEAN review passes,
the fresh standing receipt authenticates final bytes and the exact 30/70
accounting, the idea generator is live or reaches a documented retained safety
stop, status shows accounting-backed exact-depth inventory, and the scheduler
is confirmed stopped.
