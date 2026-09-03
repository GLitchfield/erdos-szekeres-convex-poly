# Continuous idea generator

Ticket 0083 superseded Ticket 0079's one-reserve protocol. Ticket 0119 now
supersedes Ticket 0083's batch-level inbox, rolling-day rate cap, cooldown, and
high-water semantics. The evidence-first campaign's seed stage is a bounded,
self-refilling, chat-independent service whose sole mathematical job is to
maintain exactly ten authenticated, not-yet-assigned proposal items for later
root selection. It is not an autonomous research director.

The v2.1 service stopped after its standing receipt was invalidated by Codex
CLI version drift. Ticket 0119 records that operational-only diagnosis and the
explicit user decision for v3. Historical authorization files remain immutable
but cannot start the new implementation. The scheduler is a separate service
and remains intentionally paused/stopped.

The v3 generator is also presently stopped: the state-machine, validated-
learning-export, and guarded-first-test repairs are not yet released. No
provider call, configuration, authorization, or start is allowed until the
focused campaign/generator/guard regressions, Wayfinder checks, guarded
`make test`, and a fresh independent CLEAN review pass against final bytes.
Only then may one fresh authorization reconfirm 30 charged calls, at most 70
remaining calls, and the final implementation and schema receipts. Nothing in
this guide reports the generator as CLEAN or live. The scheduler remains
stopped before, during, and after that generator-only release gate.

## Authority boundary

One standing authorization binds the daemon entrypoint, packet builder,
campaign validator, seed/development/task/event-verification/feedback/root-
screen/snapshot/validated-learning/execution-envelope schemas, the first-test
guard, the v3 migration root, `AGENTS.md`, this operator
contract, the campaign contract, Ticket 0119,
Codex CLI version, provider, generation modes, resource ceilings, exact ready-
depth target, circuit breakers, total invocation cap, and the immutable
accounting-migration baseline. Within that
closed envelope the service may repeatedly:

1. rebuild a fresh whole-project snapshot from current repository bytes;
2. freeze a new campaign identity, prompt, task, output schema, and packet;
3. authenticate those receipts and launch exactly one read-only Sol call;
4. validate the deficit-bound returned seed batch, remove only deterministic
   literal semantic-core duplicates, and preserve immutable receipts; and
5. continue immediately while a positive unreserved ready-item deficit and
   standing-budget capacity remain.

It may inspect the repository read-only and use live primary-source web search.
It may not run a seed's first test, edit Lean or canonical documentation, admit
or schedule a route, assign proof movement, consume or reconcile its own inbox,
spawn subagents, mutate Git, or retry an attempted packet. Root alone performs
semantic duplicate review, evidence admission, failure-genome reconciliation,
portfolio changes, and execution selection.

Before provider process creation, each charged attempt durably writes both
`attempt.json` and an immutable hash-linked service-ledger event, then atomically
advances the accounting head. After process creation, `provider-start.json`
binds PID, Linux boot, start ticks, process group, prompt, and attempt event and
is durably committed before any prompt byte is delivered. A charged attempt
with no such acknowledgement is an operator-diagnosis stop; it is neither
retried nor auto-terminalized. Its exact outcome adds the alternating outcome
event and can close only the immediately unresolved attempt. That packet can never be invoked again, including after a daemon or WSL
restart. A missing batch/ledger artifact, chain gap, partial or forged result,
or unresolved attempt is circuit-open before any fresh launch.  Partial
finalization exposes no ready seeds and may complete only the exact immutable
outcome already bound to that attempt. A later cycle always has a new campaign
identity and snapshot. Two consecutive provider stops or two consecutive zero-
seed novelty stops open a circuit rather than silently spending through a
repeated failure.

## Version-three standing envelope

- provider: `gpt-5.6-sol` at `max` reasoning effort;
- concurrency: one provider job and no subagents;
- per-call ceiling: 90 minutes, 2 local CPU cores, 4 GiB local process-tree
  RSS, and 0.05 GiB captured output;
- provider sandbox: read-only, noninteractive, ephemeral, with live web search;
- cadence: no rolling daily limit and no post-call cooldown; refill is
  event-driven and immediate while an exact deficit remains;
- standing ceiling: 100 provider invocations;
- ready queue target: exactly ten individual proposal items, with pending calls
  reserving their frozen deficit before launch;
- circuit breakers: two consecutive provider stops or two consecutive
  zero-seed batches;
- generation rotation: `context_rich`, `failure_dual`, then `recombination`;
- output: the canonical research-seed schema plus immutable provider,
  deterministic-dedup, packet, and admission receipts; and
- retry: never for an attempted packet.

The exact ready target and retained lifetime/circuit/resource limits make
“continuous” event-driven rather than a blind infinite loop. Claiming one
individual seed releases one replacement slot; no sibling is removed.
Configured safety ceilings may be tightened but never weakened. Changing the implementation, model,
effort, modes, ceilings, or authority invalidates the standing receipt and
requires a new explicit authorization.

The lifetime accounting baseline authenticates the 30 v2/v2.1 attempts charged
under Ticket 0083 and the six earlier v1 attempts explicitly excluded from that
standing lifetime count. Removing the daily limit does not reset the 30 charged
calls, so at most 70 new calls remain.  The baseline and every new event are
receipt-bound; deleting a batch cannot lower the count. A purely local chain
cannot detect coordinated rollback of the head plus every removed tail event;
an external monotonic anchor would be required for that stronger threat.
Whenever ready depth is zero and no provider reservation is pending, root-
origin seeds may fill the queue under the same schema and memory; the daemon
may not weaken or reset its own stop.

Authorization activation is itself an immutable hash-linked sequence. The
mutable pointer and head must both name its latest event and authorization; a
prior still-valid authorization file cannot be made active by rolling back only
the pointer. Every JSON state transition fsyncs new immutable bytes before
publishing a replacement and fsyncs the containing directory afterward.

## Duplicate and failure memory

Every new coordinator snapshot includes all earlier accounting-closed
continuous batch/result pairs, including ready and in-flight seeds, in
`prior-idea-registry.json`. Continuous state reaches the packet builder only
through one immutable generator-produced validated-learning export. Under the
service lock the generator authenticates the current authorization and
accounting chain, every exposed batch/result closure, exact claim, brief and
task, full feedback and reconciliation, and every selected canonical route/
failure-memory receipt. The builder may validate and materialize that export;
it may not scan raw service directories or reinterpret evidence admission.

The export includes every authenticated in-flight claim, a typed projection of
every root-admitted per-seed feedback receipt, every canonical route/failure-
memory record, a materialized learning-state manifest, and their aggregate
learning-epoch hash. Verified fields constrain duplicates and mutations only at
their admitted scope; inferred residue may generate questions but is never
positive evidence. Legacy batch-consumed seeds are marked
`legacy_reconciled_investigation_unknown`.

Feedback validation computes one canonical core digest over every field except
`root_admission`. Root admission and `research-root-reconciliation-v2` both
bind that complete core plus the exact claim, development receipt, standing
authority, and timestamp. Reconciliation is a checked cross-binding, not an
oracle: the generator independently revalidates the task, execution envelope,
event/verifier receipts, scope, proof-distance account, learned tags, next
discriminator, failure-memory reference, claim-candidate disposition, and queue
disposition before projecting them. A `verified` learned statement must be an
exact normalized result of independently checked evidence; other useful text
is `inferred` or `not-established`.

After the provider returns, the service computes a normalized fingerprint from
each seed's target, model, mechanism, and first-test question. Exact repeats are
removed and recorded in `dedup-report.json`; the batch becomes a novelty stop
when fewer than its frozen requested count remain. Target equivalence and
failure-genome scope are mathematical judgments and remain root-only. An
unattempted packet whose feedback epoch is stale is not launched. An attempted
call is never retried; if new feedback makes its output stale, its proposals
expose no ready items and a fresh identity is prepared.

## Snapshot and inventory time semantics

Current admission and historical attestation are intentionally different:

- **Current admission** regenerates the validated-learning export, rebuilds all
  seven deterministic packet outputs in quarantine with the current builder,
  byte-compares them, rechecks the campaign-excluded learning epoch and
  workspace aggregate after replay, and then writes one immutable snapshot-
  admission receipt.
- **Historical attestation** authenticates the frozen export, outputs, and
  admission cross-bindings. It neither consults today's mutable learning state
  nor claims that today's builder would reproduce the old snapshot.
- **Current currency** is a separate launch/ready-exposure check against the
  admitted campaign-excluded learning epoch, workspace aggregate, validator,
  and builder. A stale attempted result remains charged but exposes no ready
  seeds.

All authoritative v3 ready, pending, and reserved counts derive from one
current active authorization and its authenticated hash-linked accounting
view. A provider campaign becomes inventory only when its exact attempt,
outcome, result, and seed-batch receipts close in the current head. An absent
head, chain gap, unresolved attempt, or receipt mismatch fails closed even when
the queue directories are empty. Root-origin inventory instead requires its
exact result, snapshot-admission, and semantic-screen receipts and consumes no
provider invocation.

## Operator commands

The following configuration and start commands describe post-release
operation. They are forbidden in the present stopped state. Before using them,
complete the repairs, focused tests, Wayfinder/portfolio checks, guarded
`make test`, independent CLEAN review, and final-hash freeze described above;
then create one fresh authorization and confirm exact `30 charged / 70
remaining` accounting. Historical receipts are only historically attestable
under their immutable admissions and confer no current authority.

Freeze one standing authorization after its limits receive user approval:

```text
python3 scripts/continuous_idea_generator.py configure \
  --approval-ref <literal-approval-reference>
```

Start the persistent service with that exact receipt:

```text
python3 scripts/continuous_idea_generator.py start \
  --authorization <versioned-authorization-path-from-configure> \
  --authorization-sha256 <sha256>
```

The service immediately freezes and queues its own first cycle. Inspect it
without changing state:

```text
python3 scripts/continuous_idea_generator.py status
```

After root freezes an individual development brief, claim only that seed:

```text
python3 scripts/continuous_idea_generator.py claim \
  --campaign-id <campaign> \
  --seed-id <seed> \
  --seed-batch-sha256 <sha256> \
  --development-brief <path> \
  --development-brief-sha256 <sha256> \
  --task-packet <path> \
  --task-packet-sha256 <sha256>
```

The task packet must reproduce Ticket 0119's first-test authority exactly: at
most 30 minutes, 2 CPU, 4 GiB, 0.1 GiB total output, exact ignored descendants
of its own `runs/agents/<run-id>/` directory, and zero network, provider,
service, scheduler, canonical, external, installation, destructive, or
unapproved-delegation authority. It freezes one root-launched guarded Python
checker, its exact raw inputs, declared output roles, and normalized result.
Standing tasks reject manual reasoning, source reading, Lean, theorem
contracts, and `file_compiles`. No more than four claims, or two from one
mechanism family, may be active.

After root authenticates the terminal evidence and writes the typed feedback
projection, record the learned outcome:

```text
python3 scripts/continuous_idea_generator.py reconcile \
  --campaign-id <campaign> \
  --seed-id <seed> \
  --seed-batch-sha256 <sha256> \
  --feedback <path> \
  --feedback-sha256 <sha256>
```

The historical `consume` command is rejected under v3 because batch release
cannot represent individual assignment or learning.

If the ready queue is empty and no provider packet is pending, root may import
one self-generated validated proposal batch (at most five seeds) under a fresh
`-root-seeds-` identity. Root must first use the generator-owned current-
snapshot preparation path to produce an accounting-backed validated-learning
export, closed build receipt, and immutable snapshot-admission receipt in that
same ignored root run. Directly invoking the packet builder against raw
continuous-service directories is forbidden. The exact preparation command is
part of the unreleased v3 repair and may not be used or invented before its
focused tests and final CLEAN review pass.

The seed batch names that snapshot's `packet-summary.json` and immutable
snapshot-admission receipt. Import validation regenerates the validated export,
cold-rebuilds and byte-compares all seven deterministic outputs with the current
builder, and performs post-replay currency checks. Both builds exclude the
candidate campaign itself, so materializing its returned batch cannot make the
pre-call snapshot disagree with replay. A copied builder hash in a hand-written
receipt is not provenance. Root then freezes a
JSON semantic screen conforming to
`docs/agents/schemas/research-root-semantic-screen.schema.json`. The screen
binds the active authorization, source batch, build receipt, learning epoch,
exact canonical hash and working model tier of every seed, all recomputable
schema/identity/snapshot/proposal/budget checks, and explicit root judgments
for semantic duplication, target equivalence, model/return status, failure
memory, source/novelty status, family correlation, and no padding. Import with:

```text
python3 scripts/continuous_idea_generator.py import-root-batch \
  --seed-batch <path> \
  --seed-batch-sha256 <sha256> \
  --semantic-screen <path> \
  --semantic-screen-sha256 <sha256> \
  --approval-ref <ticket-or-user-decision>
```

The command rejects nonempty queues, pending provider reservations, stale
learning epochs, a screen or builder receipt from another batch, unsafe
campaign identities, and any literal core already in generated memory. The
import is proposal-only, consumes no provider
invocation, and enters the same deduplication, claim, feedback, and prior-
registry memory. Source batch, snapshot, admission, and semantic screen must
all resolve within the same ignored root run and outside the service directory.
Current authorization/accounting and snapshot currency are checked before the
first destination write and again afterward. `result-receipt.json` is written
last and is the only queue-visibility commit marker. A partial import remains
an explicit operator-diagnosis state, exposes no ready seed, and is never
silently deleted or retried.

Graceful stop disables the persistent unit and terminates only its own provider
control group:

```text
python3 scripts/continuous_idea_generator.py stop --reason <reason>
```

The stable state lives under `runs/agents/continuous-idea-generator/`. In the
post-release design, a linked and enabled user-systemd unit owns the daemon,
restarts it after process failure, and starts it again with the user service
manager after WSL restart. This describes the intended released topology, not
current authority or status: the v3 unit is presently stopped and unreceipted.
The unit enforces a 5 GiB cgroup memory ceiling, two-core CPU quota, bounded
task count, and control-group shutdown. The standing authorization's exact
implementation-set hashes prevent old or modified daemon, builder, validator,
guard, or schema code from consuming its authority. Authorizations are
immutable, versioned files; a hash-linked activation ledger and its latest head
constrain the separate active pointer, which may be rotated only while the
daemon is stopped. Earlier packets remain historically attestable under their
immutable admissions, but rolling the pointer back to one of them does not
restore authority.

Provider recovery authenticates the Linux boot identifier, process start
ticks, PID, and process group before attaching to a still-live child. A reused
PID is never followed or killed. Recovered children remain subject to the
original wall, RSS, output, and stop ceilings; a recorded attempt is finalized
without retry when its exact child no longer exists. A valid immutable outcome
written immediately before a crash may repair only the stale accounting head
that names its exact unresolved predecessor. Any other partial transition is an
operator-diagnosis stop.

## Admission boundary

Every `seed-batch.json` is proposal-level search information. Root must run

```text
python3 scripts/check_research_campaign.py --seed-batch <path>
```

and then perform the ordinary stale-snapshot, semantic-duplicate, model-tier,
source, failure-memory, and route review. Daemon uptime, batch count, provider
agreement, or deterministic literal deduplication changes no load-bearing
dependency or portfolio state.

Assignment changes one seed to `investigating`; it does not admit the seed.
Only root may write the hash-bound feedback that changes it to `investigated`.
That feedback references the authenticated development receipt and root
reconciliation, keeps each learned field's epistemic tag, and points to the one
canonical failure-genome home when a mathematical negative is admitted. The
reference binds one exact heading, a unique marker-bounded JSON core and its
canonical hash, and the selected exact falsifier artifact. Later scoped review
may append outside the core; moving, duplicating, or changing the core fails
authentication. A positive or no-signal seed is candidate-
local; a falsifier reaches at most the brief's predeclared subfamily ceiling.
Architecture- or mechanism-wide scope requires a separate authenticated
shared-cause/adversarial review in the same canonical genome home. It is
operational learning memory, not a second route tracker.
Its closed machine-readable shape is
`docs/agents/schemas/research-investigation-feedback.schema.json`; the service
also enforces terminal-specific cross-field rules that JSON Schema does not
express.

Every checked evidence event binds the immutable claim, model, and scope IDs
and the hash of its exact kind, gate branch, subject, polarity, damage, artifact,
and observation. A receipt for one observation cannot be rebound as another
claim or falsifier. One non-operational terminal selects exactly one matching
primary event: `live/supports/primary`, `kill/refutes`, or
`no_signal/observes`. The root-owned first-test guard authenticates the exact
claim/brief/task, enforces the authority and resource envelope, and materializes
only declared outputs. Root verification then reruns the frozen trusted checker
under the same guard, requires it to consume the exact event artifact and raw
inputs, and authenticates a normalized result that establishes the event's
exact semantic core. Worker telemetry or a self-authored verifier receipt is
not checked evidence. A missing or violated execution/verifier envelope is an
`OPERATIONAL_STOP / operational-only` result with no event, verified learning,
or claim candidate.
Every standing first-test feedback has net proof movement `neutral` or
`backward`; this envelope cannot support a forward claim.

The standing first-test branch has no manual reasoning, source access, Lean,
theorem contract, or `file_compiles`; collaboration-agent reasoning may be
retained only as proposal input to a guarded deterministic test. Lean may be
used only later under a separately approved canonical theorem packet and the
guarded Makefile build path. `native_decide` is always computational evidence
and must run through guarded `make test`; it is never `file_compiles` and is
never replaced with kernel `decide`. A later fixed-statement kernel event may
support `file_compiles` only through that separately approved guarded path.

The loop stops when one candidate satisfies all six “has legs” conditions:
authenticated first-hostile-test survival; independent hostile or cold
reproduction; explicit working/target model, information at risk, and return
status; the complete five-field theorem-entry memo and short consumer ladder; a
genuine mathematical delta from the nearest admitted controls; and a bounded
next theorem/falsifier whose outcome branches change allocation. At that point
new claims and loop spending stop pending the user's separate post-gate
decision. The classification is search information and normally neutral proof
movement; a full queue is not “has legs,” and only a compiling theorem that
strictly reduces a named load-bearing dependency is forward.
