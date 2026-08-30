# Multi-agent research protocol

This directory defines the durable roles and execution rules for delegated
research.  A **profile** describes how an agent reasons; a **task packet**
describes one bounded assignment.  Keeping those separate lets us reuse a
perspective without giving it vague or expanding authority.

The Wayfinder remains the only strategic tracker. Its canonical inclusive
route registry is `docs/wayfinder/frontier-portfolio.md`. Agent runs and
execution slates do not create a second roadmap: transient packets,
transcripts, and results belong under the ignored `runs/agents/` directory,
while durable conclusions are integrated into the portfolio, relevant
Wayfinder ticket, experiment note, Lean theorem, or source document. The
managed checkout reserves `.agents`, so portable project configuration is
committed here under `docs/agents/`.

## Roles

The registered profiles are listed in `manifest.toml`.

| Profile | Default authority | Primary use |
| --- | --- | --- |
| Principal Research Orchestrator | integration owner | choose bounded work, arbitrate evidence, and integrate |
| Laplace, adversarial math copilot | read-only | falsify or sharpen a proposed theorem, invariant, or route |
| Structural Proof Architect | read-only | design the conceptual dependency chain and bridge lemmas |
| Mathematical Innovation Scout | read-only | generate compact cross-domain seeds with cheap discriminators |
| Research Question Generator | named owned files | emit up to five compact, materially distinct seeds from a frozen snapshot |
| Research Lead Investigator | named owned files | execute one approved selective-context development brief and emit replayable evidence |
| Research Card Auditor | named owned files | safety-screen seeds before development and fully audit only evidence-bearing route candidates |
| Lean Kernel Engineer | named owned files | prove a frozen theorem contract in Lean |
| Finite-Model Experimentalist | named owned files | run bounded, reproducible searches and produce checkable evidence |
| Formal Proof Reviewer | read-only | independently audit statements, proof boundaries, and claims |

Agent names are runtime identities, not roles.  A newly launched agent receives
the complete profile text and one task packet.  Reusing a friendly name never
substitutes for either artifact.

## Frontier execution cycle

The orchestrator runs research batches as a closed portfolio loop:

1. close the previous slate, verify every evidence claim, integrate accepted
   results, report every predeclared outcome, and close timing estimates;
2. update and validate the canonical frontier portfolio from those results,
   including newly surfaced, expired, suspended, merged, or revived work, and
   name the exact load-bearing dependency-ledger edge changed or state that
   none changed;
3. select `N` threads from the updated portfolio as a temporary execution slate
   and record the leverage/readiness/independence/cost rationale, each slot's
   `proof-producing` or `information-gathering` label, and the mechanism-family
   concentration;
4. make the full branched work plan for every selected thread as far ahead as
   current dependencies permit, inventory approvals, and obtain user approval;
5. execute the approved slate under immutable packets and the lifecycle below,
   then return to step 1.

Step 1 is an evidence gate, not a summary ritual. Step 2 precedes selection so
the next allocation sees every consequence of the prior run. Step 3 is a
scheduling decision and never prunes the inclusive portfolio. Step 4 must name
potential outcomes and downstream continuations; uncertain branches remain
branches rather than hidden assumptions.

### Theorem-first operating rebalance

Ticket 0103 is the current user-approved selection override. Discretionary
research time is planned at 40% `D-HALF` structural work, 30% `D-DECOMP`
repair, 20% source-grounded distinct mechanism discovery, and 10% bounded
computation/process work. Mandatory evidence admission, integration, guarded
builds, and repository tests are outside those planning weights.

Before a proof-producing or intermediary-lemma packet is frozen, its
human-readable theorem-entry memo must name the exact producer, existing
consumer, strict difficulty separation, smallest plausible hostile example,
and expected geometric/combinatorial/source producer fact. A missing field
keeps the item at route-design scope. Before a fixture-dependent computation
packet is frozen, a separate semantic-readiness receipt must independently
reconstruct all role-critical predicates from raw inputs and normalize every
representation boundary used by gate precedence. Hash and schema checks alone
are not readiness evidence.

When no portfolio entry is `advancing` and no theorem-ready producer passes
that gate, run a smaller route-design or source-grounding block rather than
padding an exploration slate. Adjacent lemmas require an existing named
consumer. At most one simultaneous Fin15 lane is allowed under the current
allocation, and it must change the mathematical information rather than merely
increase computational resources. `D-NORMALIZE` remains without ordinary
allocation until its recorded revival condition is met.

### Evidence-first research campaign

Ticket 0078 replaces the publication-card-first, serial four-plus-one factory
with the campaign contract in `research-campaign.md`. The coordinator retains
the full reconciled project snapshot and generates up to five compact,
materially distinct seeds. Each schema-valid seed receives only a lightweight
safety, duplication, target-equivalence, and model-tier screen before its
cheapest hostile mathematical probe is frozen. We do not try to predict a
question's value through a large speculative card before trying to answer it.
Fewer than five honest seeds is a valid novelty stop.

A seed can be developed as soon as a compatible slot is free only after its
exact task packet and selective-context brief are frozen and approved. These
bounded probes are proposal-level information gathering outside the portfolio:
they do not count as proof-producing slots, route admission, promotion,
revival, or proof movement. Root later audits each receipt against the full
coordinator snapshot. A credible claim takes capacity away from more
generation and enters the independent verification funnel; an admitted
failure supplies scoped negative constraints for a newly identified mutation;
and serendipitous evidence is preserved in a sidecar without replacing the
assigned probe's terminal.

The old `FACTORY-REFRESH-014-CURRENT-STATE-V3` prompt and task are an immutable
historical control with disposition
`superseded-before-dispatch / immutable-historical-control-only`. They are not
reserve work and must not be run, mutated, deleted, or assigned a fabricated
result. A future prospective comparison needs its own approved wrapper task,
identity, input hashes, and output paths.

The seed stage may be operated by the bounded service in
`continuous-idea-generator.md`. Ticket 0083 makes the daemon a bounded
self-refilling proposal inbox, not an orchestrator: one standing authorization
binds the daemon, builder, validator, schema, provider executable, rate,
total-call, resource,
high-water, and circuit-breaker limits; every individual packet remains
hash-frozen; authorization rotation preserves old receipts and global rate
accounting; an attempted packet is never retried; and root alone consumes,
reconciles, admits, or schedules output.

Four concurrent mathematical investigations remains the occupancy target, and
the ordinary no-padding and mechanism-diversity rules remain unchanged. Under
Ticket 0103, spare capacity may perform campaign generation, development,
source grounding, audit, or route review only when that work has its own
decision-changing gate and exact future approval; it is not automatic backfill.
Seed generation itself is not mathematical proof work, and an unadmitted
development probe does not fill a proof-producing portfolio slot.

### Rolling execution pipeline

Ticket 0067 supersedes the synchronized-batch waiting rule. An admitted,
approved thread launches whenever a compatible slot is free; its terminal is
checked and reconciled immediately, and that slot may be backfilled without
waiting for unrelated lanes. When fewer than four mathematical gates are
ready, Ticket 0103 permits unused capacity to remain idle; campaign generation,
development, grounding, card audit, or route review runs only from a separately
justified decision-changing gate. A campaign lane uses a frozen
reconciled snapshot and may overlap execution, but its proposals and evidence
must be rebased against any intervening admitted result before portfolio entry
or scheduling. A mathematical negative receives its admitted failure-genome
anchor during that serial reconciliation before the slot is reused; unrelated
frozen lanes do not wait. Four remains the occupancy target and never licenses
padding.

The four selected investigations retain the ordinary mechanism-diversity and
proof-distance rules.  No more than two normally come from one correlated
family.  Unless no credible theorem gate is executable and the user explicitly
approves an exploration-only slate, at least one slot should be
`proof-producing`; otherwise the slate is labeled exploration. Campaign seeds
and pre-admission development are tracked separately and never count toward
that proof-producing quota.

#### Immediate backfill transaction

For occupancy purposes, a packet is **dispatch-ready** only when its exact
bytes validate, its input closure still authenticates, and the user has
approved that exact packet as part of the current rolling wave.  A frozen but
merely planned packet is useful reserve inventory, but it is not an available
replacement and must never be reported as running or ready-to-dispatch.

The orchestrator treats every worker terminal as one indivisible backfill
transaction:

1. observe the terminal with a contemporaneous collaboration-state query;
2. authenticate the task/result pair and admit its evidence at the narrowest
   supported scope;
3. reconcile the affected route and load-bearing dependency, explicitly
   recording when neither changes;
4. dispatch one compatible approved reserve packet into the freed slot before
   unrelated planning continues; and
5. freeze and seek approval for a replacement reserve until the approved queue
   returns to its declared floor.

Ticket 0103 suspends the normal four-packet operational reserve floor while no
`advancing` entry and no theorem-ready producer exist. The honest approved
reserve may then contain zero to three packets, and reserve production is not
triggered merely by queue depth. Do not author support work to restore a
numeric floor. A future exploration-only or support wave requires its own
decision-changing gates and exact user approval; none may be mislabeled as an
admitted mathematical investigation.
Result-dependent successors enter the reserve only after their prerequisites
are admitted and their new input hashes are frozen.

After each dispatch or terminal, update the board in the same transaction and
run:

```text
make rolling-pipeline BOARD=runs/agents/<run>/live-board.json
```

Then compare the validated declaration with a fresh collaboration-state query.
The checker cannot observe the agent service, so neither the board nor a stale
worker name is sufficient evidence of occupancy.  When explicit approval is
the only missing condition, request the next consolidated exact-hash wave
before active lanes are expected to finish; if approval is still absent, record
that precise unavoidable vacancy instead of inventing work or silently
broadening authority.

#### Persistent execution scheduler

The process-backed implementation of the approved-packet queue is documented
in `research-scheduler.md`. Unlike `live-board.json`, it owns durable SQLite
state, worker process telemetry, transient systemd control groups, resource
limits, crash detection, and dispatch. Unlike the continuous idea generator,
it does not manufacture packets: every job must already appear by exact hash
in an authenticated approved operational wave.

The scheduler targets four mathematical workers, prioritizes mathematical
packets over support packets, enforces the builder and mechanism-family limits,
and records exact under-capacity causes when the approved reserve is too small.
One approved reserve plan can import a complete exact-hash wave after every
packet and dispatch parameter passes preflight. A valid or operational worker
terminal immediately releases its process lane for independent approved
backfill while the terminal remains in a separate root-only reconciliation
inbox. This preserves the mandatory evidence gate: replacement cannot use the
result, infer a successor, edit the Wayfinder, assign proof movement, or widen
a packet. Late reconciliation cannot release a lane already reused by another
worker.

The terminal inbox is now paired with a serialized Wayfinder lifecycle
control plane. Every terminal receives an immutable lifecycle-inbox item.
Scheduler reconciliation requires an independently sealed receipt binding the
exact task/result, root adjudication, owning ticket, affected portfolio entry,
map/ledger statement, any required existing-record failure-genome anchor,
pre/post canonical snapshots, and passing Wayfinder checks. Thus an already
approved independent reserve may preserve process occupancy, but no
result-dependent successor can become eligible from worker prose or stale
portfolio state.

The service is separately authorized from the proposal-only continuous idea
generator. Neither daemon's standing receipt grants authority to the other.
Changing scheduler code, schemas, Codex version, models, resource limits, or
authority invalidates its receipt and requires a new explicit user decision.

### Orchestrator liveness invariant

An approved slate remains one active orchestrator turn until every dispatched
worker has a terminal result, an explicit bounded stop, or a documented
carry-forward marker.  The orchestrator must not send a final response while a
slate worker is still running.  If the user asks for status during execution,
answer in commentary and keep the wait/reconciliation loop alive.  If the turn
must end unexpectedly, first interrupt or checkpoint every worker and record
the carry-forward boundary.

While workers are live, the orchestrator rechecks worker state regularly and
emits a concise progress or unchanged-state update at least once per minute.
When a worker finishes, validate its result immediately; do not wait for the
next user message.  Before integrating or reporting slate completion, run
`python3 scripts/check_agent_slate.py --slate PATH`.  This verifies that every
frozen task in the slate has exactly one schema-valid terminal result with the
same run and task IDs.  The runtime agent-state check remains an orchestrator
responsibility because repository scripts cannot inspect the collaboration
service.

The same invariant covers serial integration commands.  A project build,
certificate replay, test, or solver run must have one named owner, a hard wall
clock and resource cap, and a terminal exit status.  While it is live, the
orchestrator stays in the monitoring loop and reports the last verified
milestone even if the command emits no new output.  A timeout is recorded as an
operational stop, never inferred to be either success or a mathematical
failure.

For generated-certificate modules, command-level serialization is not by
itself a resource guarantee.  Lake may schedule several external Lean
compilers, and each compiler may create its own worker pool.  The orchestrator
therefore samples host child count, CPU, and aggregate RSS shortly after a new
heavy build begins and again after an unexpectedly quiet interval.  If the
observed compiler set exceeds the packet's aggregate memory or builder budget,
stop the process group at once and verify that no Lean/Lake child remains.
`-Kjobs=1` is a Lake configuration override and must not be cited as evidence
that compilation was serialized.  The safe local fallback is an explicit,
one-module-at-a-time sequence of guarded direct-Lean or single-module Lake
gates, with no overlapping Lake build.  The default `make test` Lean gate builds
the umbrella `+ErdosSzekeres:olean` facet: it kernel-checks the imported proof
graph without requiring generated C and editor metadata for theorem-only
certificate modules.  `make lean-artifacts` retains the full default Lake
library-facet build when those extra artifacts are required.  Either gate is
deferred rather than crash-tested if the current checkout cannot run it within
the declared aggregate resource envelope.

## Assignment lifecycle

1. **Orient.** For admitted portfolio work, read `docs/wayfinder/map.md` and
   `docs/wayfinder/frontier-portfolio.md`, run the Wayfinder status and
   portfolio checks, and identify the `FP-NN` entry and consequential ticket
   served by the work. Root performs that global orientation for a campaign;
   a pre-admission development worker authenticates only the selected context
   in its brief and does not infer portfolio membership from the assignment.
2. **Admit and freeze.** The orchestrator records an immutable task packet with
   the base revision, workspace fingerprint, objective, exact theorem contract
   when applicable, inputs and hashes, ownership, budget, checks, success
   condition, stop conditions, deliverables, and permitted claim levels.
   Before this freeze, a proof-producing or intermediary-lemma assignment must
   pass the five-field theorem-entry memo in `AGENTS.md`. A fixture-dependent
   computation must separately freeze a semantic-readiness receipt produced by
   an independent reconstruction of every role-critical predicate and
   representation boundary. A missing memo or receipt is a readiness stop, not
   a field to be supplied by the execution worker after outcome-bearing work
   begins.
   The whole-workspace fingerprint is an admission snapshot, not a global lock
   on unrelated work.  During an admitted parallel run, the continuing gate is
   the base revision plus every explicitly frozen input hash.  A worker reports
   drift in disjoint orchestrator-owned or separately assigned paths but stops
   only if a frozen input, its owned write set, or the base revision changes.
   This distinction must be written into packets whose execution overlaps
   integration work; otherwise routine timing or documentation updates create
   false stops without improving evidence integrity.

   A rolling lane must not directly freeze a root-owned canonical file that the
   orchestrator is required to edit while the lane can remain live. In
   particular, `docs/wayfinder/map.md`,
   `docs/wayfinder/frontier-portfolio.md`, and the active reconciliation ticket
   are live integration outputs, not stable worker inputs. Before dispatch,
   root uses `scripts/freeze_agent_context.py` to embed the exact needed UTF-8
   bytes and their original paths/hashes in one immutable ignored context
   capsule. The task freezes that capsule, not the live canonical files. A
   worker verifies the capsule internally at admission and terminal; it does
   not compare the embedded provenance to live canonical bytes at terminal.
   Root performs the live comparison and semantic rebase when admitting the
   result.

   This capsule exception is narrow. Lean sources, theorem statements,
   implementation code, source evidence, experiment artifacts, and every other
   input whose exact bytes affect the task's mathematical or computational
   meaning remain direct frozen task inputs. Moving such an artifact into a
   context capsule merely to evade drift is a protocol violation. A lane that
   genuinely needs the current live canonical state must instead be serialized
   with reconciliation. Capsule corruption, direct semantic-input drift,
   owned-write drift, or base-revision drift remains terminal.
3. **Inventory approvals.** For every plan expected to take at least two hours,
   identify all foreseeable provider calls, out-of-sandbox commands, installs,
   resource increases, process termination, destructive actions, and external
   mutations before asking the user to approve the plan. State which actions
   are already authorized, which need new approval, and which remain
   conditional because their exact target is not yet known. After approval,
   trigger all foreseeable platform prompts at the beginning of the block. An
   unforeseen later prompt pauses only its dependent branch.
4. **Innovation check.** At the start of every user-approved mathematical work
   item or batch, record one of `campaign seed pass`, `dispatch scout`, `reuse
   current result`, or `skip`, with a concrete reason. A completed campaign
   seed pass satisfies this check; do not automatically launch a redundant
   scout. Use a separate Innovation Scout for a strategic route redirect or an
   explicitly independent representation-escape pass. Skip only for mechanical
   implementation of an already frozen theorem contract or repository
   maintenance.
5. **Falsify or design.** Before expensive implementation, consult Laplace for
   a questionable statement or the Structural Proof Architect for a missing
   conceptual route. When the frontier stalls or a route is retired, use the
   evidence-first campaign or an independent Innovation Scout to generate
   compact alternatives with hostile first tests. This stage is read-only
   unless a separately approved development packet grants exact owned paths.
6. **Dispatch.** Give a builder concrete, non-overlapping write paths.  Shared
   integration files remain orchestrator-owned.  A worker may not silently
   weaken or replace a frozen theorem statement.
7. **Gate locally.** A Lean worker first checks the owned file.  An experimental
   worker runs its independent checker.  The worker returns a structured result
   with an evidence level and explicit limitations.
8. **Review independently.** A read-only reviewer checks statement preservation,
   assumptions, trust boundaries, and whether the reported gate actually ran.
9. **Integrate serially.** The orchestrator inspects the diff, resolves conflicts,
   updates shared imports and documentation, and runs the project/repository
   gates.  Workers do not concurrently build, commit, or edit Wayfinder files.
10. **Record.** Promote durable conclusions into the canonical project artifact.
Retain negative results when they rule out a documented route.

The slate-level completion manifest uses
`templates/agent-execution-slate.json`.  It is transient and belongs under
`runs/agents/`; its validator is a mandatory guard against silently omitting a
finished, blocked, or failed lane from reconciliation.

### Failure-genome admission and propagation

A worker may propose a failure genome, but root owns admission after checking
the terminal evidence. The admitted block records one provenance subject, four
verified core fields, and five individually tagged design-memory fields under
the schema in `AGENTS.md`; the result schema does not change. Unsupported
design lessons become `not-established`, and purely operational stops receive
no mathematical genome.

The full block has exactly one existing durable home: its originating
idea-ledger entry; otherwise its `FP-NN` entry; otherwise the decision ticket
that owns a pre-admission rejection. Portfolio reconciliation copies only the
ordinary evidence, scope, gate, and revival consequences and links the durable
block rather than duplicating it. The next coordinator snapshot reads the
block from that existing home with its evidence hash and
`verified`/`inferred`/`not-established` tags intact; a worker sees only the
selected digest required by its brief. A mutation receives a new immutable
identity and must state the material mathematical information changed. A
discriminator, mutation, or falsifier remains proposal memory and cannot become
a backfill lane without a separately approved packet and, for portfolio work,
ordinary route admission.

## Plan outcome contract

Every planned mathematical work item must declare its possible outcomes before
execution. The outcomes must be specific enough to determine the next route
decision; a generic promise to "make progress" is not an outcome contract.
Use stable labels in the plan and preserve those labels through execution.

At minimum, distinguish:

1. **Proved/closed:** the frozen target compiles in Lean and the named consumer
   is available;
2. **Reduced/modified:** a strictly stronger normalization or smaller open
   obstruction compiles, but the parent target remains open;
3. **Refuted/expired:** the frozen target or route is contradicted at a stated
   model and evidence level; and
4. **Inconclusive/operational stop:** the bounded work ends without deciding
   the mathematical target.

Tailor these branches to the actual theorem. For example, a falsification task
should name the surviving repaired statement, while a proof task should name
the downstream theorem unlocked by success. Computational evidence, proposal
evidence, `file_compiles`, and a full project theorem remain separate evidence
levels inside each outcome.

Every completion or checkpoint report must name exactly which predeclared
outcome occurred, explain why its evidence gate was met, and state the next
work item implied by that branch. If execution reveals a genuinely new
outcome, stop or replan explicitly rather than silently replacing the original
labels. Multi-item and multi-hour plans report an outcome for every thread,
including threads that were skipped, superseded, or stopped by another result.
An unexpected observation is recorded as a scoped serendipity sidecar to one
of the ordinary primary terminals. It does not replace the frozen target,
expand authority, or self-admit a claim or route.

## Route-portfolio rule

The canonical portfolio is
`docs/wayfinder/frontier-portfolio.md`. It is an inclusive mathematical and
research-system inventory, not the list of agents currently running. Before
each bounded batch, the orchestrator selects a temporary execution slate from
its executable entries using leverage, readiness, independence, information
gain, cost, and focus-expiry considerations. The slate and its task packets
record scheduling; they do not define portfolio membership. Results update the
evidence, obstruction, gate, and state of the stable portfolio entry in place.
The concise load-bearing dependency ledger in `docs/wayfinder/map.md`, not the
portfolio entry count, states proof distance to the destination.  Every entry
records its stable mechanism family, named dependency, scope ceiling, missing
generalization bridge, and last forward result.  Descendants sharing one
unproved producer inherit the same evidence streak and are correlated routes.

`Advancing` is reserved for a thread with recent forward proof movement and a
next gate capable of producing a compiling theorem that closes or strictly
reduces a named dependency.  A finite theorem updates a uniform parent only
when it is a required base case of an existing induction or supplies a
parameterized lemma used beyond that instance.  Conditional interfaces,
finite survival, SAT/UNSAT, and certificate compression alone remain `gated`
or retain their existing non-advancing state.

Substantial mathematical batches should exploit independent parallel thought,
not only parallel execution of one route.  By default, pair the nearest formal
theorem with a structurally different load-bearing thread and a bounded
innovation/falsification sidecar.  After two consecutive open-ended batches on
one obstruction, perform a route-level audit before granting it another full
batch.  Continue concentrated work when a frozen proof is measurably closing;
suspend speculative grinding when successive refinements inherit the same
countermodels and no new distinguishing invariant is available.

By default no more than half a slate belongs to one mechanism family; a
concentrated exception requires an explicit mathematical justification.  A
slate with no proof-producing slot is reported as exploration.  After an exact
SAT/UNSAT gate, further certificate work requires either a named Lean theorem
it can close or a frozen semantic-extraction hypothesis; proof shrinking alone
does not define another mathematical lane.

A suspended route remains in the Wayfinder with a concrete revival gate.  It
may be screened cheaply by the Innovation Scout, but it does not regain a
builder merely because it is unfinished.  The orchestrator reports portfolio
outcomes by mathematical leverage and evidence level, not by agent activity.
Independent thought does not mean overlapping high-memory elaboration: only
one delegated builder runs at a time, while read-only design, falsification,
and review threads supply the parallel breadth.

## Estimate calibration

Every work item forecast at fifteen minutes or more must be entered in
`time-estimates.csv` before execution and closed with its actual wall time and
outcome. Follow `time-estimation.md`. Multi-agent task effort is not elapsed
time: overlapping work is counted by its critical path, and an unused stop
budget is not reported as time consumed. Plans without three comparable
completed rows must be labeled uncalibrated.

The bounded Sol/Fable review remains the strategic gate for selecting or
changing the main route.  It is not required for ordinary implementation of an
already-vetted theorem contract.

The project approval rule for the provider harness is
`.codex/rules/adversarial-review.rules`. Codex loads project rules when a
session starts; adding or changing this file does not alter permissions in an
already-running session. `codex execpolicy check` can validate the command
match immediately, but the operational fix is verified only after a restarted
session completes a real provider run without an approval prompt.

## Authority and concurrency

- The orchestrator is the sole integrator and owns every path listed in
  `policy.orchestrator_owned` in `manifest.toml`.
- Specialists and reviewers are read-only by default.  Builders may edit only
  the exact paths assigned in their packet.
- Write sets must not overlap.  Reads may overlap, but their hashes must match
  the frozen packet.
- At most three delegated workers may run concurrently, and at most one of
  them may be a builder.  Delegation depth is one: only the orchestrator
  allocates project work.
- Project-wide builds, repository tests, commits, pushes, Wayfinder edits, and
  shared import edits are serialized through the orchestrator.
- Default resource limits are inherited from `AGENTS.md` and repeated in the
  manifest.  Exceeding them requires a new bounded packet and user approval
  where project policy requires it.

## Evidence and disagreement

All worker output is an untrusted proposal until its claimed gate passes.  A
result must report one of the manifest's claim levels.  In particular,
`computational_evidence` is not a theorem, `file_compiles` is not a project
build, and agent consensus is never a proof.

Each result states both what it **supports** and what it **does not support**.
When agents disagree, the orchestrator preserves the competing claims, asks
each side for the smallest distinguishing theorem, counterexample, or bounded
test, and schedules that test.  One concise rebuttal round is preferred over an
open-ended debate.  Provider failure, timeout, or silence is operational
evidence only and says nothing mathematical.

## Task and result contracts

The machine-readable contracts are:

- `schemas/task-packet.schema.json`
- `schemas/result.schema.json`
- `templates/agent-task-packet.json`
- `templates/agent-result.json`

Run `python3 scripts/check_agent_orchestration.py` to validate the committed
system.  Pass `--task-packet PATH` or `--result PATH` to validate a concrete
runtime artifact against the repository policy.
