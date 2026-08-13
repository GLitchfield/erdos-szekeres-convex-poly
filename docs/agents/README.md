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
| Mathematical Innovation Scout | read-only | generate cross-domain approaches with cheap falsifiers and Lean landing points |
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
   including newly surfaced, expired, suspended, merged, or revived work;
3. select `N` threads from the updated portfolio as a temporary execution slate
   and record the leverage/readiness/independence/cost rationale;
4. make the full branched work plan for every selected thread as far ahead as
   current dependencies permit, inventory approvals, and obtain user approval;
5. execute the approved slate under immutable packets and the lifecycle below,
   then return to step 1.

Step 1 is an evidence gate, not a summary ritual. Step 2 precedes selection so
the next allocation sees every consequence of the prior run. Step 3 is a
scheduling decision and never prunes the inclusive portfolio. Step 4 must name
potential outcomes and downstream continuations; uncertain branches remain
branches rather than hidden assumptions.

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

1. **Orient.** Read `docs/wayfinder/map.md` and
   `docs/wayfinder/frontier-portfolio.md`, run the Wayfinder status and
   portfolio checks, and identify the `FP-NN` entry and consequential ticket
   served by the work.
2. **Admit and freeze.** The orchestrator records an immutable task packet with
   the base revision, workspace fingerprint, objective, exact theorem contract
   when applicable, inputs and hashes, ownership, budget, checks, success
   condition, stop conditions, deliverables, and permitted claim levels.
   The whole-workspace fingerprint is an admission snapshot, not a global lock
   on unrelated work.  During an admitted parallel run, the continuing gate is
   the base revision plus every explicitly frozen input hash.  A worker reports
   drift in disjoint orchestrator-owned or separately assigned paths but stops
   only if a frozen input, its owned write set, or the base revision changes.
   This distinction must be written into packets whose execution overlaps
   integration work; otherwise routine timing or documentation updates create
   false stops without improving evidence integrity.
3. **Inventory approvals.** For every plan expected to take at least two hours,
   identify all foreseeable provider calls, out-of-sandbox commands, installs,
   resource increases, process termination, destructive actions, and external
   mutations before asking the user to approve the plan. State which actions
   are already authorized, which need new approval, and which remain
   conditional because their exact target is not yet known. After approval,
   trigger all foreseeable platform prompts at the beginning of the block. An
   unforeseen later prompt pauses only its dependent branch.
4. **Innovation check.** At the start of every user-approved mathematical work
   item or batch, record one of `dispatch now`, `reuse current result`, or
   `skip`, with a concrete reason. Dispatching the Mathematical Innovation
   Scout is the default for a new invariant, a route selection or redirect, a
   recent counterexample, a multi-item research batch, or work expected to
   consume substantial time. Skip only for mechanical implementation of an
   already frozen theorem contract or repository maintenance. The scout is a
   read-only sidecar: it runs alongside the main stream and is reviewed at the
   next cycle boundary rather than blocking implementation.
5. **Falsify or design.** Before expensive implementation, consult Laplace for
   a questionable statement or the Structural Proof Architect for a missing
   conceptual route.  When the frontier stalls or a route is retired, consult
   the Mathematical Innovation Scout for a bounded portfolio of alternatives.
   This stage is read-only.
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

## Route-portfolio rule

The canonical portfolio is
`docs/wayfinder/frontier-portfolio.md`. It is an inclusive mathematical and
research-system inventory, not the list of agents currently running. Before
each bounded batch, the orchestrator selects a temporary execution slate from
its executable entries using leverage, readiness, independence, information
gain, cost, and focus-expiry considerations. The slate and its task packets
record scheduling; they do not define portfolio membership. Results update the
evidence, obstruction, gate, and state of the stable portfolio entry in place.

Substantial mathematical batches should exploit independent parallel thought,
not only parallel execution of one route.  By default, pair the nearest formal
theorem with a structurally different load-bearing thread and a bounded
innovation/falsification sidecar.  After two consecutive open-ended batches on
one obstruction, perform a route-level audit before granting it another full
batch.  Continue concentrated work when a frozen proof is measurably closing;
suspend speculative grinding when successive refinements inherit the same
countermodels and no new distinguishing invariant is available.

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
