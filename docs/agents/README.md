# Multi-agent research protocol

This directory defines the durable roles and execution rules for delegated
research.  A **profile** describes how an agent reasons; a **task packet**
describes one bounded assignment.  Keeping those separate lets us reuse a
perspective without giving it vague or expanding authority.

The Wayfinder remains the only strategic tracker.  Agent runs do not create a
second roadmap: transient packets, transcripts, and results belong under the
ignored `runs/agents/` directory, while durable conclusions are integrated
into the relevant Wayfinder ticket, experiment note, Lean theorem, or source
document.  The managed checkout reserves `.agents`, so portable project
configuration is committed here under `docs/agents/`.

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

## Assignment lifecycle

1. **Orient.** Read `docs/wayfinder/map.md`, run the Wayfinder status command,
   and identify the consequential ticket served by the work.
2. **Admit and freeze.** The orchestrator records an immutable task packet with
   the base revision, workspace fingerprint, objective, exact theorem contract
   when applicable, inputs and hashes, ownership, budget, checks, success
   condition, stop conditions, deliverables, and permitted claim levels.
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
