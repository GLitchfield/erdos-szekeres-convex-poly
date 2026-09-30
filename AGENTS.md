# Agent guidance (any agent: Claude Code, Codex, a human)

**Project.** Formal research on the exact Erdős–Szekeres happy-ending conjecture: the least
number of planar points in general position forcing `n` points in convex position is
`2^(n-2) + 1` for every `n ≥ 3`, with a compiling Lean 4 proof. Progress consists only of
explicitly stated, compiling Lean theorems that remove a documented obstruction or establish a
reusable part of that proof; the `es` harness (`tools/es`, design in `docs/harness-design.md`)
derives what is open, claimed and closed from the compiled Lean environment.

**Agent identity.** Export `ES_AGENT=<tool>:<session id>` (Claude Code sessions get it from the
SessionStart hook; other tools set it themselves, e.g. `ES_AGENT=codex:<id>`). Every claim, job,
log entry and falsifier run is recorded under that id.

**Harness state and sandboxes.** The shared database, logs and extract cache live in
`.es/erdos-szekeres/` inside the checkout (gitignored; `[project] es_home` in
`harness/config.toml`), so an agent that may only write the workspace, such as Codex in
workspace-write mode, can write them; `~/.es/erdos-szekeres` is a symlink to the same
directory. A git worktree shares the state of the checkout it belongs to (the path is
resolved against the primary checkout), so claims, jobs and log entries made from a
worktree land in the same journal; a worktree on a branch older than 2026-09-07 needs
`.es/erdos-szekeres` symlinked to the primary checkout's copy by hand. If the database is still not writable, read commands (`es status`, `es ready`,
`es journal`, `es job list`, `es node show`, `es search`) work and write commands (`es claim`,
`es release`, `es log`, `es job run`, `es node add`) refuse with a message saying so.
`es job run` needs the systemd user bus (`systemd-run --user`) to create the memory-guarded
scope; from a sandbox that hides `/run/user/<uid>/bus` the job is queued instead, and an
`es worker` started from an unsandboxed shell runs queued jobs one at a time (`es job status
<id>` to follow, `es job requeue <id>` after a failure). `es build` and `es check` need the bus
directly.

**Working rules.** The list below is identical to `CLAUDE.md` (a test in `tools/es/tests`
fails if they drift); edit both together.

These rules are the same for every agent (Claude Code, Codex, a human); `AGENTS.md`
carries the identical list and a test keeps the two in sync.

- Project state comes from `es status`; do not read docs/wayfinder to learn what is open. If `es status` says the index is stale, run `es extract` before choosing work.
- Pick work with `es ready`; run `es claim <node> --why "<what you intend to do>"` before starting. When you stop, `es release <node> --outcome closed|partial|blocked|abandoned|refuted --note "<what was done, what stopped you>"`; a claim that merely expires is recorded as abandoned.
- Every command that runs longer than a minute (Python enumerations, SAT solvers, sweeps, anything under `nohup` or `systemd-run`) goes through `es job run --why "<purpose>" --out <runs/... or data/...> [--node <node>] [--mem 2G] -- <command>`. It records purpose, cap, outputs, agent and measured peak, enforces the memory budget in `harness/config.toml` `[jobs]`, and is what other agents see in `es status` and `es journal`. Results belong under `runs/` or `data/`, never in a session scratch directory.
- Job submission is not task completion. Keep the reporting turn open while authorized jobs are queued or running; use `es job wait <id> --timeout 55` (MCP `job_wait`) and continue when `terminal=false`. On completion, failure, or a review gate, inspect the outputs, handle authorized follow-up work, and report the result without waiting for the user to ask. End early only for a required user input, an explicit user pause, or a verified callback that will resume reporting. A checkpoint file alone is not a callback. If the client/session is interrupted, save the job IDs and pending reporting work, and check them first on resume; do not promise notifications while the client is closed.
- Long computations get progress checkpoints, not deadlines. Never stop a test, probe, falsifier, enumeration or solver at a time limit you chose yourself: no `timeout N` wrappers, and no `es job run --budget` or `es falsify --timeout` unless the user set that deadline. Run anything not measured to finish within a minute as a background job (`es job run`, `es falsify --async`). Before launching, time a small instance and extrapolate; make the job report progress (items done out of the total, rate) in its job log or an `--out` file, and set `--review MIN` from the estimate (default `[jobs] review_after_min`).
- At each checkpoint (`es job wait` returns `review_due`; `es job list` shows REVIEW DUE), read the progress and estimate the time left, then decide. On track or nearly done: leave it alone. Too slow (for example 2% done): find out why (measure how the cost scales), then either make it cheaper (shard, parallelize, a compiled evaluator, pruning) or get the answer another way, keeping the question the same. Record the estimate and the decision with `es job review <id> --note "..."`. A stopped, cancelled or narrowed run is neither a result nor a dead end: `es log` what it covered, why it stopped and the follow-up that will answer the question, and keep any coverage you dropped listed as open. A synchronous guard firing (the `es falsify` sync limit, a build or extract budget) means the same: rerun in the background and review it.
- Delegate routine research, Lean repair, and job follow-up to Sol at xhigh; Astra directs the mathematics and reviews completed work. `es run agent` registers an ordinary-code observer in `es worker`. Use `es run progress OUT` for human status and `es delivery status` to check callback readiness. Before yielding unattended, verify the exact coordinator/thread with `es delivery verify --thread "$CODEX_THREAD_ID"` and confirm the challenge only when it arrives through that client; queued submission alone is not verification. With a verified callback and a running worker, avoid Astra polling turns: escalate only a terminal run or persistent infrastructure blocker, not individual compiler failures. The configured capacity retry preserves the same thread and deadlines; never reset a user pause, quota, or uncertain submission. If callbacks are unavailable, the completion-reporting rule still applies.
- Record coordinator monitoring in its own usage window with an observational 10,000-output-token target; keep final mathematical review and library maintenance in separate windows. On the terminal event, read its compact review reference or run `es run review OUT` (supply `--artifact-root RUN_DIR` when scripts live outside the host directory), inspect the relevant proof receipts, report the outcome promptly, and reconcile late usage. A review inventory or successful process exit grants no theorem credit. Judge savings from all-in matched work, including setup, failed attempts, recovery, and review.
- Record every research finding in the shared harness as it arises, including failed conjectures, proof routes, probes, counterexamples, meaningful compiler failures, and infrastructure limitations, even when the plan does not change. Use `es log "<finding and consequence>" [--node <node>]` before the next substantive attempt; include the exact claim and hypotheses or probe semantics, what was tried, the observed result, why it did or did not work, and the job ID, proof receipt, commit, or durable `runs/` or `data/` artifact that supports it. State when evidence is diagnostic rather than Lean-certified, and record missing output or uncertain results explicitly. Log a plan change and its reason before making it. An undocumented failure must not be silently retried or presented as an established fact.
- Before pausing, handing off, or closing a research run, write a concise research handoff under `runs/` that names the exact open obligation, accepted theorems and receipts, failed approaches and their failure modes, reusable observations, unresolved questions, and evidence paths; link it with `es log` and include its path in the claim release or run report. `es run handoff` provides factual operation and usage records but does not replace this mathematical account. On resumption, read `es status`, the relevant `es journal` history and latest research handoff before choosing an attempt; use a longer `--since` interval or node filter when 24 hours misses earlier work.
- New statements go only in ESBlueprint via `es node add`. Never edit a statement by hand; use `es node restate`.
- Before writing any lemma, run `es search "<what it says>"` and cite the result in the PR.
- One node per branch, named `node/<Name>`. A PR closes exactly one node and edits no statements.
- Never add an axiom, `native_decide`, or `sorry` outside ESBlueprint without an allowlist entry (`harness/allowlist.json`).
- Generated certificate modules (the ESCertificates layer, see `harness/config.toml`) are only regenerated by `scripts/generate_*.py`.
- Do not write tickets; `es note` writes the weekly note.
- Builds go through `es build` / `es check` (memory-guarded, budgeted); never run bare `lake build` on big targets.
- Git metadata lives in `.git-data`; `es` handles this, and manual git commands need `git -c gc.auto=0 -c maintenance.auto=false --git-dir=.git-data --work-tree=.` so background maintenance does not retain guarded job reservations.
- The harness is `tools/es` (`tools/es/bin/es`, MCP server `es`); design in `docs/harness-design.md`.
- Prefer the reusable automation commands before writing another workflow script: `es proof capture/check/prove`, `es node finish` (review policy), `es probe run/replay`, `es context`, and `es run handoff`. Record research windows with `es run begin/end` and import available usage with `es usage sync` so comparisons include failed work and setup cost. See `docs/automation-implementation.md` for verified capabilities and remaining gates; the completion-reporting rule above still applies.
- Before writing Python or workflow glue, run `es lib search "<task or algorithm>"`, then `es lib show <id>` for the relevant API, example, and semantic limits. Reuse or extend the shared implementation where its contract fits; if the catalog has no match, search the source before creating another implementation. Keep new mathematical candidates small and separate from execution, budgets, result storage, and reporting.
- At the end of each research run, and before launching the next trial, Astra reviews new or changed ad hoc code under the run's artifact directory, changed tracked scripts, and inline commands recorded in the job journal. Promote useful recurring algorithms to `harness/research/` and generic workflow helpers to `tools/es/es/`; preserve original artifacts, explicit semantics, and behavior with small checked-in regression fixtures. Add or update the library catalog and a runnable example with each promotion. Log what was reused, promoted, or deferred and why. Do not generalize one-off mathematics solely to grow the library. Record review and maintenance usage separately; a Sol-led run does this Astra review after the research window.
