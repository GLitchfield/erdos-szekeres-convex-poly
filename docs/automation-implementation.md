# Harness automation: operating guide and rollout gates

Implemented on branch `harness/automation-20260912`. This is the first usable slice of
the [automation plan](automation-plan-2026-09-12.md), with independently gated search,
delivery and index paths. Wake-up of the current interactive Codex connection is unverified;
retain the existing completion-reporting rule. No cloud prover submission is required.

## Available now

| Area | Behavior |
|---|---|
| Workflows | `operation submit/show/list/resume/retry/cancel/reconcile`; finite stages run through existing guarded jobs. Successful stages survive failure. Submission keys are idempotent. |
| Resources | Atomic admission, shared primary-checkout RAM/build limits, exclusive worktree stages, aged-job reservation, runner identity and heartbeats. Nested checks inherit their stage's cap. Cancellation requests remain distinct from termination acknowledgement. |
| Results | Immutable SHA-256 artifacts, compact CLI/MCP results, paginated `artifact show`; `--full` explicitly requests full CLI output. Compact frontier replies prioritize counts and freshness/problem indicators; `ready` includes its total and up to four short node summaries within the byte budget. Oversized convenience fields remain in the full artifact. MCP does not repeat human tables beside JSON. |
| Completion | Durable outbox/inbox with leases, retries, consumer acknowledgement and pause/resume. `delivery probe` makes no model request. The opt-in Codex proxy adapter checks idle state, sends compact terminal summaries with immutable full-result references, and reconciles lost acknowledgements using event markers. |
| Proofs | `proof capture/check/prove` freezes a byte span and source/dependency identities, compiles a candidate in a networkless `bwrap` namespace, and audits the complete parent in a separate Lean process. Native tactics stop on first acceptance. |
| Finalization | `node finish` validates claim/branch/statement lock, checks the candidate, substitutes only its proof span, checks original source, runs full extraction and audits, and writes a reviewable diff. Publication policy currently supports **review**. |
| Search | `probe run/replay` uses a registered, versioned project plugin. Rank extension, clipping, ordered cover and normalization primitives are shared under `harness/research/`. Finite/abstract witnesses never close or refute Lean nodes. |
| Context | `context NODE --previous BUNDLE` returns changed fields with provenance; `run handoff` generates recorded outcomes and pending decisions. Freshness is explicit. |
| Library discovery | `lib search "TASK"` returns short ranked matches; `lib show ID` gives the API, example, semantics and source. `lib list` gives the available entries. The curated catalog checks source symbols without importing scientific dependencies. |
| Index | `index shadow` merges invalidated records and compares them against a supplied full oracle. It never publishes an index. |
| Measurement | `run begin/pause/resume/end/report/handoff`, `usage import/sync/report/compare`; exact response deduplication, source reconciliation, cached/uncached input, output and reasoning subset, worker resources and tool-result bytes. |

Default operation replies expose `stage`, `stages_done`, and `stages_total` at both
small and compact response sizes. A stage marked running may have a queued job;
use `job status` for execution state. Failed compiler checks include bounded error
headers and UTF-8 byte offsets into their complete diagnostic artifact, including
Lean's tagged `error(...)` messages. Explicit `--full` returns the raw full result.

The command registry exposes these through CLI and MCP. Restart an already-running MCP
server to load new tools. Restart the WSL worker on the updated code before submitting operations. The pilot found
that a worker loaded before the upgrade can admit conflicting jobs and strand their newer
runners in `starting`. Updated workers reserve admission atomically and run controller ticks;
workflow stages also enqueue their own successors. Pilot evidence is in
`runs/automation-pilot-20260912/worker-restart.json`.

Artifact publication rejects read-only database connections before writing files.
When artifact storage is unavailable, compact read commands preserve their full result
and explain why compaction was unavailable. New artifact files and the bounded directory
hierarchy beneath the checkout are synced before a database reference is committed,
including when directories already exist from an interrupted or concurrent writer.

The 2026-09-13 follow-up also tests bounded Sol delegation for harness review,
implementation, result analysis, and Lean candidate generation, with Astra assigning
tasks and verifying results. The user selected `gpt-5.6-sol` at `xhigh` for subsequent
subagents; the initial three inherited `max` and remain labeled that way. This is an
experimental routing preference, not a claim of measured goal-wide savings. Child
usage and coordinator work must both be counted, with model-specific totals preserved.

Extraction computes node opening dates with at most four concurrent read-only Git
queries. It retains the existing rename-following semantics and does not cache dates
across commits. A pilot sample produced identical dates in 5.82 seconds parallel
versus 18.52 seconds serial; that sample is not a full-refresh speedup measurement.

## Proof and search use

Continue selecting/claiming nodes and searching existing theorems under the project rules.
For a registered node:

```bash
es proof capture NODE
es proof check FIXTURE_ID --body runs/my-work/body.txt --memory 4G --minutes 20
es proof prove FIXTURE_ID --memory 4G --minutes 15
es operation show OPERATION_ID
es node finish NODE --body runs/my-work/body.txt --policy review --extract-memory 28G
```

The returned fixture and operation IDs are the inputs to subsequent commands. Supply an
explicit extraction cap when needed based on measured peaks. The primary configured default
is 28G, which fits the shared 30G budget alongside a 2G agent host. The harness reports
`blocked_resource` for requests that cannot fit; a stage override remains inside the shared cap.

Capture automatically recognizes ordinary generated theorem modules. `--start` and `--end`
select exact UTF-8 byte offsets within the parent proof. Local captures are checked by
rebuilding the entire parent; automatic elaborated local-goal discovery and extraction of
arbitrary provider-returned enclosing proofs are not implemented. Ambiguous declarations
or changed source/dependency identities require recapture. The checker mounts compiled
`lib/lean` roots, the selected toolchain and isolated output only. It refuses an unsupported
library layout or missing isolation, rather than falling back to unrestricted elaboration.
Source files, Lake `.olean.hash` markers and package/toolchain pins are frozen; this does
not detect deliberate out-of-band tampering with an olean while preserving its hash marker.
`node finish` additionally rebuilds and checks the original module and full frontier.
Failed candidate checks include bounded compiler-error headers, the candidate file path,
and byte offsets into the preserved diagnostic artifact. Use `artifact show ID --offset N`
for the relevant context. These summaries are diagnostic only; kernel acceptance is unchanged.

Use a spec such as `runs/automation-implementation-20260912/probe-spec.json`:

```bash
es probe run --spec runs/my-work/probe.json --window WINDOW_ID
es probe replay RESULT_ARTIFACT_ID
```

The shipped `context_rank` plugin requires `abstract-rank-strip-v1`, an explicit seed,
case/time/memory bounds, `sorted_intervals`, and `clipped_potential`. Change a small registered
candidate module to explore another potential; process launch, provenance, result storage
and replay remain shared. The recursive compatibility factory requires either
`historical-f2-v1` or `context-bound-zero-children-v1`. Its name is an implementation choice,
not an equivalence theorem. The legacy scripts and their retained outputs remain intact.

## Library reuse and recurring review

Before writing Python or workflow glue, query the catalog:

```bash
es lib search "recursive bounds"
es lib show research.recursive-bounds
es lib search "proof finalization"
```

Search is deterministic and bounded; it does not call a model or import the scientific
modules. Show retrieves the selected contract and example. The catalog lives in
`harness/research/catalog.json`; its schema and maintenance convention are in
`harness/research/README.md`. Source validation catches missing files and renamed
symbols. A missing search hit is a reason to inspect the source, not evidence that no
implementation exists.

The registered `recursive_cut` plugin promotes the recent two-marker cut experiment.
Start with `harness/research/examples/recursive-cut-small.json` and run it through
`es probe run --spec ...`. It names its generator, domain, coupling budgets, case/time
limits and recursion semantics. Install the harness's optional `research` extra in the
worker interpreter for NumPy. Small tracked fixtures exercise recursive zero-child
behavior and shared primitives without requiring old `runs/` directories. Witness
replay recomputes the selected cuts; neither a finite negative nor a replay is a Lean
proof or an equivalence theorem for the evaluator.

At each run's close, Astra reviews newly written ad hoc code. Recurring algorithms
belong in `harness/research/`; generic execution/accounting helpers belong in
`tools/es/es/`. Each promotion includes behavior-preserving tests, an example and a
catalog entry. Record reused/promoted/deferred decisions, preserving old artifacts.
For Sol-led trials, do this review after the research window and count its maintenance
cost separately as well as in all-in accounting. The preflight review for the first
twelve-hour trial is `runs/sol-12h-20260913/REUSE-REVIEW.md`.

### Findings from the first Sol-led run

The September 13 trial stopped at the native account usage limit after 4 hours
25 minutes of its planned twelve-hour window. Ten new Lean nodes passed all
five finalization stages; the original parent obstruction remained open.
See `runs/sol-12h-20260913/REPORT.md` for the receipts and separate cost totals.

The post-run review includes inline job commands and changed tracked scripts,
as well as files under the run directory. The finite probes reused the registered
recursive evaluator. The cache-copy/trace-rebasing command remains an experiment:
it lacks a general source-identity and invalidation contract and is not a shared
cache API.

Guarded command jobs now set their recorded checkout root and memory reservation
for nested commands. Their extraction cap comes from that checkout's config,
not a long-lived worker's inherited `ES_EXTRACT_MEMORY_MAX`. For a deliberate
per-job override, put `env ES_EXTRACT_MEMORY_MAX=SIZE` in the submitted command.
When the configured executable is `lake` and PATH does not resolve it, the harness
uses the executable `~/.elan/bin/lake` shim if present; explicit executables and
PATH entries retain precedence.

Use `es lib show workflow.node-add` for registration requirements: targeted
extraction still needs the configured build reservation (currently 20G), and a
normal full extraction needs 28G. Use `es lib show workflow.jobs` for bounded
execution and receipt handling. Harness Git calls disable automatic background
maintenance. Direct Git job commands must likewise pass `-c gc.auto=0
-c maintenance.auto=false`; otherwise a background child can leave a completed
commit's reservation uncertain. Reconcile the stopped scope instead of replaying
the commit. Restart long-lived workers after deploying harness code updates.

## Measuring future token savings

Start a window before a bounded task and associate operations with the returned ID:

```bash
es run begin "known-proof replay" --cohort replay-v1 --arm baseline --pair-key TASK_AND_SOURCE_HASH
es usage sync --window WINDOW_ID
es run end WINDOW_ID --accepted 1
es usage sync --window WINDOW_ID
es run report --window WINDOW_ID
```

Use the same cohort, task/source key and checked outcome count for its `treatment` window.
Include failed attempts, repairs, reporting and finalization. Record implementation and
maintenance in separate `setup` windows. Set `ES_WINDOW_ID` for instrumented tools; pass
`--window` when submitting operations. `usage sync` uses the local Codex session ID; use
`usage import PATH --window ID` for an archived or different session.

End the window after the last response you intend to count. Telemetry for an active
response can lag; re-import afterward. A successful import reconciles a recorded snapshot,
not future requests. Empty coverage is unknown, not zero. Root sessions are counted;
unproven child-session lineage is not silently added. Claude usage import and account-level
weekly quota accounting are not implemented.

```bash
es usage compare --baseline BASELINE_ID --treatment TREATMENT_ID \
  --setup SETUP_ID --future 10
```

Repeat baseline/treatment flags in matched order for several cases. Comparison refuses
overlapping IDs, incomplete windows, unreconciled sources, mismatched cohorts/source keys,
or unequal/unrecorded outcome counts. Counts are operator supplied: retain the actual check
receipts. It reports mean savings per comparable window, field-wise percentages, the
observed range, projected recurring/net savings, and output-token break-even. Missing setup
usage leaves net savings and break-even unknown; nonpositive recurring savings has no
break-even. An observed range is not a confidence interval. No dollar or weekly-allocation
conversion is inferred. Budgets are **observational**, because this CLI does not control
admission of the next model request.

The current implementation window is `window-9d3361a3407f40bd`; its source, start boundary
and reconciliation checkpoint are in `runs/automation-implementation-20260912/measurement.json`.
It starts at the implementation approval, excludes earlier prover experiments, and ended
at the implementation/reporting boundary (2026-09-12 18:28:18.465 UTC). The later six-hour
pilot has separate windows. Re-import completed windows to include delayed usage.
There is no measured recurring savings percentage yet.

## Completion and recovery

### Bounded Sol research host

The installed Codex App Server can own a durable research goal in a separate session.
The host records its thread, fixed model/effort, prompt artifact, usage window and absolute
deadlines in the run directory.

The native goal has a 4,000-character limit including the host's execution contract;
submission checks this before queuing a session. Keep the prompt compact and refer to
a reviewed instruction file for longer research plans.

Submit it from the intended research checkout:

```bash
es run agent --out runs/sol-trial --prompt /absolute/path/research-prompt.md \
  --model gpt-5.6-sol --effort xhigh --hours 12
es run agent-status runs/sol-trial
es job wait HOST_JOB_ID --timeout 55
```

The host reserves 2 GiB and uses the ordinary `es worker`. Research commands get independent
guarded jobs; a 28 GiB extraction fits beside the host in the project's 30 GiB budget.
Status reads do not call the model. The native goal supplies continuation in the same session;
the host does not create a fresh model turn on each poll. Its state contains lifecycle and
usage metadata, not conversation text or credentials.

Research admission ends at the frozen deadline. If needed, exactly one report/finalization
turn is permitted, with a further 30-minute hard stop. A terminal or failed host is not
evidence of successful research: inspect the report, goal status, check receipts and usage
coverage. Premature completion is recorded as such.

After an interruption, inspect the host job and `agent-run.json`. Once the old host is
confirmed stopped, resume the same run explicitly:

```bash
es run agent --out runs/sol-trial --resume
```

Resume preserves the thread, prompt, model, effort and original deadlines. It refuses a
duplicate live host or an unknown thread-start receipt. A lost final-turn acknowledgement
requires reconciliation; it is not retried automatically. No deadline or usage limit is
silently extended. This separate host does not establish that the current interactive
attachment can receive an unsolicited completion message.

An explicit resume can also recover a provider capacity failure before the original
research deadline. The latest durable turn must have failed with `serverOverloaded`,
and its completion must not precede the goal's latest update. Other blocked goals and
quota failures remain blocked. The host stores the error code and lifecycle metadata,
not the provider message, and records the recovery without changing the thread or deadline.

After a guarded command exits, scope acknowledgement briefly polls systemd for delayed
teardown. A collected transient unit (`LoadState=not-found`) is stopped evidence even
when systemctl returns a nonzero status. An unreachable bus or a scope still active
after the polling deadline preserves the reservation for explicit reconciliation;
external effects are never replayed by that reconciliation.

```bash
es inbox list
es inbox claim --consumer CLIENT_CONNECTION_ID
es inbox ack EVENT_ID --consumer CLIENT_CONNECTION_ID
es inbox pause
es inbox resume
es operation cancel OPERATION_ID
es operation reconcile
es resources reconcile
```

An inbox pause suppresses new deliveries while compute continues. A cancelled observer does
not imply cancellation of a remote provider. Events are delivered at least once; consumers
must deduplicate event IDs and acknowledge after acceptance. Lost turn-start acknowledgement
is reconciled from thread history before another continuation is considered. A missing
receipt is `needs_reconciliation`, not permission to blindly repeat an external effect.

The Codex adapter uses the installed `app-server proxy` protocol. It requires an explicit
enabled agent/thread binding under `[automation.delivery.bindings."AGENT"]`, with `thread`
and `enabled` fields, and a reachable control socket. `es delivery dispatch --thread ID`
performs one dispatch for a configured binding; it preserves the thread's model/effort and
permissions. It does not make an unattached CLI conversation observable or launch another
agent. Continuous host integration and Claude delivery remain gated. The shipped project
configuration leaves delivery disabled. **Do not promise an unsolicited completion message
from the present CLI attachment.**

On 2026-09-13, a job-owned `codex app-server --stdio` test passed real success,
failure, timeout and cancellation delivery. Its ordinary-code monitor made zero model
requests while jobs ran; each terminal event caused one continuation. Transport restart
preserved delivery, and a deliberately lost turn-start acknowledgement reconciled from
history without a duplicate model turn. See
`runs/automation-followup-20260913/delivery-live.json`. This verifies the separate test
session, not wake-up of the current interactive attachment. The latter's proxy control
socket was absent. Continuous host wiring remains an explicit integration gate.

A dead runner retains its reservation as `unknown_execution`. Scope reconciliation releases
capacity only after confirming the cgroup stopped. External effects still need review;
unknown operations are never automatically replayed. Retry known failed stages explicitly.
Successful artifacts and old job receipts remain available. Disabling `[automation] enabled`
stops new admissions; it does not erase in-flight work. SQLite backup precedes the additive
automation migration. There is no destructive schema rollback command.

## Verification and remaining gates

Verified so far:

* The September 9 and 10 archived goal windows reconcile exactly with the earlier profiler:
  1,659,844 / 1,837,176 output tokens, with 1,937 / 1,874 responses respectively.
* A real project proof (`ctx_bound_antitone`) was replayed in isolation, retaining its
  statement hash and only the three configured standard axioms (53.5 seconds).
* An isolated Lean project passed the complete five-stage finalization path; native tactics
  accepted its known proof and a remaining open goal was rejected. This earns no research
  theorem credit. The v2 run completed in 33.5 seconds, peak 2,149 MiB.
* The versioned probe reproduced a retained abstract witness after 456 tested cases and
  independently replayed it. Its semantic outcome is explicitly separate from job success.
* Failure tests cover concurrent admission, rollback, stale runners, nested resource caps,
  cancellation acknowledgement, duplicate delivery, lost client acknowledgements,
  source changes, primitive parity, source deletion/dependency invalidation, and usage errors.

Evidence is under `runs/automation-implementation-20260912/`. See `VALIDATION.md` there for
the latest test count and delayed-job result.

The following gates remain open and are not advertised as deployed optimizations:

* Actual client continuation on active/reconnected Codex or Claude, including a zero-model
  long-wait test through that client. A durable inbox or fake client is not this gate.
* Authorized commit/push/PR publication, elaborated local-goal capture, and remote-provider
  receipt/cancellation adapters. The review workflow and CPU tactic portfolio are available.
* Lean equivalence bridges for shared finite evaluators, broad real-workload parity, and
  authoritative incremental indexing. `index shadow` requires explicit manifests and a full
  oracle; no production index shortcut is enabled.
* A prospective matched evaluation demonstrating lower all-in frontier usage. The estimator
  is ready to collect it; implementation and deterministic tests cannot establish that saving.

Neural and cloud proving remain outside the default route because earlier experiments did
not establish an all-in token advantage. This change submits no new Aristotle project.
