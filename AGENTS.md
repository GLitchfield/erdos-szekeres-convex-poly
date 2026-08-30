# Erdős--Szekeres convex-polygon research guidance

This repository is an AI-assisted formal mathematics project initialized from
`open-math-research-template`.

> **Project:** Formal research on the exact Erdős--Szekeres happy-ending
> conjecture.
>
> **Destination:** Prove that the least number of planar points in general
> position forcing `n` points in convex position is `2^(n-2) + 1` for every
> `n ≥ 3`, with a compiling Lean 4 proof. Intermediate progress consists only
> of explicitly stated, compiling Lean theorems that remove a documented
> obstruction or establish a reusable part of that proof.

## Completion and claim discipline

- A mathematical result is complete only when its stated theorem compiles with
  no `sorry`, `admit`, unsafe axiom, or unverified external oracle.
- Prose, experiments, SAT output, and informal arguments may be useful evidence
  but are not completed results. Label them accordingly.
- Distinguish the classical planar conjecture, its exact small cases, asymptotic
  bounds, and stronger or relaxed variants. A variant is in scope only when it
  supplies machinery, an equivalent formulation, an obstruction, or formal
  infrastructure for the exact formula. Implication or equivalence between
  models must itself be proved or precisely cited.
- State all general-position, coordinate-order, orientation, convex-position,
  and degeneracy conventions explicitly. Treat order types and realizable
  planar configurations as different objects until a bridge is proved.

## Skeptical proof-distance accounting

Do not describe all increased understanding as progress toward the destination.
Maintain two separate ledgers:

1. **Proof movement:** whether a compiling theorem closes a named dependency on
   a currently viable path to the destination.
2. **Search information:** whether verified evidence changes which routes should
   receive resources.

For every substantial result, classify net proof movement as `forward`,
`neutral`, or `backward`. A negative result, surviving finite control,
conditional interface without its producer, computational SAT or UNSAT result,
sharper obstruction, or reduction to a narrower question is not proof movement
by itself. It may be valuable search information, but report it separately.

A reduction counts as forward proof movement only when all of the following
hold:

- it strictly decreases a predeclared measure such as the number of open cases,
  hypothesis strength, quantifier complexity, certificate size, or unresolved
  dependency depth;
- it does not merely move the original difficulty into a new premise or
  terminal; and
- it exposes a credible closing mechanism that has not already failed in the
  same form.

Every run summary and affected portfolio reconciliation must state:

- **Net proof movement:** forward, neutral, or backward;
- **Evidence:** compiling theorem, checked computation, proposal, or operational
  stop;
- **Damage scope:** `candidate-local`, `subfamily`, `architecture-level`,
  `mechanism-wide`, or `operational-only`;
- **Difficulty displaced:** the hard obligation that remains and whether it is
  demonstrably smaller;
- **Counterfactual test:** if the outcome had been known before the run, whether
  the estimated remaining proof work or probability of success would actually
  improve; if not, do not call it proof progress; and
- **Planning consequence:** promote, retain, demote, suspend, or expire.

Negative evidence may justify demotion or retirement, but must not by itself
promote a refined descendant of the same mechanism. Charge a failure to the
narrowest scope actually tested:

- `candidate-local` rejects only the frozen statement or construction;
- `subfamily` rejects variants sharing the identified failing premise;
- `architecture-level` rejects a representation, reduction architecture, or
  consumer pattern while leaving materially different mechanisms open;
- `mechanism-wide` requires evidence that covers the credible variants of the
  whole stable mechanism family; and
- `operational-only` records a source, resource, tooling, or protocol stop and
  is not negative mathematical evidence.

Do not roll candidate-local, subfamily, or operational failures into a
mechanism-wide losing streak without an adversarial review establishing the
shared mathematical cause. After two related architecture-level or
mechanism-wide information-only or negative outcomes, require an adversarial
route review before scheduling another descendant. No fixed outcome count
automatically suspends a family: suspension requires an explicit exhaustion
argument for the stated scope, while a genuinely different hypothesis or
mechanism may remain eligible for bounded probing. Never use `closer`,
`advancing`, `breakthrough`, or equivalent language unless net proof movement
is forward and the exact closed dependency is named.

### Failure-genome memory

Every independently admitted mathematical negative, refutation, or model gap
must receive one compact failure genome during reconciliation. Record its
stable card/family, model tier, scope ceiling, terminal artifact and hash; then
record the verified failing feature, strongest supported statement at the
admitted scope, evidence level, and damage scope. Add representation blindness,
candidate discriminator, mutation directions, anti-duplication warning, and
cheapest falsifier only with an individual `verified`, `inferred`, or
`not-established` tag. Evidence level and damage scope must copy the admitted
fields above exactly.

A genome is duplicate-avoidance and mutation-constraint memory, not a new
route, score, or authorization. It cannot revive, promote, or schedule a
descendant; any mutation must separately pass source, novelty, premise,
target-equivalence, model-tier, producer, return-bridge, and immutable-gate
review. Store the full genome in exactly one existing route record: the
originating idea-ledger entry, otherwise the affected `FP-NN` entry, otherwise
the owning decision ticket. Do not create a second tracker or a synthetic
idea/portfolio entry. Purely `operational-only` stops receive no mathematical
genome.

## Exploratory patience and mechanism discovery

Skeptical proof-distance accounting governs claims about progress; it does not
by itself decide whether a difficult mechanism deserves further exploration.
A neutral result may support bounded continuation when it exposes at least one
of the following: reproducible unexplained structure, an exact representation
or decomposition, a stable invariant across genuinely different controls, a
source-backed mechanism not yet tested in the relevant model, or a next test
that discriminates between live mathematical explanations.

Such continuation is `probing`, not `advancing`.  A probing entry must record
the concrete observation being pursued, the live explanations, the cheapest
discriminating gate, an incubation budget or review boundary, and what result
would stop each explanation.  Preserve failed descendants as closed controls
without treating them as a verdict on untested mechanisms at a broader scope.

Larger instances alone, more solver seeds, premise patching, certificate
compression, renaming a failed construction, or repeating the same test with
more resources do not justify probing.  The next gate must vary the mathematical
information, not merely the amount of computation.

## Architecture-level frontier discipline

The frontier portfolio is inclusive and must not be interpreted as a count of
independent proof routes. Every entry records a stable mechanism family, the
named destination dependency it can close, its scope ceiling, the missing
generalization bridge, and its last forward result. Threads which share the
same unresolved producer or are expected to fail for the same mathematical
reason are correlated even when their files, finite states, certificates, or
agent assignments differ. Architecture-level and mechanism-wide evidence, and
only narrower evidence whose shared cause has been established by review,
applies across descendants in the same mechanism family; assigning a new
`FP-NN` identifier does not reset it.

Maintain the load-bearing dependency ledger in `docs/wayfinder/map.md`
separately from the inclusive portfolio. Every portfolio reconciliation must
name the exact ledger edge changed or state that no load-bearing destination
dependency changed. Portfolio entry counts, state counts, code volume, and
completed runs are not substitutes for this ledger.

A portfolio entry may be `advancing` only when it has recent forward proof
movement and its next gate can itself yield a compiling theorem that closes or
strictly reduces a named dependency. Conditional interfaces, surviving finite
controls, computational SAT or UNSAT, certificate compression, and stronger
proposed premises cannot by themselves sustain `advancing`; use `probing` for
bounded mechanism discovery around a concrete unexplained observation, and
`gated` when the route is waiting on a known prerequisite or discriminating
test.

A discovery thread need not already have a direct destination consumer, but it
must fit a short consumer ladder of the form
`structural theorem -> named intermediary bridge -> load-bearing consumer`.
Beyond the proposed structural theorem, at most one arrow in that ladder may be
speculative.  If both the bridge and its connection to the load-bearing
consumer require new mechanisms, classify the work as foundational probing,
give it a small explicit incubation budget, and do not imply near-term proof
movement.

Every finite-case or restricted-class result must state its scope ceiling and
the exact generalization bridge still required. It advances a uniform parent
only when it closes a required base case in an already-defined induction or
proves a parameterized lemma used beyond that instance. A certificate-only
finite closure does not become evidence for a uniform mechanism merely because
it concerns the first open state.

Before promoting a reduction, list the unresolved obligations before and after
the reduction and name the strict measure decrease. If a new premise is
strategically equivalent to the old target, lacks an independent producer, or
restores context discarded by the reduction, classify the result as neutral.

For every execution slate, label each slot `proof-producing` or
`information-gathering` and report the counts. Failure independence is judged
at the mechanism-family level, not by disjoint files or separate workers. By
default no more than half the slots belong to one mechanism family; exceeding
that concentration requires an explicit mathematical justification. A slate
containing only information-gathering gates must be described as exploration,
not as a proof-advancement block.

After an exact SAT or UNSAT gate completes, further certificate engineering is
authorized only when it will either produce a Lean theorem closing a named
dependency or test a frozen semantic-extraction hypothesis. Smaller proofs,
additional solver seeds, deeper cubes, and kernel-replay attempts are
operational improvements rather than mathematical progress by themselves.

## Primary formal system

- Lean 4 with mathlib, pinned by `lean-toolchain` and `lakefile.toml`.
- Project declarations live in the `ErdosSzekeres` namespace.
- `lake build` is the proof gate. `make test` runs both Lean and repository
  workflow checks.
- Prefer reusable definitions and small lemmas over one opaque theorem script.
- External Lean developments are read-only references unless their licenses and
  exact revisions are recorded before reuse.

## Sources and reproducibility

- Prefer original papers, publisher pages, arXiv records, and official source
  repositories. Record DOI/arXiv identifiers and retrieval date.
- The living survey is `docs/literature_review.md`; the source ledger is
  `docs/bibliography.md`. Never call the ledger exhaustive without a documented
  database query and citation-chaining audit.
- Keep papers and third-party code out of the repository by default. If a local
  snapshot is genuinely needed, put provenance and license metadata in
  `data/reference/README.md`.
- Computational searches require bounded Wayfinder criteria, deterministic
  inputs, a compact certificate, and an independent checker. Machine-local
  activity belongs under ignored `runs/`.

## Wayfinder

- The canonical map is `docs/wayfinder/map.md`; the canonical inclusive route
  registry is `docs/wayfinder/frontier-portfolio.md`; decision tickets are
  under `docs/wayfinder/tickets/`.
- Start strategic work by reading the map and frontier portfolio, then run
  `python3 scripts/wayfinder_status.py` and
  `python3 scripts/check_frontier_portfolio.py`.
- Treat portfolio membership and execution scheduling as separate decisions.
  The portfolio retains every thread with a credible contribution path and a
  bounded discriminating gate. A work plan selects a temporary execution slate
  from that registry; slot limits, recent activity, and omission from one slate
  do not promote, demote, or delete a portfolio thread.
- Resolve one consequential ticket per session. Use the repository's bounded
  Sol/Fable review before selecting or changing the main route.
- Launch provider reviews directly with the exact prefix
  `python3 scripts/adversarial_review.py run`. Request out-of-sandbox execution
  for that command; the trusted project rule authorizes this one prefix without
  a repeated prompt after session startup. Do not add a shell wrapper.
- Keep the map, frontier portfolio, README, survey, and Lean statement aligned
  when scope changes.

## Frontier execution cycle

Use this cycle for every substantial multi-thread research block. Do not select
the next slate from stale pre-run priorities.

1. **Close and integrate the previous run.** Wait until every selected thread
   has reached a predeclared outcome, an explicit bounded stop, or a documented
   carry-forward point. Verify its claimed evidence gate, report the outcome
   and limitation for every thread, integrate accepted results serially, and
   record actual time and resource use.
2. **Reconcile the frontier portfolio.** Update each affected `FP-NN` entry in
   place: evidence, state, obstruction, next gate, payoff, expiry/revival rule,
   and any newly surfaced child or main thread. Preserve negative knowledge and
   its admitted failure-genome anchor, then run
   `python3 scripts/check_frontier_portfolio.py` before scheduling more work.
3. **Select a temporary execution slate.** Choose `N` executable threads from
   the updated portfolio according to mathematical leverage, readiness,
   independence, information gain, calibrated cost, available concurrency, and
   focus-expiry history. Record why each was selected and identify any
   advancing high-leverage entry deliberately deferred. Selection never changes
   portfolio membership. Use bounded Sol/Fable review when this selection adds,
   retires, or materially redirects a main route.
4. **Plan the selected threads.** For every selected `FP-NN`, plan as far ahead
   as its dependencies responsibly allow. State the exact theorem or falsifier,
   staged dependencies, predeclared outcome branches, evidence gates, budgets,
   approvals, stop conditions, and the downstream plan implied by each outcome.
   Distinguish calibrated forecasts from uncalibrated ones. Present the complete
   slate to the user and obtain approval before beginning a multi-hour block.
5. **Execute the approved slate.** Freeze task packets, keep write sets
   disjoint, exploit parallel mathematical breadth, serialize builders and
   integration, provide progress updates, and do not silently change a theorem
   contract or outcome label. When the slate reaches its boundary, return to
   step 1.

Ticket 0078 supersedes the old **four-plus-one idea-generation semantics** with
the evidence-first campaign in `docs/agents/research-campaign.md`; it does not
supersede the rolling scheduler or the four-investigation occupancy target.
The coordinator keeps a full hash-frozen reconciled snapshot, generates up to
five compact and materially distinct proposal-level seeds, applies only the
lightweight safety and model-tier screen, and develops a seed through its
cheapest hostile mathematical test as soon as a compatible slot and a
separately approved immutable packet exist. Seed generation and these bounded
pre-admission probes are information-gathering support: they are not portfolio
threads, proof-producing slots, route admission, promotion, revival, or proof
movement. Fewer than five honest seeds is a valid novelty stop; never pad the
batch.

Workers receive only the selected context frozen in their development brief,
while root retains the full snapshot for later duplicate, stale-input, and
route review. Admitted failures become evidence-scoped mutation constraints;
every mutation receives a new immutable identity and no inferred genome field
becomes positive evidence. A claim candidate enters the independent
verification funnel before route admission, serendipitous evidence is an
optional sidecar to the assigned terminal, Lean enters at the gap-shaped mode
declared in the brief, and campaign performance is recorded as an evidence
vector rather than a scalar idea score. The historical
`FACTORY-REFRESH-014-CURRENT-STATE-V3` prompt and task are preserved byte for
byte but are superseded-before-dispatch and may not be run, mutated, deleted,
or given a fabricated result. Any future experimental control requires a new
approved wrapper task, identity, and output path.

Ticket 0083 supersedes Ticket 0079's one-reserve and per-call approval clauses
for the campaign's seed-generation service in
`docs/agents/continuous-idea-generator.md`. One exact standing authorization
may let the daemon rebuild current context, freeze a new immutable packet, and
make another proposal-only Sol call without this chat while all of these bounds
hold: one call at a time; at most six calls per rolling 24 hours; at least 30
minutes between completed calls; 100 calls total; at most ten unreconciled
batches or fifty seeds; and circuit-open after two consecutive provider stops
or two consecutive zero-seed batches. Each call retains the 90-minute, 2-CPU,
4-GiB local RSS, 0.05-GiB output, read-only, no-subagent envelope. An attempted
packet is never retried. The daemon may not run first tests, consume or
reconcile its output, edit canonical files, admit or schedule routes, assign
proof movement, or widen its own authority. Root must authenticate and
reconcile every batch. The receipt binds the daemon, packet builder, campaign
validator, and seed schema; configured limits may be tightened but not
weakened. Immutable versioned authorization files preserve historical packet
receipts, and crash recovery must authenticate boot/start process identity
before following a PID. Any model, code, mode, limit, or authority change
invalidates the active standing receipt and requires a new user decision.

Four remains a capacity target, not a quota: if fewer than four mathematically
distinct gates are executable, run the smaller honest slate. Spare capacity may
be used for approved campaign support, source grounding, card audit, or route
review only when that work has its own decision-changing gate under the current
operating policy; never author support work merely to fill a lane. With four
active-agent slots, the normal full-slate allocation is three delegated lanes
plus one root-owned lane.

### Theorem-first operating rebalance

Ticket 0103 is the current user-approved operating policy. Ticket 0107's first
scheduled review retains it unchanged and records a snapshot-specific empty
execution slate; that empty slate is not route retirement or a standing ban on
new work. The policy temporarily
supersedes automatic spare-capacity campaign backfill and the default
four-packet reserve-floor rule, while preserving the rolling pipeline,
mechanism diversity, evidence admission, and all proof-distance requirements.
Review the policy again after two complete post-Ticket-0107 frontier cycles or
immediately after a load-bearing ledger edge changes; review does not
automatically expire it.

Use these rolling planning weights for discretionary mathematical research
time, excluding mandatory reconciliation, independent verification, guarded
builds, repository tests, and integration:

- **40% `D-HALF` structural work.** Prefer a uniform geometric producer for a
  coherent half-sized predecessor-free support. Use at most one simultaneous
  Fin15 lane, and only from an independently motivated source for the missing
  cross-color or selection law. Do not increase solver time, proof allowance,
  seed count, cube depth, or certificate compression merely to continue Fin15.
- **30% `D-DECOMP` repair.** Seek a boundary-aware invariant or direct injection
  for the uniform decomposable induction. Do not mine proof traces or restore a
  clipped child summary already ruled out by recorded collisions.
- **20% source-grounded mechanism discovery.** Study minimal indecomposable
  structure or another mathematically distinct exact-upper mechanism with a
  short consumer ladder and a cheap hostile test.
- **10% bounded computation and process work.** Use computation only for a
  decision-changing falsifier, semantic verification, or required integration;
  process throughput and larger finite searches are not producer substitutes.

`D-NORMALIZE` receives no ordinary execution allocation while its current
mutation-descent family is suspended. It may revive only through the positive
source-side producer or genuinely new monotone mechanism required by `FP-04`.
Adjacent lemmas are demand-driven: an existing named consumer and the short
consumer-ladder rule must identify the missing lemma before a builder is
allocated.

Before freezing any proof-producing theorem packet or intermediary-lemma
packet, record a human-readable **theorem-entry memo** with all five fields:

1. the exact producer theorem, model tier, and hypotheses;
2. the existing named downstream consumer;
3. the strict difficulty separation or predeclared measure decrease;
4. the smallest plausible counterexample or hostile neighboring world; and
5. the geometric, combinatorial, or source-authenticated fact expected to
   produce the theorem.

If a field is missing, the item remains route design. It may receive at most
one separately approved cheap falsifier when that test can change allocation;
it may not receive a Lean builder, certificate-engineering packet, or
`proof-producing` label.

Before freezing a computation or solver packet whose conclusion depends on a
fixture, corpus, role label, or serialized mathematical object, require a
separate **semantic-readiness receipt**. An implementation independent of the
primary outcome engine at the role-critical boundary must reconstruct the
object from raw frozen inputs, recompute every gate-critical predicate
(including general position, target-free or strong-free status, model
membership, and positive/negative control behavior), and normalize tuple/list,
index, order, sign, and label conventions. Hash, schema, and provenance checks
remain necessary but are not semantic readiness. Any disagreement stops before
outcome-bearing work and grants no repair, substitution, retry, or successor.

When no portfolio entry is `advancing` and no theorem-ready producer passes the
memo, prefer a smaller route-design or source-grounding block. Do not default to
an exploration slate or automatic campaign support. The honest approved reserve
may contain zero to three packets; an exploration-only slate still needs a new
explicit user approval and decision-changing gates.

The scheduler remains intentionally paused/stopped and the continuous idea
generator remains failed/stopped. Neither may be repaired, reconfigured,
reauthorized, or restarted merely to occupy capacity. A future restart requires
a fresh diagnosis and report, a theorem-first workload satisfying Ticket 0103,
a valid current implementation and receipt, and a new explicit user decision.
Historical receipts grant no current execution authority.

The evidence-admission part of step 1 is mandatory: agent prose or unchecked
computation must not update the portfolio. Portfolio reconciliation in step 2
is likewise mandatory before choosing the next slate, so new threads and route
expiry affect the next allocation rather than one cycle later.

### Rolling-pipeline override

As of Ticket 0067, the user has replaced the synchronized batch-start barrier
with a rolling research pipeline. This subsection supersedes any requirement
to wait for every lane, to delay campaign support until an entire slate ends,
or to possess four ready lanes before any execution:

- once one portfolio thread has an approved immutable plan, dispatch it as soon
  as a compatible slot is free; do not wait for a four-thread batch;
- independently admit and reconcile each terminal result before using the freed
  slot, while unrelated frozen lanes continue against their own input hashes;
- target four concurrent mathematical investigations, but use spare capacity
  for idea generation, source grounding, card audit, and route review whenever
  fewer than four honest execution gates exist;
- campaign seed generation and approved bounded development may run from a
  hash-frozen reconciled snapshot; every proposal or evidence receipt must be
  rebased against results integrated after that snapshot before admission,
  seed generation never counts as mathematical proof work, and pre-admission
  development never fills a proof-producing portfolio slot;
- plan and approve threads individually or as a rolling wave. A named approval
  covers only its frozen packets; any thread expected to exceed two hours or
  requiring new external authority still needs the approval inventory required
  below; and
- preserve the no-padding, evidence-admission, mechanism-correlation, root-only
  integration, and proof-distance rules unchanged.

Thus four is an occupancy target, not a start gate or reconciliation barrier.
Fast lanes may finish, reconcile, and be backfilled while longer lanes remain
active.

## Multi-agent orchestration

- The canonical role manifest and execution protocol are
  `docs/agents/manifest.toml` and `docs/agents/README.md`.
- Keep durable persona profiles separate from immutable task packets. Every
  delegated assignment must freeze its objective, inputs, ownership, budget,
  evidence gate, success condition, and stop conditions before dispatch.
- The top-level orchestrator owns integration files and serializes shared-file
  edits, project builds, repository tests, commits, and Wayfinder changes.
  Specialists are read-only unless a task packet grants exact, non-overlapping
  write paths.
- Treat agent output as an untrusted proposal. Record the precise evidence
  level; consensus, prose, and computation do not become Lean proofs through
  review or repetition.
- Store transient task packets, transcripts, and results under ignored
  `runs/agents/`. Promote durable conclusions into existing Wayfinder tickets,
  experiments, source documents, or Lean theorems rather than creating a
  second strategic tracker.
- Use bounded Sol/Fable review for route selection or route changes. Ordinary
  implementation of a vetted frozen theorem contract does not require another
  strategic review.

## Multi-hour plan approvals

- Before presenting any plan expected to take two hours or more, inventory all
  reasonably foreseeable actions that need user or platform approval. Include
  external provider or network calls, out-of-sandbox commands, software
  installation, resource-limit increases, process termination, destructive
  operations, and external repository or review mutations.
- Resolve exact commands, targets, resource ceilings, and reusable approval
  prefixes before requesting approval whenever the plan already determines
  them. Present one consolidated approval request with the plan, distinguishing
  actions already authorized, actions needing new approval, and conditional
  actions that cannot yet be made exact.
- Plan approval does not bypass a platform approval prompt. Trigger every
  foreseeable prompt at the beginning of the approved work block rather than
  waiting until the dependent item is reached.
- If an unanticipated approval becomes necessary later, pause only the
  dependent branch, continue any safe independent work, and ask for the narrow
  additional authority. Never broaden the approved mathematical or operational
  scope merely to avoid another prompt.

## Git discipline

- Preserve user work and unrelated changes. Stage only intended files.
- Run `make test` before each commit, then push when a remote is configured.
- This managed checkout mounts `.git` read-only. Local metadata is in ignored
  `.git-data`; use `git --git-dir=.git-data ...`. The GitHub repository and
  normal clones use standard Git metadata.

## Current resource policy

- No unbounded searches. Default exploratory computation limit: 30 minutes,
  8 CPU cores, 16 GiB RAM, and 5 GiB under `runs/`, unless a ticket declares a
  different bound.
- Neighboring repositories, the template repository, published formalizations,
  and provider services are read-only references.
- The project source is MIT-licensed. Third-party papers and code retain their
  own licenses.
