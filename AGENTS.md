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
- **Difficulty displaced:** the hard obligation that remains and whether it is
  demonstrably smaller;
- **Counterfactual test:** if the outcome had been known before the run, whether
  the estimated remaining proof work or probability of success would actually
  improve; if not, do not call it proof progress; and
- **Planning consequence:** promote, retain, demote, suspend, or expire.

Negative evidence may justify demotion or retirement, but must not by itself
promote a refined descendant of the same mechanism. After two consecutive
information-only or negative outcomes in one mechanism family, require an
adversarial route review before scheduling another refinement. After three,
suspend that family unless a genuinely new positive theorem or mechanism
appears. Never use `closer`, `advancing`, `breakthrough`, or equivalent language
unless net proof movement is forward and the exact closed dependency is named.

## Architecture-level frontier discipline

The frontier portfolio is inclusive and must not be interpreted as a count of
independent proof routes. Every entry records a stable mechanism family, the
named destination dependency it can close, its scope ceiling, the missing
generalization bridge, and its last forward result. Threads which share the
same unresolved producer or are expected to fail for the same mathematical
reason are correlated even when their files, finite states, certificates, or
agent assignments differ. Evidence streaks and the review/suspension rules
above apply across descendants in the same mechanism family; assigning a new
`FP-NN` identifier does not reset them.

Maintain the load-bearing dependency ledger in `docs/wayfinder/map.md`
separately from the inclusive portfolio. Every portfolio reconciliation must
name the exact ledger edge changed or state that no load-bearing destination
dependency changed. Portfolio entry counts, state counts, code volume, and
completed runs are not substitutes for this ledger.

A portfolio entry may be `advancing` only when it has recent forward proof
movement and its next gate can itself yield a compiling theorem that closes or
strictly reduces a named dependency. Conditional interfaces, surviving finite
controls, computational SAT or UNSAT, certificate compression, and stronger
proposed premises cannot by themselves sustain `advancing`; use `gated`.

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
   run `python3 scripts/check_frontier_portfolio.py` before scheduling more
   work.
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

The evidence-admission part of step 1 is mandatory: agent prose or unchecked
computation must not update the portfolio. Portfolio reconciliation in step 2
is likewise mandatory before choosing the next slate, so new threads and route
expiry affect the next allocation rather than one cycle later.

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
