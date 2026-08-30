# Evidence-first research campaign

This document is the canonical discovery protocol adopted by Ticket 0078. It
replaces the publication-card-first semantics of the recurring one-turn
Research Factory while preserving the rolling pipeline and every mathematical
evidence boundary in `AGENTS.md`.

The campaign optimizes the conversion of a small mathematical seed into
checked evidence. It does not optimize the number, length, novelty language,
or apparent completeness of generated ideas.

## Supersession and preserved invariants

The following older requirements are superseded:

- downstream development workers need not ingest the whole-project context,
  complete prior registry, or complete Lean declaration index;
- the first generation stage emits five brief seeds rather than five
  publication-grade research cards;
- a seed need not already contain a source-complete transfer, full consumer
  ladder, immutable experiment, four outcome branches, or Lean landing;
- idea generation, mathematical development, route admission, and
  formalization are separate stages; and
- the frozen `FACTORY-REFRESH-014-CURRENT-STATE-V3` packet is a historical
  control and is not dispatchable unchanged.

The following invariants remain mandatory:

- the Wayfinder map and frontier portfolio remain the only strategic trackers;
- root alone admits evidence, edits canonical strategy, and assigns damage
  scope;
- every delegated task has an immutable task packet and explicit authority;
- model tiers, realizability bridges, target equivalence, and conclusion
  erasure remain literal obligations;
- computation, sources, prose, and model agreement retain their actual
  evidence levels;
- failure genomes retain one canonical home and their admitted scope;
- no failed descendant is automatically promoted through mutation;
- four is an occupancy target, never a padding quota; and
- no seed enters the portfolio or an execution slate without the existing
  route decision and any required Sol/Fable review.

## Campaign topology

The root orchestrator and default context-rich seed pass hold the authenticated
project snapshot, full route history, complete failure memory, and admission
rules. Build that snapshot with

```text
python3 scripts/build_sol_idea_packet.py --output-dir runs/agents/<campaign>/coordinator-snapshot
```

and bind the seed batch to the resulting `packet-summary.json`, whose receipts
commit the manifest, inline context, Lean declaration index, and prior-idea
registry. Rebuild it after reconciliation rather than incrementally editing an
old packet. A development worker receives only the selected seed, immutable
brief, and small explicit input closure. The full coordinator snapshot is
provenance, not downstream worker context. A `representation_escape` seed pass
is the deliberate exception: it receives only the exact target and selected
verified results so the existing route vocabulary does not constrain its
representation.

With four active-agent slots, the normal discovery allocation is three
delegated investigations plus one root-owned investigation. Root may spend its
slot integrating or verifying when evidence warrants it. A terminal lane is
reconciled and backfilled independently under the rolling-pipeline rules.
At most one delegated builder may perform mutating Lean, solver, or finite-model
work at a time; other lanes provide mathematical breadth without overlapping
high-memory builders.

A pre-admission development brief is bounded information-gathering, not a
portfolio thread, proof-producing slot, route admission, promotion, revival, or
proof movement. This is the narrow exception to the ordinary rule that
mathematical execution slates are selected from admitted `FP-NN` entries. It
still requires an immutable packet and exact user approval. "Immediate" means
the next approved compatible free slot after screening; it grants no provider,
network, tool, or mathematical execution authority by itself.

### Ticket 0103 theorem-first selection override

Ticket 0103 suspends automatic campaign backfill while the reconciled portfolio
has no `advancing` entry and no theorem-ready producer passes the theorem-entry
memo in `AGENTS.md`. An idle lane is not a reason to generate, develop, or
repair a seed. Select a pre-admission development only when its cheapest hostile
test can change mathematical allocation and the future user approves its exact
packet. Otherwise use a smaller route-design or source-grounding block and
leave the lane empty.

The rolling discretionary research weights are 40% `D-HALF` structural work,
30% `D-DECOMP` repair, 20% source-grounded distinct mechanism discovery, and
10% bounded computation/process work. They are planning weights rather than
seed quotas. Campaign activity belongs to the final two categories unless a
later admitted theorem card places it under a load-bearing parent.

The scheduler and continuous idea generator remain stopped under Ticket 0103.
This protocol documents their allowable behavior if separately reauthorized;
it supplies no present restart authority. Diagnosis, a theorem-first workload,
a valid current implementation and receipt, and a new explicit user decision
are all required before either service can restart.

The campaign has six stages.

### 1. Generate five brief seeds

Request up to five seeds as a breadth target. If fewer than five honest seeds survive
the generator's literal duplicate and target-equivalence screen, return a
novelty stop rather than padding.

Record whether the pass is `context_rich`, `representation_escape`,
`failure_dual`, or `recombination`. This is provenance for later evidence-vector
comparison, not a score or a promise that every campaign uses every mode.

Each seed states only:

- one precise mathematical question;
- its representation, operation, model tier, and the information it preserves
  or forgets;
- a tentative mechanism-family hint and destination/intermediary hint;
- zero, one, or two parents and the genuinely new operation;
- the nearest admitted negative references;
- one first falsifier executable in at most thirty minutes; and
- at most one closest primary-source lead, if already known.

A seed is proposal-level search information. It deliberately omits a full
route audit, detailed source receipt, final consumer proof, immutable long-run
gate, and Lean declaration.

At least one generation mode in a broad campaign should be a
`representation_escape`: it receives the exact target and selected verified
results but not the complete route taxonomy. This protects higher-dimensional,
algebraic, topological, dual, projection, and counterexample ideas from being
prematurely expressed in the current portfolio vocabulary. Root performs the
full duplicate and model-tier comparison afterward.

The machine-readable contract is
`docs/agents/schemas/research-seed-batch.schema.json`.

The optional chat-independent implementation of this stage is
`docs/agents/continuous-idea-generator.md`. Under Ticket 0083 it may
self-refill an immutable proposal inbox within one exact standing authorization:
one call at a time, bounded rolling and total call counts, bounded unreconciled
batches/seeds, a minimum cooldown, and explicit provider/zero-seed circuit
breakers. Daemon persistence does not grant retry of an attempted packet,
development, reconciliation, route admission, scheduling, proof movement, or
canonical write authority.

Ticket 0103 currently holds this optional service stopped. Do not invoke it to
restore seed count, queue depth, or occupancy.

### 2. Apply only the seed safety screen

Before mathematical work, reject a seed only when it is malformed, a literal
duplicate, target-equivalent, based on a stored conclusion witness, outside its
declared model tier, unfalsifiable within its first budget, or operationally
unauthorized. Do not reject a seed because it lacks publication-grade sources,
a completed return bridge, a Lean landing, or persuasive prose.

This screen does not rank seeds or admit routes. Readiness, family correlation,
and available slots determine temporary campaign selection; portfolio
membership remains unchanged.

### 3. Develop immediately under selective context

Every selected seed receives an immutable development brief plus the ordinary
agent task packet. The task packet is authoritative for ownership, tools,
network/provider access, resources, and external actions; a development brief
can never expand that authority.

Before freezing that execution packet, apply two additional readiness gates
when relevant:

- a proof-producing or intermediary-lemma target must have the five-field
  theorem-entry memo required by `AGENTS.md`; without it the work remains route
  design and cannot receive a Lean builder or proof-producing label; and
- any finite fixture, corpus, role label, or serialized mathematical object
  controlling gate precedence must have a separate semantic-readiness receipt.
  An independent reconstruction must recompute every role-critical predicate
  from raw frozen inputs and normalize representation boundaries before the
  outcome engine is frozen.

Schema, hash, and selected-context validation do not replace semantic
readiness. A readiness mismatch is an input stop with no automatic repair,
substitution, retry, packet mutation, or descendant authority.

A version-one brief contains at most five selected research artifacts and
2,000,000 bytes. A larger closure requires a new reviewed schema version plus a
new immutable approved packet; editing only the brief cannot waive the cap. A
`representation_escape` brief may not contain a whole-project context dump,
the complete prior-idea registry, or the complete Lean declaration index.

Every brief includes:

- the frozen question and model tier;
- selected input hashes and the nearest relevant failure-memory references;
- at least one hostile control or known-false neighboring world;
- the first falsifier and concrete mathematical tasks;
- tools expressly allowed by its task packet;
- a checkpoint within the first ten tool calls;
- a first-falsifier deadline no later than thirty minutes;
- output artifacts and evidence gates;
- one Lean timing mode; and
- the persistence-neutral instruction below.

The worker may research literature, derive mathematics, write small programs,
run experiments, or use Lean only when those actions are explicitly authorized
by the task packet. The same worker may cycle through conjecture, computation,
refutation, and revision inside its bounded brief. It must not silently change
the target, model tier, evidence label, or authority.

The assigned probe has exactly one primary terminal:

- `GATE_POSITIVE_SIGNAL`: the assigned falsifier produced its predeclared live
  signal;
- `GATE_FALSIFIER`: the assigned falsifier killed the frozen mechanism at its
  supported scope;
- `NO_DISCRIMINATING_SIGNAL`: neither live nor kill signal occurred; or
- `OPERATIONAL_STOP`: source, authority, resource, or tooling prevented the
  mathematical test.

A claim candidate or serendipitous scoped result is an optional sidecar to that
primary terminal, never a replacement terminal. The sidecar freezes its exact
statement and evidence but does not authorize a pivot.

The machine-readable contract is
`docs/agents/schemas/research-development-brief.schema.json`.

### 4. Mutate evidence, not prose

After root independently admits a mathematical negative, its existing failure
genome remains the canonical memory. Within that same existing record, the
reconciliation may additionally identify:

- an unexpected invariant or structure that survived;
- a dual, reversal, quotient, lift, projection, or recombination suggested by
  the evidence;
- reusable exact artifacts; and
- one cheapest mathematically different mutation test.

Every such field keeps its individual `verified`, `inferred`, or
`not-established` tag. This generative residue is not a route, score, positive
result, or scheduling authorization. A mutation needs a fresh seed, a changed
mathematical-information audit, and the ordinary route and packet gates. More
instances, more seeds, larger bounds, premise patching, or a renamed failed
construction are not mutations.

The campaign's evolutionary fitness is a vector of checked outcomes, never a
single model-generated score. Useful coordinates include decisive
falsification, a reproducible invariant, a surviving hostile control, an exact
new representation, a source-authenticated bridge, and a compiling
load-bearing theorem.

### 5. Pivot capacity into the verification funnel

When a result sidecar contains a credible theorem or construction claim, root
authenticates and freezes the exact claim before follow-up. Available
capacity then favors validation over additional generation:

1. one hostile referee receives the claim, its proof or construction, and the
   hostile controls;
2. one cold re-deriver receives only the exact statement, definitions, and
   approved sources;
3. one source/novelty audit verifies every imported theorem and the claimed
   research position; and
4. after survival, the smallest load-bearing formal or independent-checker
   hinge is attempted.

These roles may be filled rolling rather than simultaneously when capacity or
dependencies require. Agreement among model instances is correlated review,
not proof. A claim advances only through its separately declared evidence
gate. A refuted claim is reconciled at the narrowest supported damage scope.

A serendipitous result never rewrites the original packet. Its report must give
the literal statement, model tier, scope ceiling, evidence, relation to the
assigned seed, and first hostile test. Root may then reject it, preserve it as
search information, or freeze a new packet; the worker cannot promote it.

### 6. Admit and formalize only after evidence

Only after development and validation does root construct a full route card,
source receipt, consumer ladder, immutable main gate, and proof-distance
account. That card is rebased against all results admitted since the seed
snapshot and then passes the existing portfolio decision.

Lean timing is chosen from the actual gap shape:

- `not_yet`: broad mechanism discovery with no semantically audited isolated
  theorem; use exact examples, computation, and informal derivation first;
- `fixed_statement_in_loop`: one immutable theorem is surrounded by existing formal
  infrastructure, has a human-audited model correspondence, and feeds an
  already-compiling consumer without a target-equivalent premise; use Lean
  goals and diagnostics during search; or
- `post_survival_only`: an informal argument or construction must first survive
  its experiment and hostile checks before a separately frozen Lean packet; or
- `post_discovery_certificate`: a complete informal argument or construction has survived hostile
  validation; formalize the smallest load-bearing hinge or complete certificate
  afterward.

Compiling a true but inert local statement is not evidence that Lean entered at
the right time. Lean acceptance proves the encoded declaration, not the
semantic fidelity of its definitions or novelty.

## Persistence-neutral instruction

Every development brief carries this exact instruction once:

> The frozen target and conventions may not be weakened or replaced. Seek a
> proof, exact counterexample, strongest scoped obstruction, or explicitly
> inconclusive terminal. Continue only while an undepleted predeclared
> discriminating test remains within budget. Negative, empty, and inconclusive
> terminals are acceptable. Effort, prior belief, worker agreement, and failure
> to find a counterexample are not evidence. Do not infer that the requested
> conclusion is true or smuggle it into a premise.

Do not add desired-outcome encouragement such as instructions to believe that
a proof exists. Persistence is licensed by remaining discriminating tests, not
by optimism.

## Checkpoints and crash recovery

Substantive work belongs in the worker's owned artifacts. The first checkpoint
must occur within ten tool calls and record the authenticated inputs, current
hypotheses, tests already run, smallest live obstruction, and next test. Later
checkpoints should make an interrupted worker resumable from disk under the
same immutable packet. Root consumes compact terminal reports and selected
artifacts rather than importing a worker's entire conversation.

## Campaign metrics

Record these measurements when the runtime exposes them; use `null` rather
than estimates when it does not:

- active and elapsed wall time;
- input and output tokens and provider cost;
- tool calls, source requests, and experiment/checker runs;
- seeds generated, selected, attempted, duplicated, and target-equivalent;
- first-falsifier outcome and terminal distribution;
- reproducible structures, decisive falsifiers, and claim candidates;
- claims killed before Lean, claims surviving cold derivation, and Lean rework;
- evidence artifacts admitted at each claim level; and
- load-bearing dependencies strictly reduced by compiling results.

Raw idea count, prose length, agent agreement, portfolio-entry count, and token
burn are not success metrics. Compare prompt length, selective-context size,
and model effort only through prospective A/B pilots with identical targets and
independent scoring.

## Factory v3 historical control

The packet
`runs/agents/20260824-continuous-backfill/ready/factory-refresh-v3/task.json`
and its prompt remain immutable historical evidence. They may run only as an
input to a new, separately frozen and approved experimental-control wrapper
with a new task identity, isolated outputs, and an explicit historical-control
claim ceiling. The old task itself is superseded before dispatch: do not run,
mutate, delete, or fabricate a terminal for it. It is not a live seed generator,
reserve packet, or scheduler. No provider call is authorized merely by adopting
this protocol.

## Required local validation

Run:

```text
python3 scripts/check_research_campaign.py --templates
python3 -m unittest scripts.test_check_research_campaign
python3 scripts/check_agent_orchestration.py
python3 scripts/check_frontier_portfolio.py
```

An actual campaign must additionally validate each seed batch and development
brief, with its matching task packet, before dispatch.
