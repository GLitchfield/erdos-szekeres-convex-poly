---
title: Calibrate graph-derived semantic admission for Research Factory v2
type: research
mode: HITL
status: closed
claim: codex-research-factory-v2a-2026-08-18
blocked_by: none
---

# Ticket 0034: calibrate graph-derived semantic admission for Research Factory v2

## Question

Can a bounded, independently implemented semantic-admission instrument derive
research-card defect classes from exact statement structure, the compiling
theorem graph, the load-bearing dependency graph, and frozen negative knowledge
without trusting generator-supplied semantic fields?

This is the mandatory `FP-14.C` v2a canary after ticket 0032 and Research
Factory v1 produced two consecutive information-only question-selection
outcomes.  It is a process experiment, not a mathematical route.  V2b
generation remains closed even on success until this result is reconciled and
a fresh execution slate is approved.

## Frozen semantic contract

The input card language is a restricted typed AST.  A card may contain only:

- exact premise and conclusion expressions;
- references to existing theorem/interface nodes;
- an explicit proposed transformation or missing edge;
- a proposed consumer node; and
- a bounded falsifier sketch.

It may not supply accepted/rejected status, mechanism family, model tier,
producer independence, duplicate status, target-equivalence status, witness
provenance, return-bridge validity, or proof-distance decrease.

Each engine must derive the first applicable class and a replayable certificate
for the following priority order:

1. `KNOWN_COUNTEREXAMPLE`;
2. `TARGET_EQUIVALENT_PREMISE`;
3. `STORED_WITNESS_OR_SELECTOR`;
4. `DELETION_UNDISCRIMINATED`;
5. `MODEL_TIER_SLIPPAGE`;
6. `PRODUCER_GAP`;
7. `UNFALSIFIABLE_RETURN_BRIDGE`;
8. `DUPLICATE_COMPLETED`;
9. `STRATEGICALLY_INERT`;
10. `SEMANTIC_UNRESOLVED`; and
11. `ACCEPTED_LITERAL_CARD`.

`SEMANTIC_UNRESOLVED` fails closed.  It is required whenever the frozen graphs
do not mechanically establish a fact needed for acceptance.  Provider or
agent agreement is never a certificate.

`ACCEPTED_LITERAL_CARD` is an affirmative closed-world certificate, not the
unexplained residue after other rules fail.  Relative to the exact frozen
graph and registry hashes, it must contain replayable negative-search or
positive-path witnesses for every earlier class: no applicable recorded
counterexample; no normalized premise occurrence or exact dependency path to
the target; no binder-flow path from a premise to a conclusion witness; every
load-bearing premise deletion discriminated; type-derived model tiers equal or
joined by an exact transfer path; a compiling producer path for every required
source fact; a named consumer path and independently registered bounded
falsifier; no unifying completed theorem; and a strict decrease in the frozen
unresolved-obligation multiset.  If any obligation cannot be discharged within
the frozen world, the class is `SEMANTIC_UNRESOLVED`.

The certificate must expose concrete evidence rather than Booleans:

- theorem match and binder substitution for duplicates;
- normalized occurrence or exact graph path for target equivalence;
- binder-flow path for stored witnesses or selectors;
- deleted field and changed derivation for deletion discrimination;
- source and consumer type/tier signatures plus any transfer edge;
- compiling producer path or the first missing producer edge;
- exact consumer path and bounded falsifier for a return bridge;
- matched negative-knowledge record and scope substitution; and
- before/after unresolved-obligation multisets for strategic value.

Root freezes a certificate schema and a validator before either engine sees the
held-out corpus.  Invalid certificates are material errors even when the class
label happens to agree.

Generator-authored transformation, missing-edge, consumer, and falsifier text
is a non-evidentiary hint and is stripped from engine inputs.  A return-bridge
certificate may cite only exact graph nodes and a separately frozen falsifier
registry entry.  Normalization is limited to 512 AST nodes per statement,
exact graph searches to 10,000 visited nodes per obligation, and registered
finite falsifiers to 10,000 states; reaching a cap yields
`SEMANTIC_UNRESOLVED` rather than acceptance.

Engine input closure is enumerated in each immutable task packet.  In
particular, engines may read the development cases and labels, held-out
statements, frozen contract/graph/registry files, and their own source.  They
may not read v1 semantic review files, held-out labels or gold certificates,
the sibling engine, provider review internals beyond the accepted contract, or
generator semantic fields.

## Frozen canary design

The canary has exactly 240 cases:

- 80 independently audited accepted historical cards;
- 80 audited non-accepted cards, including all 39 v1 material mismatches; and
- 80 fresh metamorphic corruptions of compiling interfaces.

The corruptions include target insertion, stored-witness insertion,
finite-to-uniform producer replacement, model-tier substitution, completed-
consumer wrapping, deletion-undiscriminated fields, missing return edges,
known-counterexample aliases, and counterfactually inert conclusions.

A deterministic mechanism-family-blocked split assigns 120 development and
120 held-out cases.  Every class occurs in both halves.  Engine authors may
iterate only on development cases.  Held-out statements and labels belong to a
separate curator, labels remain sealed until both engine processes terminate,
and no held-out rerun or post-outcome repair is permitted.

The canary is process evidence only.  Audit labels and certificates may reject
a research card but do not prove or refute its mathematical statement.

The curator owns the family-blocking function.  It derives a key from the
normalized premise/conclusion head symbols, transitive theorem ancestry in the
frozen dependency graph, matched negative-knowledge aliases, parent card, and
corruption template/seed.  No generator family name is an input.  Related
ancestry or corruption descendants remain in one split.  Every gold label must
carry a certificate accepted by the same frozen certificate validator; prose-
only v1 judgments are not admitted as gold.

## Execution slate

This is a deliberately concentrated `FP-14.C` calibration slate with zero
proof-producing and three information-gathering specialist assignments.  The
concentration is justified because the object under test is one admission
instrument; the assignments supply implementation and blindness independence,
not purportedly independent mathematical routes.

1. **Semantic engine A.** Implement graph traversal, theorem matching,
   restricted unification, and binder-flow certificates.  It cannot read
   held-out labels or engine B.
2. **Semantic engine B.** Independently implement rule-specific fact indices
   and certificate construction.  It cannot read held-out labels or engine A.
3. **Canary curator and auditor.** Construct and label the development/held-out
   split, own held-out labels, and inspect neither engine until both sources
   and commands are frozen.

Root owns the AST/certificate schemas, frozen inputs, comparator, execution
manifest, output opening, final reconciliation, and all Wayfinder edits.

Both engine sources receive arbitrary development-set tests before freeze.
After freeze, their held-out commands run once, concurrently, under disjoint
CPU assignments.  Neither output is inspected until both terminate.  The
labels are opened only after both outputs are terminal and their hashes are
recorded.

## Acceptance and stops

`RFV2A-SEMANTIC-CANARY-PASS` requires all of the following on 120 held-out
cases:

- at most 5 percent material error;
- no defect class or mechanism-family stratum above 10 percent material error;
- zero false acceptance of target-equivalent premises, stored witnesses,
  known counterexamples, or completed duplicates;
- at most 5 percent false rejection of accepted controls;
- every emitted certificate passes the independent replay validator; and
- the two engines agree on the first class and decisive certificate evidence.

More than 10 percent overall material error is an unconditional hard stop.  A
result between 5 and 10 percent is still failure.  There is no repair, backfill,
threshold retuning, or held-out rerun.

Canary scoring is exact and treats `SEMANTIC_UNRESOLVED` like every other
class.  A prediction is correct only when it equals the frozen gold class and
its certificate replays.  Predicting `SEMANTIC_UNRESOLVED` for a gold accepted
or defect case is a material error; predicting any other class for a gold
`SEMANTIC_UNRESOLVED` case is likewise a material error.  The canary includes
gold unresolved cases in both halves.  The 5 percent number is only a bounded
regression threshold on this correlated corpus, never a population-error
claim.

Predeclared terminals are:

- `RFV2A-ADVERSARIAL-REJECT`;
- `RFV2A-CANARY-DEFECT`;
- `RFV2A-SEMANTIC-CANARY-PASS`;
- `RFV2A-SEMANTIC-CANARY-FAIL`;
- `RFV2A-CHECKERS-DISAGREE`; and
- `RFV2A-RESOURCE-STOP`.

Any outcome has neutral proof movement.  Failure is the third consecutive
information-only or negative `FP-14.C` outcome and suspends that child absent a
genuinely new positive mechanism.  Pass permits only reconciliation and a
separately approved v2b generation plan.

## Resources and approvals

The uncalibrated forecast is 210--420 wall minutes with a hard seven-hour stop.
Each held-out engine process is capped at 30 minutes, four CPU cores, 8 GiB
address space, and 512 MiB output.  Aggregate held-out execution is capped at
eight CPU cores, 16 GiB address space, and 1 GiB output.  Development tests use
the same per-process caps and have an aggregate limit of 120 active minutes per
engine.  The seven-hour stop covers all activity from ticket freeze through
terminal reconciliation.  A provider rejection maps to
`RFV2A-ADVERSARIAL-REJECT`; invalid, unbalanced, leaking, or non-replayable
canary data maps to `RFV2A-CANARY-DEFECT`; engine process/cap failure maps to
`RFV2A-RESOURCE-STOP`; class or decisive-evidence disagreement maps to
`RFV2A-CHECKERS-DISAGREE`; and a completed agreement that misses any threshold
maps to `RFV2A-SEMANTIC-CANARY-FAIL`.

The approved block authorizes the one exact Sol/Fable provider review, three
specialist assignments, local bounded Python execution, ignored run artifacts,
this ticket, timing records, and final `FP-14.C` reconciliation.  It does not
authorize v2b generation, literature/network research beyond the provider
review, Lean/Lake, solver scale-up, software installation, destructive action,
commit, push, or external repository mutation.

The required review returned `MODIFY`.  Report SHA-256 is
`0d364d691cd891fbea199071750972f022735c6742168885deb27f372a3d341c`.
The affirmative acceptance certificate, unresolved scoring matrix,
non-evidentiary hint stripping, input closure, graph-derived family blocking,
replayable gold certificates, bounded searches, and complete terminal mapping
above are the adopted corrections.  No mathematical scope or v2b authority was
added.

## Decision criteria

Admit implementation only if the fresh Sol/Fable review accepts a contract
whose semantics are reconstructed independently of generator fields.  Admit
v2b planning only after the one-shot held-out canary passes every frozen
threshold.  Do not salvage v1 cards or count a canary pass as proof movement.

## Resolution

`RFV2A-CANARY-DEFECT`.

The fresh Sol/Fable review returned `MODIFY`, and its required contract
corrections were frozen before implementation.  The canary curator then
stopped before any semantic-engine dispatch.  The 205 independently audited
v1 records contain 120 rows previously labeled `ACCEPTED_LITERAL_CARD`, but
their proposed producer statuses are 67 `unresolved`, 46 `unproved`, and 7
`proposed`; none is compiling or known.  Exact lookup against all 7,551 frozen
interface declarations resolves only seven of their stated source nodes and
zero unresolved producer identifiers.  Source-name resolution is merely a
necessary condition, so seven is a generous upper bound before actual path
replay.  The frozen canary requires 80 historical controls satisfying the
affirmative `compiling_producer_path_for_each_required_source_fact`
obligation, leaving a minimum shortfall of 73.

Creating the required positive half would therefore require inventing graph
edges, treating prose audits as certificates, replacing historical controls
with synthetic positives, or weakening the frozen acceptance contract.  All
four are forbidden repairs.  No corpus, split, registry, label, certificate,
held-out artifact, or engine output was created.  The engine-A and engine-B
assignments were skipped because their precondition failed, not because their
implementations were tested.

**Net proof movement:** neutral.  **Evidence:** checked deterministic
corpus/interface accounting plus proposal-level interpretation of the frozen
acceptance obligation.  **Difficulty displaced:** none; `D-HALF`, `D-DECOMP`,
`D-NORMALIZE`, and `D-UPPER` are unchanged.  **Counterfactual:** knowing this
before v2a would avoid the curator and engine allocation, but would not shorten
the mathematical proof.  **Planning consequence:** this is the third
consecutive information-only or negative outcome for typed question
selection, so suspend `FP-14.C`.  Do not repair the v1 corpus or schedule
another factory refinement.  Revival requires a genuinely new positive
mechanism that supplies a sizeable replayably certified affirmative-control
population independently of generated research cards.

## Evidence

- `docs/wayfinder/tickets/0033-research-factory-v1.md`
- `runs/agents/20260818-research-factory-v1/factory-result.json`
- `runs/agents/20260818-research-factory-v1/audit/reconciliation.json`
- `runs/reviews/20260818-research-factory-v2a/sol-fable/REPORT.md`
- `runs/agents/20260818-research-factory-v2a/canary/curate.py`
- `runs/agents/20260818-research-factory-v2a/canary/static-audit.md`
- `runs/agents/20260818-research-factory-v2a/canary/result.json`
- `runs/agents/20260818-research-factory-v2a/slate.json`
- `runs/agents/20260818-research-factory-v2a/result.json`
