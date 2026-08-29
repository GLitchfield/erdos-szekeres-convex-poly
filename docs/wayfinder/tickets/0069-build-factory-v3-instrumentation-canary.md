---
title: Build the Factory v3 instrumentation canary
type: research
mode: HITL
status: closed
claim: codex-factory-v3-instrumentation-canary-2026-08-22
blocked_by: none
---

# Ticket 0069: build the Factory v3 instrumentation canary

## Question

Can the proposed Batch013 context-policy and triage-policy pilot be given a
deterministic, independently checked instrumentation layer before any further
provider call, so that sparse-memory boundaries, raw-candidate pairing,
blinding, timing, aggregation, and rejected-text privacy are executable rather
than prose promises?

## Decision criteria

- `V3-CANARY-READY`: one valid synthetic fixture passes; six independently
  frozen corruptions for fork drift, duplicate/refill IDs, allocation
  imbalance, invalid timing, public-text leakage, and private-path context
  inclusion fail for their intended reason; and a seventh auditor-disagreement
  control passes only as an exact unresolved outcome contributing zero novelty.
- `V3-CANARY-SCHEMA-GAP`: the ten-call staged dependency graph, exact 40-raw to
  80-evaluation fork, or dual-auditor aggregation cannot be represented and
  checked without ambiguous fields.
- `V3-CANARY-PRIVACY-GAP`: rejected candidate prose cannot be withheld from
  public, canonical, and future factory-packet surfaces under an exact checked
  basename/path policy.
- `V3-CANARY-CONTEXT-GAP`: a deterministic genomes-only divergence packet
  cannot include the canonical state and every admitted tagged failure genome
  while excluding the prior registry, idea-ledger prose outside those genomes,
  prior factory ideas, and private pilot artifacts.
- `V3-CANARY-OPERATIONAL-STOP`: implementation, fixture generation, or the
  bounded local test gate cannot finish without unplanned authority or scope.

Canary success authorizes only a later execution plan. It does not authorize a
provider call, generate a mathematical idea, change a factory recipe, admit a
route, or move a proof dependency.

## Resolution

Build and test the instrumentation canary before freezing the full pilot. The
original one-completion-per-cell proposal is not executed: independent review
identified candidate pseudoreplication and an invalid comparison between
different raw ideas under the two triage policies.

The corrected future pilot has four fresh raw-generation calls—two under the
full-registry context policy and two under the genomes-only context policy—with
ten unique raw seeds per call. Each of the 40 raw byte strings is frozen before
annotation and is evaluated byte-identically under both free sequencing and
pre-source skeleton triage, yielding 80 paired evaluations. Four future
evaluators are balanced so each receives five candidates from each raw call;
two fresh arm-blind auditors independently judge the same opaque bundle, and
disagreements remain unresolved. The canary must encode and test that graph
without making any of those calls.

The memory factor is a comparison between two complete context policies, not a
causal claim about memory alone. Context length, composition, and provider
stochasticity remain part of the policy effect. The four raw calls and four
evaluator calls are clustered replicate units; neither the 40 candidates nor
80 evaluations may be reported as independent provider trials.

Private means withheld from agent messages, public outputs, canonical files,
and future packet manifests. It does not claim OS-level secrecy from the root
or other processes sharing the workspace. Private artifacts use nonselected
basenames under the ignored run tree; every ordinary `result.json` remains
aggregate-only. A deterministic checker must also inspect a future full-packet
manifest, because basename convention alone is not the privacy gate.

## Evidence

- Ticket 0068 closes on `FACTORY-NOVELTY-STOP` with zero exposed ideas and
  SHA-256
  `40159eac382fbdc1854c4dae524b92e3c1cc5a42ccfaa5f02d45d4899cfa7bd7`;
- the admitted Batch012 process-memory report and result have SHA-256 values
  `4c358908ebe36061d34d383c3f6959a95beb5b24b2fa25a20bf82ceae34aa3b7`
  and
  `210b6e7be000150b3a3dac294aa2f75ee39d89967c77db8cd24f8f5ce71251f9`;
- independent read-only harness audit finds no existing sparse-context
  projector, pilot-DAG checker, blinded convergence assembler, or telemetry
  validator; `scripts/adversarial_review.py` is a route-review harness and is
  not reused; and
- independent design counteraudit requires identical raw bytes across triage
  arms, clustered replication, two-stage arm-blind auditing, invalid-timer
  stops, and a synthetic canary before provider execution.

## Exact canary implementation

One delegated builder may edit only:

- `scripts/build_factory_v3_context.py`;
- `scripts/check_factory_v3_pilot.py`;
- `scripts/test_build_factory_v3_context.py`; and
- `scripts/test_check_factory_v3_pilot.py`.

Root alone owns this ticket, ignored fixture generation under
`runs/agents/20260822-factory-v3-instrumentation-canary/`, repository-wide
validation, and later Wayfinder reconciliation. No Lean or shared mathematical
source is edited.

### Context projection contract

The context builder must provide a deterministic genomes-only mode with an
explicit allowlist, entry hashes, byte counts, and aggregate hash. Its
generation-visible substrate includes the current destination/dependency state,
README, map, frontier portfolio, Lean declaration index, literature review,
bibliography, model/proof-distance rules, Batch012 aggregate baseline, and one
complete extract of every admitted tagged failure genome from its authorized
durable home.

It excludes the 1,128-entry prior registry, prior factory `ideas.md`, the
living idea ledger except for the extracted genome blocks, raw review/provider
transcripts, and every private Batch013 subtree. Malformed, duplicate, or
partial genome extraction is a hard mismatch. The existing
`scripts/build_sol_idea_packet.py` remains the full-memory builder; reducing its
inline-byte limit is explicitly not a genomes-only projection.

### Pilot checker contract

The checker must validate one frozen design manifest and staged task/result
artifacts for:

- four raw calls, exactly ten unique opaque raw IDs per call, no duplicate,
  refill, or adaptive replacement;
- two raw calls per context policy and one common non-memory prompt contract;
- exactly 40 frozen raw texts and 80 triage evaluations;
- identical raw path and SHA-256 input for each free/skeleton pair;
- four evaluator blocks, with each block receiving exactly five IDs from each
  raw call and corresponding free/skeleton blocks receiving the same IDs;
- disjoint write sets and aggregate-only standard `result.json` files;
- opaque arm-neutral bundles for two independent full-memory auditors;
- unresolved treatment of any auditor disagreement;
- integer positive, candidate-local, nonoverlapping source intervals contained
  inside their evaluator boundary, with no skeleton source event preceding its
  skeleton freeze;
- recomputation of all public counts and threshold numerators/denominators from
  private adjudication plus a held-back mapping;
- absence from public output of raw text, rejected titles, family labels,
  source titles/URLs, candidate IDs, and private reasoning; and
- absence of every private pilot path from a future factory context manifest.

### Synthetic corruption matrix

The ignored fixture must include one valid aggregate and separate immutable
corruptions that:

1. change only one evaluation's declared raw SHA while leaving the canonical
   raw bytes unchanged;
2. duplicate/refill one raw ID;
3. change a required `5+5+5+5` evaluator allocation to `4+6+5+5`;
4. force the two auditors to disagree on one candidate and verify that it
   becomes unresolved and cannot contribute to novelty counts;
5. insert one positive-duration source interval overlapping its predecessor
   (negative duration remains a separate unit control);
6. copy a unique 12--16-token private sentinel into public output; and
7. insert one private path into a synthetic future packet manifest.

The exact primary oracle is `V3_CANARY_VALID` for the valid fixture;
`V3E_FORK_RAW_MISMATCH`, `V3E_RAW_ID_DUPLICATE_OR_REFILL`,
`V3E_EVALUATOR_ALLOCATION_IMBALANCE`, `V3E_SOURCE_INTERVAL_OVERLAP`,
`V3E_PUBLIC_PRIVATE_TEXT_LEAK`, and
`V3E_PRIVATE_PATH_IN_FUTURE_MANIFEST` for the six failing corruptions; and
exit-zero `V3U_AUDITOR_DISAGREEMENT` for the disagreement control. The latter
must increment `unresolved_count`, make the disputed candidate
`novelty_eligible=false`, and remove its otherwise unique counted family
signature. Retaining the pre-disagreement aggregate must fail with
`V3E_AGGREGATE_MISMATCH`.

The valid fixture must deterministically reproduce
`U_full=10`, `U_sparse=14`, `D_full=8`, `D_sparse=10`, defective source-active
seconds `(free,skeleton)=(400,280)` under full memory and `(400,300)` under
sparse memory, eleven full-card identities per memory policy under each triage
policy, and zero unresolved items. Thus its public process inputs include
memory deltas `(+4,+2)` and skeleton time ratio `580/800 = 0.725`, with both
predeclared process signals true. The aggregate-only fixture must reproduce
every exposed total and threshold numerator/denominator without access to
rejected prose.

## Future-pilot dependency and resource consequence

This ticket does not launch the pilot. If the canary passes, the later plan
must freeze three staged slates because downstream hashes do not exist at raw
launch: four raw generators, four paired evaluators, then two independent
auditors. With three delegated slots and full barriers, the provider critical
path is five call waves. At 30 minutes per substantive call the honest
post-admission ceiling is 180 minutes after adding deterministic aggregation
and public-output validation; 120 minutes is not retained. The later plan must
inventory all ten max-effort Sol calls, read-only primary-source access, exact
resource caps, conditional named-agent interruption, and packet/output audits
for consolidated user approval.

## Execution packet

| stream | class | owner | ceiling | write set |
| --- | --- | --- | --- | --- |
| instrumentation builder | process implementation | one delegated builder | 45 min, 1 CPU, 2 GiB, 0.05 GiB | the four named `scripts/` files only |
| adversarial specification | read-only process audit | two independent reviewers | 20 min each | none |
| fixture, tests, integration | root-owned process validation | root | 45 min, 2 CPU, 4 GiB, 0.10 GiB | this ticket and the exact ignored canary directory |

Slate count: zero proof-producing and zero information-gathering mathematical
threads. This is operational research-system validation, not a proof block.
The critical-path forecast is 60--90 minutes and uncalibrated; the hard wall is
120 minutes. No external provider/network call, software installation,
resource increase, destructive operation, process termination, external
repository mutation, commit, push, issue/PR action, publication, GUI, Lean,
Lake, SAT/SMT, or solver execution is planned.

## Proof-distance accounting at launch

- **Net proof movement:** neutral.
- **Evidence:** admitted proposal-level process audit and frozen synthetic
  corruption contracts; no canary result yet.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** none. The open mathematical producers remain
  unchanged; even a passing canary only removes ambiguity from a later process
  experiment.
- **Counterfactual test:** a passing canary can prevent invalid provider spend
  and false process conclusions but cannot reduce destination proof work.
- **Planning consequence:** implement only the deterministic scaffolding and
  synthetic fixture, admit its result, then either freeze a separately approved
  ten-call pilot or stop on the exact canary gap.
- **Load-bearing ledger:** no edge changed.

## Closeout

The ticket closes on `V3-CANARY-READY` at the deterministic synthetic
instrumentation scope.  No provider call was made.

The admitted genomes-only projection contains exactly eight canonical
substrate entries and eight admitted failure-genome extracts.  Its entry
aggregate, manifest, visible context, and packet-summary SHA-256 values are
respectively
`4574b083fa82bf43c742deb8a9db0c17d3a678c0f3cce4d0246f689863dc53be`,
`d301966cc6607fcc9d4f6f94fa466145568be43da9b8c9694f737d4878d670e7`,
`f4da2547cb900d9a2ea993d5f656b54c54fb086c40c9c3610cd683bd4cf050cb`,
and
`d961b325db4af4ef9577258b89c8ff5a188b95250436a01f9e82be6c21140bc2`.
The final builder and its sixteen-test module have SHA-256 values
`8b5eba89b6a31b8a36d75dacf85bf2bf81488af4206e7f3dcd0fdd1c2f8b01e3`
and
`556df4404e598b459106676c2540650481d6644984a0f3d23462b30abb39a8a0`.
Independent final context admission reauthenticated every frozen input,
replayed the real packet byte-for-byte, and rejected all 39 handed-off
structural-block controls plus the six formerly accepted empty-list and
no-space block-quote forms.  Its task, report, and normalized result SHA-256
values are
`b18cf640ff91be923e2baf3c6d8824e99be966eb004324637f8f60460e6c1ab5`,
`d6c1b841e6b181d291963e258ed6ae68e6cc9e57147b36f0543df44d4d5961c7`,
and
`c52a5705afcaf241b0d129df2909b690ce0e6008b36bf4d4c31bb77b9dbea501`.
The bounded parser intentionally does not semantically classify ordinary
two-space wrapped prose after its durable source and extract hashes have been
reauthorized; those hashes, exact anchors, and frozen task fingerprint remain
the governance boundary.  This is not a general Markdown parser claim.

The admitted pilot checker and its twenty-three-test module have SHA-256
values
`a033fd753ca2ce4537711a61c58c234246f32719b21a2b9e24970b7904494c4b`
and
`064799a2d5da5a3c40a9565e3501f69361df6ec29df20c95031f8d406adbc2a0`.
The durable suite oracle has SHA-256
`d2e603c58857c444bd9e3fd631a85ccf83e6fb6fb68ea67af642b189c6a88d14`.
Independent final checker audit returned
`V3-CHECKER-FINAL-AUDIT-ADMIT`: the valid fixture and auditor-disagreement
fixture reproduce their complete aggregates, while fork drift,
duplicate/refill, `4+6+5+5` allocation, timing overlap, public sentinel, and
private-manifest corruptions return their exact codes.  The checker also
rejects every previously reproduced stage-input, all-40 projection, arm-label,
recursive-leak, path-alias, cross-candidate-time, duplicate-JSON, and reused
invocation control without echoing protected values.  Its report and
normalized result SHA-256 values are
`f6426bbb98dad880cd2a0e48f059a8f785175d0c0d6336f61cdd7bbc89e89c0f`
and
`e9a17215041b71c56b7d70bfa7fe287319e4c46e5806cf2811ec72f26f314adf`.

The audit history is retained rather than overwritten.  Early versions
accepted surplus stage inputs, complete raw-call exposure, protected-text and
future-manifest leaks, overlapping timing, reused synthetic provenance,
duplicate JSON, and adjacent Markdown block forms.  Each admitted false accept
received an exact regression before the final independent admissions.  These
were `operational-only` validator gaps, so they create no mathematical failure
genome.

The conditional pilot-plan audit at report SHA-256
`ab18b5a32ff9af538fa582f415f00ea1f2468c9b3835b66be74ac79790d02abb`
is planning evidence only.  Before any live experiment, a separately approved
plan must still provide authentic platform receipts, enforced exact input
isolation, trusted source-event timing, a sealed skeleton-before-source event,
dual-auditor agreement on every counted semantic field, fresh post-closeout
context manifests, a clean ignored runtime root, exact resource caps, and all
provider/network approvals.  Synthetic invocation JSON does not establish any
of those live facts.

The final repository gate passed end to end after the last grammar repair:
Lake built 10,314 jobs, all 166 discovered Python tests passed, and every
deterministic replay and canonical validator in `make test` completed.

## Final proof-distance accounting

- **Net proof movement:** `neutral`.
- **Evidence:** checked deterministic process computation, byte-identical
  context replay, exact corruption controls, and independent checker/context
  admissions; no mathematical theorem or candidate was inspected.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** no Erdős--Szekeres obligation is smaller.  The
  canary removes known instrumentation ambiguity; live provenance, isolation,
  telemetry, semantic adjudication, and every mathematical producer remain.
- **Counterfactual test:** the admitted checks would have prevented invalid
  comparisons, leakage, and wasted provider calls, but do not improve the
  estimated remaining proof work or success probability of a load-bearing
  route.
- **Planning consequence:** retain the synthetic canary bytes; rebuild all
  live contexts after this canonical reconciliation; do not launch anything
  until the telemetry preflight and a separate exact approval are obtained.
- **Failure genome:** none, because all negative evidence here is
  `operational-only`.
- **Frontier portfolio:** no entry changes.
- **Load-bearing ledger:** no node or edge changes; `D-UPPER`, `D-HALF`,
  `D-DECOMP`, `D-NORMALIZE`, and the gated `D-ASSEMBLE` boundary remain as
  before.
