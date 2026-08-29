---
title: Plan the post-Batch-005 rolling grounding wave
type: research
mode: HITL
status: closed
claim: codex-post-batch005-rolling-grounding-2026-08-24
blocked_by: none
---

# Ticket 0081: plan the post-Batch-005 rolling grounding wave

## Question

Which exact successors should occupy the rolling pipeline after Ticket 0080,
given that no current portfolio entry has an executable proof-producing gate
and Batch 005's mathematical first tests are not yet route-ready?

## Decision criteria

Select only gates that authenticate the reconciled current snapshot, change a
route or operational disposition under every terminal, have immutable disjoint
write sets and bounded resources, preserve mechanism-family concentration, and
state the exact later action authorized by success. Record proof-producing and
information-gathering counts, all foreseeable approval needs, exact provider
commands, forecasts, stop conditions, and deferred high-leverage work. Obtain
fresh exact user approval before dispatch.

## Resolution

### Reconciled snapshot and factory staleness check

Ticket 0080 admits all four prior terminals and consumes the Batch-005 reserve
without promoting a seed. Packet 005's snapshot predates the terminal MUTSTAR,
retriever-author, and DRET567 audits. Those later results are operational or
route-feasibility evidence only; none proves, refutes, duplicates, or supplies
a consumer for one of the five seeds. DRET's corrected 1,900-grid count is
relevant to decomposable-pascal cost discipline but does not decide
`FD005-JUMP-PROFILE`. Every proposal is therefore rechecked rather than
silently stale-promoted.

The canonical portfolio currently has zero `advancing` entries. Its 19 main
entries are completed 3, gated 4, merged 2, parked 1, retired 2, and suspended
7. No compiling theorem target is honestly executable from the current
producer boundaries. This wave is therefore an **exploration/grounding wave**:
zero proof-producing gates and six information-gathering gates. It must not be
described as proof advancement.

### Selected rolling work

| Order | Gate | Mechanism family | Boundary and downstream branch |
| --- | --- | --- | --- |
| initial agent | MUTSTAR implementation repair | predecessor-half / `FP-01.D` | close exactly five audited source defects without opening a real row; `READY` permits only a newly frozen non-author audit |
| initial agent | redirect-safe retriever non-author audit | research-system/source grounding | source and hostile-replay audit of exact author bytes; `ACCEPT` permits only URL-specific planning, never a request |
| initial agent | `FD005-HELLY-MAT2` route audit | typed-core matroid decomposition | decide definitions, true 8+8/type-scramble controls, and the one allowed speculative return bridge; `READY` permits only a new first-test packet |
| root initial | DRET567 bounded Fable/Sol route review | decomposable-pascal / `FP-02.C` | decide whether staged prefilter/benchmarking changes mathematical information or merely operational amount; no screen runs |
| first backfill | `FD005-JUMP-PROFILE` route audit | decomposable-pascal / `FP-03` | freeze common lattice, parity, exchange/convolution semantics, exact controls, and one named numerical Pascal consumer or reject |
| second backfill | `FD005-DECK-QUARTET` route audit | deletion-deck normalization / `D-NORMALIZE` | independently disposition the prime-versus-proper-split tension, misidentified nearest controls, positive-control tier, and strict measure; likely mismatch is not assumed |

The initial occupancy is three delegated lanes plus the root-owned provider
review. `JUMP-PROFILE` and then `DECK-QUARTET` backfill the first compatible
freed agent slot after that terminal is admitted. DRET and JUMP are the only two
decomposable-pascal gates, two of six total; no family exceeds half the wave.
The remaining families have distinct primary failure modes. No advancing
high-leverage portfolio entry is deferred because none is presently
executable. Mathematical first tests for HELLY, JUMP, or DECK and the DRET
staged screen are deliberately deferred until their respective review returns
`READY` or `ACCEPT` and a new packet receives separate approval.

### Immutable local packets

1. MUTSTAR repair:
   `runs/agents/20260824-continuous-backfill/ready/mutstar-implementation-repair-v1/task.json`,
   SHA-256
   `f7ca7c167fbf2d2e1155dfb632aac4b19e5a9d1e1c980c429c8ee5f1e9ae52af`;
   75 minutes, 1 CPU, 4 GiB, 0.08 GiB; exactly eight new repair artifacts.
2. Retriever audit:
   `runs/agents/20260824-continuous-backfill/ready/redirect-safe-retriever-audit-v1/task.json`,
   SHA-256
   `77d412e863fd94d562fe058d114e5e7e4291f8ab9771e8e71b3e218e78ed4c39`;
   45 minutes, 1 CPU, 2 GiB, 0.05 GiB; exactly five audit artifacts.
3. HELLY route audit:
   `runs/agents/20260824-continuous-backfill/ready/fd005-helly-mat2-route-audit-v1/task.json`,
   SHA-256
   `6b0c8ac7ad65864b7b66b536eb1268d66b69b21701e062b77bd0a70c95febf31`;
   30 minutes, 1 CPU, 2 GiB, 0.03 GiB; exactly two planning artifacts.
4. JUMP route audit:
   `runs/agents/20260824-continuous-backfill/ready/fd005-jump-profile-route-audit-v1/task.json`,
   SHA-256
   `7e0e2b8e481e02dd7be49b2d3f0d1d138aafd3a9a59dbf02606cb7b45cdd96e3`;
   30 minutes, 1 CPU, 2 GiB, 0.03 GiB; exactly two planning artifacts.
5. DECK route audit:
   `runs/agents/20260824-continuous-backfill/ready/fd005-deck-quartet-route-audit-v1/task.json`,
   SHA-256
   `38e45ee5173931085c0a8369e82821c79a6d3f331efd0f5ff68629855ef36697`;
   30 minutes, 1 CPU, 2 GiB, 0.03 GiB; exactly two planning artifacts.

All five task packets pass `scripts/check_agent_orchestration.py`; all frozen
inputs currently authenticate and all owned output paths are disjoint.

### DRET567 provider review

Question SHA-256:
`b9a75b52534aa6d220cd2b3a166f4c5b64041507f51f057c1a3f01ef2abd770c`.
Approval-plan SHA-256:
`65ffe4f25a6cefc146061c032a1b42be72f835108e3e0f1596cfb9fc2fe98410`.
The 394,455-byte evidence packet binds Ticket 0080, the current portfolio,
Ticket 0002, the admitted DRET audit/interface bundle, the frozen screen task,
and current governance. Claude authentication is live on the Max subscription;
Codex CLI is available. The exact command is:

```text
python3 scripts/adversarial_review.py run --question-file runs/reviews/20260824-dret567-staged-feasibility-route-review/question.md --evidence AGENTS.md --evidence docs/wayfinder/tickets/0080-reconcile-approved-wave-and-batch005.md --evidence docs/wayfinder/frontier-portfolio.md --evidence docs/wayfinder/tickets/0002-test-e3-and-select-repair.md --evidence runs/agents/20260824-continuous-backfill/planning/dret567-screen-route-audit-v3/audit.md --evidence runs/agents/20260824-continuous-backfill/planning/dret567-screen-route-audit-v3/result.json --evidence runs/agents/20260824-continuous-backfill/execution/dret567-interface/report.md --evidence runs/agents/20260824-continuous-backfill/execution/dret567-interface/result.json --evidence runs/agents/20260824-continuous-backfill/ready/dret567-contiguous-screen/task.json --claude-model claude-fable-5 --codex-model gpt-5.6-sol --rounds 1 --timeout 1800 --max-evidence-bytes 500000 --allow-dirty --output runs/reviews/20260824-dret567-staged-feasibility-route-review/run
```

This permits four bounded provider stages—blind Fable, blind Sol, and one
reciprocal critique each—with a 30-minute timeout per stage and a two-hour
absolute provider ceiling. It writes only ignored review receipts and remains
advisory proposal evidence. It authorizes no DRET enumeration or portfolio
change.

### Forecasts and rolling branches

- MUTSTAR repair: 45--75 minutes, uncalibrated repair forecast; the prior
  author closed in 39 active minutes but the independent predicate rewrite is
  new.
- Retriever audit: 20--45 minutes, uncalibrated hostile-audit forecast.
- Each seed route audit: 10--30 minutes, uncalibrated planning forecast.
- DRET Fable/Sol review: 30--120 minutes, uncalibrated; four stages each have a
  30-minute hard timeout and exact-prefix resume only.

At initial occupancy the delegated local aggregate ceiling is 3 CPUs, 8 GiB
RAM, and 0.16 GiB output. Backfill does not increase that concurrency. The DRET
harness uses provider clients and small local receipts rather than a
mathematical compute process.

Each terminal is admitted and reconciled independently before backfill. A
repair/audit `READY` or `ACCEPT` never executes its successor; it permits root
only to freeze that successor and request new approval. `REVISE`, `MISMATCH`,
`STOP`, or a provider disagreement closes or repairs only the stated gate. No
silent theorem-contract change, new premise, route promotion, first test,
source request, real mutation row, or full screen is allowed.

### Consolidated approval inventory

Fresh exact user approval is required for the five task hashes and the frozen
DRET question/approval-plan plus exact command above.

The five local packets require no platform escalation, network, provider,
installation, external solver, Lean/Lake, resource increase, process
termination, destructive action, credential access, canonical edit, git
mutation, commit, or push. The DRET command requires out-of-sandbox provider
execution through the repository-authorized exact prefix
`python3 scripts/adversarial_review.py run`; its platform prefix is already
approved, but this plan still needs user authorization. No source URL or live
retrieval is included.

Conditional later actions are expressly excluded and cannot yet be made exact:
a MUTSTAR non-author audit, URL-specific retrieval plan, DRET staged feasibility
run, HELLY/JUMP/DECK first test, future idea-generator packet, Lean theorem,
commit, and push each require a new freeze and, where applicable, separate user
or platform approval.

## Evidence

Root independently replayed all five task validators, the Wayfinder validator,
the frontier validator, and the ten focused continuous-generator regressions.
`git --git-dir=.git-data --work-tree=. diff --check` passes. The DRET review
harness doctor reports Claude Code 2.1.235 authenticated through `claude.ai`
subscription Max and Codex CLI 0.149.0. No successor packet or provider review
has run at this planning boundary.

## Rolling execution log

The user approved all six frozen gates on 2026-08-24. Root authenticated the
five task-packet hashes, the DRET question and approval-plan hashes, and all
five orchestration validators before dispatch. The approved pre-execution
Ticket-0081 SHA-256 was
`bad70d0a2ac6ab2ca55481321cf0c370ab3b3714f63a4316b7c2f4b286202f8a`.

At `2026-08-24T18:39:14-04:00`, the non-author retriever-audit agent was
stopped by a platform cybersecurity classifier before audit work or owned
outputs were produced. Root admits this only as an operational terminal:

- **Net proof movement:** neutral.
- **Evidence:** operational stop; no audit evidence and no mathematical
  retriever result.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** none; the exact non-author source/hostile-replay
  audit remains unresolved.
- **Counterfactual test:** advance knowledge of the classifier stop would only
  have changed worker allocation, not estimated proof work or retriever
  confidence.
- **Planning consequence:** retain the retriever audit as unresolved and use
  the freed approved rolling slot for the frozen `FD005-JUMP-PROFILE` audit.
- **Load-bearing ledger:** no edge changed.

This operational stop receives no failure genome and is not negative evidence
about the retriever, its author bytes, or its future URL-specific use.

At `2026-08-24T18:44:02-04:00`, root authenticated and admitted the HELLY audit
terminal `FD005-HELLY-MAT2-AUDIT-MISMATCH`. The result-schema validator passes;
the report/result SHA-256 values are respectively
`e482661dd2bb9da7b0dc89933c7ae629ecee372a7cc010a7f1d7dd0645bf8cf8`
and `41b14945ce165661dab218bd1c63e1c1c29a47d070f30761be3da7b7c7a32b39`.
The literal all-pairs incidence/projectability rule forces all 121 columns to
one side, the type-only scramble is invariant under the proposed algebra, the
claimed 8+8 control is actually a different-model artifact while the live
caller is 15+1, and one returned split does not supply the recursive or
numerical `D-DECOMP` producers.

- **Net proof movement:** neutral.
- **Evidence:** independently authenticated proposal-level semantic audit over
  prior admitted checked computation and compiling definitions.
- **Damage scope:** `candidate-local`, limited to exact
  `FD005-HELLY-MAT2`.
- **Difficulty displaced:** none; an independently sourced representation,
  nontrivial projection, lawful controls, geometric return theorem, recursive
  producers, and numerical consumer remain.
- **Counterfactual test:** knowing the mismatch earlier prevents an invalid
  first test but does not reduce destination proof work.
- **Planning consequence:** reject this exact seed and do not schedule a
  descendant; use the released approved slot for `FD005-DECK-QUARTET`.
- **Load-bearing ledger:** no edge changed.

The Batch-005 continuous seed has no originating canonical idea-ledger entry.
Its one required failure genome is therefore anchored below in this owning
decision ticket after the JUMP and DECK snapshot locks were released.

The four-stage DRET provider review completed at
`2026-08-24T22:49:29.148303+00:00`. The harness authenticated the exact frozen
question and all nine evidence inputs; its packet SHA-256 is
`6b033f62ee95908f6ddfd16b5e1b2405a875227f057355511c53c243e6dc44be`.
After reciprocal critique, Fable and Sol both returned the strategic terminal
`DRET-STAGED-REVIEW-REVISE`. The final `REPORT.md` SHA-256 is
`3c45e62ffb3f0f345a76e2c2b6333140ef5f4d2094165239350983f7400049df`
and the manifest SHA-256 is
`e94e331fff0d49db2a9845331808dee6bb14f688692850ba84b7f8a1b1edb731`.

The reviewers agree that the strict Fin12 arbitrary-carrier,
uniform-orientation decomposable subfamily is not decided by the admitted
consecutive-slice UNSAT or the nondecomposable arbitrary-placement witness.
Its complete prefilter can therefore change search information. They also
agree that no current execution packet is eligible: a corrected staged packet
must freeze an outcome-blind conservative projection rule, two
source-independent complete-census implementations with predicate
corruptions, survivor-dependent claim ceilings for `S = 0`, `1 <= S <= 64`,
and `S > 64`, an exhaustive terminal/next-action table, and the already audited
exact semantics. Only that corrected 20-minute staged packet may later be
presented for approval; no exhaustive screen was run or authorized.

- **Net proof movement:** neutral.
- **Evidence:** bounded Fable/Sol advisory proposal review; no mathematical
  computation or theorem.
- **Damage scope:** `operational-only` at this review boundary.
- **Difficulty displaced:** unchanged in
  `DecomposableBalancedGridForcesTarget567`, the collision terminal,
  state-567 integration, and the uniform Pascal transition.
- **Counterfactual test:** the review improves gate design and prevents an
  under-specified run, but does not reduce formal proof work.
- **Planning consequence:** retain `FP-02.C` gated and later freeze the bounded
  amendment; do not execute the old exhaustive packet.
- **Load-bearing ledger:** no edge changed; `D-DECOMP` remains open.

The shared frontier entry remains unedited until the active JUMP and DECK
packets release their authenticated snapshot locks; this exact provider
receipt is the serial-reconciliation source.

Root then authenticated and admitted
`FD005-DECK-QUARTET-ROUTE-AUDIT-MISMATCH`. The result-schema validator passes;
the report/result SHA-256 values are respectively
`efbccaa784b8a1db5f06899b70733763121163944c7d5e6a7e92a778f67dd057`
and `b5aad370a84e01a989cbc61b1088a27239e76f615a8def988c965a6219b8da8d`.
The frozen seed assumes `IsDecompositionPrimeOn chi X`, hence
`not HasProperDeepBelowSplitOn chi X`, while its live reconstructed
full-support edge is required to return exactly
`HasProperDeepBelowSplitOn chi X`. No in-tier positive control can satisfy both.
The full multivalued-deck consensus remains extensionally distinct from the
cited controls, so the damage is confined to this signature rather than to
deletion-deck ideas generally.

- **Net proof movement:** neutral.
- **Evidence:** authenticated proposal-level definitional/interface audit over
  compiling definitions and admitted controls.
- **Damage scope:** `candidate-local`, limited to the exact full-support
  prime-to-full-support-split package.
- **Difficulty displaced:** none; changing to a sub-support, nonprime source,
  or after-mutation split creates a new mechanism and still lacks same-ground
  target-reflecting recombination.
- **Counterfactual test:** the contradiction avoids an impossible first test
  but does not reduce destination proof work.
- **Planning consequence:** reject this exact seed and do not schedule a
  descendant; preserve the multivalued-deck observation only as constrained
  mutation memory.
- **Load-bearing ledger:** no edge changed.

Its one required failure genome is anchored below in this owning decision
ticket; no duplicate idea-ledger or portfolio genome is created.

Root authenticated and admitted `FD005-JUMP-PROFILE-AUDIT-MISMATCH`. The
result-schema validator passes; the report/result SHA-256 values are
respectively
`98fe0aee34b6448cc4c0bd9733bf9a1d49ae1b4a3d5f18e927371ff0bf9c61e1`
and `5775b521be0e667e5e941d662acaf7e93506ef4ca77833ca53fda5a48482c011`.
A common lattice and exact within-tag jump axiom can be stated, but fixed child
embeddings and ordinary Minkowski addition cannot reconstruct consecutive-gap
profiles when child labels interleave; crossing strong polygons need a new
producer. Even granting that producer, an independent ambient-cardinality
theorem is still required to reach the exact `left.card + right.card <= 21`
state-567 consumer.

- **Net proof movement:** neutral.
- **Evidence:** authenticated proposal-level semantic/provenance audit over
  prior compiling and checked controls.
- **Damage scope:** `candidate-local`, limited to the exact gap-rank,
  decomposition-tag, Minkowski-convolution, and jump-to-cardinality package.
- **Difficulty displaced:** none; both the parent crossing-profile theorem and
  the numerical cardinality producer remain, so the consumer ladder has more
  than one speculative transfer.
- **Counterfactual test:** the mismatch prevents a semantically invalid or
  vacuous first test but does not reduce destination proof work.
- **Planning consequence:** reject this exact seed and do not schedule a
  descendant; require a materially new representation/operation and an
  independently grounded numerical theorem.
- **Load-bearing ledger:** no edge changed; `D-DECOMP` remains open.

Root also authenticated and admitted
`MUTSTAR-IMPLEMENTATION-REPAIR-READY`. The result-schema validator passes; its
implementation report/result SHA-256 values are
`aa09d0f5ce110003988ab38976ba5ad31621f4428082acb38ae98b9648eb32cf`
and `cf123c6b78512c888782a2af23f78f11ef52ddc100a3b2c8fa078a9e2bd9079e`.
Both exact 13/13 suites agree, all 40 corruptions fail at their intended
smallest errors, the protected phase-I hash remains
`5c0b81d64277c89a77f5a8f3b3e381378e55673f038356fba95b31229fc3309c`,
and all five real-pair guards stop with every mathematical counter zero.

- **Net proof movement:** neutral.
- **Evidence:** proposal-level source and isolated synthetic implementation.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** none; the real star is unopened and the uniform
  predecessor-half producer for `D-HALF` is unchanged.
- **Counterfactual test:** the repair avoids the prior interface rejection but
  contributes no mathematical fact or smaller proof obligation.
- **Planning consequence:** retain `FP-01.D` gated; only a fresh non-author
  audit over these exact eight hashes may follow.
- **Load-bearing ledger:** no edge changed.

Root then completed the still-approved retriever gate after the delegated
attempt's classifier stop, without changing its immutable task or output
contract. The terminal is `REDIRECT-RETRIEVER-AUDIT-MISMATCH`. The five owned
audit artifacts authenticate with SHA-256 values:

- `audit.md`:
  `a841d16bbec25c123095ade5e06f46971d415eab3a6d0ae688a1a47756f03567`;
- `replay.json`:
  `add0a2e6a33e7cac27df9f75eda10702b7f9880672e97380a20a0df0c929104e`;
- hostile replays A and B:
  `a720abfdc6cc2a4e58943cb355305a000de30a52ca957a836055065071e4eb06`
  and
  `7175f159bd010c4f092b60d586ed04b2443b1870eb8754d9b9446e023e07009c`;
- `result.json`:
  `3d9eec27d9fb7abd1252d50e44cb0e2a8dc0a85915f50e0e82c865278b30b4b6`.

The result-schema validator passes. Two fresh-root hostile replays have the
same stdout SHA-256,
`633c611d77be435ba6fcedaed41b00aa1449a233917d1649af3ce0be3c9afd23`,
from the exact embedded harness SHA-256
`e207fa71eeade41b01ff326772932e85b6a6b1bcd64a6d4c34756f7ba65cb691`.
No actual network, DNS, or TLS activity occurred. A forged caller authority
nevertheless reached the patched production connection hook; the plan
capability is directly constructible and shallowly mutable; legacy numeric
loopback forms and a literal URL space pass; scoped nonordinary transitions
are not mechanically restricted to metadata, first hop, and no onward
redirect; cloned or post-open replaced artifact roots remain accepted; and a
zero-byte mandatory primary body completes. The package's exact transition
matcher, nonempty role barrier, byte limits, common journal checks, and two
independent semantic projections survived.

The mandated author suite was invoked exactly twice. The first invocation
returned but its orchestration capture was lost, so no result is claimed for
it and no third run was made. The second passed `18/18`, with semantic digest
`8c935c8e2999d58e0808fd941a662c4112996f17c39e267a1441ecfb3e3aca10`
and captured-output SHA-256
`74bd2e4150776bb6063b1fe2ddf00489e7f576551b832a353a622b46bbd2fff1`.

- **Net proof movement:** neutral.
- **Evidence:** proposal-level non-author source analysis and two identical
  hostile synthetic replays; no mathematical computation or theorem.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** the source tool now needs a material capability,
  immutable-plan, scoped-transition, nonempty-primary, transport-provenance,
  and stable-root redesign; every live-source and proof obligation remains.
- **Counterfactual test:** knowing the defects earlier prevents an unsafe live
  acquisition plan but does not reduce mathematical proof work.
- **Planning consequence:** reject the exact author package; do not freeze a
  URL-specific plan. A new architecture and new non-author audit must precede
  any request.
- **Load-bearing ledger:** no edge changed.

This implementation mismatch is purely `operational-only`, so it receives no
mathematical failure genome. The earlier classifier stop remains an honest
worker-allocation record but is superseded as the terminal disposition of the
approved audit gate.

### Failure-genome anchors

These are the only full genomes for the three admitted Batch-005 candidate
mismatches. The continuous seed batch created no canonical idea-ledger entry,
and none of the seeds was admitted as an `FP-NN`, so this owning decision ticket
is the required fallback anchor.

#### `FD005-HELLY-MAT2`

- **Stable card/family:** `FD005-HELLY-MAT2` / typed-core matroid
  decomposition.
- **Model tier / scope ceiling:** one fixed-realization 16-label insertion;
  the 8,043-by-121 binary core-incidence representation with the literal
  all-incident-columns-on-one-side projection; one planning package only.
- **Terminal artifact and hash:**
  `runs/agents/20260824-continuous-backfill/planning/fd005-helly-mat2-route-audit-v1/report.md`,
  `e482661dd2bb9da7b0dc89933c7ae629ecee372a7cc010a7f1d7dd0645bf8cf8`.
- **Verified failing feature:** the all-pairs parent-support incidence is
  connected, so the literal projection forces all 121 columns to one side;
  type-only scrambling changes neither the matrix, rank, connectivity, nor
  projectability.
- **Strongest supported statement:** this exact representation has no
  nontrivial projectable split on its frozen caller; no conclusion extends to
  a materially different typed representation or projection.
- **Evidence level:** `proposal`.
- **Damage scope:** `candidate-local`.
- **Representation blindness (`verified`):** retained type metadata never
  enters the algebra or projection predicate.
- **Candidate discriminator (`inferred`):** a successor must make typed data
  algebraically active and prospectively admit a nontrivial same-caller split.
- **Mutation directions (`inferred`):** replace the atomic universe or
  projection with an independently sourced geometric return map and lawful
  same-caller controls.
- **Anti-duplication warning (`verified`):** adding or renaming type tags,
  selecting columns from the known root, or rerunning rank enumeration does
  not change the failing mechanism.
- **Cheapest falsifier (`verified`):** prove nontrivial projectability from the
  support incidence before enumerating a single matroid separation.

#### `FD005-DECK-QUARTET`

- **Stable card/family:** `FD005-DECK-QUARTET` / deletion-deck normalization.
- **Model tier / scope ceiling:** full-support decomposition-prime source,
  complete one-deletion split deck, forced quartets, and a reconstructed
  proper full-support edge; this exact prime-to-split signature only.
- **Terminal artifact and hash:**
  `runs/agents/20260824-continuous-backfill/planning/fd005-deck-quartet-route-audit-v1/report.md`,
  `efbccaa784b8a1db5f06899b70733763121163944c7d5e6a7e92a778f67dd057`.
- **Verified failing feature:** `IsDecompositionPrimeOn chi X` contains
  `not HasProperDeepBelowSplitOn chi X`, while the advertised full-support
  edge returns exactly `HasProperDeepBelowSplitOn chi X`.
- **Strongest supported statement:** the frozen prime/lift conjunction is
  inconsistent; complete multivalued decks, quartet reconstruction, and
  proper-sub-support or after-mutation statements remain untested.
- **Evidence level:** `proposal`.
- **Damage scope:** `candidate-local`.
- **Representation blindness (`verified`):** the signature does not distinguish
  a full-support return, which primality forbids, from a materially different
  sub-support or post-mutation return.
- **Candidate discriminator (`verified`):** any live successor must change the
  input tier or return support explicitly and independently supply same-ground
  normalization/recombination.
- **Mutation directions (`inferred`):** proper-sub-support, nonprime-source,
  and after-mutation versions are new cards requiring new controls and bridges.
- **Anti-duplication warning (`verified`):** silently dropping primality,
  renaming the reconstructed edge, or retaining deck consensus alone cannot
  revive this signature.
- **Cheapest falsifier (`verified`):** reduce the proposed output to
  `HasProperDeepBelowSplitOn` and compare it with the prime premise before any
  deck or quartet enumeration.

#### `FD005-JUMP-PROFILE`

- **Stable card/family:** `FD005-JUMP-PROFILE` / decomposable-pascal project
  profiles.
- **Model tier / scope ceiling:** a fixed finite ordered carrier with a supplied
  decomposition tree, binary gap-rank lattice, address tags, ordinary integer
  Minkowski child convolution, and the lower state-567 two-side subgate only.
- **Terminal artifact and hash:**
  `runs/agents/20260824-continuous-backfill/planning/fd005-jump-profile-route-audit-v1/report.md`,
  `98fe0aee34b6448cc4c0bd9733bf9a1d49ae1b4a3d5f18e927371ff0bf9c61e1`.
- **Verified failing feature:** child gap ranks move under interleaving,
  nonnegative Minkowski addition cannot delete a child-consecutive gap split
  by the other child, crossing polygons occur in neither same-size child
  support, and exchange/convolution do not imply the required ambient
  cardinality bound.
- **Strongest supported statement:** this exact additive representation and
  return package neither reconstructs parent profiles nor produces the
  `<= 21` consumer; jump systems and other nonadditive labelled encodings are
  not refuted.
- **Evidence level:** `proposal`.
- **Damage scope:** `candidate-local`.
- **Representation blindness (`verified`):** rank-indexed child vectors erase
  the partner-dependent interleaving and mixed-polygon information needed at
  the parent.
- **Candidate discriminator (`inferred`):** a successor must prospectively
  reconstruct mixed parent profiles and independently connect support
  structure to ambient multiplicity.
- **Mutation directions (`inferred`):** labelled-endpoint coordinates with a
  nonadditive crossing operation plus a separately grounded counting theorem.
- **Anti-duplication warning (`verified`):** adding tags, calling full
  recomputation a convolution, or storing the `<= 21` conclusion in the
  certificate repeats or circularizes the failed package.
- **Cheapest falsifier (`verified`):** test one fixed child embedding against a
  single interleaving and name the numerical Pascal consumer before support
  enumeration.

## Proof-distance accounting

- **Net proof movement:** neutral for the completed six-gate exploration wave.
- **Evidence:** one checked operational repair, one non-author source/hostile
  replay audit, three authenticated proposal-level semantic route audits, and
  one bounded Fable/Sol proposal review; no new mathematical theorem or
  admitted mathematical computation.
- **Damage scope:** `candidate-local` for the exact HELLY, DECK, and JUMP
  packages; `operational-only` for MUTSTAR, the retriever, and DRET review.
- **Difficulty displaced:** none. `D-HALF`, `D-DECOMP`, `D-UPPER`, and
  `D-NORMALIZE` retain the same hard producers; `D-ASSEMBLE` remains gated.
- **Counterfactual test:** the wave avoids three invalid first tests, an unsafe
  retriever, a deficient mutation implementation, and an under-specified DRET
  screen, but none of those facts reduces the estimated remaining proof work.
- **Planning consequence:** retain `FP-01.D` and `FP-02.C` gated behind newly
  frozen audit/staging packets; require a new retriever architecture; reject
  the three exact Batch-005 candidates without scheduling descendants; select
  the next rolling work only from this reconciled state.
- **Load-bearing ledger:** no edge changed.
