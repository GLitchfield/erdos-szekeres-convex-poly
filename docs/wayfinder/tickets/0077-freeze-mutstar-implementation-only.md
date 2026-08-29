---
title: Freeze the mutation-star implementation-only author packet
type: research
mode: HITL
status: open
claim: codex-mutstar-implementation-only-freeze-2026-08-23
blocked_by: none
---

# Ticket 0077: freeze the mutation-star implementation-only author packet

## Question

Can the accepted `FP01D-OFFPATH-MUTSTAR-02` semantics be instantiated as a
dependency-free exact-rational producer, genuinely independent checker, fixed
schemas, and complete synthetic corruption suite without exposing any of the
authenticated 286 one-flip outcomes before the implementation is frozen and
non-author reviewed?

## Admission boundary

This ticket selects one honest rolling-pipeline lane from the reconciled
portfolio: `FP-01.D`'s already-vetted implementation-only prerequisite.  It is
`proof-producing: no` and `information-gathering: yes`, but only at the
research-infrastructure level.  It is not a mathematical acquisition and
cannot fill the off-path deconfounder prerequisite.

No other thread is added merely to reach four slots.  Implementation authorship
and its later non-author source audit are dependency-serial: the latter cannot
be hash-frozen until the former's source bytes exist.  The redirect-safe
source retries and any new Factory or portfolio lane have different
prerequisites and are not authorized by this packet.  Rolling-pipeline spare
capacity therefore remains available for separately admitted work, but no
such work is smuggled into this approval.

The innovation check is `skip`: this is mechanical implementation of an
independently accepted frozen semantic contract, not a new invariant, route
selection, or redirect.  The bounded Sol/Fable route gate is likewise not
repeated.

## Decision criteria

- `MUTSTAR-IMPLEMENTATION-PACKET-READY`: the immutable author packet passes
  the canonical validator and independent packet audit; its source ownership,
  synthetic-only command surface, real-pair guard, outcomes, resources, and
  approval inventory are exact enough for a hash-bound user approval.
- `MUTSTAR-IMPLEMENTATION-PACKET-REVISE`: the independent audit finds a
  packet-level omission or ambiguity; preserve the first defect and freeze a
  successor without executing this packet.
- `MUTSTAR-IMPLEMENTATION-PACKET-MISMATCH`: the proposed authorship stage
  changes the accepted semantics or cannot prevent real-outcome leakage;
  return to the implementation architecture rather than dispatching.
- `MUTSTAR-IMPLEMENTATION-PACKET-STOP`: frozen-input drift or the local
  planning/audit envelope prevents an authenticated approval handoff; record
  operational evidence only.

## Resolution

`MUTSTAR-IMPLEMENTATION-READY`; the exact-hash v2 author authority was consumed
successfully. Its mandatory non-author source/synthetic audit remains open
after an authenticated frozen-input-drift stop described below.

The first immutable author packet was correctly stopped at
`MUTSTAR-AUTHOR-PACKET-AUDIT-REVISE`: its ordered corruption inventory omitted
the accepted contract's required missing closed-path cross-reference case
while retaining the forged-reference case.  The audit is proposal-level and
`operational-only`; it opened no mathematical outcome.  V1 remains preserved
at SHA-256
`a25397541d5cc7a6980c687eddb9a49546227b2e26753deaff8d1551a835f1a7`
and must not be dispatched.

The content-addressed v2 successor changes only its task identity/result
binding, adds `missing_path_cross_reference` immediately before
`forged_path_cross_reference` in the now 38-entry inventory, and authenticates
the rejected-v1 audit provenance.  Its fresh non-author audit returned
`MUTSTAR-AUTHOR-V2-PACKET-AUDIT-ACCEPT`.  No implementation source, synthetic
test, real mutation row, matrix, certificate, subset, cut, mask, or predicate
has run.  This resolution permits only the approval request below; the ticket
remains open until the author terminal is admitted.

## Evidence

The packet is bound to:

- the reconciled map SHA-256
  `f45c0abb0244a9cf623ec723d4c5e180ca4ca75294914e637db48c65ec064f54`;
- the reconciled portfolio SHA-256
  `2061e6f61dd7ca42bbac938ee562c6f6d71266a85ecc486ca921a02baff6ff86`;
- the accepted semantic contract SHA-256
  `40f245b48528135eceab40c104ede3e30d9865e0227f01f6185955960a9fbba6`;
- the independent semantic audit SHA-256
  `20a21f6326da2e2c24e8f04282db84239691a18d3f996338fe8bfc0d1b5a4489`;
- the implementation architecture SHA-256
  `ebfff0b5eb2d7f4856d343f1bf41747b2326fcc3310a8d30fce47a118fee678a`;
- the concrete schema/command design SHA-256
  `0b665d5560d0d2caf66ed434f87515de4149984e16b6d7e73fa1fe72e195b000`;
- the closed 99-row path SHA-256
  `78a179bead0c5c0a54f9f1856d347e02780642756419d5919b52aec6284e5185`;
- base revision `e1751075e5632c93a7b406136ed5d93b6fbe919e`; and
- pre-freeze whole-workspace admission fingerprint
  `770bb7274812e74d5411513d46fc19bdf050320e0fd196b72b54f96698a7b3a6`.

The rejected v1 author task is
`runs/agents/20260823-mutstar-implementation-only/ready/author/task.json` at
SHA-256
`a25397541d5cc7a6980c687eddb9a49546227b2e26753deaff8d1551a835f1a7`.
Its non-author packet audit is frozen at
`runs/agents/20260823-mutstar-implementation-only/planning/author-packet-audit/task.json`,
SHA-256
`0a74bb26992df7f430b2f7416e9b8efc8d81ef1a3dbd7f52447f0d0cd2ad2cd2`.
The audit report SHA-256 is
`910d71fb70ae730431be37a0b7850a9c924a353dd8687ffcf5e051013b819b7e`
and its schema-conformant result SHA-256 is
`3136c1c66ed089a01219b97bb8985d85edc28c8a64337cbea90db98969083d3c`.

The approved-for-request v2 author task is
`runs/agents/20260823-mutstar-implementation-only/ready/author-v2/task.json`,
SHA-256
`fcdf0637461736f3f97ce7adc089cc0b9afc6bdfc891b3ca46f49e0ffad8023f`.
Its separately frozen audit task SHA-256 is
`8aad8e9b3b58bce0da32b4aa9fa6954cece20570703ae513df5285c8721eed0a`;
the accepted audit report SHA-256 is
`03951bb0b8bfa4193ce34dd81cc297db3d4ab6f67a2976f84999db10f106dd5b`
and result SHA-256 is
`61f0a260ce4b07e2fd38529ec0a061d1434d9764e29c8b8c0df8a355e757764c`.
V1, v2, both audit tasks, and both task/result pairs pass the canonical
validator.  Neither audit may create or run implementation code.

## Exact implementation contract

The author owns only:

```text
runs/agents/20260823-mutstar-implementation-only/execution/author/schema.md
runs/agents/20260823-mutstar-implementation-only/execution/author/producer.py
runs/agents/20260823-mutstar-implementation-only/execution/author/checker.py
runs/agents/20260823-mutstar-implementation-only/execution/author/corruptions.py
runs/agents/20260823-mutstar-implementation-only/execution/author/finalize.py
runs/agents/20260823-mutstar-implementation-only/execution/author/test_synthetic.py
runs/agents/20260823-mutstar-implementation-only/execution/author/implementation-report.md
runs/agents/20260823-mutstar-implementation-only/execution/author/result.json
```

The implementation uses only Python's standard library.  Its exact phase-I
system is

```text
B x = 1,  B = [A | -A | -I_286],  x = (p,q,s) >= 0,
```

with `fractions.Fraction`, a deterministic least-label pivot rule, a hard
pivot cap, primitive coordinate certificates at objective zero, and primitive
nonnegative Gordan certificates at negative optimum.  The checker never
imports the producer or runs its simplex; it replays only exact certificates
and independently reconstructs all geometry and predicate domains.

`generate` and `classify` are separate command surfaces.  Generation must
close and hash all 286 dispositions before classification can inspect a
predicate.  During this packet, however, both commands carry a fail-closed
guard keyed to the accepted contract and path hashes.  The authenticated pair
must be rejected before target construction, matrix construction, a pivot,
certificate derivation, subset/cut/mask enumeration, or predicate evaluation.
The packet may create no real-run authorization token.

The only executable test command is:

```text
python3 -B -m unittest discover -s runs/agents/20260823-mutstar-implementation-only/execution/author -p test_synthetic.py -v
```

It uses isolated small synthetic matrices, configurations, manifests, and
receipts.  It must cover exact feasible, infeasible, and degenerate phase-I
controls, deterministic replay, resource stop, atomic output, real-pair guard,
and all 38 named rehashed corruptions in the accepted contract, including
separate missing and forged closed-path cross-reference controls.  The only
other command is the canonical task/result validator bound to v2.  No real
mutation feasibility row or strong/affine/decomposition predicate may run.

## Predeclared outcomes

- `MUTSTAR-IMPLEMENTATION-READY`: all sources and schemas exist, isolated
  synthetic/corruption tests pass, replay is deterministic, the real-pair
  guard proves zero mathematical work, and the task/result pair validates.
  This permits only a separately frozen non-author source/synthetic audit.
- `MUTSTAR-IMPLEMENTATION-REVISE`: the source is coherent but misses at least
  one frozen implementation obligation.  Preserve the smallest defects and
  freeze a corrected author packet; do not acquire the star.
- `MUTSTAR-IMPLEMENTATION-MISMATCH`: the accepted contract cannot be
  instantiated as frozen or source independence/outcome isolation fails.
  Return to contract-level review; do not silently change semantics.
- `MUTSTAR-IMPLEMENTATION-RESOURCE-STOP`: frozen-input drift or the exact
  resource envelope prevents completion.  Preserve partial owned artifacts
  without readiness or mathematical claims.

The later non-author source/synthetic audit is a new rolling packet whose
inputs must include the exact implementation hashes.  Even an accepted audit
does not run the star: real 286-row generation/classification remains a third,
separately frozen and approved acquisition packet under the original
30-minute, 2-CPU, 4-GiB, 0.2-GiB ceiling.

## Author terminal and root replay

The approved v2 author returned `MUTSTAR-IMPLEMENTATION-READY`.  The package
contains exactly the eight owned files and no `__pycache__` or ninth artifact.
Its report SHA-256 is
`2de8d9b642686f4a0866e57d2e2104051cd1263a8669f94ea5d3a56b03fd2216`;
its schema-conformant result SHA-256 is
`e4ae0b981488f2f3b64c24112c58844bd84b73d9249c905c7e83d3a55295947b`.
The source hashes are frozen in that report and independently reauthenticated
by root.

The final author suite passed all 11 isolated tests in 5.044 seconds and all
38 ordered corruptions at their intended smallest errors.  It reports one CPU,
27,248 KiB peak RSS, 128,606 packaged bytes, and deterministic phase-I repeat
SHA-256
`5c0b81d64277c89a77f5a8f3b3e381378e55673f038356fba95b31229fc3309c`.
The real contract/path guard exited before all eight mathematical counters,
and the exact v2 task/result validator passed.

Root ran the same authorized unittest twice.  Both replays passed all 11 tests
and reproduced the phase-I repeat hash exactly.  The complete synthetic
corruption artifact hash did not reproduce: the author reported
`19c12f8f7229231eaba8ba5c6b2ba696c84abccef7514c9be04accd6cbde7d23`,
while root's two runs reported
`3610f441a3d25f2734d0922b2fdcb4b436416649ce505aa6f7fcb24679863e1e`
and
`f0208e99eca3847104cc5efc4184497c7ef342f0d7ba94e6bd1dbdbd7d3fa3bf`.
All 38 semantic dispositions still agreed.  Source inspection suggests the raw
variance may be confined to random temporary paths stored in each
`checker_command`, but that inference is not admitted as harmless.  The
non-author audit must compare a canonical semantic projection, decide whether
the raw variance violates the frozen byte-repeat/schema claim, and return
`REVISE` rather than accepting an unresolved discrepancy.

The authenticated author terminal is therefore admitted only as a
proposal-level implementation result awaiting its mandatory non-author audit.
It is not acquisition evidence and changes neither `FP-01.D` nor a
load-bearing edge.

The mandatory non-author audit is now frozen at
`runs/agents/20260823-mutstar-implementation-only/ready/source-synthetic-audit/task.json`,
SHA-256
`365f9a0db0d802c3a50ce534af04ad63d1fa0775cea496d7a8680f1304f555c9`.
It owns only five audit artifacts, has a 50-minute/1-CPU/4-GiB/0.05-GiB
ceiling, and permits two isolated unittests, two isolated corruption replays,
source/projection inspection, and the canonical validator.  Its accept gate
requires line-by-line mathematical source review and an exact disposition of
the raw corruption-receipt variance; it cannot rely on the author's green
tests or edit the source.

The user approved that exact audit packet, but preflight returned
`MUTSTAR-SOURCE-AUDIT-RESOURCE-STOP` before source inspection or execution.
The task and base revision authenticated, as did `21/24` direct inputs, the
exact eight-file author set, and absence of author `__pycache__`. Direct frozen
inputs `AGENTS.md`, `docs/wayfinder/map.md`, and `docs/agents/README.md` had
legitimately changed to SHA-256 values
`d001fd48f768e80b4e7964fd73f1eed9aac4165d8565e6a413304d0b851a650d`,
`8afbe7e77caf2dbd1fc7fa8874a6d6bb075db1fb6bb699f43abc00f1d89dffba`,
and `d022123d0776f7880a88f825268424eefdd47cf5798cffdd8d859eaefb0f9627`.
The stop report, replay receipt, and schema-conformant result have SHA-256
values
`2c97063753b1bb12e223bfc2d6ee2d54e8c5072702479f7d1dd0b6ef0af862f3`,
`cc737569ab003dd2313c2beae7af55e2adadc8067ecafed1e8e34ce8baed3f85`,
and `c88f9dfe3b7d63d0fb103f93827f7aad55197a3b9070911d11703a19d1ae4c83`.
Root replayed the exact task/result validator successfully. The run was
preflight-only, produced `14,225` owned bytes, and finished within the
root-observed five-minute interval; exact CPU and peak RSS were not
instrumented. No unittest, corruption replay, real-pair guard, source audit,
mutation row, or predicate ran. This is an `operational-only` stop with
neutral proof movement and no mathematical failure genome.

The flat current successor is frozen at
`runs/agents/20260824-continuous-backfill/ready/mutstar-source-audit-v3/task.json`,
SHA-256
`aca55e37fa9b08bf51ac65384386ae9e4c6fe63523a60ac6952749ad63a92df4`.
All 26 direct inputs authenticate and the canonical task validator passes.
The user approved that exact successor and it returned
`MUTSTAR-SOURCE-AUDIT-REVISE`.  Root authenticated the task/result pair and
the complete result bundle.  The audit, replay, two direct corruption replays,
and result have SHA-256 values
`7317d918412428abe88067f9b1ac04b865118febe8e57634049b17d32bf5832e`,
`90a2808f5f0a5f3691ed27aca8a75e9d60a47eb1eb42a161fbe9a054d6fb1b01`,
`ee099a26b7b28358474e9435db148776ec73a1a161067ef1dbd3ec211eb28ec5`,
`37539dd17dd6cc8b1b28b706438496bb06343478c70a6d1ce7e97e3deb7790cc`,
and
`754c07d634031706fab46e24e4b9a5c70900bd81db39977bf96db80cb1d70f1e`.

The exact rational phase-I core, sign/gauge convention,
`[A|-A|-I]` standard form, Bland pivots, coordinate/Gordan extraction, replay,
contract guard, and predicate formulas survive the source audit.  Both direct
corruption passes reject all `38/38` mutations at their intended errors.  The
raw corruption variance is confined to temporary paths: its canonical semantic
projection reproduces at SHA-256
`66d6c98655c1a9e2c65734a2a94e01ac6ee053faeaff0da41b5247657e0204`.

Acceptance nevertheless fails on five bounded implementation defects.  The
checker exposes no real `classify` command; the producer hard-codes
`synthetic: true`; the finalizer treats the Markdown contract as JSON and does
not bind every predecessor completely; producer/checker predicate independence
is not established because they copy the same algorithms; and positive affine
artifacts omit the promised 1,287-bit predicate profile.  No real mutation row
or return predicate was opened.  The exact next gate is therefore an immutable
implementation repair followed by a fresh non-author audit.  A real
286-row acquisition remains separately unapproved.

This is proposal-level source/synthetic evidence only. **Net proof movement:**
neutral. **Damage scope:** `operational-only`; no mathematical failure genome
applies. **Difficulty displaced:** none; the off-path control and uniform
`D-HALF` producer remain open. **Counterfactual:** the audit prevents a
malformed real acquisition but would not reduce the remaining proof work.
**Planning consequence:** retain `FP-01.D` as gated, repair the five exact
defects, require another independent audit, and do not open the star or panel.
No load-bearing ledger edge changed.

## Forecast and resources

The author packet has a hard ceiling of 120 wall minutes, 1 CPU core, 4 GiB
RAM, and 0.1 GiB output.  The elapsed forecast is 60--120 minutes and is
uncalibrated: the ledger has no three comparable exact-rational
implementation-only author runs.  It is recorded prospectively as
`2026-08-23-mutstar-implementation-author` in
`docs/agents/time-estimates.csv`. It closed in 39 active wall minutes, below
the 60--120-minute forecast. The non-author source/synthetic audit has a
review-category calibrated 20--50-minute forecast. Its first dispatch stopped
at input authentication and therefore supplies no duration calibration for the
substantive audit.

## Consolidated approval inventory

Already authorized in the present planning step:

- local read-only authentication, hashing, packet construction, validation,
  ticket/time-ledger recording, and two non-author packet audits; and
- no mathematical computation beyond checking task/schema bytes.

The user approved the exact immutable author packet hash
`fcdf0637461736f3f97ce7adc089cc0b9afc6bdfc891b3ca46f49e0ffad8023f`.
That approval covers only the eight owned implementation artifacts, the one
standard-library synthetic unittest command, the canonical task/result
validator, and the 120-minute/1-CPU/4-GiB/0.1-GiB ceilings above.  No platform
escalation prompt is foreseeable.

It does **not** authorize network/provider calls, credential use, software
installation, external LP/SAT/SMT solvers, Lean/Lake, resource increases,
process termination, destructive actions, canonical or Lean edits, external
repository mutation, git commit/push, the real contract/path execution,
opening any of the 286 outcomes, predicate classification, `HALF-HULLALT`, a
non-author source audit, or the later acquisition.  An unforeseen approval
pauses only its dependent branch.

The author authority and the first audit authority are now consumed. A newly
frozen flat successor audit requires its own exact user approval. Its scope
must remain limited to five owned audit artifacts, static source and
mathematical review, two runs of the same isolated unittest, two isolated
corruption replays, canonical semantic-projection comparison, and the task/
result validator under the 50-minute envelope. No platform escalation is
foreseeable. It still excludes all real mutation acquisition, author-source
edits, network/providers, installs, external solvers, Lean/Lake, process
termination, destructive or Git actions, canonical edits, and the later
acquisition packet.

## Proof-distance accounting at freeze

- **Net proof movement:** `neutral`.
- **Evidence:** authenticated proposal-level contract, architecture, rejected
  v1 packet audit, and accepted v2 packet audit; no implementation test or
  mathematical acquisition has run.
- **Damage scope:** `operational-only` for the v1 packet omission; none for the
  accepted v2 planning terminal.  A later packet/resource stop is likewise
  operational unless it independently contradicts the accepted semantics.
- **Difficulty displaced:** none.  The off-path affine-good/decomposition-
  prime/strong-six-free control remains unacquired, the uniform predecessor-
  half producer remains absent, and `D-HALF` is not smaller.
- **Counterfactual test:** an accepted implementation can make the later finite
  gate trustworthy and outcome-blind, but does not reduce proof work or raise
  the destination probability until a separately checked acquisition changes
  route information.
- **Planning consequence:** preserve the stopped packet, freeze one current
  flat successor, dispatch it only after exact approval, and design an
  acquisition packet only if its accepted branch occurs.
- **Frontier portfolio:** unchanged; `FP-01.D` remains gated.
- **Load-bearing ledger:** no edge changed; `D-HALF` remains open.
