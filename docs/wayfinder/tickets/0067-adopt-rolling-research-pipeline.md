---
title: Adopt and launch the rolling research pipeline
type: research
mode: HITL
status: closed
claim: codex-rolling-research-pipeline-2026-08-22
blocked_by: none
---

# Ticket 0067: adopt and launch the rolling research pipeline

## Question

How should the project stop wasting concurrency on synchronized four-lane
batch barriers and instead execute each admitted thread while continuously
generating, grounding, and reviewing replacements?

## Decision criteria

The pipeline must keep exact task contracts, disjoint ownership, independent
evidence gates, narrow damage scopes, and serialized integration. It must not
wait for four ready lanes, but it also must not fill occupancy with an inert,
correlated, expired, operational, or unreviewed card. A factory proposal is not
a research lane until route admission. Each result must be reconciled against
the current portfolio before its slot is reused.

## Resolution

User directive: adopt the rolling pipeline and begin with the three admitted
threads immediately while discovery continues. The historical four-lane hard
start gate in Tickets 0065--0066 is superseded for scheduling, not erased as a
record of those decisions.

The first rolling wave is:

| stream | entry | class | owner | ceiling | write set |
| --- | --- | --- | --- | --- | --- |
| WIN11 | `FP-17` | proof-producing | Lean Kernel Engineer | 120 min, 2 CPU, 4 GiB | `ErdosSzekeres/SynchronizedFiveFanFin11WindowTransport.lean` |
| LCOUNT | `FP-18` | information-gathering | Research Lead Investigator | 30 min, 1 CPU, 2 GiB | `runs/experiments/20260822-lcount-fin13/**` |
| BETA2 | `FP-19` | information-gathering | root | 30 min, 2 CPU, 4 GiB | `runs/agents/20260822-rolling-pipeline/beta2/**` |
| discovery | none | proposal generation | Research Question Generator / Sol | 120 min, 1 provider lane | `runs/agents/20260822-sol-idea-loop/batch-011/{ideas.md,result.json}` |

The factory is concurrency-support work, not a fourth mathematical lane. Root
uses the remaining local stream for BETA2 while the three delegated agents own
WIN11, LCOUNT, and Batch 011. As soon as LCOUNT or BETA2 terminates, root admits
and reconciles it and may use the freed capacity to ground the strongest
reviewable candidate without interrupting WIN11.

An independently admitted mathematical negative or model gap receives its
compact tagged failure genome during the same serial reconciliation before the
slot is reused. Purely operational stops are excluded, and unrelated frozen
lanes continue. A genome constrains duplicate generation; no inferred mutation
is itself a backfill candidate.

The exact WIN11 and LCOUNT contracts remain those in Ticket 0065. BETA2 remains
the exact transform/cone card admitted in Ticket 0066: three transform controls,
then `(9,5)` and `(17,6)` rational cones with exact primal/Farkas replay and no
post-outcome repair. Batch 011 receives the whole post-Ticket-0066 corpus and
must emit exactly five nonduplicate ideas or the declared novelty/provider
stop.

## Evidence

- validated 19-entry frontier portfolio and Ticket 0066 reconciliation;
- unchanged WIN11 and LCOUNT mathematical input hashes from Ticket 0065;
- independently audited BETA2 grounding and reciprocal Fable/Sol admission;
- the user's explicit instruction to plan and execute ready threads while
  discovery continues; and
- post-Ticket-0066 Sol packet aggregate SHA-256 to be frozen in the Batch-011
  task packet after this process record is included.

## Approval and mutation inventory

The user's directive authorizes this named rolling wave. WIN11 and the factory
have 120-minute ceilings; LCOUNT and BETA2 have 30-minute ceilings. No task may
silently extend past its ceiling. Workspace writes are confined to the table's
paths. Local task timeouts may terminate only named child processes.

The factory may use primary-source web research through the delegated Sol
agent. No software installation, resource-limit increase, destructive action,
GUI, commit, push, issue/PR action, publication, or external repository
mutation is planned. Project-wide Lean builds, repository tests, Wayfinder
edits, and integration remain root-serialized. Any new authority or task over
two hours pauses only that stream for a narrow approval request.

## Outcome contract

- `ROLLING-THREAD-LAND`: independently admit a thread terminal, reconcile its
  entry, and refill the slot from the current reviewed queue.
- `ROLLING-THREAD-STOP`: preserve the exact bounded stop and refill only after
  its narrow damage scope and, for mathematical negatives, failure-genome
  anchor are reconciled. The next factory snapshot receives that anchor; no
  inferred mutation becomes a backfill candidate without route review.
- `ROLLING-DISCOVERY-READY`: validate Batch 011, route-review credible cards,
  and ground the strongest candidate in the next free compatible slot.
- `ROLLING-PIPELINE-OPERATIONAL-STOP`: preserve active task checkpoints and
  stop only the affected stream; do not collapse unrelated work into one batch
  failure.

## First rolling-wave outcome

- **WIN11 / `FP-17`:** the exact public arbitrary-window theorem and reusable
  image/restriction equivalence compile. Root replayed 4,236 target jobs and an
  independent audit admitted the compositional standard-axiom boundary. The
  one-shot card is completed. A successor audit then returned
  `COMPAT-PREMISE-EQUIVALENT`: a six-point local support satisfies the ambient
  half inequality only for `n <= 12`; bare coherence has no growth or
  cross-window freeness, while sufficient strengthened interfaces restore the
  target witness.
- **LCOUNT / `FP-18`:** two exact reconstructions agree on 114 strong-five
  masks and `m2=3280>630` on the frozen 13-point control. The candidate is
  retired locally; no retuning or second instance is authorized.
- **BETA2 / `FP-19`:** all transform controls pass, but the first `(9,5)`
  cardinality-only cone has an exactly replayed rational primal. The subfamily
  is retired and `(17,6)` remains unopened.
- **Backfill grounding:** the canonical Pappus frame stops at an unforced first
  bracket sign; the deterministic one-layer Helly core projection is connected
  on all 16 vertices. Pappus remains a candidate-local model gap; the Helly
  card expires at candidate-local scope.
- **Batch011:** Sol returned `FACTORY-NOVELTY-STOP` with two survivors and three
  closed controls. Independent rebase retains rooted bowtie convexity and
  one-interior wedge charging only as ledger proposals. Source audit corrects
  both cards; the wedge divider is ill-defined, and independent gate inventory
  finds neither proposal dispatch-ready. The completed bounded Fable/Sol route
  review and root adjudication return exactly `NO-BATCH011-ROUTE-READY`: both
  survivors remain ledger-only, all three closures are upheld, and no
  Batch011 execution slot is recommended.
- **Operational repair:** four mutable process documents were removed from the
  Fin11 semantic generator's live mathematical hash gate while their historical
  hashes remain in generated provenance. All 165 generated Lean files are
  byte-identical; the 10,314-job Lean build, all 127 Python tests, and the full
  repository gate pass.

The wave launched one proof-producing and two information-gathering
mathematical slots, then used free capacity for two independent grounding
controls, three Batch011 audits, failure-genome process admission, and route-
review preparation. These later tasks are information/process work and do not
inflate the original slate's proof-producing count.

## First-wave proof-distance reconciliation

- **Net proof movement:** neutral. The FP-17 contract compiles, but the audited
  remaining global-support obligation has no demonstrably smaller credible
  closing mechanism; no load-bearing edge changed.
- **Evidence:** one compiling theorem with independently admitted trust
  boundary; four checked computations/model-interface terminals; authenticated
  primary-source evidence; and proposal-level route/readiness audits.
- **Damage scope:** `subfamily` for obvious WIN11 selector/gluing descendants
  and cardinality-only beta cones; `candidate-local` for LCOUNT, Pappus, Helly,
  and the malformed Batch011 gates; `operational-only` for the repaired fixture.
- **Difficulty displaced:** none at the destination level. `D-HALF` still needs
  ambient growth, cross-window freeness, and an all-`k` producer; `D-UPPER`
  still needs a uniform exact mechanism.
- **Counterfactual test:** the exact theorem removes its literal implementation
  and the negative results prevent repeated work, but knowing the successor
  audit beforehand would not reduce the estimated remaining destination proof.
- **Planning consequence:** complete `FP-17`, retire `FP-18` and `FP-19`, store
  the admitted failure genomes, retain the two Batch011 survivors ledger-only,
  uphold the three closures, and dispatch no Batch011 descendant. Rebuild the
  whole-project factory from the reconciled state.
- **Load-bearing ledger:** no edge changed; `D-UPPER` and `D-HALF` remain open.

## Final route decision and closure

The exact direct command `python3 scripts/adversarial_review.py run` completed
one reciprocal round with `claude-fable-5` and `gpt-5.6-sol` over 19
hash-bound evidence files. All four outputs independently agree on the same
advisory disposition. Manifest SHA-256
`f149630a19fd4e0009ce7fb771625e46229e32e7bbe8af506436b4a1dd260b99`;
root adjudication
`runs/reviews/20260822-post-batch011-corrected-route-review-fable-sol/adjudication.json`
SHA-256
`e24b52df011acfd0b29cdd6c2ec95a9f784262a032f32a33bbe1346a2ab4f966`.

- B011-I01 remains ledger-only. Reconsideration requires one exact
  source-authenticated factor/proxy/product fixture with prospective boundary
  conventions; this ticket does not schedule it.
- B011-I04 remains ledger-only. Reconsideration requires one deterministic
  `p`-wedge divider/two-block definition fixing direction, orientation, and
  boundary assignment; this ticket does not schedule it.
- B011-I02, B011-I03, and B011-I05 retain candidate-local closure.
- Recommended slate: zero proof-producing and zero information-gathering
  slots. `NO-BATCH011-ROUTE-READY` is the terminal, not a request to pad the
  slate.

The review also found a 63-character source-digest transcription in the
original Batch011 source-audit result. The reviewed artifact remains immutable;
`runs/agents/20260822-rolling-pipeline/batch011-source-audit/erratum.json`
(SHA-256
`4e1501e6ccabdf25ab92eeeeef3dec5a0dd0cd87488629e43687e9a124f0fa51`)
binds the correct 64-character value for future reuse. This is
`operational-only` and changes no mathematical conclusion.

The rolling policy itself is now adopted and the first wave is closed. A
separate refreshed Batch012 factory packet may use this reconciled terminal as
novelty memory, but factory output remains proposal-level until its own route
decision.

## Actual time and resource record

The independent timing audit returns `TIME-AUDIT-INCOMPLETE` (result SHA-256
`293de33ac0904117b3e65f47703a3433e2254c4ee0941815cd72a995a6360af9`).
Exact active-lane timers and pauses were not logged, so the values below are
filesystem packet-to-result envelopes, not measurements of uninterrupted
work. They are retained rather than retroactively inventing forecast rows in
`docs/agents/time-estimates.csv`.

| lane | artifact envelope | exact or bounded resource evidence |
| --- | ---: | --- |
| WIN11 | 15.743 min | direct axiom traversal reached about 17.4 GiB after 3 min 20 sec; guarded variants stopped at 4,411 and 4,339 MiB; structural control took 3 sec |
| LCOUNT | 7.208 min | producer 0.14 sec / 17,192 KiB; checker 0.14 sec / 17,176 KiB |
| BETA2 | 48.720 min | two transforms about 1.7 sec; each cone command below 0.2 sec; whole-lane RSS not established |
| Pappus | 18.685 min | no exact subprocess telemetry |
| Helly | 16.043 min | successful primary 8.57 sec / 34,688 KiB; checker 1.20 sec / 30,568 KiB |
| Batch011 factory | 113.432 min | no exact provider-active or RSS telemetry |
| final route review | 10.535--10.536 min | exact manifest start and completion-metadata interval; CPU and RSS not established |

The same audit records eleven integration/audit artifact envelopes between
5.204 and 11.051 minutes. Its full table and source hashes remain in
`runs/agents/20260822-rolling-pipeline/time-audit/report.md`. Packet resource
caps are not reclassified as forecasts or usage measurements.

Three supporting packets were initially dispatched with a nonstandard schema.
Read-only inspection had begun before the defect was caught, but no v1 result
was admitted; every accepted result was reauthenticated and packaged against a
schema-valid v2 packet. The exact operational history is bound by
`runs/agents/20260822-rolling-pipeline/task-packet-supersession-erratum.json`,
SHA-256
`6bb409ee0f6b1c14cab1b7b0df1888a432c509cd81b1cd62441c50a2590df3ac`.

## Proof-distance accounting

- **Net proof movement:** neutral at launch.
- **Evidence:** three admitted frozen cards, one proposal-generation packet,
  and an explicit process authorization; no new theorem or computation yet.
- **Damage scope:** none at launch.
- **Difficulty displaced:** none until a thread passes its evidence gate.
- **Counterfactual test:** this policy reduces idle wall time and exposes
  results sooner, but does not itself shorten a mathematical dependency.
- **Planning consequence:** dispatch the four streams now, reconcile terminals
  independently, and keep discovery/backfill live.
- **Load-bearing ledger:** no edge changed at launch.
