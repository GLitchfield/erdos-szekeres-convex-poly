---
title: Plan the EX19 complete-premise decision
type: research
mode: HITL
status: closed
claim: codex-ex19-premise-decision-plan-2026-08-21
blocked_by: none
---

# Ticket 0060: plan the EX19 complete-premise decision

## Question

Can the sole item selected by Ticket 0059 be made into an immutable,
resource-bounded, independently checkable execution packet that decides the
complete abstract Fin19 premises without promoting an isolated finite
certificate or silently changing the model tier?

## Decision criteria

- `EX19-PLAN-READY`: both mathematical propositions, CNF clause families,
  independent SAT/UNSAT evidence paths, corruption controls, outcomes,
  downstream stops, resources, ownership, and approvals are exact enough to
  freeze an immutable packet after user approval.
- `EX19-PLAN-SEMANTIC-GAP`: the Lean predicates, exchange-gluing
  interpretation, or abstract model tier cannot be matched exactly; stop
  before encoding.
- `EX19-PLAN-EVIDENCE-GAP`: SAT model replay or independently reconstructed
  UNSAT replay cannot be specified without relying on the primary producer or
  an unverified oracle.
- `EX19-PLAN-RESOURCE-GAP`: exact formula sizing or the required evidence
  artifacts cannot fit a bounded, prospectively declared envelope.
- `EX19-PLAN-APPROVAL-GAP`: a foreseeable external or resource action cannot
  be made exact enough for consolidated user approval.

Planning success is neutral. It authorizes neither execution nor a proof
claim, and it changes no portfolio state or load-bearing dependency.

## Resolution

Outcome: `EX19-PLAN-READY`.

Yes. The plan below freezes two separate premise formulas, one for the `9+10`
block orientation and one for `10+9`. It uses a run-local compiling Lean smoke
proof for the exchange-to-strong-eleven interpretation, a streaming primary
encoder, a separately implemented semantic reconstructor, direct model replay
on SAT, and independent full-CNF LRAT replay on UNSAT. No formula has been
generated and no solver has been launched.

The execution slate remains **zero proof-producing and one
information-gathering lane**. It is exploration. Every mathematical outcome is
neutral with respect to the load-bearing ledger.

## Governing selection and scope

Ticket 0059 selected only `EX19` under `FP-09`. This ticket plans that selected
item; it does not select another lane, revive a portfolio entry, authorize the
deferred state-567 interface amendment, or change a theorem contract.

Model tier: arbitrary abstract `TripleColoring 19` satisfying `OneChangeOn` on
`Finset.univ`. Sweep realizability, coordinates, decomposability, and an order
type are deliberately absent. A SAT assignment therefore decides the literal
abstract `FP-09` candidate without any coordinate-realization sequel.

Scope ceiling: satisfiability or emptiness of the two fixed Fin19 premise
families. Even independently replayed UNSAT is not a uniform successor and is
not an induction base in a defined induction. No result closes or strictly
reduces `D-DECOMP`.

## Exact mathematical objects

For `chi : TripleColoring 19`, define the common premise fields:

```text
OneChangeOn chi Finset.univ
not ContainsCapSet chi Finset.univ 4
not ContainsStrongPolygonSet chi Finset.univ 11
```

The two separately decided propositions are:

```text
EX19Premise910 := exists chi : TripleColoring 19,
  OneChangeOn chi Finset.univ and
  IsCupSet chi {0,...,8} and
  IsCupSet chi {9,...,18} and
  not ContainsCapSet chi Finset.univ 4 and
  not ContainsStrongPolygonSet chi Finset.univ 11

EX19Premise109 := exists chi : TripleColoring 19,
  OneChangeOn chi Finset.univ and
  IsCupSet chi {0,...,9} and
  IsCupSet chi {10,...,18} and
  not ContainsCapSet chi Finset.univ 4 and
  not ContainsStrongPolygonSet chi Finset.univ 11
```

No reflection equivalence is assumed or sought in this block. Both formulas
must be generated, solved, and checked separately.

### Exchange interpretation

Before encoding, a run-local Lean file
`runs/agents/20260821-ex19-premise-decision/ExtremeExchangeK10SemanticSmoke.lean`
must compile without `sorry`, `admit`, or nonstandard axioms and prove these
two exact implications:

```text
EX19PremiseFields910 chi ->
  not IsCupSet chi (insert 0 {9,...,17}) and
  not IsCupSet chi (insert 8 {9,...,17})

EX19PremiseFields109 chi ->
  not IsCupSet chi (insert 10 {1,...,9}) and
  not IsCupSet chi (insert 18 {1,...,9})
```

Each proof must instantiate
`isCupSet_insert_two_of_extreme_cup_extensions` and then
`IsCupSet.isStrongPolygonSet`. In the first orientation the far endpoint of
the existing ten-cup is `18`; in the second it is `0`. Thus any exchange
ten-cup would glue with the existing opposite extreme to an eleven-cup and
contradict the frozen no-strong-eleven premise.

This smoke proof validates the interpretation only. It is ignored run-local
evidence and is not a new finite theorem promoted into the project library.
Failure to compile the unchanged statements is `EX19-SEMANTIC-STOP`; do not
repair the SAT formula around the failure.

## Exact Boolean encoding

For every `0 <= i < j < k < 19`, use a base variable `x(i,j,k)` whose true
value means `Turn.left`. The primary encoder uses lexicographic triple order.

For every `a < b < c < d`, write

```text
(x(a,b,c), x(a,b,d), x(a,c,d), x(b,c,d)).
```

The clause families are exactly:

1. **One change.** Forbid the eight four-bit words with more than one adjacent
   sign change. This is eight four-literal clauses per four-set.
2. **Equality definitions.** Introduce two auxiliaries per four-set,
   `e0 <-> (x(a,b,c) = x(a,b,d))` and
   `e1 <-> (x(a,c,d) = x(b,c,d))`, with four ternary clauses per auxiliary.
3. **No four-cap.** For every four-set, emit the four-literal clause saying at
   least one of its triples is left-turning.
4. **No strong eleven-set.** For every eleven-set `S`, emit the single clause
   containing `-e0` and `-e1` for every four-set contained in `S`. This is the
   exact finite expansion of
   `not_containsStrongPolygonSet_iff_all_not_middleDetermined`.
5. **Cup blocks.** Emit one positive unit for every triple in the two frozen
   blocks of that orientation.

There are no exchange-cup clauses, selector variables, realizability clauses,
coordinate constraints, decomposition premises, symmetry assumptions, or
solver-selected subsets. Exchange-cup absence is a checked consequence of the
premise, not an input.

### Exact size contract

The count-only audit
`runs/agents/20260821-ex19-premise-plan/size_audit.py` records contract SHA-256
`801d8b1669e2426e841571164e5f97e3f81ec4c3a34c5f4ff3add9e46fddf3ee`.
For each orientation it gives:

| item | exact count |
| --- | ---: |
| triple variables | 969 |
| equality auxiliaries | 7,752 |
| total variables | 8,721 |
| one-change clauses | 31,008 |
| equality-definition clauses | 31,008 |
| no-four-cap clauses | 3,876 |
| no-strong-eleven clauses | 75,582 |
| cup-block units | 204 |
| total clauses | 141,678 |
| literal occurrences | 50,116,884 |

Under the frozen primary DIMACS serialization, `9+10` is exactly 300,443,017
bytes and `10+9` is exactly 300,443,008 bytes, about 573.1 MiB combined. Any
count or byte mismatch is an encoder stop before solving.

## Independent evidence architecture

Execution owns one ignored directory:
`runs/agents/20260821-ex19-premise-decision/`. Shared Lean and Wayfinder files
remain root-owned and are not edited while computation is live.

After user approval, root freezes one schema-valid task packet and slate
manifest, then implements these non-importing code paths:

- `encode_a.py`: streams the two lexicographically mapped DIMACS files and an
  origin/count/hash ledger without retaining the 50-million-literal formulas
  in memory;
- `audit_b.py`: independently reconstructs the semantics using a distinct
  triple/equality enumeration and parses the primary DIMACS files line by
  line, translating back to semantic keys before comparison;
- `semantic_check_a.py`: directly replays any SAT model over all 969 base
  signs and independently checks CNF satisfaction;
- `semantic_check_b.py`: a separate bit-set implementation directly checks
  the Lean predicates, both exchange cups, completeness of the assignment,
  and auxiliary definitions; and
- `check_lrat.cpp`: the existing independently implemented streaming
  positive-hint RUP/LRAT checker is copied by source and rebuilt locally. Its
  source SHA-256 before copying is
  `640c0d79b7f77add384085ba3387360c277334190eeaee2322944808489c9d26`.

The two semantic programs may share only the frozen JSON schema, not helper
code. Before the solver token is released, they must agree on both full CNF
hashes, the exact table above, the semantic origin count of every family, and
all controls. Controls include a valid tiny LRAT trace, a corrupted LRAT hint,
a deleted cup unit, an altered long strong-set clause, an incomplete SAT
assignment, and a forced-block sign flip. Every relevant corruption must be
rejected.

The solver is the already recorded local CaDiCaL binary at
`runs/agents/20260811-four-slot-structural-round/half-pure-singleton-fin9/cadical-root/usr/bin/cadical`.
Its embedded version is 1.7.3, its SHA-256 is
`7b73df0a6d9cf3c751a1948300e5baff8e82c4d39bcd88f0c063b5f5cfb8b33e`,
and its recorded package copyright declares the MIT license. Version or hash
drift is an operational stop; no download or substitution is authorized.

### SAT evidence gate

For every SAT orientation, both semantic checkers must authenticate:

- a complete 969-sign assignment and consistent auxiliary values;
- all 141,678 frozen clauses;
- `OneChangeOn` directly from every four-word;
- both prescribed cup blocks;
- absence of every four-cap;
- absence of every strong eleven-set by direct middle-determinacy checks; and
- explicit failure of both exchange ten-cups.

The SAT claim level is checked computation at the abstract `OneChangeOn` tier.
No coordinate search is needed or allowed.

### UNSAT evidence gate

For every UNSAT orientation:

- `audit_b.py` must independently reconstruct and accept the exact full CNF;
- CaDiCaL must emit a complete text LRAT trace for that exact CNF;
- the freshly rebuilt independent checker must replay the trace to an empty
  clause and reject the frozen corrupted-proof control; and
- hashes, counts, solver exit status, proof size, elapsed time, and peak RSS
  must be recorded.

CaDiCaL's internal result is not enough. A proof truncated by the file cap, a
negative/RAT hint rejected by the checker, or replay exhaustion is
`EX19-INCONCLUSIVE` or `EX19-OPERATIONAL`, never UNSAT evidence. No core
trimming, dense remapping, checkpointing, Lean generation, or proof shrinking
follows a verified UNSAT result.

## Execution stages and dependency tree

1. **X0 — immutable admission and Lean semantics** (30--60 minutes). Freeze
   task/slate objects, all cited input hashes, the exact two propositions, and
   the run-local Lean smoke proof. Stop on semantic mismatch.
2. **X1 — two-path implementation** (60--120 minutes). Implement the streaming
   primary encoder, independent reconstructor, two model checkers, and rebuilt
   LRAT checker within the owned run directory. No solver runs.
3. **X2 — preflight and formula freeze** (10--30 minutes). Run both encoders,
   compare exact sizes and semantic origins, run corruption controls, hash all
   programs and formulas, and write `frozen-execution.json`. Any disagreement
   stops without choosing a preferred encoder.
4. **X3 — prospective solver gate** (at most 30 elapsed minutes). Launch the
   two already-frozen orientations concurrently, one single-core solver each,
   with seed zero and no retuning. Let both reach their own status even if one
   finishes first, unless the aggregate resource stop fires.
5. **X4 — conditional evidence replay** (normally 5--30 minutes; hard maximum
   30 minutes per UNSAT orientation). Directly replay every SAT model. Replay
   each UNSAT proof serially. No result is interpreted until its evidence gate
   passes.
6. **X5 — root admission and integration** (30--60 minutes). Validate the
   task/result pair and slate, independently inspect every report, record one
   predeclared outcome, update `FP-09`, the map, timing row, and a new
   integration ticket in place, and run the Wayfinder/repository text gates.

No later stage may repair an earlier formula after seeing a solver result.
Changing a block, premise, variable meaning, no-strong encoding, solver seed,
or proof format requires a new plan.

## Outcome contract and downstream branches

### `EX19-PREMISE-SAT`

At least one orientation has a model passing both direct replays. This refutes
the literal fixed-`k=10` complete-premise extreme-exchange successor in that
orientation at the exact abstract model tier. Record the other orientation's
independent status. Charge the damage to the frozen candidate unless a later
adversarial review establishes a broader shared cause. Stop: do not seek
coordinates, repair the premise, launch a second family, or generalize to
`k=11`.

### `EX19-PREMISE-UNSAT`

Both orientations have independently reconstructed CNFs and independently
replayed LRAT proofs. This closes only the finite premise-emptiness question.
It does not prove a nonvacuous exchange theorem, revive `FP-06`, support the
uniform successor, or authorize a Lean certificate. Stop all certificate work
and reconcile `FP-09` as a finite nonvacuity obstruction.

### `EX19-ORIENTATION-SPLIT`

One orientation is authenticated SAT and the other authenticated UNSAT. Retain
both artifacts and stop before mathematical interpretation. The next action is
a bounded route review of whether this is a genuine ordered asymmetry or a
contract error; no third encoding or reflection repair runs automatically.

### `EX19-INCONCLUSIVE`

No SAT model is authenticated and at least one orientation times out, exceeds
resources, produces an unreplayable proof, or otherwise remains undecided.
Preserve any independently checked partial orientation result, but do not call
the complete Fin19 gate decided and do not rerun with another seed or larger
budget.

### `EX19-SEMANTIC-STOP` or `EX19-OPERATIONAL`

The Lean interpretation, encoder agreement, corruption controls, solver
identity, task integrity, tooling, or resource enforcement fails before an
admissible mathematical result. Damage is `operational-only` unless the exact
frozen proposition itself is shown mismatched. Preserve the stop and return to
portfolio reconciliation without substitution.

Every branch has neutral net proof movement. A result can change search
allocation or damage scope, not a load-bearing dependency.

## Resource and time forecast

The construction/audit forecast is calibrated against the Ticket 0057 FAN13
run: its 77,094,379-byte CNF generated in 12.24 seconds at 1.18 GiB RSS and was
independently audited in 48.40 seconds at 193 MiB RSS. The earlier Fin17
extreme-exchange formulas had 60,056 clauses, solved UNSAT in about 0.3 seconds,
and emitted roughly 50 MB LRAT traces. EX19 has only 141,678 clauses but about
50.1 million literal occurrences, so I/O scaling is partly calibrated while
solver and proof size remain uncalibrated.

The historical ledger reports median error ratios of about 0.320 for
`bounded-computation` and 0.168 for `mixed-research`; the closest recent FAN13
and EX10 lanes also finished well below their raw stage sums. Applying that
calibration to the 2.75--6-hour unadjusted stage sum, then widening upward for
573.1 MiB of new formula I/O and two conditional proof replays, gives an
expected wall time of **1.5--3 hours**. The hard lane wall remains five hours.
The binding local limits are:

| phase | CPU | memory | elapsed/CPU cap | output |
| --- | ---: | ---: | ---: | ---: |
| generation and audit | at most 2 cores | 8 GiB aggregate | 30 minutes | included below |
| two solver processes | 1 core each | 8 GiB each, 16 GiB aggregate | 30 minutes concurrently | 2 GiB per proof |
| proof replay | 1 core, serial | 8 GiB | 30 minutes per UNSAT orientation | no new large artifact |
| whole run | at most 2 concurrent cores | 16 GiB aggregate | 5 hours wall | 5 GiB under `runs/` |

The conditional maximum of 30 solver minutes plus two 30-minute proof replays
is an explicit increase over the default 30-minute exploratory compute window;
user approval of this plan is required for that bounded exception. It does not
increase the default 8-core, 16-GiB, or 5-GiB limits. Current host availability
was 44 GiB RAM and 601 GiB disk, but the smaller project limits remain binding.

The two exact solver commands are:

```text
timeout --signal=TERM --kill-after=10s 1800s prlimit \
  --as=8589934592 --fsize=2147483648 --cpu=1800 -- \
  /usr/bin/time -v \
  -o runs/agents/20260821-ex19-premise-decision/solver-9-10.time \
  taskset -c 0 \
  runs/agents/20260811-four-slot-structural-round/half-pure-singleton-fin9/cadical-root/usr/bin/cadical \
  --seed=0 --lrat --binary=false \
  -w runs/agents/20260821-ex19-premise-decision/model-9-10.sol \
  runs/agents/20260821-ex19-premise-decision/ex19-9-10.cnf \
  runs/agents/20260821-ex19-premise-decision/ex19-9-10.lrat \
  > runs/agents/20260821-ex19-premise-decision/solver-9-10.log 2>&1

timeout --signal=TERM --kill-after=10s 1800s prlimit \
  --as=8589934592 --fsize=2147483648 --cpu=1800 -- \
  /usr/bin/time -v \
  -o runs/agents/20260821-ex19-premise-decision/solver-10-9.time \
  taskset -c 1 \
  runs/agents/20260811-four-slot-structural-round/half-pure-singleton-fin9/cadical-root/usr/bin/cadical \
  --seed=0 --lrat --binary=false \
  -w runs/agents/20260821-ex19-premise-decision/model-10-9.sol \
  runs/agents/20260821-ex19-premise-decision/ex19-10-9.cnf \
  runs/agents/20260821-ex19-premise-decision/ex19-10-9.lrat \
  > runs/agents/20260821-ex19-premise-decision/solver-10-9.log 2>&1
```

Only these two separate commands may run concurrently. Before release,
`frozen-execution.json` records them literally together with every
input/program hash. A timeout may terminate only its own task-owned process
group; root verifies no child remains.

For an authenticated UNSAT status, root runs the corresponding one of these
commands serially:

```text
timeout --signal=TERM --kill-after=10s 1800s prlimit \
  --as=8589934592 --fsize=268435456 --cpu=1800 -- \
  /usr/bin/time -v \
  -o runs/agents/20260821-ex19-premise-decision/lrat-check-9-10.time \
  taskset -c 0 \
  runs/agents/20260821-ex19-premise-decision/check_lrat \
  runs/agents/20260821-ex19-premise-decision/ex19-9-10.cnf \
  runs/agents/20260821-ex19-premise-decision/ex19-9-10.lrat \
  > runs/agents/20260821-ex19-premise-decision/lrat-check-9-10.log 2>&1

timeout --signal=TERM --kill-after=10s 1800s prlimit \
  --as=8589934592 --fsize=268435456 --cpu=1800 -- \
  /usr/bin/time -v \
  -o runs/agents/20260821-ex19-premise-decision/lrat-check-10-9.time \
  taskset -c 0 \
  runs/agents/20260821-ex19-premise-decision/check_lrat \
  runs/agents/20260821-ex19-premise-decision/ex19-10-9.cnf \
  runs/agents/20260821-ex19-premise-decision/ex19-10-9.lrat \
  > runs/agents/20260821-ex19-premise-decision/lrat-check-10-9.log 2>&1
```

## Ownership, concurrency, and innovation check

Root owns the lane and all integration. There is no delegated builder and no
shared-file editing during the solver/replay phases. The two solver processes
parallelize the genuinely distinct orientation checks, not independent proof
routes. All proof replays and integration are serial.

Innovation check: `skip`. Ticket 0059 already froze and adversarially reviewed
the mathematical question; this block is mechanical implementation and
evidence replay of that contract. An innovation scout would introduce new
routes outside the selected scope. New ideas wait for the normal post-result
factory boundary.

An additional Sol/Fable route review is not required before execution because
this plan implements the already-vetted Ticket 0059 contract. A provider review
is conditional at integration only if the admitted result proposes a material
`FP-09` redirect, suspension, or broader damage scope.

## Approval inventory

### User approval requested

Approval of this plan will authorize:

- the complete 1.5--3-hour root-owned EX19 execution block under the frozen
  formulas and five-hour wall;
- the explicit conditional compute exception of one 30-minute two-solver phase
  plus at most two serial 30-minute LRAT replays;
- local workspace writes only under
  `runs/agents/20260821-ex19-premise-decision/` and later serialized Wayfinder
  integration files;
- compilation of the run-local Lean smoke file and C++ LRAT checker;
- timeout termination of only the two exact task-owned solver or replay
  process groups; and
- if and only if the admitted outcome materially redirects `FP-09`, one
  bounded provider route review using the already authorized exact prefix
  `python3 scripts/adversarial_review.py run`.

### Already available; no new platform authority expected

- Python, Lean/Lake, `g++`, `timeout`, `prlimit`, `taskset`, and `/usr/bin/time`;
- the hash-frozen local CaDiCaL binary and its recorded license; and
- workspace writes and read-only access to all cited project artifacts.

### Not authorized or planned

No network download, package installation, system mutation, coordinate search,
resource increase beyond the explicit compute-time exception, destructive
operation outside task-owned timeout cleanup, tracked Lean certificate,
certificate trimming, external repository mutation, commit, push, factory
batch, second solver seed, second formula family, or `k=11` continuation is
part of this block. Plan approval does not bypass any unexpected platform
approval prompt; an unforeseen prompt pauses only its dependent branch.

## Required closing gates

Before admitting a result, root must run:

```text
python3 scripts/check_agent_orchestration.py --task-packet TASK --result RESULT
python3 scripts/check_agent_slate.py --slate SLATE
python3 scripts/check_frontier_portfolio.py
python3 scripts/wayfinder_status.py
git --git-dir=.git-data diff --check
```

The run-local Lean smoke receives `lake env lean` and an axiom audit. No
project-wide Lean build is claimed because the plan forbids tracked Lean
promotion. A future commit or push is not authorized here.

## Pre-execution proof-distance accounting

- **Net proof movement:** neutral; this ticket is a plan and no selected gate
  has run.
- **Evidence:** compiling existing Lean interfaces, exact combinatorial size
  audit, prior checked SAT/LRAT infrastructure, and the completed Ticket 0059
  Opus/Sol route review.
- **Damage scope:** none from planning.
- **Difficulty displaced:** none. The complete finite-premise question remains
  undecided, and the uniform extraction premise remains unknown.
- **Counterfactual test:** this plan prevents an underchecked SAT model,
  encoding-only UNSAT claim, or unbounded certificate sequel, but it does not
  reduce remaining proof work until an admissible result exists—and no planned
  result is itself forward proof movement.
- **Planning consequence:** await explicit user approval; then freeze the task
  packet and execute exactly X0--X5.
- **Load-bearing ledger:** no edge changes. `D-UPPER`, `D-HALF`, `D-DECOMP`,
  `D-NORMALIZE`, and `D-ASSEMBLE` retain their prior status.

## Evidence

- Ticket 0059 and its root adjudication;
- `FP-09` in `docs/wayfinder/frontier-portfolio.md`;
- `ErdosSzekeres/StructuralCharging.lean` (`OneChangeOn`);
- `ErdosSzekeres/Decomposable.lean` (cup, cap, strong-set, and
  middle-determinacy semantics);
- `ErdosSzekeres/StructuralChargingPascalCupBlocks.lean` (extreme cup gluing);
- `ErdosSzekeres/ExtremeExchangeK9Certificate.lean` and the existing Fin17
  encoders/replayers;
- Ticket 0057's admitted FAN13 and EX10 resource records; and
- `runs/agents/20260821-ex19-premise-plan/size_audit.py`.
