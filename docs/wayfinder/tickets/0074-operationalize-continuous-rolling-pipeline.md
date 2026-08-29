---
title: Operationalize continuous four-slot rolling execution
type: research
mode: HITL
status: closed
claim: codex-continuous-rolling-pipeline-2026-08-23
blocked_by: none
---

# Ticket 0074: operationalize continuous four-slot rolling execution

## Question

Can the adopted Ticket 0067 rolling policy be made enforceable in ordinary
operation, so that the root plus three delegated slots remain productively
occupied through planning, execution, per-terminal admission, portfolio
reconciliation, route grounding, and factory refresh, without padding the
portfolio or misreporting support work as mathematical investigation?

## Diagnosis

The policy exists, but its enforcement layer did not. The repository had
static task/result and completed-slate validators, while the orchestrator kept
no live occupancy declaration, no prospectively approved ready queue, and no
machine-detectable avoidable-vacancy condition. After Ticket 0073, all three
delegated workers were terminal and the root continued route reconciliation
alone. The collaboration occupancy was therefore one of four even though
Ticket 0067 required spare capacity to perform grounding, audit, or factory
work.

Repository code cannot query or mutate the collaboration service. A local
checker can validate a root-declared board, frozen packet hashes, queue state,
family concentration, and heartbeat, but only the active root orchestrator can
compare that declaration with actual agent state and dispatch a replacement.

## Operational contract

1. The four named slots are `root`, `worker-1`, `worker-2`, and `worker-3`.
   The root serializes canonical integration and owns one mathematical or
   discovery task whenever integration is idle.
2. Every delegated slot points to an immutable, validator-passing task packet.
   Each packet freezes objective, inputs, ownership, budget, evidence gate,
   success terminals, and stop conditions.
3. Occupancy is classified honestly as `proof-producing`,
   `information-gathering`, `discovery-support`, or `orchestration`. Only the
   first two count as mathematical investigation.
4. Four active slots are the target. If fewer are active, the board records the
   exact unavoidable vacancy and next action. An idle slot alongside an
   approved compatible ready packet is an error.
5. No more than two active mathematical lanes normally share one mechanism
   family. An override must give a mathematical reason; files or worker names
   do not establish independence.
6. Before an operational execution wave starts, the approved ready queue has a
   floor frozen by that wave. The initial target is at least four reserve
   packets, with discovery/source/card work allowed when fewer honest
   mathematical gates exist. Queue packets are not portfolio routes and do not
   change route state.
7. A terminal is checked, admitted, and reconciled independently. The freed
   slot is backfilled during the same active orchestrator turn from the current
   compatible approved queue; unrelated lanes continue on their frozen input
   hashes.
8. The root does not send a final response while a worker is live. It polls
   agent state, reports material progress or unchanged state at least once per
   minute, and checkpoints every lane before an unavoidable turn/session stop.
9. After WSL or session restart, the root first reads the board, authenticates
   packets and artifacts, compares the declaration with actual collaboration
   state, and resumes or supersedes each lane explicitly.
10. The board is declared state, not platform telemetry. Every user-facing
    occupancy claim requires a contemporaneous collaboration-state check.

## Bootstrap planning wave

The user authorized the next planning step, not mathematical panel execution.
The root launched three read-only proposal lanes from the post-Ticket-0073
hash-frozen snapshot while implementing the operational checker:

| Slot | Packet | Family | Classification | Budget | Authorized output |
| --- | --- | --- | --- | --- | --- |
| root | Ticket/checker/queue design | research-system | orchestration | under 45 min | operational plan and local validator |
| worker-1 | `hullalt-equality-fixture-plan` | `FP-01` | discovery-support | 25 min, 1 CPU, 2 GiB | exact equality-fixture execution contract or gap |
| worker-2 | `hullalt-deconfounder-plan` | `FP-01` | discovery-support | 25 min, 1 CPU, 2 GiB | exact deconfounder acquisition contract or gap |
| worker-3 | `nonfp01-backfill-plan` | cross-portfolio | discovery-support | 25 min, 1 CPU, 2 GiB | at most one non-`FP-01` backfill contract or honest none |

This is `0` proof-producing, `0` information-gathering, and `4` support/
orchestration slots. It is planning, not a proof-advancement block. No panel,
solver, Lean build, route mutation, provider call, or source download is
authorized.

## Decision criteria

- `ROLLING-PLAN-READY`: the checker and tests pass; every planning lane has an
  authenticated terminal; the first operational wave and its reserve queue
  have exact packets, classifications, budgets, branches, and permission
  inventory; and the user can approve them in one decision.
- `ROLLING-PLAN-THIN`: the machinery works, but fewer than four honest active
  or reserve tasks can be frozen. Preserve the explicit vacancies and request
  only bounded route grounding; do not pad.
- `ROLLING-CONTROL-GAP`: the local board cannot represent or validate a
  necessary operational invariant. Name the missing enforcement mechanism and
  do not claim the pipeline is operational.
- `ROLLING-BOOTSTRAP-STOP`: input drift, task-schema failure, or an operational
  resource stop prevents reliable planning. No mathematical damage follows.

## Evidence

The local gate is:

```text
python3 -m unittest scripts.test_check_rolling_pipeline
python3 scripts/check_rolling_pipeline.py \
  --board runs/agents/20260823-continuous-rolling-bootstrap/live-board-current.json \
  --max-age-minutes 5
python3 scripts/check_agent_orchestration.py --task-packet <each packet>
```

The collaboration gate is separate: a contemporaneous agent-state listing
must show root plus three running workers before reporting `4/4`. The local
checker explicitly says it did not independently observe that service.

Before mathematical execution, root must additionally:

1. admit the three proposal terminals without treating them as mathematical
   evidence;
2. freeze the exact active wave and at least the declared reserve-queue floor;
3. validate every packet and check the two-lanes-per-family rule;
4. identify the exact user approvals and platform prompts; and
5. present the complete wave for user approval.

At closure, the digest-bound controller and its `58` regressions pass. The
controller authenticates one root-declared board, the operational-wave
manifest, and every referenced task/result hash; it does not independently
observe collaboration state or know which manifest the user approved. Those
two correlations remain root responsibilities. The exact proposed wave is:

| Packet | Class | Family | Budget | SHA-256 |
| --- | --- | --- | --- | --- |
| `ready/equality16-acquisition/task.json` | information-gathering | `FP-01` | 30 min, 1 CPU, 2 GiB, 0.02 GiB output | `61f6b5912eb47c9b9fc54f1ff3b0b681c57469bc24df6709929113290ba18dee` |
| `ready/deconfounder-path/task.json` | information-gathering | `FP-01` | 30 min, 2 CPUs, 4 GiB, 0.2 GiB output | `0fc8c318987c25c38b4b8a1e866a18b02810b4908cc336b4dba07573cdaada42` |
| `ready/native-registry-metadata/task.json` | discovery-support | none | 5 min, 1 CPU, 1 GiB, 0.005 GiB output | `b9602a480c9c2f03a89498d5b747de7edb1d656a96615ce29dc37a040b5ab2f8` |

This is `0` proof-producing, `2` information-gathering mathematical, and `1`
nonmathematical support packet, plus root orchestration. The two mathematical
lanes exactly meet the `FP-01` concentration cap. An independent reserve audit
found no honest result-independent compatible packet, so the approved reserve
floor is zero. The canonical four-key manifest has expected SHA-256
`f6188cd1609ba3851d8a2a0eba522b154e683ee4dc50aa9df8481eb95f980cb9`;
it is created only after user approval.

## Approval inventory

Authorized and completed during this bootstrap:

- local read-only inspection and writes under the workspace;
- three read-only collaboration planning lanes;
- Python task, portfolio, Wayfinder, and rolling-board validators; and
- creation of this planning ticket and ignored task/board artifacts; and
- one exact local mode-`0700` execution-parent preparation, with the
  packet-owned registry child left absent.

Requires one exact user decision before execution:

- equality acquisition packet
  `61f6b5912eb47c9b9fc54f1ff3b0b681c57469bc24df6709929113290ba18dee`;
- deconfounder-path packet
  `0fc8c318987c25c38b4b8a1e866a18b02810b4908cc336b4dba07573cdaada42`;
  and
- registry-metadata packet
  `b9602a480c9c2f03a89498d5b747de7edb1d656a96615ce29dc37a040b5ab2f8`.

The registry packet then requires one separate, nonpersistent platform prompt
for its exact frozen credential-free `curl` argv to the one canonical npm
metadata URL. User approval does not satisfy that platform prompt. The wave
does not authorize the `HALF-HULLALT` panel, a retry or alternate URL, source
or tarball download, provider/model/Codex execution, credentials, Lean/Lake,
software installation, tracing or process termination, destructive action,
route mutation, external repository mutation, commit, or push. Every
result-dependent follow-up and every reserve packet must be separately frozen
and approved.

## Proof-distance accounting at launch

- **Net proof movement:** `neutral`.
- **Evidence:** operational policy, validator implementation, and
  proposal-level planning lanes only.
- **Damage scope:** `operational-only` if the bootstrap stops.
- **Difficulty displaced:** no mathematical obligation. `D-HALF` still lacks
  `PredecessorHalfSubsetAt k` for every `k >= 5`; the immediate work is to make
  its admitted `FP-01.D` falsifier packet executable while acquiring an
  independent backfill route.
- **Counterfactual test:** continuous occupancy can reduce avoidable idle wall
  time and expose route information sooner, but cannot reduce remaining proof
  work by itself.
- **Planning consequence:** finish and admit the bootstrap proposals, freeze
  the first operational wave and ready queue, then stop for user approval
  before mathematical execution.
- **Frontier portfolio:** unchanged at launch.
- **Load-bearing ledger:** no edge changed.

## Resolution

`ROLLING-PLAN-THIN`.

The declaration-level controller and the three exact packets above are
admitted for one partitioned approval decision. The proposed dispatch starts
at `4/4`: root orchestration, two correlated `FP-01` information-gathering
lanes, and one nonmathematical discovery-support lane. The approved reserve is
zero. After any terminal, root must authenticate and admit that result,
reconcile only affected canonical records, and either dispatch a separately
approved compatible packet or publish a precise temporary vacancy while the
next honest packet is frozen. It may not reuse, silently approve, or pad work.

The final registry-packet audit history is admitted at its actual scopes. One
auditor exceeded its wall budget without returning evidence and was stopped as
`operational-only`. A fresh audit found the exact missing execution-parent
precondition. Root froze and checked the local preparation, created only that
real mode-`0700` parent, left the packet child absent, and a final independent
audit accepted the unchanged packet after all `21` checker tests passed. No
mathematical failure genome is warranted for either operational event.

- **Net proof movement:** `neutral`.
- **Evidence:** proposal-level frozen packets, checked controller computation,
  checked local operational preparation, and independent read-only audits; no
  theorem or mathematical packet result.
- **Damage scope:** `operational-only` for the bounded audit stop and missing
  parent; no mathematical damage is admitted.
- **Difficulty displaced:** none. `D-HALF` still requires
  `PredecessorHalfSubsetAt k` for every `k >= 5`.
- **Counterfactual test:** the controller and exact handoff reduce avoidable
  idle time and approval ambiguity, but do not reduce the remaining proof work.
- **Planning consequence:** close operational planning, request approval for
  the three immutable packets, obtain the separate network prompt, then
  dispatch and reconcile each terminal independently. The `HALF-HULLALT` panel
  remains unapproved.
- **Frontier portfolio:** unchanged; parent `FP-01` remains suspended and
  child `FP-01.D` remains probing under its existing one-panel boundary.
- **Load-bearing ledger:** no edge changed; `D-HALF` remains open for all
  `k >= 5`.

## Rolling mathematical admission: equality-16 fixture

The equality lane generated its complete mathematical artifacts before the
wall boundary but did not return its result packaging within the packet's
30-minute limit.  Root therefore interrupted the worker, preserved that
overrun as `operational-only`, and independently reran the exact recursive
producer, import-independent flat checker, and corruption suite.  The root
replay reproduced byte-identical fixture, provenance, primary, independent,
and corruption hashes in 1.23 measured seconds with 22,524 KiB peak RSS.  The
canonical task/result validator passes and all 12 frozen inputs
reauthenticate.

The admitted mathematical terminal is `EQUALITY16-AUTHENTICATED`.  The literal
fixture has 16 strict-`x`-ordered general-position points; every one of 8,008
six-subsets fails the strong-six law; all 15 composition nodes and all 560
mixed-triple constraints replay exactly; and two hull algorithms agree on
alternating support of size 10.  The strict panel range is genuine:
`2 * 6 - 3 = 9 < 16`.  All eight required corruptions reject.  The packet did
not run `HALF-HULLALT` and the recursively built fixture cannot replace the
missing affine/primality deconfounder.

- **Net proof movement:** `neutral`.
- **Evidence:** independently replayed checked computation; no Lean theorem.
- **Damage scope:** none mathematically; delayed agent packaging is
  `operational-only`.
- **Difficulty displaced:** no `D-HALF` obligation.  One equality-control
  acquisition field is closed, while the off-path deconfounder and the panel
  itself remain missing.
- **Counterfactual test:** the exact fixture makes a future equality observation
  interpretable, but does not reduce remaining formal proof work.
- **Planning consequence:** retain the equality fixture as a closed control,
  keep `FP-01.D` gated, and do not run the panel until a separately reviewed
  off-path control is admitted and a new immutable panel is approved.
- **Frontier portfolio:** `FP-01.D` reconciled in place; parent `FP-01` remains
  suspended.
- **Load-bearing ledger:** no edge changed; `D-HALF` remains open for all
  `k >= 5`.

## Post-approval registry-lane admission

The user approved the three immutable packets recorded above and the live
dispatch began at `4/4`.  The registry-support lane reached
`METADATA-OPERATIONAL-STOP` before creating its owned child or sending a
request.  Its frozen source-plan result said that five installed artifacts had
been authenticated, but did not record their exact paths and digests, so the
packet's mandatory pre-request reauthentication could not be reproduced from
its authorized inputs.  Root preserved the stop as
`native-registry-metadata-execution-stop/result.json`; the canonical
task/result validator accepts it.

Independent root replay also confirmed a second checker defect: Python parses
the otherwise valid JSON token `1e999` as positive infinity, while the frozen
checker supplied only `parse_constant` and therefore accepted that value
despite its finite-JSON contract.  This defect was not exercised on network
data because no request occurred.  Root froze, but did not dispatch, corrected
successor packet `ready/native-registry-metadata-v2/task.json` at SHA-256
`8bb36b9ddea94d691ba1544b6887d86208c634654d13ae9f73314adad4321005`.
It records the exact five installed paths and hashes, layers a finite-float
parser over the unchanged checker, and passes all `23` inherited and new
regressions.  The earlier approval does not cover this new hash; the network
query remains unperformed pending a fresh user decision and its separate
platform prompt.

- **Net proof movement:** `neutral`.
- **Evidence:** checked operational stop, canonical result validation, exact
  installed-file hash replay, and checked local checker regressions; no
  mathematical result.
- **Damage scope:** `operational-only`.
- **Difficulty displaced:** no mathematical obligation.  The registry support
  dependency is narrowed to approval and execution of the corrected exact
  packet; `D-HALF` is unchanged.
- **Counterfactual test:** prior knowledge would have prevented an empty
  registry dispatch, but would not reduce the remaining Erdős--Szekeres proof
  work.
- **Planning consequence:** retain the corrected packet as unapproved support,
  keep the freed slot explicitly vacant, and continue the two approved
  `FP-01.D` mathematical lanes.  Do not retry the old packet.
- **Frontier portfolio:** unchanged; this is not route evidence.
- **Load-bearing ledger:** no edge changed.

## Rolling mathematical admission: deconfounder path

The deconfounder lane completed independently of the still-running equality
lane.  Root reran its import-independent direct checker after terminal return.
The replay again reconstructed 96 determinant walls and 99 exhaustive
endpoint/open-cell representatives, returned the empty winner set, and
reproduced byte-identical hashes for the independent classification and all 19
corruption controls.  The canonical task/result validator passes and all 14
frozen inputs reauthenticate.

The exact terminal is `DECONF-PATH-NONE`.  The complete disjoint disposition
vector is 95 representatives containing a strong six-set, two affine-bad
representatives, and two representatives admitting a proper split.  This does
not say that a deconfounding fixture is absent elsewhere.  Root admits the
damage as `candidate-local`, narrower than the delegated proposal's
`subfamily` wording, because the path's failures have no verified shared cause
beyond membership in the one frozen interpolation.  The required failure
genome is anchored exactly once in `FP-01` under
`FP-01.D-DECONF-PATH-01`.

- **Net proof movement:** `neutral`.
- **Evidence:** checked computation with two independent implementations,
  complete path replay, exact hashes, and corruption rejection; no Lean
  theorem.
- **Damage scope:** `candidate-local`, exactly the frozen interpolation.
- **Difficulty displaced:** none.  The required affine-good,
  decomposition-prime, strong-six-free in-range control is still missing, and
  `D-HALF` still requires `PredecessorHalfSubsetAt k` for every `k >= 5`.
- **Counterfactual test:** knowing this result would prevent repeating the same
  determinant-cell path, but would not reduce remaining formal proof work or
  establish that another control cannot exist.
- **Planning consequence:** expire only this path, change child `FP-01.D` from
  `probing` to `gated`, and forbid the `HALF-HULLALT` panel until a separately
  admitted off-path control closes the missing prerequisite.  No descendant is
  promoted by this failure.
- **Frontier portfolio:** `FP-01.D` reconciled in place; parent `FP-01` remains
  suspended.
- **Load-bearing ledger:** no edge changed; `D-HALF` remains open for all
  `k >= 5`.
