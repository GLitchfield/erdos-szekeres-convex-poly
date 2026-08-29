---
title: Plan the FP-17 and FP-18 two-lane execution slate
type: research
mode: HITL
status: closed
claim: codex-fp17-fp18-two-lane-plan-2026-08-22
blocked_by: none
---

# Ticket 0065: plan the FP-17 and FP-18 two-lane execution slate

## Question

How should the reviewed `FP-17` arbitrary-window Lean theorem and `FP-18`
quantitative simple-pair falsifier run concurrently, with exact contracts and
honest family-correlation accounting, before returning to portfolio
reconciliation?

## Decision boundary

This ticket plans the selected slate from Ticket 0064. It does not edit Lean,
write an evaluator, run a count, build the project, dispatch an agent, or
authorize execution. Both lanes require separate user approval after this plan
is presented.

## User disposition and four-lane dispatch gate

The user did **not** approve this two-lane slate for execution.  On 2026-08-22
they imposed a hard prerequisite: no research execution block may begin until
four dispatch-ready lanes have been admitted and planned together.

Accordingly, `WIN11` and `LCOUNT` remain two frozen candidate lanes, not an
authorized execution slate.  The missing obligation is to acquire and
route-review at least two additional lanes in mechanism families other than
`predecessor-half`; otherwise a four-slot slate would exceed the default
half-per-family concentration ceiling.  No stale, correlated, undefined, or
ledger-only card may be counted merely to reach four.

The next permissible work is therefore **lane acquisition**, not execution:

1. rebuild the whole-project max-effort Sol factory packet from the fully
   reconciled post-Ticket-0064 state;
2. generate one new five-idea batch with the complete duplicate and negative
   ledger;
3. ground the strongest non-`predecessor-half` candidates, with the corrected
   BETA2 transform and the exact local matchgate-orbit question retained as
   predeclared reserve candidates rather than presumed admissions;
4. run bounded Fable/Sol route review over literal candidate cards; and
5. admit and select work only if the portfolio then contains four
   dispatch-ready lanes, with no more than two from one mechanism family.

If fewer than two additional candidates pass, stop without dispatch and
reconcile the failed acquisition evidence.  This section supersedes every
later reference in this ticket to the two-lane block "awaiting approval";
those details remain reusable specifications for two members of a future
four-lane slate.

## Decision criteria

- `FP17-FP18-SLATE-PLAN-READY`: both tasks have immutable theorem/falsifier
  contracts, exact inputs and hashes, disjoint write sets, budgets, evidence
  gates, branches, stops, and downstream consequences; all foreseeable
  approval needs are inventoried.
- `FP17-FP18-SLATE-PLAN-GAP`: any theorem premise, counting convention,
  independent-checker requirement, owner, resource bound, or outcome branch
  remains open to post-outcome choice.
- `FP17-FP18-SLATE-PLAN-STALE`: an input hash or portfolio disposition changed
  after Ticket 0064, requiring reconciliation before execution.

Planning success is neutral and supplies no mathematical evidence.

## Resolution

Historical planning outcome: `FP17-FP18-SLATE-PLAN-READY`.

Current scheduling disposition: `FOUR-LANE-PRECONDITION`; the planned pair is
not authorized to run by itself.

The execution block has two concurrent research lanes:

| label | entry | class | owner |
| --- | --- | --- | --- |
| `WIN11` | `FP-17` | proof-producing | root / one serialized Lean builder |
| `LCOUNT` | `FP-18` | information-gathering | one finite-model specialist |

Root remains the only owner of Wayfinder integration, project-wide builds,
repository tests, and shared imports. A conditional read-only formal reviewer
may audit the frozen WIN11 source after the builder stops; that is an evidence
check, not a third portfolio thread.

## Correlation and concentration

Both entries inherit the predecessor-half architecture. This is a 100%
single-family slate, not two independent proof routes, and it exceeds the
default no-more-than-half-per-family allocation. The exception is explicit and
bounded:

1. no entry in another mechanism family is dispatch-ready;
2. no stale card may be used as breadth-padding;
3. WIN11's proximate gate is a compiling theorem, while LCOUNT's is a finite
   exact falsifier; and
4. dropping LCOUNT would discard the cheapest discriminator for the only new
   reviewed producer without increasing failure independence.

Evidence from the lanes must be combined conservatively at the architecture
level. Simultaneous success does not count as two independent route successes.

## Frozen input snapshot

Base revision: `e1751075e5632c93a7b406136ed5d93b6fbe919e`.

| input | SHA-256 |
| --- | --- |
| `ErdosSzekeres/StructuralChargingTransport.lean` | `e9c29338c7d3902d3b81f8efff18a2637474ae88a59d8b88006915f356d944b9` |
| `ErdosSzekeres/StructuralChargingCore.lean` | `967e111f5b07ed473b45b527633fb184c5f107479459862c9ef8a4645021c715` |
| `ErdosSzekeres/SynchronizedFiveFanFin11AltDepth2Endpoint.lean` | `5299f750ef28a59caab13f1be475414ae5933540bce1b180dd3c8d07342ed28e` |
| `ErdosSzekeres/SynchronizedFiveFanFin11PredecessorConsumer.lean` | `4264195cd8549bd65971379d83ad05bac1b07cb060b5a5f759ee1a51d04ea074` |
| `ErdosSzekeres/SynchronizedFiveFanFin11SemanticInterface.lean` | `e91aeb4630e25c42e40b90bf3cff3d7bce2a05202a2fadd42e85d60158101ba3` |
| `ErdosSzekeres/Sweep.lean` | `6c3d002db0ea6c8b3ae6a8e0671c51ac39adefff41c0dbfe8ddfab64bf3ba8a8` |
| `ErdosSzekeres/StrongPredecessorBicoloring.lean` | `19d3452f1213356ad8d1d0e6b9be86fe19ce84c7a2b7ff983f34b010e26015db` |
| `ErdosSzekeres/Decomposable.lean` | `96729bad53eb7b6a0e4824762eac0fc56c968e8469a9567fff70164aea35cba4` |
| 13-point predecessor manifest | `db32d94049c163f37d9579b233f7f448eadb816e14988a52c6ae35fb0dde3768` |
| prior independently checked predecessor result | `a8cb994d57d6082011b55eed11d256d9d8a65f852ba3fd36465de8ce0a81b350` |
| Ticket 0063 | `3f05b1c23e4330a609f505141c72db384de2156d7856eb152854a58b841a1242` |
| frozen WIN11 contract audit | `e7d65b575457c0afeed8c64582181b76feb9cdf6d311e7c4b17b2a619619f7ab` |
| completed Ticket 0064 reciprocal report | `30fdcf3247f1b918c35e09f8d9675e3c00a2366d24497acecc2edff6ab98afd5` |

Before dispatch, root freezes machine-readable task packets under
`runs/agents/20260822-fp17-fp18-two-lane/` and reruns every hash. A mismatch
stops only the affected lane for adjudication; it does not authorize silently
refreshing the theorem or control.

## Lane 1: WIN11 (`FP-17`)

### Immutable public contract

Create
`ErdosSzekeres/SynchronizedFiveFanFin11WindowTransport.lean` with the exact
public endpoint, permitting ordinary binder and theorem-name style only:

```text
theorem predecessorFreeSixSubsetAtSixFinElevenWindow_of_oneChange
    {n : Nat} (chi : TripleColoring n) (f : Fin 11 ↪o Fin n)
    (hone : OneChangeOn chi (Finset.univ.image f))
    (hnoStrong :
      not ContainsStrongPolygonSet chi (Finset.univ.image f) 6) :
    exists side : Finset (Fin n),
      side subset Finset.univ.image f and
      side.card = 6 and
      not ContainsStrongPolygonSet chi side 5
```

The implementation may first prove the reusable exact equivalence

```text
theorem containsStrongPolygonSet_image_restrict_iff
    {m n k : Nat} (chi : TripleColoring n) (f : Fin m ↪o Fin n)
    (s : Finset (Fin m)) :
    ContainsStrongPolygonSet (chi.restrict f) s k iff
      ContainsStrongPolygonSet chi (s.image f) k
```

and a local OneChange restriction helper. It may not add sweep realizability,
ambient target-freeness outside the window, a fixed embedding, a supplied
support selector, or any premise stronger than the frozen window-local
hypotheses. It may not edit or replay any Fin11 certificate or generated
checkpoint file.

### Stages

1. Prove exact `Finset.image` membership and injective cardinality helpers only
   as needed inside the new module.
2. Prove arbitrary-support strong-polygon image/restriction equivalence in
   both directions. Existing full-universe forward transport is insufficient.
3. Restrict the window-local OneChange and no-strong-six hypotheses to
   `chi.restrict f` on `Fin 11`.
4. Apply `synchronizedFiveFanSideAtSixFinEleven`, reuse the existing
   predecessor-free branch argument, image its exact six-set through `f`, and
   prove the ambient negative strong-five conclusion by the equivalence.
5. Run the targeted build, standard-axiom audit, full project build, and
   repository tests serially after source ownership closes.

### Ownership and resources

- Primary write set:
  `ErdosSzekeres/SynchronizedFiveFanFin11WindowTransport.lean` only.
- Root-only conditional integration write:
  `ErdosSzekeres.lean`, only if the established aggregate-import policy
  requires the new module; the current Fin11 modules are not aggregate imports,
  so the default is no edit.
- No other Lean or generated file may change.
- Wall ceiling: 120 minutes.
- CPU ceiling: 2 cores; RAM ceiling: 4 GiB; output ceiling: 0.5 GiB.
- Forecast: 30--75 minutes to a targeted theorem gate, calibrated from recent
  small transport/new-lemma tasks; the 120-minute stop is deliberately wider
  because exact `Finset.image` normalization is the known risk. Full repository
  tests add a calibrated 15--30 minutes after success.

### Evidence gates

Run, in order:

```text
lake build ErdosSzekeres.SynchronizedFiveFanFin11WindowTransport
lake env lean /tmp/fp17-window-axiom-audit.lean
lake build
make test
```

The temporary audit imports the new module and prints axioms for both public
theorems. Only the standard project axioms (`propext`, `Classical.choice`, and
`Quot.sound` when actually inherited) are accepted. The source must contain no
`sorry`, `admit`, unsafe declaration, or unverified oracle. Root or a read-only
formal reviewer independently checks the final source hash and proof graph.

### Predeclared outcomes

- `WIN11-LAND`: the exact endpoint compiles and all gates pass. Net proof
  movement is `forward` only at the named fixed-`k=6` restriction/relabeling
  dependency. The before/after unresolved sets are
  `{arbitrary-support transport, window relabeling, compatible/global support}`
  and `{compatible/global support}`.
- `WIN11-CONTRACT-FAIL`: the endpoint needs any forbidden stronger premise or
  is false at the stated abstraction tier. Stop candidate-locally; do not
  repair the statement.
- `WIN11-BOUNDED-PROOF-STOP`: the 120-minute boundary arrives without the
  public theorem. Preserve any compiling helper as neutral infrastructure,
  record the exact Lean residue, and permit no certificate work or contract
  change. A carry-forward requires a new review.
- `WIN11-GATE-FAIL`: the targeted theorem compiles but an axiom, full build, or
  repository gate fails. Treat this as operational until the precise failure
  is isolated; do not claim completion.

### Downstream plan

On `WIN11-LAND`, complete or merge `FP-17` into the fixed Fin11 record and
plan—but do not automatically begin—the genuinely new compatible-window or
common-support producer. All other outcomes retain `D-HALF` unchanged.

## Lane 2: LCOUNT (`FP-18`)

### Immutable finite question

Using only the integer coordinates in
`runs/experiments/20260819-unrestricted-predecessor-core/manifest.json`,
reconstruct the exact family `E` of strong five-subsets on the 13 vertices and
compute

```text
m2(E) = number of ordered pairs (A,B) in E x E
        with A != B and card(A intersection B) = 1.
```

Compare with `L_5 = 5 * choose(9,5) = 630`. No other point set, parameter,
seed, or fitted inequality may be opened after the result is known.

### Independent implementations

Freeze before execution:

1. a producer that derives exact determinant turns and applies the literal
   four-index `IsStrongPolygonSet` equal-color law on every five-subset, then
   counts ordered bit-mask pairs by a nested loop; and
2. a checker that independently computes the exact monotone-chain convex hull
   of every five-subset, requires all five vertices on the hull, and counts
   ordered pairs by summing exact-one-vertex incidences.

Both must reproduce the same sorted 114 edge masks and digest before the pair
count is admitted. Both must compute `m2(K_9^5)=630`; a frozen corruption that
divides ordered pairs by two must return 315 and be rejected. The checker must
also reject an omitted edge and a changed coordinate/determinant sign. The
prior result's 114 count is a required control, not an input edge list.

### Files, commands, and resources

The finite-model specialist owns only
`runs/experiments/20260822-lcount-fin13/**`, containing immutable
`manifest.json`, `produce.py`, `check.py`, `primary.json`, `check.json`,
`result.json`, and `summary.md`. It may read the frozen coordinate manifest but
not the prior emitted edge lists.

Each evaluator runs once with an exact command of the form

```text
/usr/bin/time -v timeout --signal=TERM 300s prlimit --as=2147483648 \
  --fsize=67108864 taskset -c 0 python3 <evaluator> <frozen arguments>
```

The task packet declares a 30-minute agent wall ceiling, one CPU core, 2 GiB
address-space ceiling, 128 MiB aggregate output, and 64 MiB per-command file
ceiling. These are explicit smaller limits inside the project default outer
ceiling of 30 minutes, eight cores, 16 GiB RAM, and 5 GiB output. Forecast:
under one minute of computation and 15--25 minutes including implementation
and independent checks, calibrated from the prior 0.09/0.32-second complete
13-point predecessor run.

No network, solver, Lean/Lake command, random seed, source download, or tracked
file edit is permitted. Producer and checker outputs remain outcome-sealed
until both processes terminate. Root independently reruns only their pure
check modes, not the one-shot producer.

### Predeclared outcomes

- `LCOUNT-FALSIFIED-13`: both implementations agree on the 114 edges and on
  `m2 > 630`. Expire `FP-18` candidate-locally; do not charge this finite
  counterexample to all predecessor-half mechanisms.
- `LCOUNT-FIN13-SURVIVES`: both agree on `m2 <= 630`. Retain `FP-18` as probing
  search information only. Stop the finite program; another instance is
  unauthorized until a separate review freezes a geometric charging or
  injection statement.
- `LCOUNT-MODEL-MISMATCH`: either edge family, digest, ordered count, or
  corruption control disagrees. Record an operational/model stop, admit no
  mathematical result, and do not repair after seeing which side differs.
- `LCOUNT-RESOURCE-STOP`: a declared time, memory, or output bound fires.
  Record operational-only evidence and do not enlarge the bound in this block.

Even a surviving finite count is neutral. The eventual uniform inequality and
formalization or lawful admission of the Ferber--Shapira theorem remain
separate proof obligations.

## Integration and cycle boundary

1. Wait until both lanes have one terminal result or declared carry-forward
   point; no early finite outcome may change the Lean contract.
2. Validate each task/result pair with
   `scripts/check_agent_orchestration.py`; treat delegated prose as untrusted.
3. Independently inspect the WIN11 theorem/source hash and LCOUNT manifests,
   controls, complete edge digest, count, and resource logs.
4. Serialize the targeted/full Lean gates and repository tests through root.
5. Reconcile `FP-17`, `FP-18`, the idea ledger, map, README, and this ticket;
   state the exact load-bearing edge changed or explicitly none.
6. Run `scripts/check_frontier_portfolio.py`, `scripts/wayfinder_status.py`,
   `scripts/check_agent_slate.py`, and `git --git-dir=.git-data --work-tree=.
   diff --check`.
7. Only after admission and reconciliation choose the next slate. A later idea
   factory refresh is serial post-integration work and is not authorized by
   approval of this execution ticket.

## Approval and mutation inventory

The combined block is forecast at 60--120 wall minutes, with a hard
two-hour WIN11 lane ceiling plus integration gates. The mathematical proof
forecast is moderately calibrated; exact Finset normalization remains the
largest uncertainty. This inventory is supplied even if the block finishes
under two hours.

Already authorized or requiring no new platform authority after the user
approves this plan:

- workspace writes in the exact Lean and ignored-run paths above;
- local bounded Python, Lean/Lake, validator, and `make test` commands;
- root plus one delegated finite-model specialist, with one conditional
  read-only formal reviewer after the Lean source freezes; and
- local timeout termination of only the two named evaluator child processes.

No external provider or network call, software installation, resource-limit
increase, GUI, destructive operation, external repository mutation, issue/PR
action, commit, push, or publication is planned. No new reusable escalation
prefix is requested. If an unforeseen approval or larger resource limit is
needed, pause only that lane and continue safe independent work.

## Proof-distance accounting

- **Net proof movement:** neutral at planning.
- **Evidence:** compiling predecessor infrastructure, exact frozen inputs,
  authenticated source conventions, and completed advisory route review.
- **Damage scope:** none added by planning.
- **Difficulty displaced:** none until a gate succeeds. WIN11 still owes the
  arbitrary-window theorem; LCOUNT still owes its first count and the uniform
  producer.
- **Counterfactual test:** the plan improves evidence isolation and prevents
  outcome fitting, but does not reduce mathematical work by itself.
- **Planning consequence:** preserve these two exact contracts, acquire and
  review two additional non-`predecessor-half` lanes, then present one complete
  four-lane slate for separate approval. Do not freeze or dispatch this pair
  alone.
- **Load-bearing ledger:** no edge changed; `D-HALF` remains open.

## Post-acquisition resolution

Ticket 0066 executes the permitted lane-acquisition work and returns
`FOUR-LANE-NOT-READY`. Corrected BETA2 is admitted as probing `FP-19`, but
Lambda is gated without a discriminating next theorem, the exact copoint card
is refuted candidate-locally, and heap stops operationally. The surviving pool
is therefore WIN11, LCOUNT, and BETA2: three cards, not a slate. WIN11 and
LCOUNT remain frozen and unrun; this ticket supplies no execution
authorization and its four-lane prerequisite remains binding.

Ticket 0067 later supersedes that scheduling prerequisite: WIN11 and LCOUNT may
now launch as individually frozen parts of a rolling wave while BETA2 and the
discovery pipeline run concurrently. The mathematical contracts and all stop
rules in this ticket remain unchanged.
