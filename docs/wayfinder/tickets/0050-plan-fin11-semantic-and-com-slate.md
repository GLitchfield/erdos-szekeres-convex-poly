---
title: Plan the selected Fin11 semantic and COM-corner slate
type: research
mode: HITL
status: closed
claim: codex-fin11-semantic-com-plan-2026-08-20
blocked_by: none
---

# Ticket 0050: plan the selected Fin11 semantic and COM-corner slate

## Question

How should the two threads selected by Ticket 0049 be executed so that one can
land a scoped Lean theorem and the other can decisively test, without retuning,
the chord-arrangement corner mechanism?

This ticket plans execution only. It does not authorize a computation, a Lean
build, a portfolio-state change, or a claim about either mathematical card.

## Decision criteria

The plan is admissible only if each lane freezes its exact mathematical object
before outcome computation, names every evidence gate and terminal branch,
preserves the selected scope ceiling, and states what later obligation remains.
The Fin11 lane must end in a theorem over project predicates rather than SAT
atoms. The COM lane must implement the cited corner-block definition and use
authenticated coordinates rather than an abstract order type. Neither lane may
repair a frozen outcome, add a target-equivalent premise, or consume a positive
fixture as if it were a target-free falsification control.

## Slate accounting

The slate has two slots in distinct mechanism families:

1. `FP-01.A`, **proof-producing after preflight**: reflect the exact semantics
   of the selected Fin11 cube into its compiling LRAT checkpoint leaf.
2. `FP-09.A`, **information-gathering**: exhaust source-valid corner peelings
   of exact rational chord arrangements at `k=9` and `k=10`.

Count: one proof-producing and one information-gathering slot. No thread is
added merely to fill the two unused concurrency slots.

## Lane 1: `FP-01.A` indexed semantic reflection

### Frozen mathematical contract

The selected cube uses original triple variables, not auxiliary SAT atoms.
Under the frozen lexicographic triple enumeration its six literals are

```text
chi(0,2,8)  = left       chi(1,5,7)  = right
chi(3,4,6)  = left       chi(4,7,10) = right
chi(5,9,10) = left       chi(0,1,3)  = right.
```

The planned module defines `SynchronizedFiveFanFin11Conclusion chi` to mean
that there are a six-element side and an exterior pivot with one common lower
or upper deep-split direction, and every five-subset of the side that is strong
is respectively a cup or a cap. It defines the conjunction above as
`SynchronizedFiveFanFin11SelectedCube chi`.

The sole endpoint theorem is fixed as

```text
theorem synchronizedFiveFanSideAtSixFinEleven_of_selectedCube
    (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : not ContainsStrongPolygonSet chi Finset.univ 6)
    (hcube : SynchronizedFiveFanFin11SelectedCube chi) :
    SynchronizedFiveFanFin11Conclusion chi
```

Here `not` denotes Lean negation in this prose rendering. The actual Lean
statement will use the project notation and exact `Turn.left`/`Turn.right`
ordered triples. The statement may not gain a semantic-clause premise, an
auxiliary-atom valuation, a certificate hypothesis, or a supplied conclusion.
All encoding and clause helpers remain private.

This theorem closes exactly one selected-cube semantic interface. It does not
prove the other 63 cubes or the unrestricted Fin11 theorem.

### Stage F0: immutable admission and reconstruction

- Freeze the checkpoint modules, selected-cube record, child/core CNFs, core
  maps, LRAT, indexed-family ledger, original semantic generator, and the
  relevant project definitions by SHA-256.
- Independently reconstruct the original 1,881-variable meaning, the selected
  1,822-variable renaming, all 9,181 selected clauses, and the six triple
  literals above.
- Reject any disagreement before writing Lean source.

### Stage F1: eight-schema and six-unit preflight

Before generation, freeze two independent evaluators. For one fixed indexed
object in each family, exhaust the Boolean truth table and compare the frozen
CNF clauses with the direct mathematical predicate:

1. one-change on an ordered quadruple;
2. strong-quad definition;
3. strong-five definition;
4. lower-bad definition;
5. upper-bad definition;
6. no-strong-six;
7. no-synchronized-lower;
8. no-synchronized-upper.

Separately verify all six old-variable, triple-index, selected-core-renaming,
and sign maps. The preflight must reject an omitted family member, one changed
literal sign, and one family/index substitution. Output remains sealed until
both evaluators terminate.

Any mismatch, undefined adapter, or need for a new LRAT transformation stops
the lane. The preflight is checked computation and is not proof movement.

### Stage F2: generated semantic layer

Only after exact F1 agreement:

- generate the Fin11 conclusion, selected-cube predicate, selected auxiliary
  atom definitions, and semantic clause lemmas from the frozen maps;
- group the 9,175 semantic clauses into bounded generated modules aligned with
  the existing 32 checkpoint segments;
- instantiate the unchanged checkpoint leaf from those semantic lemmas and the
  six selected-cube hypotheses;
- expose only the two definitions and endpoint theorem above.

The generator must be deterministic and have a source-level reconstruction
test. No `sorry`, `admit`, new axiom, `unsafe`, `native_decide`, unbounded
heartbeat override, or external proof oracle is admissible.

### Stage F3: Lean evidence gates

Run, serially and under the existing guard:

```text
python3 scripts/run_lean_guarded.py --timeout-seconds 1800 \
  --max-rss-mib 12288 --max-lean-processes 1 \
  --heartbeat-seconds 45 -- \
  lake env lean ErdosSzekeres/SynchronizedFiveFanFin11SemanticReflection.lean

python3 scripts/run_lean_guarded.py --timeout-seconds 1800 \
  --max-rss-mib 12288 --max-lean-processes 1 \
  --heartbeat-seconds 45 -- \
  lake build ErdosSzekeres.SynchronizedFiveFanFin11SemanticReflection
```

Then run a declaration-only `#print axioms` audit for the two definitions and
the endpoint. The theorem may depend only on the standard accepted axioms.

### Fin11 outcomes

- `FIN11-SEMANTIC-REFLECTION-LAND`: F1 agrees, the exact theorem compiles
  warning-clean, targeted build passes, and the axiom audit is standard-only.
- `FIN11-SCHEMA-MISMATCH`: either independent preflight rejects an adapter or
  they disagree. Stop before Lean generation; do not repair the interface in
  the outcome-aware run.
- `FIN11-SEMANTIC-MODEL-GAP`: the six literals or an auxiliary atom cannot be
  identified with the intended project predicate without changing tier or
  adding a premise. Stop and expire this exact interface.
- `FIN11-SEMANTIC-OPERATIONAL`: generation or guarded Lean reaches its frozen
  limit. Preserve the strongest verified layer; do not split the LRAT again or
  increase limits automatically.

### Fin11 proof-distance contract

Only `FIN11-SEMANTIC-REFLECTION-LAND` is forward proof movement: the declared
open count for the selected-cube semantic interface decreases from one to
zero. The other 63 cubes, relabeling/restriction, compatible-window
synchronization, the uniform half-support producer, and `D-HALF` remain open.
Every other outcome is neutral proof movement and potentially useful search
information. No outcome changes a load-bearing destination edge.

Counterfactual test: a compiling endpoint removes real future proof work for
this exact cube; a truth-table pass without the endpoint does not.

## Lane 2: `FP-09.A` chord-arrangement COM corners

### Exact finite question

For `k` equal to 9 or 10, take exact rational points

```text
A = (a_0 < ... < a_(k-2)), a (k-1)-cup,
B = (b_0 < ... < b_(k-1)), a k-cup,
C = (b_0 < ... < b_(k-2)),
```

with the two blocks in the required left-to-right order; include the reflected
order as a separate case. Form the affine arrangement of every chord line
through two points of `C`. Every point of `A` has a sign vector and occupies a
unique arrangement tope because admitted cases are in general position.

The source notion of corner is a **set of topes**, and a corner peeling is an
ordered partition of the tope set into such corner blocks. Accordingly, the
planned experiment uses the source-faithful definition

```text
first sampled corner = the least peeling block meeting
  {tau_C(a_t) : 0 <= t <= k-2}.
```

It is endpoint-first when that block contains `tau_C(a_0)` or
`tau_C(a_(k-2))`; if it contains both, the deterministic endpoint is `a_0`.
There is no invented ordering inside a corner block.

The tested existential is: some source-valid peeling is endpoint-first and its
deterministic endpoint `p` satisfies at least one of

```text
p followed by C is a k-cup;
A union B contains a 4-cap;
A union B contains a strong (k+1)-set.
```

Endpoint-first existence and target extraction are recorded as separate
fields for every case.

### Stage C0: source and control admission

- Authenticate the exact corner/chunk/corner-peeling definitions from Knauer
  and Marc, and the realizable-COM interpretation of an affine arrangement
  from Bandelt--Chepoi--Knauer. The frozen primary references are
  arXiv:`2002.11403`, DOI:`10.1016/j.ejc.2023.103714`, and
  arXiv:`1507.06111`, DOI:`10.1016/j.jcta.2018.01.002`, retrieved
  2026-08-20.
- Freeze a finite graph/covector certificate for `corner` that is equivalent
  to the cited definition on every tested arrangement. If completeness cannot
  be certified, stop `COM-CORNER-CARD-NOT-FROZEN`; testing a convenient subset
  of removable chambers is forbidden.
- Build a prospectively fixed finite integer/rational parameter grid for fresh
  `k=9` and `k=10` two-cup-block realizations. Freeze every generated case and
  independently check all determinant signs, cup premises, general position,
  4-cap witnesses, strong-set witnesses, and reflections before the peeling
  outcome code is run.
- Keep old recursive, rank-collision, affine-predecessor, and Monge witnesses
  only as implementation/corruption controls unless they satisfy the complete
  two-block contract. Abstract order types and coordinate-free SAT models are
  inadmissible.
- If there is no authenticated premise-valid target-free `k=10` case, stop
  `COM-CORNER-CONTROL-GAP`. A positive but target-bearing case cannot stand in
  for the missing falsification control.

### Stage C1: independent exact enumeration

Freeze two implementations before either outcome is opened:

- a producer based on exact rational line signs, feasible sign vectors,
  tope-graph adjacency, source-corner certificates, and memoized corner-block
  deletion;
- an independent checker based on exact planar subdivision/covector
  reconstruction and independent validation of every proposed corner,
  deletion state, endpoint chamber, determinant target, and completeness
  certificate.

For every admitted arrangement, enumerate every source-valid corner peeling,
not only the first successful one. Record the full distribution of first
sampled corner blocks, endpoint-first witnesses, endpoint extensions, 4-caps,
and strong sets. Reject at least one coordinate-sign corruption, one omitted
chamber, one false adjacency, one invalid corner, one truncated peeling tree,
and one endpoint relabeling.

The cap is 250,000 chambers per arrangement, 20 minutes, one CPU core, 2 GiB
RAM, and 1 GiB total output per evaluator. Reaching a cap is operational, not
negative evidence. Outputs remain sealed until both implementations terminate.

### COM outcomes

- `COM-CORNER-FALSIFIED`: both evaluators agree on a complete premise-valid
  rational case for which no source-valid peeling satisfies the existential.
  The certificate must distinguish endpoint-first failure from extraction
  failure. Expire `FP-09.A` without changing the sample rule or chord set.
- `COM-CORNER-SURVIVES`: both evaluators agree that every frozen `k=9` and
  `k=10` case passes, with complete peeling certificates. This is checked
  computation only. Next plan one coordinate theorem and its
  determinant-to-chamber adapter; do not claim the uniform lemma.
- `COM-CORNER-CARD-NOT-FROZEN`: the cited source definition cannot be given a
  complete finite checker at this tier. Do not run a weakened experiment.
- `COM-CORNER-CONTROL-GAP`: no authenticated target-free rational `k=10`
  control is produced by the frozen source-only grid. Preserve the search
  ledger and do not infer anything about the corner lemma.
- `COM-CORNER-CHECKER-DISAGREEMENT`: the two exact implementations disagree on
  arrangements, corners, peelings, or targets. No mathematical outcome.
- `COM-CORNER-OPERATIONAL`: a declared resource or chamber cap is reached.

### COM proof-distance contract

Every outcome in this lane has neutral proof movement. A falsifier is negative
search information; finite survival is positive search information. Only a
later uniform compiling corner-exchange theorem, plus the realizable-to-
`OneChangeOn` transfer, could reduce the diagonal successor below `D-DECOMP`.

Counterfactual test: a complete falsifier would prevent further work on this
refinement, and complete survival would justify stating one coordinate Lean
contract. Neither changes the estimated exact proof until that contract
compiles.

## Ownership and serialization

The execution packet will freeze disjoint writes:

- Fin11: `ErdosSzekeres/SynchronizedFiveFanFin11Semantic*.lean`,
  `scripts/generate_synchronized_five_fan_fin11_semantic.py`, its test, and
  `runs/agents/20260820-fin11-com-slate/fin11/**`.
- COM: `runs/agents/20260820-fin11-com-slate/com/**` only.
- Root integration only: this ticket, `docs/wayfinder/map.md`,
  `docs/wayfinder/frontier-portfolio.md`, and
  `docs/agents/time-estimates.csv`.

No Lean or Lake process may overlap another builder. COM exact computations
may run while no Lean builder is active if the global 16-GiB memory ceiling is
maintained. Integration is serial after both lanes reach a declared terminal.

## Integration gates

After both lanes terminate:

1. independently verify every claimed artifact hash and evidence gate;
2. run the direct/targeted/axiom Lean ladder for any Fin11 source;
3. if tracked proof source changed, run the repository test gate before any
   requested commit;
4. reconcile `FP-01.A` and `FP-09.A` in place, preserving scope ceilings and
   negative knowledge;
5. update the map and time ledger;
6. run `wayfinder_status.py`, `check_frontier_portfolio.py`, orchestration
   validation, and `git diff --check`;
7. stop for discussion before selecting another slate or launching the next
   idea-factory batch.

## Forecast and stop boundary

Calibrated against the prior Fin11 checkpoint run, the Fin11 lane is estimated
at 60--150 minutes. The COM implementation is new and uncalibrated; estimate
45--120 minutes, with its explicit 20-minute-per-evaluator cap. Serial
integration is estimated at 20--45 minutes. Total elapsed work is therefore
roughly 2--5 hours depending on how early the preflight gates decide the lanes.

The overall workspace limits remain 8 CPU cores, 16 GiB RAM, 5 GiB under
`runs/`, and five hours. A lane stops rather than increasing a limit,
weakening a contract, selecting a favorable control, or repairing a frozen
outcome-aware script.

## Approval inventory

One user approval is required to begin the complete slate. No software
installation, destructive operation, external repository mutation, commit,
push, or message to a third party is planned. Primary-source web retrieval is
read-only. All computations write only inside the declared workspace paths.
Guarded timeout termination applies only to processes started by this slate.

If later work requires a larger resource ceiling, a new external service, an
unfrozen theorem statement, or a commit/push, pause that branch and request
separate authority.

## Pre-execution proof-distance accounting

- **Net proof movement:** neutral; this ticket is a plan.
- **Evidence:** authenticated repository interfaces, one compiling
  propositional checkpoint leaf, exact checked index reconstruction, and two
  primary-source COM definitions.
- **Difficulty displaced:** none. The selected Fin11 semantic implication and
  the endpoint-first corner refinement remain unproved and untested.
- **Counterfactual test:** the plan is useful because it prevents a semantic
  mismatch, incomplete corner enumeration, or missing coordinate control from
  being mislabeled as theorem evidence. It does not itself reduce proof work.
- **Planning consequence:** await approval, then freeze immutable task packets
  and execute exactly these two lanes without backfill.
- **Load-bearing ledger:** no destination edge changes at planning.

## Innovation check

- Fin11 semantic reflection: `skip`. This is mechanical implementation of the
  already frozen selected-cube theorem contract and unchanged LRAT leaf; a
  second innovation task would not change the admissible statement or gate.
- COM corner peeling: `dispatch now`. A read-only mathematical-innovation
  sidecar will independently audit whether the source corner-block definition
  has a complete finite checker, whether the target-free rational control is
  constructible, and whether a smaller exact theorem or falsifier should be
  retained for the next cycle. It may not inspect mutable COM outputs or alter
  the frozen experiment.

## Resolution

Approved and executed on 2026-08-20. Outcome label
`FIN11-COM-SLATE-CLOSED`; the slate-completion validator admits all three
terminal results.

The Fin11 preflight passed independently and exactly: both implementations
reconstructed all 9,175 semantic clauses, all eight families, and the six
selected units. The frozen generator test then passed six of seven checks but
stopped on one 102-column rendered line under the 100-column source contract.
The generator, Lean direct gate, targeted build, and axiom audit therefore did
not run. This is `FIN11-SEMANTIC-OPERATIONAL`, neutral proof movement, and
operational-only damage. The selected-cube theorem remains untested; a fresh
representation-only recovery may change only that rendering defect.

The COM lane stopped `COM-CORNER-CONTROL-GAP`: two independent exact audits
agreed on 980 premise-valid `k = 10` cases, but none was target-free. No peeling
outcome was opened. The sealed innovation sidecar then found a more basic
architecture defect: the sampled ten-cup branch already implies a strong
eleven-set under the frozen premises, so the combined extraction conclusion is
equivalent to its target disjunction and cannot discriminate the COM
mechanism. Expire that exact `FP-09.A` formulation. Endpoint accessibility may
be studied separately only as an information question until a noncollapsed
consumer exists.

**Net proof movement:** neutral. **Evidence:** independently checked semantic
and rational computations, two operational/control stops, and proposal-level
primary-source review. **Difficulty displaced:** none; the selected Fin11
semantic theorem, the direct diagonal successor, `D-HALF`, and `D-DECOMP`
remain open. **Counterfactual:** the semantic preflight and COM collapse avoid
future adapter and experiment errors but do not reduce the remaining proof.
**Planning consequence:** retain the Fin11 card behind one narrowly frozen
rendering recovery; expire the combined COM target-extraction card; do not
infer a load-bearing dependency change or promote either parent.

## Evidence

- Ticket 0049 selected-slate contract and its frozen review.
- Selected cube `v015-1_v111-1_v155-1_v068-0_v142-0_v002-0`, its exact
  selected-cube record, indexed-family ledger, child/core CNFs, core maps, and
  compiling 32-segment checkpoint theorem.
- Frozen Fin11 semantic generator and computational result under
  `runs/agents/20260811-four-slot-uniform-round/uniform-fan-n11/`.
- Compiling `ExtremeExchangeK9FinSeventeen89` and
  `ExtremeExchangeK9FinSeventeen98` finite bases.
- Bandelt--Chepoi--Knauer, arXiv:`1507.06111`,
  DOI:`10.1016/j.jcta.2018.01.002`.
- Knauer--Marc, arXiv:`2002.11403`,
  DOI:`10.1016/j.ejc.2023.103714`.
