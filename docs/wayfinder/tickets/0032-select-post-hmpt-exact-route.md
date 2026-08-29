---
title: Select the first post-HMPT exact-route theorem card
type: research
mode: HITL
status: closed
claim: codex-post-hmpt-card-forge-2026-08-18
blocked_by: none
---

# Ticket 0032: select the first post-HMPT exact-route theorem card

## Question

After completing the formal reconstruction of the published-order HMPT upper
bound, which exact-conjecture mechanism should next receive Lean proof effort?

The canonical ledger still has exactly two logical routes to `D-UPPER`:

1. close `D-HALF`; or
2. close both `D-DECOMP` and `D-NORMALIZE`.

No exact-route portfolio entry is currently ready for a theorem-first proof
slate.  This ticket therefore selects a bounded exploration block whose sole
purpose is to freeze and falsify the next literal theorem cards.  It is not a
proof-advancement block.

## Reviewed route selection

The bounded reciprocal Sol/Fable review at
`runs/reviews/20260818-exact-route-exploration/sol-fable/REPORT.md` accepted the
exploration-first strategy but required material corrections.  The corrected
leverage order is:

1. `FP-03.B`, Pascal adjacent-profile lacing toward `D-DECOMP`;
2. `FP-08`, multi-anchor fractional cover toward `D-HALF`; and
3. `FP-04`, circuit-guided mutation source toward `D-NORMALIZE`.

These are distinct mechanism families, but their ultimate payoffs are not
independent: the fractional lane can complete its logical route alone, while
the Pascal and mutation lanes are conjuncts of the alternative route.  No
fourth family is ready enough to replace one of them.  `FP-09` is first reserve
only after it has a literal symbolic `k = 10` candidate.

## Stage 0: literal card forge

The first user approval authorizes only this stage.  No evaluator, search,
Lean, Lake, or solver command is permitted yet.

For each lane, produce one immutable card containing:

- exact source, intermediate, and consumer proposition signatures;
- every field and quantifier, with a dependency/witness-provenance DAG;
- a premise-occurrence audit excluding the destination, its witnesses,
  target-equivalent inequalities, and stored copies of the conclusion;
- exact positive controls, corruptions, held-out controls, and hashes;
- the cheapest falsifier and all predeclared outcomes;
- a named strict decrease in the unresolved-obligation set if the later Lean
  theorem succeeds; and
- comparison with every expired interface in the same family.

Failure to freeze a literal card is `CARD-NOT-FROZEN`.  The cards return to the
user for approval before any computation.

## Card A: Pascal adjacent-profile lacing

Freeze the source theorem before the lacing conclusion.  Its hypotheses may
contain published-slice or lowest-separated data, but no endpoint-color table
or cross-endpoint equality.  Then freeze
`PascalAdjacentProfilePairLacing` at `s = k - 1`, requiring all ordered core
pairs to see the same color at the two extension endpoints, and an exact
consumer into the existing `PascalTailTwoSideBound`/middle-profile machinery.

Before any positive search, two independent evaluators must:

1. evaluate the source premise false on the stored exact 567 countermodel and
   its 657 reflection;
2. test all endpoint/order reversals;
3. include one nonvacuous adjacent Pascal state, because the 556 control is
   vacuous for this mechanism;
4. run a conclusion-erasure determination check proving that the source data
   do not store or definitionally determine the equality; and
5. reject deletion of every proposed load-bearing source fact.

Outcomes are `PASCAL-LACING-SURVIVES`, `PASCAL-LACING-FALSIFIED`,
`PASCAL-PRODUCER-GAP`, `CARD-NOT-FROZEN`, `CHECKERS-DISAGREE`, or
`PASCAL-LACING-RESOURCE`.  Only SURVIVES may be considered for later Lean.

## Card B: multi-anchor fractional predecessor cover

Freeze a literal `MultiAnchorPredecessorCoverCertificateAt k` exposing its
anchors, bounded-local charts, overlap/transition laws, support weights,
predecessor-free support proof, vertex-cover inequalities, and total-weight
bound.  Freeze a source theorem from sweep realizability and absence of a
strong `k`-set, and a separate finite consumer into the already-compiling
`FractionalPredecessorCoverAt k` chain.

Every field must say whether it is locally computed, transported, or
existentially chosen.  The card is automatically circular if it degenerates to
one anchor with trivial transitions, stores a final global support, or admits a
projection extracting one global support before the local cover equations are
used.

Mandatory regressions include:

- machine-checked source-premise falsity on the relaxed complete-uniform `K7`
  obstruction;
- the held-out rational Fin9 ordinal 1,459 selector killer at
  `runs/agents/20260813-promising-four-slate/fp01-selector/heldout-family.json`;
- the Fin9 local-minima model at
  `runs/agents/20260814-four-route-slate/fp01-exchange/heldout-family.json`;
- a deliberately selector-encoded fake atlas that both evaluators must reject;
- the existing exact rational target-free controls through `k = 6`,
  `n <= 12`; and
- one held-out exact rational family opened only after both evaluator sources
  and all hashes are frozen.

The card must additionally exhibit two exact colorings with identical admitted
bounded-local data but different successful global supports; candidate
evaluation may not inspect which global support succeeds.

Outcomes are `ATLAS-COVER-SURVIVES`, `ATLAS-COVER-FALSIFIED`,
`ATLAS-COVER-PRODUCER-GAP`, `ATLAS-COVER-CIRCULAR`, `CARD-NOT-FROZEN`,
`CHECKERS-DISAGREE`, or `ATLAS-COVER-RESOURCE`.  Only SURVIVES may be
considered for later Lean.

## Card C: circuit-guided mutation source

Freeze one recognizable circuit or arrangement-cell predicate `S` on the
original carrier, an explicit witness map, and a symbolic uniform implication

```text
S
  -> HasCarrierInternalSourceSplitsAboveAt
  -> existing strict mutation-rank decrease.
```

The first arrow is the only proposed new mathematics.  Do not require an
inhabited above-threshold target-free realizable control: producing such a
fixture would amount to producing a counterexample at an open exact-upper
instance.

Instead, two independent evaluators replay the fourteen admitted Fin7/Fin8
controls and five exact-rational Fin8 carrier-interior persistence witnesses.
They evaluate the source condition `S`, the endpoint shield `E`, and the
source-split conclusion `H`.  Any `S ∧ ¬H` refutes sufficiency.  Extensional
coincidence `S = E` on the census triggers a mandatory symbolic
unfolding/implication audit.  If `S` is the endpoint shield by trivial
packaging, the card is circular.  Every circuit/cell clause also receives a
deletion corruption.

Outcomes are `MUTATION-SOURCE-SURVIVES`, `MUTATION-SOURCE-FALSIFIED`,
`MUTATION-SOURCE-PRODUCER-GAP`, `MUTATION-SOURCE-CIRCULAR`,
`CARD-NOT-FROZEN`, `CHECKERS-DISAGREE`, or `MUTATION-SOURCE-RESOURCE`.
Only SURVIVES may be considered for later Lean.

## Conditional execution after card approval

For each approved card:

1. freeze one immutable task packet with exact inputs, owned paths, semantic
   predicates, controls, corruptions, commands, caps, and outcomes;
2. implement two independent exact evaluators from independently frozen
   semantic ledgers;
3. verify that both sealed outputs are absent, then run each evaluator exactly
   once;
4. inspect neither output until both terminate;
5. return `CHECKERS-DISAGREE` on any semantic mismatch, with no repair/rerun;
6. classify all outcomes as search information only; and
7. reconcile the affected portfolio entries before selecting any Lean work.

Each execution has a 30-minute wall cap, at most 4 CPU cores, 8 GiB RAM, and
1 GiB output.  The aggregate block remains within 8 CPU cores and 16 GiB RAM.
There is no solver scale-up or certificate engineering.

## Survivor-to-Lean gate

A card surviving finite tests still does not earn Lean automatically.  It must
also have:

1. exact Lean source/intermediate/consumer signatures;
2. source premises independently motivated and audited for provenance;
3. symbolic non-equivalence to the named expired interfaces in its family;
4. a nonvacuous adjacent-parameter test where uniformity is claimed; and
5. a named strict decrease in the downstream obligation set, without moving
   the destination into a premise.

At most two survivors enter a later, separately approved proof slate.  The
first Lean target is the smallest load-bearing source or transport bridge, not
an entire speculative framework.  That later plan must provide exact paths,
guarded commands, attempt counts, builder serialization, and axiom audits.

## Time and resource forecast

Empirical baselines in `docs/agents/time-estimates.csv` are the 34-minute FP-01
selector falsifier, 13-minute Pascal 567 falsifier, 9--31-minute early mutation
audits, and 112-minute mutation-interface audit.

- Stage 0 card design/provenance audit: 20--45 minutes per lane.
- Evaluator construction/static freeze: 20--45 minutes per approved card.
- Frozen execution: at most 30 minutes per lane.
- Root reconciliation: 20--45 minutes.

Sequential expected wall time for all stages is 3--6 hours, with a hard
7-hour stop.  Safe independent frozen evaluator commands may overlap, but the
aggregate resource ceiling does not increase.

Approval of Stage 0 requires no external provider call, network access,
software installation, destructive action, process termination, repository
mutation outside ignored run artifacts, commit, push, Lean, Lake, or solver.
The required external route review has already completed.  Later card
execution requires a second user approval after exact cards and commands are
shown.  Lean proof work requires a third, separate approval.

## Decision criteria

Accept a card for computation only if every Stage 0 artifact is literal,
hashable, source-first, noncircular on its face, and has a decisive bounded
falsifier.  Accept a card for Lean only after the complete survivor-to-Lean
gate passes.  Never infer a uniform theorem from finite survival.

The block is an exploration slate with zero proof-producing and three
information-gathering lanes.  Its net proof movement is neutral under every
outcome.  Search information may promote, retain, demote, suspend, or expire a
mechanism only under the portfolio streak rules.

## Resolution

Stage 0 card forge approved and completed on 2026-08-18.  The source audit
returned three different dispositions:

1. Pascal adjacent-profile lacing: `PASCAL-PRODUCER-GAP`.  A source deep split
   derives both equality families, but no independent theorem produces that
   split in the universal `PascalTailTwoSideBound` context.  No computation is
   scheduled for this card.
2. Multi-anchor fractional atlas: `CARD-NOT-FROZEN`.  Every literal weighting
   attempted either inspected global predecessor-free success, selected a
   successful support, or left the transition law tautological.  No computation
   or Lean work is scheduled.
3. Top-apex mutation source: `FROZEN-FOR-FALSIFICATION`.  The literal source is
   a greatest-apex arrangement cell plus the source-only assertion that every
   relevant split-bearing carrier contains the apex.  Its deterministic witness
   map is `support.erase apex | {apex}`.  It mentions no endpoint coloring or
   shield and may receive a separately approved one-shot finite audit.

Stage 0 ran no evaluator, search, Lean/Lake, solver, network, or provider
command.  Net proof movement is neutral; no exact-conjecture ledger edge
changed.

The separately approved mutation execution then froze two independent exact
evaluators, one exact-rational Fin8 witness, fourteen abstract Fin7/Fin8 rows,
twenty actual mutation edges, a held-out row selected only after both evaluator
sources were hashed, and ten corruptions.  Both one-shot evaluators terminated
cleanly and produced identical semantic SHA-256
`3b49a4ee02f9e194960e051d6d1320022c30c07b956299134c245ff02fbaaea8`.

Its terminal outcome is `CARD-NOT-FROZEN`:

- the engineered rational witness genuinely has `S=true`, `H=true`, all 21
  top-apex signs, and exactly the five recorded canonical supports;
- every one of the fourteen abstract rows and all twenty edges has `S=false`,
  while all fourteen endpoint shields have `E=true`;
- no `S=true, H=false` falsifier occurs; but
- deleting `every_split_carrier_contains_apex` is not discriminated, because no
  admitted abstract edge passes the preceding top-apex pair-sign condition.

The card's own frozen rule therefore requires refreezing rather than retaining
the untested carrier field.  It is not eligible for Lean.  With Pascal still at
`PASCAL-PRODUCER-GAP`, the atlas at `CARD-NOT-FROZEN`, and the mutation card now
also at `CARD-NOT-FROZEN`, this ticket closes without selecting an exact-route
theorem card.  `FP-04` is suspended under the repeated information-only/
negative-outcome rule until a genuinely new positive theorem or mechanism
appears.  Net proof movement remains neutral and no load-bearing edge changes.

## Evidence

- `docs/wayfinder/map.md`
- `docs/wayfinder/frontier-portfolio.md`
- `ErdosSzekeres/StrongPredecessorBicoloring.lean`
- `ErdosSzekeres/StrongPredecessorFractionalDual.lean`
- `ErdosSzekeres/StructuralChargingPascalTailGates.lean`
- `ErdosSzekeres/StructuralChargingPascalProfileHoles.lean`
- `ErdosSzekeres/DecompositionPrimeRootedCircuitPersistence.lean`
- `ErdosSzekeres/DecompositionPrimeMutationFamily.lean`
- `ErdosSzekeres/DecompositionPrimeNormalization.lean`
- `runs/reviews/20260818-exact-route-exploration/proposed-slate.md`
- `runs/reviews/20260818-exact-route-exploration/sol-fable/REPORT.md`
- `runs/agents/20260818-exact-route-card-forge/pascal/card.md`
- `runs/agents/20260818-exact-route-card-forge/atlas/card.md`
- `runs/agents/20260818-exact-route-card-forge/mutation/card.md`
- `runs/agents/20260818-exact-route-card-forge/cross-audit.md`
- `runs/agents/20260818-mutation-top-apex-audit/controls/result.json`
- `runs/agents/20260818-mutation-top-apex-audit/controls/comparison.json`
