---
title: Prove the HMPT C1 cyclic source and C2 local profile producers
type: research
mode: AFK
status: closed
claim: codex-hmpt-h2-c1-c2-land-2026-08-17
blocked_by: none
---

# Ticket 0026: prove the HMPT C1 cyclic source and C2 local profile producers

## Question

Do the existing original-carrier Pór--Valtr support-product source and raw
one-region geometry imply the exact C1 cyclic geometry and C2 vertical-profile
interfaces needed by HMPT, without a supplied cyclic sign, coloring, maximum,
cardinality inequality, changed carrier, or later C4 conclusion?

Ticket 0025 closed C3.  C1, C2, and C4 are the three remaining subordinate H2
obligations; C4 is serially blocked on C1 and C2 and is not authorized here.

## Decision criteria

Each branch is accepted independently only when its exact public declaration
family compiles warning-clean, its targeted module builds, its static contract
and scope audit passes, and its declaration-only audit reports only the three
permitted standard axioms.  No proper finite control, proposition smoke,
conditional shell, stronger premise, or sibling theorem substitutes for that
branch's kernel gate.  C4 remains outside this ticket even if both branches
land.

## Exact public contracts

The two proof-producing lanes own the declarations frozen in
`runs/agents/20260817-hmpt-c1-c2-slate/frozen-contract.md`.  Their mathematical
inputs and outputs may not change.

C1 must prove `PorValtrSupportProductData.toHMPTCyclicSpikeGeometry` from an
arbitrary source datum at the sharp reachable endpoint `3 <= r` and general
position.  Every structure field, including cell zero and the last-to-first
adjacent window, must be derived.  Wrapped five-anchor signs may use only
`strictCap`, `periodic`, orientation identities, and arithmetic consequences
of `3 <= r`.

C2 must prove both `SukRegionGeometry.hmptVerticalTransitiveColoring` and
`SukRegionGeometry.exists_hmptVerticalProfile`.  It must internally construct
the H1 maximum chains, cardinality-maximum outer-anchored subchains, and the
exact binomial inequality.  No order, coloring, chain, maximum, or inequality
is an input.

## Proof architecture

### C1

1. Normalize the cyclic predecessor, successor, and five offsets modulo
   `2*r`, keeping the `r = 2` repeated-endpoint counterexample excluded.
2. Derive pool inclusion and pairwise disjointness from the source fields.
3. Turn each exact cyclic open pool into its four-anchor `SukRegionGeometry`.
4. Prove all five-anchor strict-cap signs and adjacent pool fields, including
   cell zero and the final successor wrap.
5. Assemble the unchanged `HMPTCyclicSpikeGeometry` structure on carrier `P`.

### C2

1. Use `SukRegionGeometry.toHMPTSpikeOrderPair` and the H1 finite consumer to
   obtain actual maximum vertical and horizontal chains and `|s| <= V*H`.
2. Prove strict HMPT vertical order is reverse strict `SukRegionLT` on pool
   points and prove the exact outer-anchor triple-color semantics.
3. Prove HMPT-direction four-point color transitivity.
4. Select actual cardinality maxima among the outer-left and outer-right
   anchored subchains by finite powerset maximization.
5. Handle vertical-chain cardinalities zero, one, and two explicitly.
6. Under failure of `V <= choose (L+R-2) (L-1)`, invoke the existing generic
   two-color recurrence with branch-to-anchor correspondence proved before
   any use of choose symmetry; contradict the corresponding anchored maximum.
7. Assemble the unchanged `HMPTVerticalProfile` on the original point set.

## Independent review

A third lane is strictly read-only.  It independently rederives the wrapped C1
sign/index ledger and the C2 order/color/recurrence ledger, then audits the
source-ready modules for hidden premises, target-equivalent fields, public
helper leakage, carrier changes, and branch-direction errors.  It runs no
Lean/Lake command and does not edit a file.  Root packages its proposal after
the response.

Ticket 0024 already supplied the mandatory Sol/Fable route review.  This
ticket implements its surviving unchanged contracts; no new provider call is
authorized.  Any contract change or stronger premise stops the affected lane
and requires a new user decision.

## Evidence gates and resources

- C1: four active proof hours and at most four localized direct attempts.
- C2: six active proof hours and at most four localized direct attempts.
- Read-only audit: two wall hours.
- Every Lean/Lake command: 1,800 seconds, 12 GiB aggregate RSS, and one Lean
  process through `scripts/run_lean_guarded.py`.
- Builders are serialized by root.  Each module requires a warning-clean
  direct gate, a separately released targeted build, static scope/style
  checks, and a separately released declaration-only axiom audit.
- Accepted declarations may depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- No new finite fixture or perturbation of ticket 0023 is authorized.  The
  earlier controls remain neutral search information; a universal Lean proof
  is the acceptance gate.

## Predeclared branch outcomes

For each of C1 and C2:

- `LAND`: the exact declaration family passes every kernel and trust gate;
- `FALSIFIED`: an admitted exact source or GP region is kernel-encoded and
  refutes the frozen theorem;
- `GAP`: a named mandatory output is not implied by the unchanged input;
- `INERT`: only a supplied result equivalent to the target closes the proof;
- `RESOURCE`: the bounded branch stops without a trustworthy classification.

Representation-only compiler diagnostics may be repaired within the direct
attempt budget.  A mathematical diagnostic, missing premise, carrier change,
or certificate-shaped workaround stops the affected lane.  The independent
branch may continue unless the defect lies in a shared frozen definition.

## Evidence

The sharp `3 <= r` endpoint matches the compiled
`exists_porValtrSupportProductData` producer, while
`HMPTCyclicSourceCounterexample.frozenContract_false` kernel-refutes only the
old `r = 2` contract.  Ticket 0023's exact controls admit both empty and
nonempty cyclic `r = 3` sources and their wrap reconstruction, but remain
neutral computation.  Ticket 0024's mandatory adversarial review gives C2 a
noncircular proof graph through the compiled H1 maximum-chain consumer,
reverse HMPT/Suk order, outer-anchor color semantics, and the generic exact
two-color recurrence.  Ticket 0025's compiling C3 theorem is the immediate
consumer of the profiles C2 will construct.  None of this proposal-level or
downstream evidence replaces the two frozen theorem gates.

## Integration and proof distance

Every accepted theorem is integrated even if its sibling branch stops.  If
both land, the subordinate H2 count decreases from three (`C1`, `C2`, `C4`)
to one (`C4`).  If exactly one lands, it decreases from three to two.  C4 is
not launched in this slate; after evidence admission the portfolio is
reconciled before a separate C4 plan.

Landing C1 or C2 is forward proof movement on that named subordinate
dependency because no new premise is introduced and the immediate C4 consumer
already exists as an exact contract.  H2's official five-layer count remains
unchanged until H2 as a whole lands.  `D-HALF`, `D-DECOMP`, and `D-NORMALIZE`
remain unchanged, and no load-bearing exact-conjecture edge changes.

## Approval inventory

User approval authorizes the two disjoint source modules, read-only audit,
serialized guarded direct/build/audit commands, exact integration edits, one
guarded full `make test`, exact staging, commit, and push to the current branch.
No provider review, external retrieval, installation, destructive operation,
resource increase, or process termination is planned.  Any newly required
authority pauses only the dependent branch.

## Resolution

Closed with outcomes `HMPT-H2-C1-LAND` and `HMPT-H2-C2-LAND`.

`PorValtrSupportProductData.toHMPTCyclicSpikeGeometry` compiles warning-clean
in `ErdosSzekeres/HMPTCyclicSpikeProducer.lean`.  It keeps carrier `P`, derives
all cyclic pool and local-region fields, proves the ten wrapped five-anchor
signs, and aligns the final successor window with cell zero.  Its third direct
attempt passed after representation-only repairs; the targeted module built
`3318/3318`; its declaration audit reports exactly `propext`,
`Classical.choice`, and `Quot.sound`.  C1 result SHA-256:
`f1b9401da3515436688a1870acd2d4ad1d310b5b20362ed7d8401ebc0ad041c9`.

`SukRegionGeometry.hmptVerticalTransitiveColoring` and
`SukRegionGeometry.exists_hmptVerticalProfile` compile warning-clean in
`ErdosSzekeres/HMPTVerticalProfileProducer.lean`.  They derive the strict
HMPT/reverse-Suk order and color laws, construct maximum vertical and
horizontal chains and both outer-anchor maxima internally, close the small
vertical-cardinality cases, and prove the exact
`choose (L+R-2) (L-1)` bound by the existing recurrence.  The second direct
attempt passed after representation-only orientation rewrites; the targeted
module built `3311/3311`; both declaration audits report exactly `propext`,
`Classical.choice`, and `Quot.sound`.  C2 result SHA-256:
`98e6a8d2c30b7c8f6b9955cfbd7ee64eb3173aef12013e993deb69e1cc97272b`.

The independent read-only lane derived both proof ledgers before either source
was released, reread the final hashes, and found no hidden premise, direction
error, carrier change, target-equivalent shell, public-helper leak, or import
cycle.  Its proposal result SHA-256 is
`16bd379f5e9d1363cf886a61309b3f32baa1a199d1d7b4d15ae69a711287bb7f`.

**Net proof movement:** forward on exact subordinate obligations C1 and C2.
**Evidence:** three compiling Lean declarations, warning-clean direct gates,
targeted builds, standard-only axiom audits, and a separate proposal-level
source review.  **Difficulty displaced:** none into a premise; C4 is the sole
remaining subordinate H2 obligation.  The open count decreases from three
(`C1`, `C2`, `C4`) to one (`C4`).  **Counterfactual:** knowing these results
before the run removes the complete cyclic projection and local profile
construction from the remaining H2 proof.  **Planning consequence:** promote
`FP-15.C` to one separately approved C4 theorem gate.  H2's official
five-layer count and every load-bearing exact-conjecture edge remain unchanged
until that composition theorem lands.

The root integration gate then passed `10301/10301` Lean jobs, all 107 unit
tests, and every deterministic certificate check under the guarded resource
policy.
