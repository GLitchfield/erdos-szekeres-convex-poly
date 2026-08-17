---
title: Repair the HMPT cyclic vertical-profile layer
type: research
mode: AFK
status: closed
claim: codex-hmpt-h2-preflight-control-mismatch-2026-08-16
blocked_by: none
---

# Ticket 0023: repair the HMPT cyclic vertical-profile layer

## Question

Can the source-faithful H2 layer of `FP-15.C` be proved from arbitrary
`PorValtrSupportProductData P r` at the sharp valid endpoint `3 <= r`, without
supplied colorings, maxima, support certificates, cardinal inequalities,
changed anchors, a linearized index family, or a changed carrier?

The first H2 packet is expired by the kernel theorem
`HMPTCyclicSourceCounterexample.frozenContract_false`: at `r = 2`, a required
five-anchor cyclic window over four anchors repeats an endpoint. The compiled
point-set producer `exists_porValtrSupportProductData` already assumes
`3 <= r`, so the repaired endpoint does not strengthen any reachable source
instance. This observation is search information only and does not close H2.

## Review and interface disposition

A fresh bounded Sol/Fable review completed over the repaired proposal. Both
reviewers rated it `partially_supported`. They agree that `3 <= r` removes
exactly the known collision and preserves the original carrier, cyclic wrap,
and distinct outer-anchor obligations. They require two corrections before
proof implementation:

1. test the closest boundary analogue of the old failure, an admitted
   all-empty-pool `r = 3` support-product datum on six strict-cap anchors; and
2. make the local-profile order and anchor bridges explicit rather than saying
   that the existing Suk recurrence applies directly.

The repository audit resolves the second point precisely.
`SukRegionGeometry.toHMPTSpikeOrderPair` is public and supplies the H1 order
pair. The equivalence between strict HMPT vertical order and reverse
`SukRegionLT` is private, and the compiled Suk two-color semantics uses the
inner anchors, whereas H2's maximum subchains are extended by the two outer
anchors. The C2 worker must therefore rederive the strict reversal and prove
new outer-anchor color semantics from raw geometry. These are proof
obligations, not new hypotheses.

Review packet SHA-256:
`630e9e7437c52fcb254d45321629f1a7a07f028f937634edb16962478e2f0631`.
Report SHA-256:
`6585e1e0fe6a253db3ec3739b1a6d2204e63b710af9ab9907182b87bbbae927a`.

## Decision criteria

The ticket succeeds only when C1--C4 below all compile from the unchanged
source interfaces after both independent control suites pass. Any proper
subset, declaration smoke test, control outcome, or corrected endpoint alone
is neutral. No supplied or target-equivalent premise may replace a listed
obligation.

## Candidate public contracts

These mathematical statements are fixed by this ticket. Before worker task
packets are frozen, their exact Unicode Lean forms must pass a declaration-only
elaboration smoke test. Binder order and private representations may change
only before that freeze; the mathematical inputs and outputs may not.

### C1: cyclic source projection

```lean
theorem PorValtrSupportProductData.toHMPTCyclicSpikeGeometry
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r)
    (hr : 3 ≤ r)
    (hgp : InGeneralPosition P) :
    HMPTCyclicSpikeGeometry P r h
```

The proof must derive all fields of the unchanged structure, including cell
zero and the last-to-first adjacent window. Wrapped five-anchor signs must
come only from `h.strictCap`, `h.periodic`, orientation identities, and the
arithmetic `6 <= 2*r`; no cyclic-sign premise may be added.

### C2: local vertical profile

```lean
theorem SukRegionGeometry.hmptVerticalTransitiveColoring
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s) :
    HMPTVerticalTransitiveColoring outerLeft outerRight
      (hmptVerticalTripleColor (s := s))

theorem SukRegionGeometry.exists_hmptVerticalProfile
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s) :
    Nonempty (HMPTVerticalProfile
      outerLeft rightAnchor leftAnchor outerRight s)
```

The source must construct the H1 maximum vertical/horizontal chains, actual
cardinality-maximum outer-left/outer-right anchored subchains, and the exact
binomial inequality. Mandatory private bridges are:

- strict HMPT vertical order iff reverse `SukRegionLT` on pool points;
- four-point transitivity for `hmptVerticalTripleColor` in HMPT direction;
- negative triples extend to `outerRight` and positive triples extend to
  `outerLeft`, with the converse under GP; and
- reversal of the vertical chain into the existing finite transitive
  cup/cap theorem without changing the selected point finsets.

Under failure of the desired binomial bound, invoke the recurrence with
successor sizes `rightChain.card + 1` and `leftChain.card + 1`; either output
contradicts the corresponding maximum. Vertical-chain cardinalities zero,
one, and two are separate mandatory branches. No order, coloring, chain,
maximum, or inequality is an input.

### C3: distinct-outer-anchor adjacent gluing

```lean
theorem HMPTAdjacentSpikeGeometry.right_left_union_convex
    (h : HMPTAdjacentSpikeGeometry
      x0 x1 x2 x3 x4 leftPool rightPool)
    (leftProfile : HMPTVerticalProfile x0 x1 x2 x3 leftPool)
    (rightProfile : HMPTVerticalProfile x1 x2 x3 x4 rightPool) :
    InConvexPosition
      (hmptChainPoints leftProfile.rightChain ∪
        hmptChainPoints rightProfile.leftChain)
```

The selected chains are extended by the distinct outer anchors `x3` and
`x1`. The proof must derive both `3+1` replacement directions and the `2+2`
opposite-pair support case from raw adjacent geometry and the two produced
anchored-chain facts. The common `x2` theorem is not a substitute, and no
support certificate or convex-union conclusion may be supplied.

### C4: cyclic no-target consumer

```lean
theorem PorValtrSupportProductData.exists_hmptCyclicProfiles
    {P : Finset (Point 2)} {r n : ℕ}
    (h : PorValtrSupportProductData P r)
    (hr : 3 ≤ r)
    (hgp : InGeneralPosition P)
    (hno : ¬ ContainsConvexSubset P n) :
    ∃ profile : ∀ i : Fin (2 * r),
        HMPTVerticalProfile
          (h.hmptAnchor i 0) (h.hmptAnchor i 1)
          (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i),
      ∀ i : Fin (2 * r),
        (profile i).rightChain.card +
          (profile (hmptCyclicSucc i)).leftChain.card < n
```

C4 may be implemented only after C1--C3 pass. It must prove the successor
window-alignment equalities, use C3 at every cyclic index, obtain exact union
cardinality from pool disjointness, transport all points into the original
carrier `P`, and take an exact `n`-subset when the sum is at least `n`.

## Preflight gate before proof workers

The approved execution must stop before proof implementation unless all of
the following pass:

1. **Declaration smoke:** elaborate the exact four contract families in an
   owned run-only file, without `sorry`, `admit`, an axiom, or a shared-source
   edit. This checks only their types and freezes the resulting text.
2. **Boundary source control:** independently verify an exact-rational
   `r = 3` six-anchor `PorValtrSupportProductData` fixture with every pool
   empty, then check every field expected of `HMPTCyclicSpikeGeometry`, all
   six five-anchor windows, cell zero, and the wrap pair.
3. **Nondegenerate controls:** independently check a nonempty adjacent-pool
   fixture, both vertical colors, exhaustive maximum anchored subchains, the
   exact binomial inequality, both `3+1` directions, the `2+2` case, and the
   cyclic no-target cardinality reconstruction.
4. **Corruptions:** reject `r = 2`, a repeated anchor, one wrapped-sign flip,
   omitted cell zero, omitted wrap pair, vertical reversal, outer-anchor swap,
   common-`x2` substitution, region escape, GP boundary, disjointness loss,
   nonmaximum subchain, altered ambient carrier, and a broken successor-window
   alignment.

Use independently implemented exact-rational producer and checker programs,
freeze both before either outcome, and inspect neither output until both
terminate. Successful controls are an explicit condition of `LAND`; they are
checked evidence, not proof movement.

## Execution slate

After green preflight controls, freeze all worker packets at one exact
HEAD/fingerprint and use three proof-producing slots plus one
information-gathering/orchestration slot:

1. C1 in `ErdosSzekeres/HMPTCyclicSpikeProducer.lean`;
2. C2 in `ErdosSzekeres/HMPTVerticalProfileProducer.lean`;
3. C3 in `ErdosSzekeres/HMPTAdjacentSpikeGluing.lean`;
4. root-owned controls, evidence admission, serialized builder lane, C4 in
   `ErdosSzekeres/HMPTCyclicNoTarget.lean`, and integration.

C1--C3 mathematical source work may overlap after preflight because their
public inputs are already compiled and their write sets are disjoint. All
Lean/Lake commands, C4, umbrella edits, full tests, Wayfinder reconciliation,
commit, and push are serial root operations. All four slots intentionally
belong to the same quantitative-cup-cap mechanism family: H2 is a serial cut
vertex, so this concentration is not evidence of independent route risk.

## Outcome and stop gates

- `HMPT-H2-REPAIR-LAND`: both independent control suites are green; C1--C4
  compile warning-clean; each module's targeted build and declaration audit
  passes with only standard axioms; the full repository test passes; H2's
  finite-layer count changes five to four.
- `HMPT-H2-REPAIR-GAP`: an unchanged source or local-geometry premise cannot
  produce a mandatory C1--C4 field without strengthening the contract.
- `HMPT-H2-REPAIR-FALSIFIED`: an admitted exact `r >= 3` Euclidean fixture
  refutes any C1--C4 public statement.
- `HMPT-H2-REPAIR-INERT`: only a supplied-color, supplied-maximum,
  common-anchor, linear-no-wrap, changed-carrier, or target-equivalent shell
  compiles.
- `HMPT-H2-REPAIR-RESOURCE`: a bounded branch reaches four localized direct
  attempts, four active proof hours, or its process/output cap without a
  mathematical outcome.

A failure in any preflight gate stops all proof workers. A C1--C3 terminal
stops C4. No post-outcome semantic repair or theorem-contract change is
authorized without a new review and user decision.

## Resource and approval inventory

- Declaration smoke and every Lean/Lake command: 1,800 seconds, one Lean
  process, 12 GiB aggregate RSS, through `scripts/run_lean_guarded.py`.
- Each control process: 10 minutes, at most four CPU cores, 8 GiB RAM, and
  0.25 GiB aggregate owned output.
- Each theorem module: warning-clean direct check, targeted module build,
  static forbidden/style check, and declaration-only axiom audit. Accept only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Integration: one full `make test`, then a commit and push of only intended
  source, umbrella, ticket, map, portfolio, README, and literature-ledger
  changes.

No network retrieval, provider review, software installation, destructive
operation, resource-limit increase, or process termination is planned. The
bounded adversarial review has already run. Future user approval authorizes
the mathematical slate but does not bypass any platform prompt for guarded
execution or the final push.

## Forecast and proof-distance accounting

The calibrated routine Lean/build history is fast, but C2's new outer-anchor
semantics and C3's distinct-anchor `3+1`/`2+2` geometry are structurally novel.
Forecast 5--10 elapsed hours with parallel C1--C3 source work and serialized
builders, or roughly 12--24 proof-worker hours in aggregate. The upper half
is intentionally uncalibrated around C3.

**Net proof movement at planning:** neutral. **Evidence:** kernel-checked
counterexample to the old packet, static source/interface audit, primary-source
authentication, and advisory review. **Difficulty displaced:** none; all
four repaired H2 obligations remain. **Counterfactual:** the review and
boundary control prevent another false packet and expose the true C2 bridge,
but do not reduce the H2 proof until all four declarations compile.
**Planning consequence:** retain `FP-15.C` as gated and execute only after
explicit user approval. Any proper subset of C1--C4 is neutral. Complete
`LAND` is forward within `FP-15.C` because the predeclared open-layer count
decreases from five to four; no load-bearing exact-conjecture ledger edge
changes.

## Resolution

Closed at the mandatory preflight boundary with
`HMPT-H2-REPAIR-PREFLIGHT-CONTROL-MISMATCH`.  The exact C1--C4 proposition
families passed their declaration smoke.  Two independently authored
exact-rational evaluators then agreed on the same truth vector and the same
canonical semantic projection.  Both accepted the all-empty-pool `r = 3`
source, the nonempty cyclic source and wrap reconstruction, the complete C3
`3+1`/`2+2` tables and all 35 four-subsets, the maximum-chain arithmetic, and
all fourteen named corruptions.

The proposed local C2/C3 positive fixture was nevertheless inadmissible:
`(p0,p3,p4)` and `(p1,p2,p5)` are collinear.  Consequently its two C2 gates
fail the required general-position premise in both evaluators.  This is not a
counterexample to either C2 theorem, because the frozen theorem input includes
general position through `SukRegionGeometry`.  It is also not a successful
control, so the predeclared stop prevented every C1--C4 proof worker from
starting.  No post-outcome perturbation or rerun was made.

**Net proof movement:** neutral.  **Evidence:** checked computation and a
compiling proposition-only declaration smoke; no C1--C4 proof theorem.
**Difficulty displaced:** none; all four corrected H2 obligations remain.
**Counterfactual:** prior knowledge of the two collinear triples would have
prevented this slate but would not have shortened the H2 proof.  **Planning
consequence:** retain `FP-15.C` as gated, close this packet, and count ticket
0022 plus ticket 0023 as two consecutive negative/information-only outcomes in
the H2 mechanism family.  A fresh adversarial route review is mandatory before
any replacement fixture or further H2 refinement is scheduled.  The finite
open-layer count remains five and no load-bearing destination edge changes.

## Evidence

- Kernel counterexample and expired packet:
  `ErdosSzekeres/HMPTCyclicSpikeGeometry.lean` and ticket 0022.
- Compiled source and H1 interfaces: `PorValtrSupportProduct.lean`,
  `HMPTSpikeOrderGeometry.lean`, `HMPTSpikeOrderConsumer.lean`, and
  `HMPTVerticalChainDefs.lean`.
- Primary-source authentication:
  `runs/literature/20260816-hmpt-h2-auth/source-authentication.md`.
- Repaired review proposal and advisory report:
  `runs/reviews/20260816-hmpt-h2-repair-plan/`.
- Declaration smoke and independent frozen controls:
  `runs/agents/20260816-hmpt-h2-repair-slate/`; control result SHA-256
  `dc70707d35d291f8447ac201d7c6f200b6196488dbb72865d0c2a8c622c32e69`,
  evaluator outputs `9647fabd...ae3af27` and `03fefe4c...aa5b70`, and
  comparison `f85b83d5...f12d0`.
