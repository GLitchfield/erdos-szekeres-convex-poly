---
title: Prove the HMPT adjacent-spike C3 gluing theorem
type: research
mode: AFK
status: closed
claim: codex-hmpt-h2-c3-land-2026-08-17
blocked_by: none
---

# Ticket 0025: prove the HMPT adjacent-spike C3 gluing theorem

## Question

Do the compiled HMPT vertical profiles and signed adjacent-pair transports imply
that the selected right chain in one spike and the selected left chain in the
next spike are jointly in convex position, without a supplied convexity
certificate, common `x2` anchor, additional profile premise, target subset, or
carrier change?

This is the exact C3 consumer checkpoint authorized after ticket 0024's
`HMPT-H2-PAIR-LAND`.  It does not authorize C1, C2, C4, a full cyclic HMPT
composition, or any change to the exact-conjecture dependency ledger.

## Decision criteria

The ticket succeeds only when the exact public theorem below compiles
warning-clean, its targeted module builds, and its declaration-only trust audit
contains only the standard permitted axioms.  Every `4+0`, `3+1`, `2+2`,
`1+3`, and `0+4` four-subset pattern must be discharged from the frozen raw
geometry and actual profile fields.  A supplied certificate, common anchor,
extra premise, relaxed/non-GP computation, or passing finite control does not
satisfy the ticket.

## Frozen theorem

The proof-producing slot owns only
`ErdosSzekeres/HMPTAdjacentSpikeGluing.lean` and must export exactly one public
mathematical declaration:

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

Binder order, implicitness, line breaking, and private helper organization may
vary.  The hypotheses and conclusion may not change.  A private two-anchor
same-cell certificate is permitted only as an internal proof device; it may
not become a public premise or public declaration in this packet.

## Proof architecture

The proof must consume the actual selected maximum chains from the two
profiles.

1. Decode membership in `hmptChainPoints` and orient every distinct selected
   pair using the maximum-chain fields and the strict HMPT order.
2. Apply the compiled `leftPair_orientation_neg` and
   `rightPair_orientation_pos` theorems, reversing pairs when necessary.
3. Derive private line-arrangement-cell replacement from pairwise
   `SameStrictSide` facts.
4. Close `3+1` left subsets by replacing the actual cap anchor `x3` with a
   right-chain point; close reflected `1+3` subsets at `x1`.
5. Close `2+2` subsets by strict support in both opposite-pair directions and
   `inConvexPosition_four_of_opposite_pair_supports`.
6. Inherit `4+0` and `0+4` subsets from the corresponding profile caps.
7. Apply `inConvexPosition_iff_four_subsets` to the whole selected union.

The proof may reuse lower-level project and mathlib geometry and private
helpers proved in the owned module.  It may not assume a common `x2` cap,
supplied same-cell/support/convex-union certificate, supplied branch choice,
extra maximum or cardinality premise, changed carrier, transformed geometry,
or target-equivalent statement.

## Independent controls

The information-gathering slot freezes two deterministic, independently
implemented exact-rational evaluators before either outcome is opened.  A
positive fixture must be genuinely in general position, satisfy the complete
raw adjacent geometry and both complete `HMPTVerticalProfile` premises, and
have at least three selected points on each side.  It must exercise every
mixed-four-subset pattern `4+0`, `3+1`, `2+2`, `1+3`, and `0+4`, plus an affine
image.

Negative controls separately reject at least: broken five-anchor signs,
support-region escape on either side, joint-GP failure, pool overlap,
nonmaximum selected chain, reversed vertical order, common-`x2` substitution,
omitted `3+1` checking, and omitted `2+2` checking.  A bounded rational search
must also look for a fully admitted input whose selected union is nonconvex.

A computed witness is a falsifier candidate only until the orchestrator
kernel-encodes it against the frozen theorem.  A green finite suite is search
information, not theorem evidence.

## Resources and gates

- One proof-producing slot and one information-gathering slot; both belong to
  the HMPT mechanism family because this is a bounded theorem/falsifier test at
  a serial cut vertex.
- Proof hard-obligation budget: four active hours.
- Direct Lean, targeted build, and axiom-audit commands: 30 minutes, 12 GiB
  aggregate RSS, and one Lean process each; all builders are serialized.
- At most four localized direct-file attempts total.  A mathematical
  diagnostic or contract defect stops the proof lane.
- Each control evaluator: 30 minutes, four CPU cores, 8 GiB, and 0.25 GiB
  output.  Neither output may be inspected before both commands terminate.
- LAND requires a warning-clean direct file gate, targeted module build,
  static contract/style checks, and a declaration-only audit containing only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Repository integration additionally requires a guarded full `make test`,
  serial Wayfinder reconciliation, exact staging, commit, and push.

## Frozen outcomes

- `HMPT-H2-C3-LAND`: the exact theorem compiles and passes all trust gates.
- `HMPT-H2-C3-FALSIFIED`: an admitted exact Euclidean GP fixture is
  kernel-encoded and refutes the theorem.
- `HMPT-H2-C3-GAP`: an unchanged profile/raw field does not imply a required
  mixed-four-subset fact.
- `HMPT-H2-C3-INERT`: only a supplied certificate, common anchor, or
  target-equivalent shell closes the proof.
- `HMPT-H2-C3-CONTROL-MISMATCH`: the frozen evaluators disagree or a required
  positive/corruption is invalid.
- `HMPT-H2-C3-RESOURCE`: a bounded lane stops without trustworthy
  classification.

Every non-LAND terminal stops integration and returns to frontier
reconciliation.  A control mismatch is never repaired or promoted after the
outcome is opened without a new user-approved packet.

## Evidence

Ticket 0024's independent proof audits and bounded Sol/Fable review derive the
C3 proof graph.  The compiled
`HMPTAdjacentSpikeGeometry.leftPair_orientation_neg` and
`HMPTAdjacentSpikeGeometry.rightPair_orientation_pos` theorems now close its
two raw signed-pair inputs; both passed warning-clean direct elaboration,
targeted build, and standard-only axiom audits.  The prior exact-rational lane
also found no pair-sign falsifier, but that finite evidence is neutral and does
not establish this union theorem.

## Proof-distance contract

Before this run, C1, C2, C3, and C4 are the four open subordinate H2
obligations; the signed-pair subobligation of C3 is already closed.  A LAND
result closes C3, strictly decreasing that subordinate measure from four to
three open obligations (`C1`, `C2`, `C4`) without adding a premise.

The overall HMPT finite-layer count remains five until the whole H2 layer
lands.  C3 alone changes no load-bearing edge in `docs/wayfinder/map.md` and
does not close `D-HALF`, `D-DECOMP`, or `D-NORMALIZE`.  Controls alone are
neutral search information.

## Resolution

Closed with outcome `HMPT-H2-C3-LAND`.

`HMPTAdjacentSpikeGeometry.right_left_union_convex` compiles warning-clean in
`ErdosSzekeres/HMPTAdjacentSpikeGluing.lean`.  Its first direct gate passed in
46 seconds, the targeted module build passed `3311/3311`, and its
declaration-only audit reports exactly `propext`, `Classical.choice`, and
`Quot.sound`.  The theorem consumes the actual profile chains and compiled
signed-pair transports, closes every frozen mixed-four-subset pattern, and
introduces no public helper, certificate, common anchor, target, carrier
change, or added premise.  Proof result SHA-256:
`f41915978060e673715b023e6ca1712b7c7693e90db38e006fc45e55b545a0bd`.

The independent lane closed with `HMPT-H2-C3-CONTROLS-PASS`.  Two exact
rational evaluators admitted the base and affine-image `4+4` profiles, rejected
all ten frozen corruptions, agreed on all 467,963 fully admitted bounded
unions, and found no nonconvex candidate.  This is computational evidence only.
Control result SHA-256:
`04b815a069dfa71ee3c68d2b541a865ac080d6e2ade1fd342b268bd28a49db2f`.

**Net proof movement:** forward on the exact C3 obligation.  **Evidence:** a
compiling theorem with warning-clean direct/targeted gates and a standard-only
axiom audit; checked controls are separate neutral search information.
**Difficulty displaced:** none into a premise.  The complete adjacent gluing
consumer is closed, leaving distinct C1, C2, and C4 obligations.  The
subordinate H2 open-obligation count strictly decreases from four to three.
**Counterfactual:** knowing this result before the run removes all C3
mixed-four-subset geometry and finite branch bookkeeping, materially reducing
the remaining H2 proof work.  **Planning consequence:** retain `FP-15.C` as
gated, mark C3 complete, and reconcile C1 and C2 before selecting another
slate; C4 stays blocked on their producers.

The official HMPT finite-layer count remains five until all of H2 lands.  No
load-bearing edge in `docs/wayfinder/map.md` changes; `D-HALF`, `D-DECOMP`, and
`D-NORMALIZE` remain open.
