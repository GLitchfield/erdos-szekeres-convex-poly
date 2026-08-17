---
title: Prove the HMPT cyclic no-target consumer
type: research
mode: AFK
status: closed
claim: codex-hmpt-h2-c4-land-2026-08-17
blocked_by: none
---

# Ticket 0027: prove the HMPT cyclic no-target consumer

## Question

Can the exact cyclic H2 consumer be proved from the compiled C1 source
geometry, C2 profiles, and C3 adjacent gluing theorem without accepting a
profile, desired inequality, target subset, changed carrier, or weakened wrap
condition as an input?

Ticket 0026 closed the C1 and C2 producers, while ticket 0025 already closed
C3.  The unchanged C4 theorem is therefore the sole subordinate H2
obligation.  This ticket authorizes only that theorem and its serial
integration; it does not authorize H3 or any exact-conjecture claim.

## Frozen public contract

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

The mathematical statement, carrier, anchor convention, and hypotheses are
frozen.  Only binder implicitness, line wrapping, and private helper
organization may vary.

## Decision criteria

Accept C4 only if the exact frozen declaration compiles warning-clean, its
targeted module builds, its public surface and trust boundary pass static
review, its declaration-only audit reports only the three permitted standard
axioms, an independent reviewer accepts the authenticated final source, and
the root-owned full repository gate passes.  A conditional shell, supplied
profile or inequality, changed carrier, lost cyclic wrap, or public transport
certificate is a non-LAND terminal rather than partial completion.

## Required proof graph

1. Construct `HMPTCyclicSpikeGeometry P r h` with the compiled C1 theorem.
2. Choose one C2 `HMPTVerticalProfile` from every local region.
3. Prove the four successor-anchor equalities privately, including the
   final-to-zero wrap, and transport the successor profile without changing
   its selected left chain.
4. Apply C3 at every cyclic index to the current right chain and successor
   left chain.
5. Use adjacent-pool disjointness and `hmptChainPoints_card` to identify the
   union cardinality with the displayed sum exactly.
6. Transport both selected chains into the original carrier `P`.
7. If the sum is at least `n`, select an exact `n`-subset of the convex union
   and contradict `hno` by convexity monotonicity.

No public successor certificate or new profile structure is permitted.  A
private duplicate of the already proved modular anchor calculation is allowed;
changing C1--C3 or strengthening their interfaces is not.

## Execution slate

- One proof-producing Lean kernel-engineer lane owns only
  `ErdosSzekeres/HMPTCyclicNoTarget.lean` and its ignored run artifacts.
- One information-gathering formal-review lane is read-only.  It derives the
  transport/cardinality ledger before inspecting the source-ready hash, then
  checks the exact statement, premise provenance, carrier, wrap, cardinality,
  circularity, and trust boundary.
- Root owns this ticket, all shared documentation and umbrella imports,
  serialized builders, the full test, staging, commit, and push.

Both slots intentionally concern one mechanism family because C4 is the
single serial cut vertex selected by the reconciled portfolio.  Innovation
review is skipped: this is mechanical implementation of the unchanged theorem
contract already reviewed in tickets 0023 and 0024.

## Outcome and stop gates

- `HMPT-H2-C4-LAND`: the exact theorem passes warning-clean direct, targeted
  module, static scope/style, standard-only axiom, independent review, and full
  repository gates.
- `HMPT-H2-C4-GAP`: a named compiled input cannot produce a mandatory field
  without a stronger premise or public-interface change.
- `HMPT-H2-C4-FALSIFIED`: an admitted exact `r >= 3` source kernel-refutes the
  frozen theorem.
- `HMPT-H2-C4-INERT`: only a supplied profile/inequality/target, carrier
  change, linear no-wrap replacement, or target-equivalent shell compiles.
- `HMPT-H2-C4-RESOURCE`: four direct attempts, four active proof hours, or a
  declared process/output cap expires without a mathematical classification.

Stop at the first non-LAND terminal.  Do not revise the theorem statement or
integrate a partial helper result after an outcome is known.

## Evidence

The compiled C1, C2, and C3 declarations provide every predecessor required by
the frozen graph.  The C4 candidate passed its first guarded direct check, its
targeted module build, and its declaration-only audit with exactly `propext`,
`Classical.choice`, and `Quot.sound`.  A read-only reviewer derived the cyclic
transport and cardinality ledger before source release and then accepted the
authenticated final source hash.  The root-owned full repository gate then
passed 10,302 Lean jobs, all 107 unit tests, and every deterministic
certificate check.

## Resource and approval inventory

Every Lean/Lake command runs through `scripts/run_lean_guarded.py` with an
1,800-second wall limit, one Lean process, and 12 GiB aggregate RSS.  Direct
elaboration, targeted build, declaration-only axiom audit, and the final full
`make test` are separate serialized commands.  Only `propext`,
`Classical.choice`, and `Quot.sound` are accepted.

No provider review, network retrieval, solver, installation, destructive
operation, resource increase, or process termination is planned.  The final
Git push is the sole external mutation and was explicitly included in the
approved slate.

## Proof-distance accounting

At admission the subordinate H2 measure is one open obligation, `{C4}`.  A
LAND result changes it to the empty set and decreases the official HMPT finite
layer count from five to four.  That is forward scoped proof movement because
the no-target inequalities are proved rather than supplied.  It does not by
itself change `D-HALF`, `D-DECOMP`, or `D-NORMALIZE`.  Any non-LAND result is
not forward proof movement and triggers route review rather than automatic C4
refinement.

## Resolution

Closed with outcome `HMPT-H2-C4-LAND`.

`PorValtrSupportProductData.exists_hmptCyclicProfiles` compiles warning-clean
in `ErdosSzekeres/HMPTCyclicNoTarget.lean`.  It constructs the C1 geometry,
chooses one compiled C2 profile in every local region, transports the same
successor profile through all four anchor equalities including final-to-zero
wrap, and applies C3 without changing its selected left chain.  Adjacent-pool
disjointness gives the displayed sum exactly; both selected chains remain in
the original carrier; and any failure of the strict bound supplies an exact
convex `n`-subset contradicting `hno`.

The first direct attempt passed warning-clean in 11 seconds, the targeted
module built `3324/3324`, and the declaration-only audit reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.  The final module SHA-256 is
`ffe8c0fc8b9f6762395ae363899c398a5b003137d6ca85bca84490bf4a7c38ce`.
The proof result SHA-256 is
`687b5abadd6cfd3b2ceddb48e26272b81f00b20b5f7205b862020a7e04b4bd69`.
The independent review result SHA-256 is
`93161827ffdccc5d31ea1c943da220d61059015d9d739f0b17cd7e23e46ba0ce`.
The final guarded repository gate passed `10302/10302` Lean jobs, all 107 unit
tests, and every deterministic certificate check.

**Net proof movement:** forward on exact subordinate obligation C4.
**Evidence:** a compiling Lean theorem, targeted build, standard-only axiom
audit, independent authenticated-source review, and full repository gate.
**Difficulty displaced:** none into a premise; the subordinate H2 set changes
from `{C4}` to empty, while the distinct H3--H6 layers remain.
**Counterfactual:** knowing this theorem before the run removes the last H2
obligation and reduces the formal route's finite-layer count from five to
four.  **Planning consequence:** mark H2 complete and gate `FP-15.C` on an
authenticated H3 statement plus bounded route review.  No load-bearing
`D-HALF`, `D-DECOMP`, or `D-NORMALIZE` edge changes.
