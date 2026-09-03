---
title: Select the next common-anchor actual placement case
type: research
mode: HITL
status: closed
claim: gap04-source-incubation-lsp-clean-neutral-2026-09-01
blocked_by: none
---

# Ticket 0122: select the next common-anchor actual placement case

## Question

After placement `03` became an LSP-clean source candidate, which of the six
remaining actual router cases has the best combination of exact theorem
readiness, unavoidable consumer value, and low proof risk?

## Decision criteria

1. Require a complete five-field theorem-entry memo and exact actual-order
   proof plan; a symbolic dual is insufficient.
2. Prefer a premise-minimal case whose successful source elaboration strictly
   reduces the frozen actual-placement inventory.
3. Rank unavoidable representative value, direct reuse of existing APIs, and
   hostile-neighbor discrimination ahead of parallel lane occupancy.
4. Preserve mechanism correlation and select no more than one source lane
   unless a second candidate has a mathematically independent gate.
5. Authorize no project build, test, service action, premise repair, ambient
   reflection, or change to computational evidence during source incubation.

## Selection method

Root froze one current source snapshot and ran three read-only audits in
parallel.  They partitioned contradictions `04` and `13/14` from dual
transports `23/24/34`.  This was one correlated `FP-01` selection audit, not
three independent proof routes or execution slots.  Root separately checked
the current router contract and source declaration inventory.  No route was
added, retired, promoted, revived, or materially redirected, so a new
Sol/Fable route review was not required.

The frozen snapshot SHA-256 is
`e692e78d50ca384b20f5c59c58280389b34107dee9bde0e64e94ea6d109edc6b`.
All three workers authenticated source SHA-256
`55c06639193c2affa12b71626ac79a79d37f09f9777458268f3d0d305de2e2a4`
before and after their analysis.

## Evidence

### Placement `04`

The report
`runs/agents/20260901-ticket0122-next-case-selection/gap04-entry-review.md`,
SHA-256
`b7be1995b1f841223ca5ed2fffb9eb54ba89e6951500a94cc0b04fd9baa3d0e3`,
returns `GAP04-THEOREM-ENTRY-COMPLETE`.  Under the literal exterior order

```text
o < e 0 < e 1 < e 2 < e 3 < p,
```

the two strong-owner hypotheses supply ten middle-determination reductions.
Every actual cross quadruple has the same order shape, and its edge predicate
is exactly `P i ∧ P j`.  The existing
`not_perfectMatching_activeClique` rejects a perfect matching.  The contract
needs only `o < e 0`, `e 3 < p`, and the two strong-owner hypotheses; it needs
no `OneChangeOn`, color premise, matching normal form, or ambient reflection.

### Placements `13` and `14`

The report
`runs/agents/20260901-ticket0122-next-case-selection/gap13-14-entry-review.md`,
SHA-256
`dce09ee7662dc58486c1cae3ea708075194393c4b8990cefa5202b6119b31d4d`,
returns `GAP13-THEOREM-ENTRY-COMPLETE`.  Both placements have the active-clique
factorization, and the audit recommends `13` over `14` because it reuses the
literal gap-`12` and gap-`03` reductions and has placement `12` as the sharp
neighboring failure.  It nevertheless requires four literal internal-gap
inequalities and more finite-set order shapes than `04`.  Retain it as the
next contradiction reserve; do not schedule it beside `04` merely to fill a
lane.

### Dual transports `23`, `24`, and `34`

The report
`runs/agents/20260901-ticket0122-next-case-selection/dual-transport-entry-review.md`,
SHA-256
`343e89360120b725ca1304b2fbe8f25479965cbb96ce78db705eb0e88fbf3870`,
returns `GAP24-THEOREM-ENTRY-COMPLETE`.  Placement `24` is the cheapest dual:
three placement inequalities, ten middle-determination reductions, two actual
ambient-order `TurnSequenceAllowed` words, and a proposition-only reversal
relabeling into `perfectMatching_middleGap_eqTail_pattern`.  It is qualified
but strictly more semantically exposed than `04`; `23` and `34` are larger.
No ambient order embedding is reversed.

## Resolution

Select exactly one source-incubation lane:

```lean
/-- Owners in the two exterior sweep gaps `04` cannot induce a perfect cross
matching on the ordered four-base. -/
theorem not_perfectCrossMatching_gap04
    {n : ℕ} {χ : TripleColoring n} (e : Fin 4 ↪o Fin n) {o p : Fin n}
    (ho0 : o < e 0) (h3p : e 3 < p)
    (ho : IsStrongPolygonSet χ (insert o (Finset.univ.image e)))
    (hp : IsStrongPolygonSet χ (insert p (Finset.univ.image e))) :
    ¬ IsPerfectCrossMatching χ e o p
```

The exact proof packet must use the ten reductions and six edge equivalences
in the authenticated placement-`04` report and close only with
`not_perfectMatching_activeClique`.  It may not add `OneChangeOn`, use a
symbolic reflection as an ambient transport, change any existing theorem, or
touch computational evidence.

Placement `04` wins the calibrated comparison because it is self-dual and
therefore an unavoidable representative, has the smallest hypothesis/order
surface, and uses exactly the API already exercised by the LSP-clean placement
`03` candidate.  Placement `13` and transport `24` remain qualified reserves;
portfolio membership and state do not change.

## Theorem-entry memo

1. **Producer, tier, and hypotheses:** the exact theorem above, at the
   abstract ordered-`TripleColoring` tier, under only the two exterior order
   inequalities and two strong-owner sets.
2. **Existing named consumer:** immediate consumer
   `not_perfectMatching_activeClique`; router-level consumer
   `perfectCrossMatching_same_of_commonOwner`; then the named common-anchor
   closure consumed by `fin15_commonAnchor_multiOwner_adaptiveDoubleErase`.
3. **Strict separation:** successful source elaboration changes the
   contradiction-source deficit `3 → 2` and total actual-placement source
   deficit `6 → 5`, without moving the obligation into a new premise.  It does
   not by itself close the router or a load-bearing edge.
4. **Hostile neighboring world:** placement `03` changes the ordered shapes
   but preserves the clique, while placement `02` is the nearest genuine
   failure: its edge `23` is only `z2 = z3`, and the existing transport permits
   an `M0` matching.  The theorem may not cross the `e 2 < p` boundary.
5. **Producing fact:** middle determination in each strong owner-plus-base set
   identifies the two endpoint statuses of every uniformly ordered cross
   quadruple, so edge `ij` is exactly `P i ∧ P j`.

## Frozen execution packet

The temporary slate has **zero proof-producing** and **one information-
gathering** slot.  It is source incubation because this packet does not
authorize the project proof gate.

| Lane | Exact gate | Budget, stops, and downstream outcome |
| --- | --- | --- |
| `C013-DHALF-GAP04-SOURCE-V1` | Add exactly `not_perfectCrossMatching_gap04` to `StrongCommonAnchorMultiOwner.lean`, then check only its declaration region with one Lean language server. | Root-owned; calibrated 15 minutes, hard stop 30 minutes; one interactive Lean server; no Make/Lake command, project build, repository test, solver, provider, service, network, or Git. `LSP-CLEAN` preserves an unadmitted source candidate and changes the source inventory `6 → 5`; an edge-rewrite/API mismatch stops without premise repair; frozen-input drift stops operationally. |

No advancing high-leverage portfolio entry is deliberately deferred because
none is in state `advancing`.  Parallel source execution is not selected: all
three qualified candidates are one correlated mechanism family, and `04` has
strictly lower proof risk.  Spare capacity remains unused rather than padding
the slate.  A later guarded build should wait for a coherent router package,
not run after this single local case.

## Proof-distance accounting

- **Net proof movement:** `neutral`.
- **Evidence:** three authenticated theorem-entry proposals and a root source/
  consumer comparison; no Lean theorem or checked computation from this
  selection step.
- **Damage scope:** `candidate-local` scope ceilings only; no mathematical
  negative or damage is admitted.
- **Difficulty displaced:** none yet.  The selected execution can reduce only
  the unadmitted source inventory; the router, closure, adaptive consumer,
  full-context successor, guarded admission, and uniform `D-HALF` tail remain.
- **Counterfactual test:** the comparison changes allocation by avoiding a
  larger dual transport and an unnecessary second contradiction lane.  It does
  not reduce admitted destination proof depth.
- **Planning consequence:** retain `FP-01` and `FP-03` as `gated`; select only
  `C013-DHALF-GAP04-SOURCE-V1`; retain `13` and `24` as qualified, unselected
  reserves; await explicit execution approval.
- **Load-bearing ledger edge changed:** none.

No failure genome is created.  The audits used 3 minutes 16 seconds, 4 minutes
47 seconds, and 5 minutes 46 seconds of packet-to-report wall time
respectively.  CPU time and peak RSS were not instrumented.  The scheduler and
continuous idea generator were not inspected or changed.

## Execution reconciliation

The user approved `C013-DHALF-GAP04-SOURCE-V1`, and root executed only that
frozen lane.  Source SHA-256
`00fbe8f26e0e83370a7a05abeef6542293b742f1f211bb8a5b87c274424bc728`
contains the exact theorem `not_perfectCrossMatching_gap04`.  Ten strong-owner
middle-determination reductions make the six actual edges the active-clique
factorization, and `not_perfectMatching_activeClique` closes the declaration.
The Lean language server returned success with zero diagnostics on the first
pass.  The terminal report is
`runs/agents/20260901-ticket0122-next-case-selection/gap04-source-result.md`,
SHA-256
`e1ddd1b40e38e17ea0f1c7295a5198c3f392e262c4ec3abf4babd549d823b8a8`.

- **Net proof movement:** `neutral`.
- **Evidence:** LSP-clean Lean source candidate, classified as `proposal`
  because no guarded project build reached it.
- **Damage scope:** `candidate-local` scope ceiling only; no negative damage.
- **Difficulty displaced:** the source-only contradiction deficit decreases
  `3 → 2`, and the total actual-placement source deficit decreases `6 → 5`;
  no admitted load-bearing obligation changes.
- **Counterfactual test:** the result removes one unavoidable self-dual source
  leaf and rules out premise repair for placement `04`, but without router
  composition and a guarded project gate it does not reduce admitted
  destination proof depth.
- **Planning consequence:** retain `FP-01` and `FP-03` as `gated`; preserve the
  exact candidate; reconcile before selecting among qualified reserve `13`,
  qualified dual transport `24`, or the remaining actual cases; do not retry a
  project build merely for this theorem.
- **Load-bearing ledger edge changed:** none.

The source lane used 1 minute 20 seconds of wall time and one interactive Lean
server.  CPU time and peak RSS were not instrumented.  No Make/Lake command,
repository test, scheduler action, or idea-generator action ran.  No failure
genome is created.
