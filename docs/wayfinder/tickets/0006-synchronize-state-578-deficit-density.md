---
title: Synchronize the state-578 deficit column with full residual density
type: research
mode: AFK
status: open
claim: codex-state-578-deficit-density-sync-2026-08-09
blocked_by: none
---

## Question

Can the full six-column residual matrix and exact `32/23` density eliminate
the source-disjoint and lower-local deletion escapes, or synchronize the five
entries missing one cap blocker with every blocker-avoiding residual four-cup
strongly enough to force a target or a four-cup transversal of size at most
nine?

## Frozen inputs

- `deletionEscape_or_fiveDeficitDensityCoupling_at_32`;
- `exists_fiveDeficitColumn` and the exact five-row entry set;
- the two blocker-avoiding density cups with disjoint sweep-middle pairs;
- the full residual-cup/six-cap address matrix and its common minimum;
- the exact `32/23` residual escape and restricted-transversal lower bounds;
- the relaxed 32-vertex incidence/address countermodel; and
- the exact 13-vertex no-two-cover counterexample for five local deficit rows.

## Decision criteria

- Treat source-disjoint, lower-local, and concentrated-deficit outcomes as
  explicit branches; do not assume the fan constructor's `hbase` or `hmeet`
  premises globally.
- After selecting the deficit blocker, the consumer must still use another
  cap column or quantify over the full residual family. A theorem inherited
  by the exact 13-vertex five-row model is already false.
- A synchronization statement must name the selected fan rows and the density
  witnesses and prove their claimed equality, incidence, endpoint, or address
  relation. Shared cardinality or blocker avoidance alone is insufficient.
- A transversal conclusion must state the actual finite set, prove it meets
  every ambient four-cup, and prove its cardinality is at most nine.
- Run a bounded relaxed falsifier before any large Lean proof. Computation and
  agent review are advisory until promoted to a compiling theorem or an
  independently checked certificate with its exact limitations.
- Expire the concentrated-deficit route if the next consumer inspects only
  the five selected rows, or if an exact target-free model retains the claimed
  full-family/cross-column synchronization.

## Candidate outcomes

1. A compiling cross-family synchronization closes the tight state-578
   branch.
2. A compiling theorem eliminates at least one of the three total reconnect
   branches and leaves one named global capacity obstruction.
3. An exact countermodel retaining the proposed full synchronization refutes
   the route; preserve the six-column arithmetic as infrastructure and select
   a different invariant.

## Resolution

Open. Experiment 0077 proves the six-column deficit concentration and the
exact total deletion-branch reconnect. It also proves that the first local
two-cover bridge is false. The active target must couple selected fan rows to
the full residual family without discarding the other five cap columns.

## Evidence

- `docs/experiments/0077-state-578-exterior-density-coupling.md`
- `ErdosSzekeres/StructuralChargingNextState578ExteriorDensity.lean`
- `ErdosSzekeres/StructuralChargingNextState578ExteriorDensityCounterexample.lean`
