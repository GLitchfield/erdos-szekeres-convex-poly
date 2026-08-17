---
title: Formalize the HMPT point-set spike orders
type: research
mode: AFK
status: closed
claim: codex-hmpt-h1-2026-08-16
blocked_by: none
---

# Ticket 0021: formalize the HMPT point-set spike orders

## Question

Can the first point-set layer of the
Holmsen--Mojarrad--Pach--Tardos bound be derived from the compiling
`SukRegionGeometry` interface, and can its two produced partial orders be
consumed immediately to prove the exact finite product bound on one spike
pool?

This is the first layer `H1` of `FP-15.C`.  It is a route toward the published
`2^(n + O(sqrt(n*log n)))` upper bound, not toward the exact threshold unless a
separate theorem later connects it to a load-bearing exact dependency.

## Source decision

Outcome `HMPT-POINTSET-PAIR-AUTH` authenticates the current arXiv v3 and JEMS
source.  In Section 3, lines 359--377 of the primary TeX define on each spike
pool:

- a vertical strict order by containment of the two outer-anchor triangles;
- a horizontal strict order by intersection of crossed anchor-to-point
  segments; and
- exclusive comparability: every two distinct points satisfy exactly one of
  the four directed vertical or horizontal comparisons.

Lines 380--383 then apply Dilworth.  If `v_i` and `h_i` are maximum chain
sizes, the immediate conclusion is `|P_i| <= v_i*h_i`.  This local layer has
no asymptotic rounding.  The paper's proof reduces horizontal transitivity and
exclusive comparability to finite four- and five-point configurations, so the
statements are authenticated but the proof is not formal evidence.

Ordinary general-position Euclidean point sets are a literal specialization of
the source.  No pseudo-configuration, pseudoline, or transformed-carrier API is
needed for H1.

## Existing producer fields

`SukRegionGeometry outerLeft rightAnchor leftAnchor outerRight s` already
produces:

- the four strict-cap anchors;
- general position of the anchors and pool;
- membership of every pool point in the open support region; and
- the common strict side of the two outer anchors.

The compiled `SukRegionLE outerLeft outerRight` is the reverse of the source's
vertical triangle-containment relation.  Reversal preserves chain and
antichain cardinalities.  The missing geometric producer is therefore exactly
the horizontal crossed-segment partial order plus exclusive comparability.

## Decision criteria

### Frozen public contract

The proof-producing slate may adjust binder order and private representation,
but it must retain these mathematical declarations:

1. vertical and horizontal strict relations with their reflexive closures;
2. an `HMPTSpikeOrderPair` asserting both partial-order laws and exclusive
   comparability on the actual pool;
3. `SukRegionGeometry.toHMPTSpikeOrderPair`, with no supplied order or
   comparability hypothesis; and
4. `HMPTSpikeOrderPair.exists_maxChains_card_le_product`, producing actual
   maximum vertical and horizontal chains and
   `s.card <= verticalChain.card * horizontalChain.card`.

The consumer may use `finiteDilworth_chain_or_antichain`.  It may not assume a
maximum chain, a product inequality, a rich spike, a convex target, or any
later global coloring or gluing datum.

The full schematic signatures and source hashes are frozen under
`runs/literature/20260816-hmpt-pointset-auth/`.

### Proof-distance measure

`FP-15.C` has six finite layers:

- `H1`: the local two-order producer and product consumer;
- `H2`: vertical-chain coloring, binomial bound, and adjacent gluing;
- `H3`: horizontal-chain inner/outer coloring and binomial bound;
- `H4`: alternating gluing and global forbidden inequalities;
- `H5`: conservative exact global aggregation; and
- `H6`: the optimized exact-natural asymptotic wrapper.

At admission the open count is six.  Only compilation of both H1 public
theorems from the raw geometry, followed by standard-only declaration axiom
audits, decreases the count from six to five.  Definitions alone, an abstract
supplied-order object, only one order, controls, or prose are neutral.

### Predeclared outcomes for a later approved slate

- `HMPT-H1-LAND`: the exact point-set producer and immediate product consumer
  compile; H1 closes and the layer count changes six to five.
- `HMPT-H1-INTERFACE-GAP`: a consumer premise is not produced by the frozen
  order pair or a source premise is absent from `SukRegionGeometry`.
- `HMPT-H1-FALSIFIED`: an exact Euclidean point-set counterexample refutes one
  frozen relation law or exclusive comparability.
- `HMPT-H1-INERT`: only a supplied-order or otherwise target-equivalent shell
  compiles.
- `HMPT-H1-RESOURCE`: the bounded proof gate reaches its declared operational
  stop without a mathematical outcome.

No outcome may silently change segment-intersection semantics, add a supplied
order, weaken exclusive comparability, or replace point sets by pseudolines.

## Resolution

Closed with outcome `HMPT-H1-LAND`.

- `HMPTSpikeOrderDefs.lean` defines the literal triangle-containment and
  crossed-closed-segment relations, their reflexive closures, the exact
  exclusive order-pair interface, and cardinality-maximum finite chains.
- `SukRegionGeometry.toHMPTSpikeOrderPair` derives both partial-order laws and
  exhaustive-and-exclusive comparability from raw support-region geometry.
  The proof keeps literal closed-segment semantics through an explicit Cramer
  bridge and uses general position only to exclude the two sign boundaries.
- `HMPTSpikeOrderPair.exists_maxChains_card_le_product` constructs actual
  maximum chains internally, applies finite Dilworth to the vertical order,
  and converts the antichain branch to a horizontal chain.  It assumes neither
  a chain witness nor a product inequality.

Both public theorems passed warning-clean direct checks, targeted module
builds, and declaration-only audits with only `propext`, `Classical.choice`,
and `Quot.sound`.  Independent read-only reviews accepted their contracts,
semantics, trust boundaries, and accounting.  Optional review replays under a
stricter 2 GiB cap stopped operationally before or during startup; the
authenticated 12 GiB worker gates remain the admitted kernel evidence.

The parallel rank-profile audit found that the two HMPT orders are the
agreement and disagreement orders of two projective total rankings.  This adds
no datum beyond exclusive comparability.  An exact rational permutation-2143
fixture has Greene shape `(2,2)` and saturates `|s| = v*h`, so an H1-only
positive rectangle-defect improvement is expired.  Such a refinement may be
reconsidered only if H2--H4 independently produce a nonrectangular cross-pool
restriction.

## Evidence

- Authenticated primary source: arXiv:1710.11415v3 and JEMS DOI
  10.4171/JEMS/1000.
- Frozen task, source hashes, full source audit, interface audit, Lean-shaped
  contract, layer ledger, and schema-valid result under
  `runs/literature/20260816-hmpt-pointset-auth/`.
- Existing compiled interfaces: `SukRegionGeometry`, `SukRegionLE`,
  `SukConsecutiveRawPools`, and `finiteDilworth_chain_or_antichain`.
- Compiling H1 modules: `ErdosSzekeres/HMPTSpikeOrderDefs.lean`,
  `ErdosSzekeres/HMPTSpikeOrderGeometry.lean`, and
  `ErdosSzekeres/HMPTSpikeOrderConsumer.lean`.
- Frozen worker results, controls, rank-profile audit, and independent reviews:
  `runs/agents/20260816-hmpt-h1-slate/`.

## Current accounting

**Net proof movement:** forward within `FP-15.C`: the predeclared finite-layer
count decreases from six to five by closing H1.  **Evidence:** two compiling
public Lean theorems, targeted builds, standard-only axiom audits, checked
geometric controls, and independent proposal-level reviews.  **Difficulty
displaced:** none inside H1; the literal segment order, its laws, exclusive
comparability, maximum-chain construction, and product consumer are proved
rather than moved into premises.  The remaining route begins at H2
vertical-chain coloring, its binomial bound, and adjacent gluing.
**Counterfactual:** knowing the two theorems before the run removes the entire
first HMPT layer and materially reduces the scoped proof estimate.  **Planning
consequence:** close this ticket, retain `FP-15.C`, gate the next execution on
an authenticated H2 theorem contract, and expire the H1-only Greene/profile
coefficient-refinement lane.  No load-bearing edge in
`docs/wayfinder/map.md` changed.
