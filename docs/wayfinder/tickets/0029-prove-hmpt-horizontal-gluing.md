---
title: Prove HMPT whole-chain convexity and cyclic horizontal gluing
type: research
mode: AFK
status: closed
claim: codex-hmpt-h4-land-2026-08-17
blocked_by: none
---

# Ticket 0029: prove HMPT whole-chain convexity and cyclic horizontal gluing

## Question

Can the completed H1--H3 point-set machinery derive Observation 3.6(ii)'s
whole-chain convexity and Observation 3.7's even/odd cyclic gluing directly
from `PorValtrSupportProductData`, then package the resulting numerical bounds
on the exact H2 profile family without adding a separator certificate, changing
the carrier, or reselecting the dependent profiles?

This ticket is H4 of the authenticated six-layer point-set
Holmsen--Mojarrad--Pach--Tardos route.  It does not authorize the H5 product
aggregation theorem, the H6 asymptotic wrapper, the optimized HMPT coefficient,
pseudo-configurations, or an exact-conjecture claim.  A read-only H5 natural-
arithmetic preflight may run in parallel, but no H5 proof source begins before
H4 lands.

## Source boundary

The authenticated source is arXiv `1710.11415v3`; primary `ES-v2.tex` has
SHA-256
`509fdbd14dac1a79618387dca875cb535ae3c06803c2ad92a67542ca54535573`.

- Observation 3.6(ii), lines 471--488, says every literal inner or outer
  horizontal chain is itself in convex position.
- Observation 3.7, lines 514--539, says that for even `k >= 4`, the unions of
  the inner chains over the odd spikes and over the even spikes are in convex
  position.
- Its proof has three distinct geometric cases: a three-point local chain uses
  remote arrangement-cell replacement, a two-point local chain uses horizontal
  line separation, and a singleton local chain uses the spike base edge to
  separate that point from all other same-parity pools.
- TeX lines 553--560 then give `d_i < n`, `b_i+a_(i+1) < n`, and
  `sum_i c_i < 2*n`.  Those numerical conclusions belong to the final H4
  package; the product aggregation at lines 561--575 belongs to H5.

## Adversarial review

The bounded Sol/Fable review at
`runs/reviews/20260817-hmpt-h4/sol-fable/REPORT.md` returned `MODIFY` with
medium confidence, not `STOP`.  Both reviewers accepted the source boundary
and local proof graph.  They required the following contract corrections:

1. state cyclic nonadjacency in both directions and treat the `r = 3` wrap
   pairs explicitly rather than relying on one linear index window;
2. make remote horizontal-pair separation a proved producer;
3. make the base-edge separator for empty/singleton local-chain cases a proved
   producer rather than an optional certificate;
4. test `r = 3` `2+1+1` patterns and `r = 4` four-distinct-pool patterns before
   the global proof;
5. bind the H2 family exactly once before choosing attached H3 profiles; and
6. reject the false strict H5 binomial estimate at `c=d=1` during the separate
   Nat preflight.

The possible H5 interface concern is resolved by the existing fields
`HMPTVerticalProfile.poolCard_le_product` and
`HMPTVerticalProfile.verticalCard_le_choose`; H4 must preserve access to the
same stored profiles rather than duplicate either bound as an assumption.

## Decision criteria

Accept H4 only if every exact L4, W4/R4/B4, G4, and F4 declaration compiles
warning-clean, its targeted module builds, the public surfaces and profile
identities pass independent static review, and declaration-only audits report
only the three permitted standard axioms.  The final F4 package must eliminate
the H2-family producer exactly once, attach each H3 profile to that same stored
member, retain all upstream structure fields, and derive every no-target
inequality on the original carrier.  A supplied separator, convexity or
cardinality certificate, reselected profile, changed parity/carrier, failed
wrap case, or nonstandard trust dependency is a non-LAND terminal.

## Frozen H4 contracts

The exact mathematical contracts are frozen in
`runs/agents/20260817-hmpt-h4-slate/frozen-contract.md`.  Binder implicitness,
line wrapping, and private helper organization may vary.  Hypotheses,
orientation direction, parity convention, profile identity, selected chains,
and carrier may not.

### L4: local whole-chain convexity

From one raw `SukRegionGeometry`, one exact `HMPTVerticalProfile`, and one
`HMPTHorizontalProfile` attached to that profile, prove separately that
`hmptChainPoints innerChain` and `hmptChainPoints outerChain` are in convex
position.  No convexity field may be added to either profile.

### W4/R4/B4: cyclic separation

For `3 <= r`, same-parity distinct indices in `Fin (2*r)` must be shown
cyclically nonadjacent, including the last-to-first direction.  Derive from raw
support-product fields:

- a remote strict-side theorem for a horizontally ordered pair from one pool
  and every point of another same-parity pool; and
- a base-edge strict-separation theorem placing a point of the local pool and
  every point of another same-parity pool on opposite sides of the local
  anchors numbered `1` and `2`.

Neither theorem may accept a `SameStrictSide`, separation, support-edge,
arrangement-cell, or convexity certificate as an input.

### G4: parity-union convexity

For any actual family of inner chains drawn from the cyclic source pools,
prove the union over each parity class is in convex position.  The proof must
cover all four-point pool-multiplicity patterns, including `3+1`, `2+2`,
`2+1+1`, and four distinct pools; empty and singleton chains remain valid.

### F4: dependent numerical package

Under `h : PorValtrSupportProductData P r`, `3 <= r`, general position of `P`,
and absence of a convex `n`-subset, choose the H2 family once, attach one H3
profile to each exact member, and retain:

- every H2 adjacent right/next-left inequality;
- every H3 outer-chain cardinality `< n`;
- both parity inner-chain cardinality sums `< n`; and
- their total sum `< 2*n`.

Every union stays inside `P`; all exact cardinalities are derived from source
pool disjointness and `hmptChainPoints_card`.

## Execution slate

- One proof-producing L4 lane owns only
  `ErdosSzekeres/HMPTHorizontalChainConvexity.lean` and its ignored evidence.
- One proof-producing cyclic-separation lane owns only
  `ErdosSzekeres/HMPTCyclicHorizontalSeparation.lean` and its ignored evidence.
- One information-gathering controls lane owns only its ignored exact-rational
  evaluator/checker subtree and may not edit Lean source.
- After those gates, root serially freezes and proves G4 and F4, while a
  read-only reviewer audits every released source hash.
- Root alone owns definitions, imports, this ticket, Wayfinder files, the
  serialized builder, repository tests, staging, commit, and push.

## Evidence

Proof admission requires warning-clean direct Lean gates, targeted builds,
standard-only declaration audits, exact source hashes, and an independent
review whose proof ledger is frozen before source inspection.  Bounded
exact-rational controls are search information only.  In particular, an
inadmissible positive fixture cannot corroborate or refute a theorem and must
terminate the controls lane without post-outcome repair.

All slots intentionally concentrate on FP-15.C because H4 is the unique ready
cut vertex after the completed H1--H3 chain.  The lanes nevertheless test
distinct immediate obligations: local four-point convexity, cyclic separator
geometry, and bounded falsification.

## Outcomes and stop gates

- `HMPT-H4-LAND`: L4, cyclic separation, G4, and F4 all compile warning-clean,
  pass targeted builds, static review, standard-only axiom audits, independent
  final review, and the root repository gate.  The official set changes
  `{H4,H5,H6}` to `{H5,H6}`.
- `HMPT-H4-LOCAL-LAND`: L4 passes every theorem gate but a later component
  stops.  The subordinate H4 set shrinks, but H4 and the official layer count
  remain open.
- `HMPT-H4-SEPARATION-LAND`: W4/R4/B4 pass every theorem gate but G4 or F4
  stops.  The subordinate set shrinks, but H4 remains open.
- `HMPT-H4-INTERFACE-GAP`: a required remote or base-edge separator cannot be
  derived without a stronger region premise, supplied certificate, common
  global anchor, replacement profile, or changed carrier.
- `HMPT-H4-FALSIFIED`: an admitted exact Euclidean configuration kernel-
  refutes a frozen public statement.
- `HMPT-H4-INERT`: only a supplied separator/convexity certificate,
  target-equivalent premise, reselected profile, or altered carrier compiles.
- `HMPT-H4-RESOURCE`: the declared four direct attempts, lane wall budget, or
  process/output cap expires without a theorem or trustworthy classification.

No public contract changes after dispatch.  Stop an affected branch at the
first non-LAND terminal; independently compiling subordinate results may be
integrated only under their predeclared partial-LAND labels.

## Resource and approval inventory

Each Lean/Lake command runs through `scripts/run_lean_guarded.py` with an
1,800-second wall limit, one Lean process, and 12 GiB aggregate RSS.  Each
proof module has at most four direct attempts.  Each frozen control evaluator
has an 1,800-second, 8-core, 16-GiB, and 256-MiB output cap.  Source work may
overlap; no Lean/Lake commands overlap.

The user approved parallel specialist lanes, bounded local controls,
serialized guarded Lean gates, the final repository test, and conditional
commit/push on admitted results.  The Sol/Fable call is already complete.  No
further provider/network call, solver, installation, destructive action,
resource increase, or process termination is planned.

## Proof-distance accounting

The frozen subordinate H4 measure is `{L4,W4,R4,B4,G4,F4}`.  Each compiling
producer can strictly reduce that set without moving the original difficulty
into a premise.  Only the full F4 endpoint closes H4 and changes the official
remaining finite-layer set from `{H4,H5,H6}` to `{H5,H6}`.

H4 remains within the current-best quantitative point-set route.  It changes
no load-bearing exact-conjecture `D-UPPER`, `D-HALF`, `D-DECOMP`, or
`D-NORMALIZE` edge.  Full H4 success unlocks an exact H5 theorem gate; it does
not itself prove a global upper bound.

## Resolution

Closed as `HMPT-H4-LAND`.  Lean now proves both literal local horizontal-chain
convexity theorems; cyclic same-parity placement, remote pair support, and
base-edge separation including both `r = 3` wrap directions; convexity of each
exact parity union; and the dependent numerical profile package.  The package
calls `exists_hmptCyclicProfiles` exactly once, attaches each horizontal
profile to that stored member, retains the adjacent H2 inequalities, and
derives every outer bound, both parity inner sums, and the total inner sum on
the original carrier.

All four modules pass warning-clean direct gates and targeted builds.  Their
public declarations audit only to `propext`, `Classical.choice`, and
`Quot.sound`; an independent frozen-ledger review accepts the exact source
hashes, profile identity, cyclic coverage, carrier discipline, and acyclic
trust graph.  The controls lane ended in `HMPT-H4-CONTROL-MISMATCH` because its
frozen `LOCAL_OUTER_FOUR` positive contained a collinear triple; that is
operational-only search information and neither positive nor negative theorem
evidence.

**Net proof movement:** forward on the named H4 dependency.  The frozen
subordinate set `{L4,W4,R4,B4,G4,F4}` becomes empty and the official finite
layer set changes from `{H4,H5,H6}` to `{H5,H6}`.  **Evidence:** compiling
theorems, targeted builds, standard-only axiom audits, independent review, and
the root repository gate.  **Difficulty displaced:** none within H4; H5
product aggregation and H6 exact-natural asymptotics are distinct remaining
layers.  **Counterfactual:** prior possession of these theorems removes the
entire H4 proof burden and exposes a directly executable H5 theorem gate.
**Planning consequence:** close ticket 0029 and require a separately frozen H5
contract; no load-bearing `D-UPPER`, `D-HALF`, `D-DECOMP`, or `D-NORMALIZE`
edge changes.
