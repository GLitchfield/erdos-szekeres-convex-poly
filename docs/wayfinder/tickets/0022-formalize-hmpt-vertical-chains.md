---
title: Formalize the HMPT cyclic vertical-chain layer
type: research
mode: AFK
status: closed
claim: codex-hmpt-h2-falsified-2026-08-16
blocked_by: none
---

# Ticket 0022: formalize the HMPT cyclic vertical-chain layer

## Question

Can the full cyclic Pór--Valtr support-product data be projected to the HMPT
spike geometry, then consumed to construct the source's left/right profile on
every maximum vertical chain, prove its binomial bound, glue consecutive right
and left chains, and derive every cyclic inequality
`b_i + a_(i+1) < n` without supplied colorings, maxima, certificates, targets,
or cardinal inequalities?

This is layer `H2` of `FP-15.C`. Even success reproduces one finite layer of
the published quantitative route and changes no load-bearing exact-conjecture
edge.

## Source and interface decision

Outcome `HMPT-H2-SOURCE-AUTH` authenticates `ES-v2.tex` lines 385--464 and
541--556 from arXiv `1710.11415v3`. Exact hashes and the frozen contract are
under `runs/literature/20260816-hmpt-h2-auth/`.

The top-level producer must use `PorValtrSupportProductData`, not the linear
`SukConsecutiveRawPools`: the source needs the last-to-first gluing inequality,
and the support-product structure already carries all cyclic pools and the
global product over them. The no-target hypothesis is explicitly
`not ContainsConvexSubset P n` on the original carrier.

The two adjacent anchors are distinct and frozen by type. For consecutive
pools with cyclic anchors `x0,x1,x2,x3,x4`, the first pool's right chain is
extended by `x3`, while the successor pool's left chain is extended by `x1`.
The existing common-`x2` Suk gluing theorem is not an H2 substitute.

## Decision criteria

The ticket succeeds only if all four kernel obligations land: the full cyclic
source projection, the local maximum vertical profile and binomial theorem,
the distinct-outer-anchor adjacent convex-union theorem, and the immediate
cyclic no-target inequalities. This decreases the finite H-layer count from
five to four. Any source-only audit, controls-only result, supplied coloring or
certificate, linear theorem without the wrap pair, or proper subset of the
four obligations is neutral proof movement.

## Frozen execution slate

After a root-owned definition bootstrap, use three proof-producing threads
and one information-gathering root lane:

1. **Cyclic source producer (proof-producing).** Prove the cell-zero-safe,
   modulo-indexed projection from `PorValtrSupportProductData P r` and
   `InGeneralPosition P` to every local region and every cyclic adjacent pair.
2. **Local vertical profile (proof-producing).** Prove orientation-color
   semantics/transitivity, construct actual maximum left/right anchored
   subchains of the H1 maximum vertical chain, and derive the exact binomial
   inequality through `CupCap.cup_cap`.
3. **Adjacent outer-anchor gluing (proof-producing).** Derive the correct
   `x3`/`x1` arrangement-cell and pair-support facts and prove convexity of the
   selected union.
4. **Controls and orchestration (information-gathering).** Freeze and run
   independent exact-rational controls, serialize all Lean/Lake commands, and
   integrate the cyclic no-target consumer.

All four slots are intentionally concentrated in mechanism family
`quantitative-cup-cap`. This is not route diversification: H2 is the current
serial cut vertex, and no other portfolio entry presently exposes a similarly
ready theorem-producing gate. The three proof threads have disjoint files but
their mathematical risk remains correlated at the family level.

## Predeclared outcomes

- `HMPT-H2-LAND`: cyclic projection, local profile/binomial theorem, adjacent
  gluing, and every cyclic no-target inequality compile; H2 closes and the
  finite open count changes five to four.
- `HMPT-H2-INTERFACE-GAP`: the cyclic source fails to produce a premise needed
  by a consumer, or integration requires strengthening the frozen contract.
- `HMPT-H2-FALSIFIED`: an exact valid Euclidean cyclic-support fixture refutes
  triple transitivity, anchor semantics, or adjacent gluing.
- `HMPT-H2-INERT`: only a supplied-color, supplied-maximum, conditional
  certificate, linear-without-wrap, or target-equivalent shell compiles.
- `HMPT-H2-RESOURCE`: a bounded proof gate reaches its operational stop without
  a mathematical outcome.

No outcome may silently delete cell zero, omit the wrap pair, exchange the
outer anchors for the common inner anchor, or weaken the no-target carrier.

## Controls and stop conditions

Before outcome inspection, freeze exact rational fixtures that cover:

- a vertical chain of at least four points with both triple colors;
- cyclic cell zero and last-to-first adjacency;
- the local maximum-subchain enumeration and binomial inequality;
- adjacent `3+1` arrangement-cell replacement and `2+2` pair support; and
- corruptions for a color flip, vertical reversal, outer-anchor swap, region
  escape, GP boundary, disjointness loss, invalid anchored chain, missing
  wrap, and wrong ambient carrier.

The narrow stop test identified independently by both adversarial reviewers is
the exact outer-anchor same-cell/sign check on a valid adjacent fixture, with
the outer-anchor-swap corruption required to fail. A valid falsifier stops all
H2 proof work. A script bug before outcome permits one additive versioned
repair; a post-outcome semantic repair needs fresh user authorization.

## Resource and evidence gates

- Controls: at most 10 minutes each, 4 CPU cores, 8 GiB RAM, and 0.25 GiB total
  output under the owned run subtree.
- Each Lean/Lake command: 1,800 seconds, one Lean process, 12 GiB aggregate RSS,
  guarded by `scripts/run_lean_guarded.py`.
- Builders are serialized. Each theorem module must pass a warning-clean direct
  check, targeted build, forbidden-token/style scan, and declaration-only axiom
  audit. Integration then receives one full `make test` gate.
- Only standard axioms `propext`, `Classical.choice`, and `Quot.sound` are
  accepted.

## Adversarial review disposition

The bounded Sol/Fable review packet SHA-256 is
`50f4d94aa19fc36e8db8b505a6f04245bd1a1cd12e03082aad2198652ec7bfd8`;
its report SHA-256 is
`df26e3d2cc4aa385ca3a7dbd9c58d785b52c7cbb0d985568ce78ec9ae2bc12fd`.
Both reviewers rated the first draft partially supported. Their two major
objections are resolved in this ticket: the H2 source interval is independently
authenticated, and the top-level contract now uses the full cyclic support
product with explicit outer-anchor bindings and original carrier `P`. Their
minor successor/degenerate-cardinality warning is a mandatory local proof gate.

## Proof-distance accounting

**Net proof movement at planning:** neutral. **Evidence:** authenticated source,
static interface audit, and advisory review. **Difficulty displaced:** none;
the cyclic source projection, transitive-color proof, maximum-subchain
recurrence, and outer-anchor gluing remain kernel obligations.
**Counterfactual:** the corrected contract prevents a linear no-wrap theorem or
common-anchor substitution from being misclassified as H2 progress, but does
not yet reduce remaining proof work. **Planning consequence:** promote
`FP-15.C` from source-gated to an approval-gated proof-producing execution
slate; land only on the complete four-part kernel gate. No load-bearing edge in
`docs/wayfinder/map.md` changes.

## Resolution

Closed with predeclared outcome `HMPT-H2-FALSIFIED`.  The frozen producer
contract is false at its admitted lower endpoint `r = 2`.  Here `2*r = 4`, so
the required five-anchor window repeats its outer endpoint:
`hmptAnchor i 4 = hmptAnchor i 0`.  Consequently the required
`SukFiveCapAnchors.orient014` field becomes
`orientation x0 x1 x0 < 0`, contradicting the zero alternating determinant.

This is not merely a type-level degeneracy.  The counterexample module
constructs an explicit inhabited `PorValtrSupportProductData P 2` on the four
general-position points `(0,0)`, `(1,3)`, `(2,4)`, and `(3,3)`, with the
periodic strict-cap anchors and empty cyclic open pools.  It then proves the
public negation
`HMPTCyclicSourceCounterexample.frozenContract_false`.  The theorem passed a
warning-clean direct gate, targeted module build, and declaration-only audit
with only `propext`, `Classical.choice`, and `Quot.sound`.

The root definition bootstrap compiled before the falsifier.  The local-profile
and adjacent-gluing design lanes were then superseded and the controls were not
started.  The bootstrap and counterexample were integrated into the umbrella;
`make test` passed the 10,297-job Lean build, 107 unit tests, and all
deterministic repository checks.  No positive cyclic consumer or full H2
composition was attempted.  The standalone local-profile and adjacent-gluing
statements are therefore neither proved nor refuted by this run.

**Net proof movement:** neutral.  **Evidence:** a kernel-checked counterexample,
not a compiling H2 producer.  **Difficulty displaced:** none; changing the
endpoint to `3 <= r` avoids this collision but leaves the cyclic projection,
local profile recurrence, distinct-outer-anchor gluing, and cyclic no-target
consumer unproved.  **Counterfactual:** knowing the counterexample before the
run would have prevented work on a false packet, but would not have shortened
the corrected H2 proof or raised its success probability.  **Planning
consequence:** expire this frozen packet and gate `FP-15.C` on a newly reviewed
contract.  Do not promote a `3 <= r` descendant merely from this negative
result.  The finite-layer count remains five, and no load-bearing edge in
`docs/wayfinder/map.md` changes.

## Evidence

- H2 source authentication and exact frozen contract:
  `runs/literature/20260816-hmpt-h2-auth/`.
- Compiling H1 interfaces: `HMPTSpikeOrderDefs.lean`,
  `HMPTSpikeOrderGeometry.lean`, and `HMPTSpikeOrderConsumer.lean`.
- Full cyclic point-set source: `PorValtrSupportProduct.lean`.
- Advisory Sol/Fable review:
  `runs/reviews/20260816-hmpt-h2-plan/review/REPORT.md` with packet/report
  hashes recorded above.
- Compiling shared bootstrap: `ErdosSzekeres/HMPTVerticalChainDefs.lean`,
  SHA-256 `1a6af671202285835bb21ae42d1506593f91b28cde99d39b720ce365e8cf95ff`.
- Kernel counterexample: `ErdosSzekeres/HMPTCyclicSpikeGeometry.lean`,
  SHA-256 `43e9382a0dfe9c77a62acbef9f0a0aa72060e1db00f49376ce422d2f3d67e0cb`.
- Schema-valid terminal slate:
  `runs/agents/20260816-hmpt-h2-slate/slate.json`; cyclic result SHA-256
  `b9c80ec9f048610ff7ffc015b8e7496ffaf52a4628b26ad65bda17d04a3a9d98`.
