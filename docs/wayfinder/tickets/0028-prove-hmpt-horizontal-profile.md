---
title: Prove the HMPT horizontal inner/outer profile
type: research
mode: AFK
status: closed
claim: codex-hmpt-h3-land-2026-08-17
blocked_by: none
---

# Ticket 0028: prove the HMPT horizontal inner/outer profile

## Question

Can raw `SukRegionGeometry` classify triples of the already selected maximum
HMPT horizontal chain by the source's literal inner/outer five-point predicate,
prove that coloring transitive, and construct actual maximum inner and outer
subchains satisfying the exact binomial recurrence without assuming the H4
convexity or gluing conclusions?

H1 and H2 now compile. This ticket is H3 of the authenticated six-layer
point-set Holmsen--Mojarrad--Pach--Tardos route. It does not authorize H4,
global aggregation, asymptotic rounding, or an exact-conjecture claim.

## Source boundary

The authenticated source is arXiv `1710.11415v3`; primary `ES-v2.tex` has
SHA-256
`509fdbd14dac1a79618387dca875cb535ae3c06803c2ad92a67542ca54535573`.

- TeX lines 466--469 define literal inner and outer horizontal chains using
  every three distinct chain points together with the two outer anchors.
  Chains of cardinality at most two satisfy both predicates.
- Observation 3.6(i), lines 471--475 and the first proof component at
  479--488, is the transitive-color statement used by H3.
- TeX lines 509--512 give
  `h_i <= choose (c_i+d_i-2) (c_i-1)`.
- Observation 3.6(ii) is whole-chain convexity and belongs to H4. Observation
  3.7, lines 514--539, is parity gluing and also belongs to H4.

The H3/H4 source boundary is therefore intentionally non-contiguous. Earlier
proposal prose calling these Observations 3.2/3.3 was corrected before this
ticket and before theorem-contract freeze.

## Frozen public contract

The exact definitions and statements are frozen in
`runs/agents/20260817-hmpt-h3-proof-slate/frozen-contract.md` and in
`ErdosSzekeres/HMPTHorizontalChainDefs.lean`. In mathematical form:

1. `hmptHorizontalTripleColor` labels negative triple orientation as
   `Turn.right` and nonnegative orientation as `Turn.left`.
2. `HMPTHorizontalTripleGeometry` states strict-horizontal four-point
   transitivity and, on every increasing triple, the exact equivalences
   `right ↔ literal inner five-set` and
   `left ↔ literal outer five-set`.
3. `SukRegionGeometry.hmptHorizontalTripleGeometry` produces that structure
   from raw region geometry alone.
4. `HMPTHorizontalProfile` is attached to one exact existing
   `HMPTVerticalProfile`; it stores actual maximum literal inner and outer
   subsets of that profile's unchanged `horizontalChain` and the exact bound

   ```lean
   verticalProfile.horizontalChain.card ≤
     Nat.choose (innerChain.card + outerChain.card - 2)
       (innerChain.card - 1)
   ```

5. `SukRegionGeometry.exists_hmptHorizontalProfile` explicitly takes both the
   raw geometry and the existing profile on the same anchors, pool, and
   carrier. It may not infer geometry from the profile or replace its chain.

Binder implicitness, line wrapping, and private helper organization may vary.
The mathematical statements, literal predicates, carrier, selected chain,
color direction, and hypotheses may not.

## Decision criteria

Accept H3 only if both exact frozen declarations compile warning-clean, their
targeted modules build, their public surfaces and trust boundaries pass static
review, their declaration-only audits report only the three permitted standard
axioms, an independent reviewer accepts both authenticated final source hashes,
and the root-owned full repository gate passes.  G3 alone may be accepted only
under the predeclared `HMPT-H3-G3-LAND` outcome.  A supplied classifier,
transitivity law, maximum chain, recurrence inequality, replacement carrier or
chain, H4 convexity conclusion, or target-equivalent premise is a non-LAND
terminal rather than partial completion.

## Required proof graph

### G3 geometry

1. Re-derive privately the literal strict-horizontal comparison equivalence
   with both fixed-outer-anchor orientations negative.
2. For `p <_h q <_h r`, prove
   `InConvexPosition {outerLeft,outerRight,p,q,r}` iff
   `orientation p q r < 0`; general position excludes zero.
3. Prove both colors' four-point transitivity analytically, using an explicit
   projective chart or an equivalent orientation identity. Source prose about
   checking configurations is not an oracle.
4. Bundle only transitivity and ordered-triple literal semantics in the public
   G3 endpoint.

### F3 finite profile

1. Enumerate literal inner and outer subsets of the exact stored
   `horizontalChain` and select actual cardinality maxima.
2. Handle horizontal-chain cards zero, one, and two directly; the whole chain
   is both kinds and the exact Nat bounds are `0<=1`, `1<=1`, and `2<=2`.
3. For larger chains, privately order the chain subtype by the horizontal
   relation. Do not invoke the vertically ordered public Suk wrapper.
4. Apply `CupCap.cup_cap` at offsets `inner.card-1` and `outer.card-1`.
5. Canonically sort arbitrary distinct selected triples before converting the
   ordered monochromatic output to the literal permutation-invariant Finset
   predicate.
6. Contradict the corresponding maximum at successor size and package the
   exact bound on the unchanged source profile.

## Evidence

### Review and controls

The bounded Sol/Fable review completed at evidence-packet SHA-256
`09326ebec9b646d20d30cd1fbd2218c8b02dc69f8041ddc95c3ba4a2ee8dc2fc`.
Both reviewers require the explicit raw-geometry premise in F3, strict
horizontal transitivity hypotheses, a private horizontal recurrence transport,
and exclusion of H4 conclusions. Their output is advisory.

Two independently authored exact-rational evaluators then returned
`HMPT-H3-CONTROLS-PASS` with identical semantic SHA-256
`c8a5543589496b6e67c1d5dd1a0ad526dfa447d7681c70588cf6fe4c251f7a45`.
They checked all 16 color patterns, both transitivity conclusions, 24 order
recoveries, 120 triple permutations, cards zero through two, exact binomial
rows, and eight corruptions including both premise-ablation power controls.
This is computational evidence, not a theorem.

The first proof slate terminated `HMPT-H3-RESOURCE`.  The final G3 candidate at
SHA-256
`bc1687c40f64519030a468960791f95dd62e144cf0c83a1dd08f5b5ef315a9c4`
passed independent static mathematical and contract review, but its fourth and
final authorized direct attempt left one literal `Finset` normalization goal.
No targeted build or axiom audit ran.  F3 was not started because G3 did not
become an admitted producer.  This is an operational stop, not a theorem or a
counterexample.

The separately frozen recovery slate then tested exactly one deterministic
normalization repair before touching the theorem source.  Appending
`Finset.insert_empty` after `Finset.erase_singleton` discharged the residual
without changing G3's statement, hypotheses, signs, five-set classifier, or
import boundary.  The final G3 source has SHA-256
`41f4f9dfb14d43cd1f2c99c49d491aa2f60eaca03acbdacc67fcbf56e2b97873`.
It passed a warning-clean direct gate, a 3311-job targeted build, independent
static review, and a declaration audit reporting only
`[propext, Classical.choice, Quot.sound]`.

With that producer admitted, F3 constructed the two literal filtered-powerset
maxima on the unchanged stored horizontal chain, handled cardinalities zero
through two directly, and used the private horizontal order, exact CupCap
offsets, consecutive-color propagation, and canonical triple sorting in the
large branch.  Its final source has SHA-256
`8856340e81771c7f7aa01ffb26a76d2865fec2ba43123fbdfb06ba041ee043e5`.
It passed a warning-clean direct gate, a 3314-job targeted build, independent
static review, and the same standard-only declaration audit.  These are
compiling theorem results; the earlier controls remain supporting computation
rather than proof.

## Execution slate

- One proof-producing geometry lane owns only
  `ErdosSzekeres/HMPTHorizontalColorGeometry.lean` and its ignored evidence.
- One proof-producing finite lane owns only
  `ErdosSzekeres/HMPTHorizontalProfileProducer.lean` and its ignored evidence.
- One information-gathering independent-review lane is read-only and derives
  the sign/transitivity and finite recurrence ledgers before seeing released
  worker source hashes.
- Root owns the definitions module, this ticket, all shared imports and
  Wayfinder files, the sole serialized builder lane, repository tests,
  staging, commit, and push.

All slots intentionally remain in one mechanism family because H3 is the
single serial cut vertex selected by the reconciled portfolio. The work still
uses mathematical breadth: geometry, finite recurrence, and independent audit
fail for different immediate reasons, while every Lean/Lake command remains
serialized.

## Outcomes and stop gates

- `HMPT-H3-LAND`: both exact public theorems pass warning-clean direct gates,
  targeted builds, static scope checks, standard-only axiom audits,
  independent final-source review, and the root repository gate. H3 closes
  and the official finite-layer count changes four to three.
- `HMPT-H3-G3-LAND`: the exact G3 theorem passes every gate but F3 reaches a
  mathematical or bounded operational terminal. The subordinate set changes
  `{G3,F3}` to `{F3}`, but H3 and the official layer count remain open.
- `HMPT-H3-INTERFACE-GAP`: a named raw source fact cannot produce a mandatory
  G3/F3 field without a stronger premise, changed chain, or public certificate.
- `HMPT-H3-FALSIFIED`: an admitted exact Euclidean configuration kernel-refutes
  a frozen public statement.
- `HMPT-H3-INERT`: only a supplied classifier/transitivity law, replacement
  chain/carrier, H4 conclusion, or target-equivalent shell compiles.
- `HMPT-H3-RESOURCE`: the declared four direct attempts, four active proof
  hours, or process/output cap expires without a theorem or trustworthy
  mathematical classification.

Do not revise a public statement after dispatch. Stop the affected branch at
the first non-LAND terminal; an independently compiled G3 result may still be
integrated under its own predeclared outcome.

## Resource and approval inventory

Each Lean/Lake command runs through `scripts/run_lean_guarded.py` with an
1,800-second wall limit, one Lean process, and 12 GiB aggregate RSS. Each proof
lane has at most four direct attempts and four active proof hours. The bounded
controls already completed under 4 cores, 8 GiB, 15 minutes, and 256 MiB.

The approved Sol/Fable provider call is complete. No further network call,
provider call, solver, installation, destructive operation, resource increase,
or process termination is planned. The conditional final Git push is the only
remaining external mutation and was included in the approved plan.

## Proof-distance accounting

At theorem-contract freeze the subordinate H3 measure is `{G3,F3}`. G3 alone
can decrease it to `{F3}` without changing the official layer count. Only both
compiling endpoints reduce the official HMPT finite-layer count from four to
three. Definitions, source authentication, provider review, and controls are
neutral proof movement.

Neither result changes `D-UPPER`, `D-HALF`, `D-DECOMP`, or `D-NORMALIZE`; H3
remains within the current-best quantitative point-set route. The hard work is
not displaced: G3 proves rather than assumes the five-point classifier and
transitivity, while F3 constructs rather than receives the maxima, sorting
bridge, and exact recurrence bound.

## Resolution

Closed as `HMPT-H3-LAND`.  The recovery slate changed the subordinate set from
`{G3,F3}` to empty: G3 now derives the literal horizontal five-set semantics
and both-color transitivity from raw geometry, and F3 constructs the actual
inner/outer maxima and proves the exact binomial profile on the unchanged H2
chain.  The official HMPT finite-layer count decreases from four to three.

**Net proof movement:** forward on the named H3 dependency.  **Evidence:** two
warning-clean compiling theorems, targeted builds, independent final-source
review, standard-only axiom audits, and the root exact-state repository gate.
**Difficulty displaced:** none within H3; H4--H6 are
distinct downstream source layers and remain open.  **Counterfactual:** knowing
these theorems before the run removes both frozen H3 obligations and materially
reduces the remaining formalization.  **Planning consequence:** close ticket
0028 and require a fresh authenticated H4 contract and bounded route review
before scheduling H4.  No load-bearing `D-UPPER`, `D-HALF`, `D-DECOMP`, or
`D-NORMALIZE` edge changes.
