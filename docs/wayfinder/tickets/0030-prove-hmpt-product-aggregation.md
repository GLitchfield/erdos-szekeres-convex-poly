---
title: Prove exact-natural HMPT product aggregation
type: research
mode: AFK
status: closed
claim: codex-hmpt-h5-aggregation-2026-08-17
blocked_by: none
---

# Ticket 0030: prove exact-natural HMPT product aggregation

## Question

Can the completed H1--H4 profile package and the original-carrier Pór--Valtr
support-product inequality be combined into one conservative exact-natural
cardinality bound, without the source paper's false uniform strict binomial
estimate, a supplied cyclic reindexing certificate, a changed profile family,
or an asymptotic premise?

This ticket is H5 of the authenticated six-layer point-set
Holmsen--Mojarrad--Pach--Tardos route.  It does not choose the optimized
parameter, construct the support-product data, prove H6, improve the published
coefficient, handle pseudo-configurations, or change a load-bearing exact
Erdős--Szekeres dependency.

## Source and compiled boundary

The authenticated source is arXiv `1710.11415v3`; primary `ES-v2.tex` has
SHA-256
`509fdbd14dac1a79618387dca875cb535ae3c06803c2ad92a67542ca54535573`.
Lines 553--575 combine the local product inequalities with

```text
d_i < n,
b_i + a_(i+1) < n,
sum_i c_i < 2*n
```

to obtain the unoptimized current-best exponent.  H1--H4 now compile on the
original carrier and supply those exact ingredients through
`PorValtrSupportProductData` and
`HMPTCyclicHorizontalProfilePackage`.

The exact source product is

```text
(P.card - 4*r)^(2*r)
  <= (2^(32*r))^r * product_i (h.hmptPool i).card.
```

The H4 package stores the original H2 family and dependently attached H3
profiles, not merely their cardinalities.  H5 must consume those stored
members directly.

## Natural-number correction

The source-style uniform strict estimate

```text
choose (c+d-2) (c-1) < d^c
```

is false at `c=d=1`, for all `c=0`, and at further truncated-subtraction
boundaries.  The H5 proof instead uses

```text
choose (a+b) a <= (b+1)^a
choose (c+d-2) (c-1) <= d^(c-1).
```

Every `0/1` branch is part of the theorem proof.  Controls may corroborate the
branch ledger but cannot replace it.

## Frozen public scale

The reciprocal Sol/Fable review completed under packet SHA-256
`9e636053985436d3900b7343af4173e2a03f906e66d8f86d5f554fd9242d5793`.
Its joint practical disposition was `MODIFY`: the exponent arithmetic and
root-cancellation plan survived, but dispatch was conditioned on compiling
the range-to-`Fin` product bridge and a genuine cyclic-successor equivalence.
Both checks now compile warning-clean in the frozen interface smoke source,
SHA-256
`4ae587bf410239e78ce936634e3e78fdaf0866c50f30416fdc3de971d333b2fc`.
The review also forbids using truncated choose symmetry or rotating a product
whose bases depend on the index.

The exact post-review public scale is therefore

```text
hmptAggregationExponent n r =
  n + (n * Nat.clog 2 n) ⌈/⌉ r + 16*r.
```

The intended reusable core is

```text
package.card_sub_anchor_le hr :
  P.card - 4*r <= 2^(hmptAggregationExponent n r).
```

The intended public no-target wrapper is

```text
h.card_lt_hmptAggregation hr hgp hno :
  P.card < 4*r + 2^(hmptAggregationExponent n r + 1).
```

The extra bit is deliberate conservative slack.  Exact namespace placement,
binder implicitness, and private helper organization are frozen in
`runs/agents/20260817-hmpt-h5-slate/frozen-contract.md`.  The carrier,
hypotheses, exponent and endpoint may not change after dispatch.

## Decision criteria

Close the ticket only if A5 and B5 preserve the frozen statements and stored
profile family, pass warning-clean direct and targeted Lean gates, expose no
forbidden trust construct, pass declaration-only standard-axiom audits, survive
independent exact-hash review, and pass the root exact-state repository gate.
Any strengthened premise, changed carrier, profile reselection, supplied
aggregate inequality, false strict estimate, or unresolved natural-number
boundary forces a non-LAND terminal instead.

## Staged proof

### A5: arithmetic library

Prove the two binomial estimates and only the product/power/ceiling/root
helpers required by B5.  Search mathlib first.  All truncation cases are
explicit; no custom axiom, oracle, solver, or unverified computation is
permitted.

### B5: package aggregation

Using exactly the stored family:

1. bound the vertical product by `2^((2*r)*n)` using
   `Nat.choose_le_two_pow`, the adjacent inequalities, and a proved cyclic
   successor permutation;
2. bound the horizontal product by `n^(2*n)` using the conservative H3
   binomial estimate, each outer bound, and the H4 total inner bound;
3. convert that factor to `2^(2*n*Nat.clog 2 n)`;
4. combine it with the exact source denominator and dominate the total
   exponent by `(2*r) * hmptAggregationExponent n r` through the ceiling
   cover;
5. cancel the positive common power `2*r`; and
6. split `P.card <= 4*r` before deriving the strict wrapper with one extra
   bit.

The source-threshold equality `P.card = 2^(32*r)` is an H6 branch and is not
part of H5.

## Execution slate

- One proof-producing arithmetic lane owns only
  `ErdosSzekeres/HMPTAggregationArithmetic.lean` and its ignored evidence.
- Root serially owns the proof-producing aggregation consumer
  `ErdosSzekeres/HMPTProductAggregation.lean` after the arithmetic interface
  is admitted.
- One information-gathering bounded-controls lane owns only its ignored
  integer producer/checker subtree.
- One information-gathering read-only reviewer freezes an independent proof
  ledger before inspecting released source hashes.
- Root owns this ticket, task packets, shared imports, Wayfinder files, the
  sole builder lane, repository tests, staging, commit, and push.

The slate is intentionally concentrated on `FP-15.C` because H5 is the unique
ready cut vertex after H4.  Arithmetic, aggregation, controls, and review test
different immediate failure modes but remain correlated descendants of the
same mechanism family.  It has two proof-producing and two
information-gathering slots.

## Evidence gates

Each Lean endpoint requires a warning-clean direct gate, targeted module
build, exact static/source hash, declaration-only standard-axiom audit, and
independent review.  Full H5 additionally requires the root exact-state
repository gate.  Integer controls are computational evidence only.

## Outcomes and stops

- `HMPT-H5-LAND`: A5 and B5 pass every theorem, review and repository gate;
  the official finite-layer set changes `{H5,H6}` to `{H6}`.
- `HMPT-H5-ARITHMETIC-LAND`: the conservative reusable arithmetic compiles,
  but B5 reaches a mathematical or bounded operational stop.  The subordinate
  H5 obstruction shrinks, but H5 remains open.
- `HMPT-H5-INTERFACE-GAP`: a mandatory product, cyclic reindexing, ceiling, or
  cancellation step requires a stronger package field, supplied certificate,
  reselected profile, or changed carrier.
- `HMPT-H5-FALSIFIED`: a kernel-checked natural-number counterexample refutes
  a frozen public statement.
- `HMPT-H5-INERT`: only a false strict estimate, target-equivalent premise,
  changed exponent, or supplied aggregate inequality compiles.
- `HMPT-H5-RESOURCE`: the declared direct-attempt, wall-time, memory, or output
  cap expires without an admitted theorem or trustworthy classification.

No public contract changes after dispatch.  Stop the affected branch at the
first non-LAND terminal.  An independently compiling A5 result may be
integrated under its partial-LAND label.

## Resource and approval inventory

The approved Sol/Fable review uses the exact
`python3 scripts/adversarial_review.py run` prefix with one reciprocal round,
the pinned `claude-fable-5` and `gpt-5.6-sol` models, and an 1,800-second cap.
Controls use at most 10 active minutes, 4 cores, 4 GiB RAM, and 256 MiB output.
Each Lean/Lake command uses `scripts/run_lean_guarded.py` with an 1,800-second
wall cap, one Lean process, and 12 GiB aggregate RSS.  Builders are serialized.

The user approved the provider call, parallel specialist lanes, bounded local
controls, guarded Lean gates, final `make test`, and conditional commit/push on
LAND.  No installation, destructive action, solver, resource increase, or
other external mutation is planned.

## Proof-distance accounting

The predeclared official measure is `{H5,H6}`.  A5 alone is reusable but does
not change that measure.  Full B5 success strictly changes it to `{H6}` without
moving product aggregation into a new premise.  H5 remains inside the
current-best quantitative point-set route: it changes no load-bearing
`D-UPPER`, `D-HALF`, `D-DECOMP`, or `D-NORMALIZE` edge and does not improve the
published asymptotic order.

## Resolution

Resolved on 2026-08-17 as `HMPT-H5-LAND`.

`ErdosSzekeres/HMPTAggregationArithmetic.lean` proves the frozen exponent and
both boundary-safe binomial estimates.  Its final SHA-256 is
`8d4e5085f05aa681d41b02f53b294ea8b7d83a255ea28b219634a63471db8af8`.
`ErdosSzekeres/HMPTProductAggregation.lean` proves both frozen B5 theorems on
the original carrier and exact stored profile family.  Its final SHA-256 is
`8587b215ca1806f18f7a817c6781af923fe948bdd3a247d3d08a286ff9592661`.
Both modules pass warning-clean direct checks, targeted builds, and
declaration-only audits with exactly `propext`, `Classical.choice`, and
`Quot.sound`; independent static review accepts both exact hashes.  The root
exact-state repository gate also passes.

**Net proof movement:** forward on the predeclared finite-layer measure
`{H5,H6} -> {H6}`.  **Evidence:** compiling theorems and repository tests;
bounded controls are neutral corroboration.  **Difficulty displaced:** none
inside H5; H6 remains the distinct parameter-choice and asymptotic endpoint.
**Counterfactual:** this result removes the complete product-aggregation
obligation and reduces the remaining formal work.  **Planning consequence:**
close H5 and plan H6 separately.  No load-bearing exact-conjecture edge
changed, and the published asymptotic theorem has not yet been reproduced.
