---
title: Prove the HMPT asymptotic parameter choice and public endpoint
type: research
mode: AFK
status: closed
claim: codex-hmpt-h6-endpoint-2026-08-17
blocked_by: none
---

# Ticket 0031: prove the HMPT asymptotic endpoint

## Question

Can the compiled H5 cardinality bound and the compiled Pór--Valtr support-data
producer be combined, by an exact natural-number square-root parameter choice,
into a public `ForcesConvexPolygon` theorem of order
`2^(n + O(sqrt(n * log n)))`?

This is H6, the sole remaining finite layer of `FP-15.C`.  Success reproduces
the authenticated HMPT published-order point-set upper bound.  It does not
improve that order and changes no load-bearing exact-conjecture edge.

## Frozen candidate declarations

The reciprocal adversarial review and arithmetic smoke gate must accept these
exact declarations before proof dispatch.  If either rejects them, stop as
`HMPT-H6-CONTRACT-MODIFY`; do not silently enlarge a constant or add a premise.

Module `ErdosSzekeres/HMPTAsymptoticParameters.lean`:

```lean
namespace ErdosSzekeres

/-- The conservative square-root parameter used by the HMPT endpoint. -/
def hmptAsymptoticScale (n : ℕ) : ℕ :=
  max 3 (Nat.sqrt (n * Nat.clog 2 n) + 1)

/-- The exact square-root cover and removal facts used by H6. -/
theorem hmptAsymptoticScale_spec (n : ℕ) :
    3 ≤ hmptAsymptoticScale n ∧
      n * Nat.clog 2 n ≤ hmptAsymptoticScale n ^ 2 ∧
      hmptAsymptoticScale n ≤
        Nat.sqrt (n * Nat.clog 2 n) + 3

end ErdosSzekeres
```

Module `ErdosSzekeres/HMPTExplicitUpper.lean`:

```lean
namespace ErdosSzekeres

/-- The H5 bound after the exact square-root parameter choice. -/
theorem hmpt_scale_upper (n : ℕ) (hn : 3 ≤ n) :
    ForcesConvexPolygon n
      (2 ^ (n + 32 * hmptAsymptoticScale n + 1))

/-- The explicit HMPT upper bound in published asymptotic form. -/
theorem hmpt_explicit_upper (n : ℕ) (hn : 3 ≤ n) :
    ForcesConvexPolygon n
      (2 ^ (n + 32 * Nat.sqrt (n * Nat.clog 2 n) + 128))

end ErdosSzekeres
```

Every implementation declaration not listed above must be private.

## Mandatory arithmetic ledger

Put `C = n * Nat.clog 2 n` and `r = hmptAsymptoticScale n`.

1. Prove `3 ≤ r`, `C ≤ r^2`, and `r ≤ Nat.sqrt C + 3` directly from the
   natural square-root specification and the `max` definition.
2. From `0 < r` and `C ≤ r*r`, prove `C ⌈/⌉ r ≤ r` without using division in
   a truncated or zero-denominator case.
3. Deduce `hmptAggregationExponent n r ≤ n + 17*r` exactly.
4. Prove `2^(32*r) < 2^(n + 32*r + 1)`, so the endpoint cardinality premise
   supplies the strict `exists_porValtrSupportProductData` threshold.
5. Prove
   `4*r + 2^(hmptAggregationExponent n r + 1) ≤
      2^(n + 32*r + 1)`.
   The additive `4*r` must be absorbed by explicit positive power slack; no
   asymptotic notation or false strict estimate may replace this inequality.
6. For arbitrary general-position `P` above the scale threshold, assume
   `¬ContainsConvexSubset P n`, obtain support data exactly once, apply
   `PorValtrSupportProductData.card_lt_hmptAggregation`, and derive the
   contradiction on the unchanged carrier `P`.
7. Use `r ≤ Nat.sqrt C + 3` and monotonicity of powers to obtain the frozen
   `+128` public endpoint.

No profile reselection, aggregate premise, source-threshold premise, target
certificate, changed carrier, real-valued asymptotic library, or stronger
lower bound on `n` is permitted.

## Execution slate

This is a concentrated four-slot `FP-15.C` slate because H6 is the unique
ready cut vertex and the portfolio has no other advancing entry.  The two
checking slots are not independent proof routes.

1. **Proof-producing, parameters.** Prove the exact parameter module with at
   most four guarded direct attempts, then a targeted build and declaration
   audit.
2. **Proof-producing, endpoint.** Root composes the admitted parameter module,
   source producer, and H5 theorem; kernel work starts only after the parameter
   gate passes.
3. **Information-gathering, source/contract audit.** Authenticate the source
   boundary, freeze an independent arithmetic ledger before source release,
   and review exact worker hashes read-only.
4. **Information-gathering, controls.** Freeze two independent natural-number
   evaluators before one-shot execution.  Test all ledger inequalities and
   reject corruptions including removal of the square-root `+1`, removal of
   `max 3`, floor-for-ceiling substitution, threshold equality, and loss of
   the reserved exponent bit.  Controls are never theorem evidence.

Only one Lean/Lake builder may run at a time.  Each guarded command has a
30-minute wall limit, 12 GiB aggregate RSS limit, and one Lean process.  The
controls lane has ten active minutes, four cores, 4 GiB RAM, and 256 MiB output.

## Evidence gates

Each theorem module requires exact schema/revision/input admission, an exact
statement and public-surface audit, no forbidden trust construct, no line over
100 characters, a warning-clean direct-file gate, targeted module build, and a
declaration-only axiom audit admitting only
`[propext, Classical.choice, Quot.sound]`.  Full success additionally requires
independent source review, the corroborating controls disposition, guarded
`make test`, Wayfinder reconciliation, exact staging, commit, and push.

## Decision criteria

Accept only the exact four frozen declarations on the original carrier after
all theorem, review, controls-disposition, repository, staging, and publication
gates pass.  Any added premise, changed exponent, changed carrier, nonstandard
axiom, or failed repository gate selects the corresponding stopped outcome
below rather than LAND.

## Predeclared outcomes

- `HMPT-H6-LAND`: all four frozen public declarations pass their theorem gates
  and the repository gate.  The scoped dependency set changes `{H6}` to empty.
- `HMPT-H6-PARAMETER-LAND`: the exact parameter declarations compile but the
  endpoint reaches another declared stop; H6 remains open.
- `HMPT-H6-CONTRACT-MODIFY`: review or smoke evidence rejects the frozen
  constants or signature before proof dispatch.
- `HMPT-H6-INTERFACE-GAP`: H5 and the source producer cannot compose without a
  new premise, carrier change, or missing theorem.
- `HMPT-H6-FALSIFIED`: a kernel-checked natural-number counterexample refutes a
  frozen declaration.
- `HMPT-H6-INERT`: only a target-equivalent premise, altered exponent, or
  non-public endpoint can be proved.
- `HMPT-H6-RESOURCE`: an attempt, wall-time, memory, or output limit is reached.

## Proof-distance accounting

Before this ticket the official HMPT finite-layer set is `{H6}`.  Only
`HMPT-H6-LAND` changes it to empty without displacement.  That is forward proof
movement at the published-bound scope ceiling, supported by compiling theorems
and repository tests.  It leaves `D-UPPER`, `D-HALF`, `D-DECOMP`, and
`D-NORMALIZE` unchanged.  Review and controls are neutral search information.

The counterfactual test for LAND is positive: knowing the result beforehand
removes the final dependency of the already-vetted HMPT literature route.
Planning consequence: close `FP-15.C` at its declared scope ceiling and require
a fresh route review before using the machinery toward the exact conjecture.

## Resolution

`HMPT-H6-LAND`.  All four frozen public declarations compile without changing
a statement, premise, constant, carrier, or trust boundary.

- `HMPTAsymptoticParameters.lean` has SHA-256
  `a141374ebe22f301450c7799e974e909c3115cc286cf639b1fdd55590be67df3`.
- `HMPTExplicitUpper.lean` has SHA-256
  `e38fee3ef78fafbd04851561d2472afc39ab976c034ae99d49ccdb3216f07374`.
- Warning-clean direct checks, targeted builds, and declaration-only audits
  pass; the public theorems use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Independent exact-hash review found no source, arithmetic, interface,
  carrier, public-surface, circularity, or trust defect.  Independent bounded
  controls agreed on 73,737 positive checks and rejected 49,281 corruptions;
  these controls are neutral corroboration rather than theorem evidence.
- The guarded repository gate passes before integration is committed.

**Net proof movement:** forward within `FP-15.C`; the predeclared set `{H6}`
decreases to empty.  **Evidence:** compiling theorems and repository tests.
**Difficulty displaced:** none within H6.  **Counterfactual:** positive at the
declared published-bound scope.  **Planning consequence:** mark `FP-15.C`
complete and require fresh review before any exact-route reuse.  No
load-bearing destination edge changes.
