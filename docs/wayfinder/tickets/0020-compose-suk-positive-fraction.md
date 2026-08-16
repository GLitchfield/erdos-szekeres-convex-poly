---
title: Compose the Suk positive-fraction upper bound
type: research
mode: AFK
status: closed
claim: codex-suk-positive-fraction-2026-08-16
blocked_by: none
---

# Ticket 0020: compose the Suk positive-fraction upper bound

## Question

Can the completed original-carrier Suk/Pór--Valtr source and both finite branch
consumers be composed at exact natural parameters, then bounded by one explicit
power, without assuming any pool, branch, selected target, or asymptotic
inequality?

## Decision

Execute the final two stages of `FP-15.B` in strict order:

1. prove and consume one rounding-safe natural-number parameter bundle; and
2. compare its exact forcing threshold with one conservative explicit
   `2^(n + O(n^(2/3) log n))` power.

The point-set source, cyclic raw-pool bridge, density-slack lemma, global
chain/antichain split, both branch consumers, and branch integration are
already compiling.  This ticket must not reopen or assume any of them.

## Decision criteria

Only a compiling theorem from arbitrary original point sets can close
`C-compose`, and only a compiling comparison at the canonical least cubic
scale can close `C-asymptotic`.  Controls and reviews may admit evidence or
reject a formula, but do not move either dependency by themselves.  Neither
closure may be credited to the exact-conjecture ledger without a separate
proved implication.

## Proof-distance boundary

At admission, `FP-15.B` has two open scoped dependencies:

- `C-compose`: instantiate every finite global parameter and compose the
  original-carrier point-set source through the global branch consumer;
- `C-asymptotic`: dominate the resulting exact threshold by a source-shaped
  explicit power.

Closing `C-compose` changes that scoped count from two to one.  Closing the
explicit power theorem changes it from one to zero.  Neither outcome changes
`D-UPPER`, `D-HALF`, `D-DECOMP`, `D-NORMALIZE`, or any other load-bearing exact
conjecture edge.

## Frozen parameter architecture

For a target `n` and an integer scale `s`, use

```text
m         = s
t         = ceilDiv s 2
L         = (2*t - 1)*s
K         = ceilDiv n s
capSize   = 2*K
chainSize = 2^(n + K - 4) + 1
antiSize  = choose (n + 2*K - 4) (n - 2) + 1.
```

The scale hypotheses are `5 <= s`, `(s-1)^3 < n`, and `n <= s^3`.
This makes the path length exact instead of relying on a false rounding
identity between independent real ceilings.  The threshold is the maximum of
the twice-fine-denominator requirement and the coarse-denominator multiple
needed to make every raw pool strictly exceed
`(chainSize-1)*(antiSize-1)`.

The canonical scale `sukCubeScale n` is the least `s` with `n <= s^3`.
The conservative final exponent is

```text
n + 64*(sukCubeScale n)^2*Nat.clog 2 (3*n) + 128.
```

The coefficient 64 is a formal robustness margin, not a claim to reproduce
Suk's optimized published constant 6.

## Frozen public outcomes

- `SUK-PARAM-LAND`: the exact parameter bundle compiles and the independent
  checker accepts the frozen formulas.  This is not counted as forward proof
  movement until consumed.
- `SUK-POSFRAC-LAND`: a theorem `ForcesConvexPolygon n` at the exact threshold
  compiles from an arbitrary original point set, without supplied pools,
  branches, target subsets, or global cardinal inequalities.  This closes
  `C-compose`.
- `SUK-EXPLICIT-UPPER-LAND`: the conservative explicit power theorem compiles,
  together with the exact cubic-scale certificate.  This closes
  `C-asymptotic`.
- `SUK-PARAM-FALSIFIED`: a frozen arithmetic formula has an independently
  checked exact counterexample.  Preserve the first witness and reject only
  this parameterization.
- `SUK-COMPOSITION-MISMATCH`: the admitted source and consumer expose a genuine
  unproved interface not present in the frozen dependency ledger.
- `SUK-BOUND-INERT`: the exact composition compiles but the frozen power bound
  does not; retain `C-compose` and leave `C-asymptotic` open.
- `SUK-RESOURCE`: a declared resource or unchanged-obligation stop is reached.

## Execution discipline

This is a concentrated `FP-15.B` slate because the portfolio has no other
advancing theorem gate and the two targets are serial consumers of the same
now-complete source architecture.  Three slots are proof-producing and two
are information-gathering.  Freeze all contracts and controls before outcome
inspection, keep module write sets disjoint, serialize every Lean/Lake command,
and independently review the final public declarations before integration.

Do not silently alter `n0 = 65`, the parameter formulas, the exact threshold,
or the final exponent.  Representation-only Lean repairs are allowed.  A
mathematical contract change requires a new outcome and a new plan.

## Resources and approvals

- Each process: at most 30 minutes.
- Lean/Lake: one process at a time, at most 12 GiB.
- Controls: at most 4 cores and 8 GiB.
- New run artifacts: at most 2 GiB.
- No solver, download, installation, provider call, destructive operation,
  raised cap, theorem weakening, `sorry`, `admit`, unsafe axiom,
  `native_decide`, or external oracle.
- On an admitted result, root alone integrates shared imports and strategic
  documents, runs `make test`, commits, and pushes the approved branch.

## Innovation decision

Skip a new innovation or Sol/Fable route review.  This is ordinary
implementation of the unchanged next gate selected by tickets 0018 and 0019,
not a new invariant or route redirect.  Any material source or theorem-contract
change stops this ticket and requires review before another execution slate.

## Resolution

The ticket closed with all frozen public outcomes admitted.

- `PorValtrCyclicSupportData.toSukConsecutiveRawPoolsWithCarrier` repairs the
  one missing public carrier projection without changing the older raw-pool
  bridge.
- `sukPositiveFractionParameters_valid` proves every rounding-safe natural
  parameter field.  The separately frozen finite controls ultimately admitted
  their positive range and corruption recovery, but remain computational
  evidence rather than a theorem.
- `sukPositiveFraction_forces_threshold` composes the arbitrary original
  point-set source, carrier-preserving raw pools, density conversion, and both
  global branch consumers.  It assumes no pool, branch, selected subset, or
  global inequality and closes `C-compose`.
- `sukCubeScale_sq_cube_le` and `suk_explicit_upper` prove, for `65 <= n`, the
  exact frozen cubic-scale certificate and the forcing threshold

  ```text
  2^(n + 64*(sukCubeScale n)^2*Nat.clog 2 (3*n) + 128).
  ```

  This closes `C-asymptotic` without changing the coefficient, logarithm, or
  additive constant.

## Evidence

All four modules passed warning-clean direct Lean checks, targeted module
builds, and declaration-only axiom audits with standard mathlib axioms only.
Independent read-only reviews accepted the composition and explicit-bound
statements, source consumption, carrier transport, inequality chain, import
DAG, and trust boundary.  The approved slate remained three proof-producing
slots and two information-gathering slots; the composition slot first landed
the carrier-preserving bridge exposed by its preaudit.

**Net proof movement:** forward within `FP-15.B`.  The predeclared scoped
dependency count decreases from two (`C-compose`, `C-asymptotic`) to zero.
**Evidence:** compiling Lean theorems with targeted builds and standard-only
axiom audits; finite controls and reviews are supporting checked computation
or proposal-level evidence.  **Difficulty displaced:** none inside the frozen
Suk positive-fraction ladder; the exact threshold comparison and canonical
scale are proved rather than moved into premises.  **Counterfactual:** knowing
these theorems before the run removes all remaining work in the ticket and
would materially reduce the scoped proof estimate.  **Planning consequence:**
mark `FP-15.B` complete and unlock a separately reviewed `FP-15.C` gate; do not
claim any change to `D-UPPER`, `D-HALF`, `D-DECOMP`, `D-NORMALIZE`, or
`D-ASSEMBLE`.
