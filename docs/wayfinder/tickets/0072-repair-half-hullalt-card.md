---
title: Repair the HALF-HULLALT admission packet
type: research
mode: HITL
status: closed
claim: codex-half-hullalt-card-repair-2026-08-23
blocked_by: none
---

# Ticket 0072: repair the `HALF-HULLALT` admission packet

## Question

Can the three exact defects admitted by Ticket 0071 be closed without running
the proposed `HALF-HULLALT` falsifier panel: a literal fixed `k = 4`
`PredecessorHalfSubsetAt` theorem, an authenticated in-range
decomposition-prime control, and a hash-frozen combinatorial hull-layer
producer/checker packet?

## Decision criteria

Close as `HULLALT-REPAIR-FROZEN` exactly when the literal Lean base theorem
passes its proof and axiom gates, two independent exact implementations agree
on an authenticated in-range decomposition-prime target-free control, and the
independent hull producer/checker packet passes its schema, manifest, parity,
fixture, and corruption gates. Any missing mathematical field yields the
corresponding partial or gap terminal defined below. Success authorizes only a
new route-admission review; it does not authorize the `HALF-HULLALT` panel or
portfolio promotion.

## Authorization and slate classification

The user approved this rolling repair wave. It contains **one
proof-producing mathematical gate** and **two information-gathering
mathematical gates**:

1. compile `PredecessorHalfSubsetAt 4` in Lean;
2. classify the full support of the authenticated 13-point affine-bad,
   strong-six-free realization for decomposition primality using two
   independent exact implementations; and
3. freeze the canonical alternating-hull-layer semantics, primary producer,
   independent checker, artifact schema, manifest, and corruption controls.

The two 13-point implementations are independent evidence roles for one
mathematical gate, not two portfolio lanes. All three gates repair mandatory
fields of the sole near-card upheld by Ticket 0071, so this wave intentionally
concentrates on one mechanism family. That concentration is justified by
distinct success criteria and does not represent three independent routes.

No external provider or network call, software installation, destructive
operation, process termination, external repository mutation, commit, push,
or actual `HALF-HULLALT` target/predecessor panel is authorized. A later
Sol/Fable admission review and any panel execution require separate selection
and approval after this ticket is reconciled.

## Gate A: fixed `k = 4` Lean endpoint

The immutable theorem contract is:

```lean
theorem predecessorHalfSubsetAt_four : PredecessorHalfSubsetAt 4 := by
  ...
```

It belongs in `ErdosSzekeres/StrongPredecessorBaseFour.lean`, imports only
ordinary project modules, and may use the existing realizable five-point
theorem
`SweptConfiguration.exists_strong_four_of_five_le`. The theorem statement may
not be weakened, made conditional, or moved to a different model tier.

The intended finite reduction is explicit. Target avoidance and realizability
imply `n <= 4`, because every realizable configuration with at least five
vertices contains a strong four-set. For `n <= 2`, the whole carrier is a
strong-three-free half support. For `3 <= n <= 4`, any two-element support is
strong-three-free and has at least half the carrier. Cardinality alone must
discharge predecessor freeness.

Fixed outcomes:

- `BASE4-LAND`: the literal theorem compiles, contains no `sorry`, `admit`,
  unsafe axiom, or unverified oracle, and its axiom printout contains only
  standard Lean/mathlib axioms;
- `BASE4-CONTRACT-GAP`: the existing five-point theorem cannot be transported
  to the exact contract without changing a frozen statement or model tier; or
- `BASE4-RESOURCE-STOP`: the 90-minute, one-builder, 4 GiB boundary is reached.

Evidence gates are direct-file `lake env lean`, targeted `lake build`, root
review, and eventual project build. Only `BASE4-LAND` is proof-producing.

## Gate B: exact 13-point decomposition-prime classification

The frozen fixture is
`runs/agents/20260823-hullalt-repair/prime-fixture.json`. It is a compact copy
of the exact integer witness authenticated by Ticket 0037 and records its
source artifact hashes. Its full carrier is already checked to be in general
position and strong-six-free; this gate independently rechecks those fields
but changes only the previously unknown decomposition-prime classification.

For every ordered nonempty proper subset `lower` of the 13 labels, set
`upper` to its complement. It is a proper deep-below split exactly when every
crossing increasing triple `(a,b,c)` has positive orientation if and only if
`b` lies in `lower`. All `2^13 - 2 = 8190` oriented partitions must be tested;
swapping the two sides is not a symmetry of this predicate.

The primary implementation may use bitmasks and precomputed crossing
profiles. The independent checker must enumerate subsets and crossing triples
directly with sets/tuples and must not read or copy the primary source code.
Both derive signs from exact integer determinants, authenticate the frozen
chirotope hash, verify general position and absence of strong six-sets, and
emit the first exact split certificate if one exists.

Fixed outcomes:

- `PRIME13-PRIME`: neither implementation finds a proper split and all
  authentication checks agree;
- `PRIME13-NOT-PRIME`: both implementations verify the same mathematical
  classification and at least one exact proper split certificate replays;
- `PRIME13-DISAGREEMENT`: implementations disagree on any authentication,
  target-free, or split-classification field; or
- `PRIME13-CLASSIFIER-GAP`: an input/hash/model mismatch prevents exact
  classification.

Each implementation has 30 wall minutes, one CPU core, 1 GiB RAM, and
0.01 GiB output. Repeating seeds or enlarging the instance is prohibited.
This is checked computation, not a Lean theorem. `PRIME13-NOT-PRIME` does not
refute `HALF-HULLALT`; it means this witness cannot fill the required prime
control slot.

## Gate C: canonical hull-layer packet freeze

The card's support is defined from complete ordered-triple orientation data,
not from a target witness.

For a current nonempty set of sweep labels:

1. if it has one or two labels, list them in increasing sweep order;
2. otherwise construct its counterclockwise convex-hull cycle, starting at
   its least sweep label. The primary algorithm uses the increasing/decreasing
   monotone-chain scan with strict left-turn retention. General position
   excludes the collinear branch;
3. remove the entire layer and repeat; and
4. take the labels in zero-based even positions on every canonical layer.

For three or more points the monotone-chain list is
`lower.dropLast ++ upper.dropLast`, where `lower` scans increasing labels and
`upper` scans decreasing labels, popping the middle endpoint whenever the new
triple is not a strict left turn. This convention starts at the least sweep
label and traverses the hull counterclockwise.

The independent checker must recover each hull by the support-line-edge
criterion: a directed edge is a counterclockwise hull edge exactly when every
other current point is strictly to its left. It follows the unique successor
cycle from the least label and does not use the monotone-chain implementation.
It then recomputes the alternating support and the exact identity
`support.card = sum ceil(layer.card / 2)`, hence
`n <= 2 * support.card`.

The packet must contain a human-readable contract, exact schema, primary
producer, independent checker, synthetic general-position fixtures, frozen
hash manifest, and negative corruption controls for at least a wrong cyclic
start, reversed cycle, flipped support membership, and altered input hash.
This gate may test semantics and corruptions on synthetic fixtures, but may
not check predecessor freeness on the proposed target panel.

Fixed outcomes:

- `HULL-CHECKER-FROZEN`: all artifacts and hashes are fixed, independent
  algorithms agree, and every required corruption is rejected;
- `HULL-CHECKER-SEMANTIC-GAP`: orientation data do not determine a unique
  artifact under the frozen convention; or
- `HULL-CHECKER-IMPLEMENTATION-GAP`: the independent implementation or a
  required corruption control cannot be completed inside 60 wall minutes,
  one CPU core, 1 GiB RAM, and 0.02 GiB output.

## Overall terminals

- `HULLALT-REPAIR-FROZEN`: `BASE4-LAND`, `PRIME13-PRIME`, and
  `HULL-CHECKER-FROZEN` all hold. This authorizes a new admission review, not
  the panel or portfolio promotion.
- `HULLALT-PRIME-CONTROL-MISSING`: Gate A and Gate C close, but the exact
  witness is not prime. The card still needs another authenticated in-range
  prime control.
- `HULLALT-REPAIR-PARTIAL`: at least one field closes and another reaches a
  nonmathematical gap or bounded stop.
- `HULLALT-REPAIR-GAP`: none of the three missing fields is closed.

Root alone admits evidence, edits the umbrella module and canonical
Wayfinder files, runs project-wide checks, and resolves this ticket.

## Proof-distance accounting at launch

- **Net proof movement:** `neutral` at launch.
- **Evidence:** approved immutable contracts plus existing compiling and
  checked inputs; no result from this wave yet.
- **Damage scope:** none at launch.
- **Difficulty displaced:** none. Gate A can close the fixed `k = 4`
  subobligation of `D-HALF`; Gates B and C can only make the speculative card
  honestly executable.
- **Counterfactual test:** a compiling Gate-A theorem would strictly reduce
  the open parameter domain for the half-subset recurrence from `k >= 4` to
  `k >= 5`. Gate-B or Gate-C success alone would not reduce proof work.
- **Planning consequence:** execute the three repaired fields in parallel,
  admit each independently, reconcile `FP-01`, and stop before route review or
  panel execution.
- **Frontier portfolio:** unchanged at launch.
- **Load-bearing ledger:** unchanged at launch; `D-HALF` remains open.

## Resolution

Closed as `HULLALT-REPAIR-FROZEN`. All three predeclared repair fields close,
but only the first is proof-producing.

### Gate A: `BASE4-LAND`

`ErdosSzekeres/StrongPredecessorBaseFour.lean` now proves the literal frozen
declaration

```lean
theorem predecessorHalfSubsetAt_four : PredecessorHalfSubsetAt 4 := by
  ...
```

The proof opens the sweep realization, uses the existing five-point
strong-four theorem to force `n <= 4`, and then obtains a predecessor-free
half support by cardinality. Direct-file Lean, the targeted module build, the
umbrella import, and an independent reviewer replay all pass. The admitted
axiom boundary is exactly `propext`, `Classical.choice`, and `Quot.sound`; no
`sorry`, `admit`, unsafe axiom, or external oracle occurs.

This closes the named fixed `k = 4` subobligation of `D-HALF`. The unresolved
parameter domain strictly decreases from every `k >= 4` to every `k >= 5`.
It proves nothing at those higher parameters.

### Gate B: `PRIME13-PRIME`

The exact 13-point affine-bad fixture from Ticket 0037 is now an authenticated
in-range decomposition-prime target-free control at checked-computation
level. The primary classifier uses bitmasks and precomputed triple-violation
profiles. The independent classifier uses direct combinations, frozensets,
complements, and exact determinant predicates. Their source and evidence
artifacts are distinct.

Both implementations and the canonical v2 reviewer agree on:

- 286 nonzero increasing-triple determinants, with 166 left and 120 right;
- the frozen ASCII-bitstring chirotope SHA-256
  `24ebbf6f5cece3d14756efbf2d7a11d5b78b9d127513a49519f171d3d147c716`;
- all `8190` oriented nonempty proper lower sets, without quotienting swapped
  sides;
- `1757184` crossing-predicate evaluations and zero proper deep-below splits;
- all `1716` six-subsets and their `25740` within-six quadruple evaluations,
  with zero strong six-sets;
  and
- `IsDecompositionPrimeOn` for the full 13-label support in this exact finite
  model.

The recorded signed-triple metadata hash is not newly admitted because its
serialization was not part of the frozen contract. The required fixture hash,
integer coordinates, and ASCII orientation hash all replay. This finite
classification neither proves nor refutes `HALF-HULLALT`.

### Gate C: `HULL-CHECKER-FROZEN`

The packet under
`runs/agents/20260823-hullalt-repair/hull-packet/` freezes
`canonical-alternating-hull-layer-v1`. A strict monotone-chain producer and an
independent support-line-edge/successor-cycle checker agree on five synthetic
fixtures covering empty, singleton, pair, one-layer, and two-layer carriers.
They agree on every layer, the zero-based even-position support, and the exact
per-layer parity identity proving `n <= 2 * support.card`.

The Draft 2020-12 schema passes, all ten manifest entries match, and wrong
cyclic start, reversed cycle, flipped support membership, and altered input
hash are all rejected. The manifest SHA-256 is
`deb8d8d1d769610e517475f1cc25bf55b12bc61462b6f700ce2999bb7624cb91`.
No target or predecessor predicate appears in the frozen computation, and no
mathematical panel ran.

### Evidence-admission and operational exceptions

The three original worker packets froze their objectives, base revision,
inputs/hashes, write ownership, budgets, evidence gates, branches, and stops,
but used noncanonical JSON field names and omitted the canonical workspace
fingerprint. Their result files validate, while paired task/result validation
correctly rejects those immutable packet shapes. They were not mutated after
dispatch.

Root replayed every evidence gate and then froze a canonical read-only audit.
Its first version stopped operationally when a successful axiom probe used
`3736560 KiB`, above that packet's 2 GiB ceiling. A separately frozen v2 audit
with an explicit 4 GiB ceiling completed from unchanged hashes and returned
`ADMISSION-AUDIT-ACCEPT`; its fresh axiom probe used `3734792 KiB`. Both
canonical audit task/result pairs and both one-thread audit slates validate.

The original packet-shape defect and the v1 memory stop are
`operational-only`. They neither supply negative mathematical evidence nor
weaken the v2 admission. Future dispatches must use the canonical task schema
before launch. No failure genome is warranted.

### Final proof-distance accounting

- **Net proof movement:** `forward`, solely because the compiling fixed
  `k = 4` theorem closes a named required base and strictly reduces the open
  parameter domain of `D-HALF` to `k >= 5`.
- **Evidence:** compiling Lean theorem for Gate A; independently checked exact
  finite computation for Gate B; checked semantic/tooling computation for
  Gate C; canonical read-only admission review over all three.
- **Damage scope:** `operational-only` for the original packet schemas and v1
  audit memory stop. No mathematical negative is admitted in this ticket.
- **Difficulty displaced:** the fixed base obligation is removed. The hard
  uniform obligation—prove a predecessor-free half support for every
  `k >= 5`—is unchanged; neither the finite control nor the checker makes it
  smaller.
- **Counterfactual test:** knowing Gate A beforehand would reduce remaining
  proof work by removing the fixed base. Knowing only Gates B and C would
  improve reproducibility and card discrimination, not estimated proof work.
- **Planning consequence:** retain `HALF-HULLALT` ledger-only under the
  suspended `FP-01` family and send the now-complete card through a bounded
  route-admission review. Do not run the mathematical panel or promote the
  route before that separate selection and approval.
- **Frontier portfolio:** `FP-01` gains the fixed base theorem and repaired
  near-card evidence; its state remains `suspended`, and no child is added.
- **Load-bearing ledger:** `D-HALF` remains open, but its fixed `k = 4`
  subobligation is closed and its remaining domain is exactly `k >= 5`.

The proof worker reported 4 minutes 44 seconds wall time. The two final exact
classifier runs used about 0.9 seconds each and under 22 MiB peak RSS. The hull
packet stayed far below its output ceiling, but root did not independently
meter its full wall time or peak RSS. The v1 and v2 canonical reviews consumed
9 and 17 wall minutes respectively. No broader resource claim is made.

The final repository gate `make test` passes: the umbrella Lean build completes
all 10,315 jobs, all 221 Python tests pass, and the subsequent exact certificate
and derived-data checkers return success.

## Evidence

- `ErdosSzekeres/StrongPredecessorBaseFour.lean`, SHA-256
  `ce5ccbf0a0c7ee0d69ac5301931f77d52df8e38417de3f2a50f5af6c908837ca`;
- `runs/agents/20260823-hullalt-repair/prime-primary/primary.json`, SHA-256
  `e090c8614191482d91650b2a74f82a7800d6de455c79fcce52d26dd53b169fe6`;
- `runs/agents/20260823-hullalt-repair/prime-checker/independent.json`,
  SHA-256
  `16b7b2ff3695da40d03439321e0aedb64bb72676e199e083b6881ca869447ca0`;
- `runs/agents/20260823-hullalt-repair/hull-packet/manifest.json`, SHA-256
  `deb8d8d1d769610e517475f1cc25bf55b12bc61462b6f700ce2999bb7624cb91`;
- `runs/agents/20260823-hullalt-repair/root-admission.json`, SHA-256
  `790100c576969a4e016f7e68c1052f52521f9147448fbdab197a0953867238e6`;
  and
- `runs/agents/20260823-hullalt-repair/admission-audit-v2/result.json`,
  SHA-256
  `9e24368d6107d12dc4a892a4e28807256d2e710869a3aefa54fd753a6a316804`.
