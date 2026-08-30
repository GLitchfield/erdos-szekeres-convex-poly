---
title: Audit the half-pure singleton-fan theorem entry
type: research
mode: HITL
status: closed
claim: half-pure-singleton-fan-entry-audit-2026-08-30
blocked_by: none
---

# Ticket 0105: audit the half-pure singleton-fan theorem entry

## Question

Can `HalfPureSingletonFanProducerAboveAt k` be factored into a genuinely
smaller geometric pivot/fan theorem, with a decreasing measure and the existing
half-subset consumer, so that the first post-Ticket-0103 `D-HALF` structural
block can honestly freeze a proof-producing Lean packet?

## Decision criteria

1. Reconstruct the exact producer, inverse-stepping kernel, and named
   `PredecessorHalfSubsetAt` consumer before proposing another interface.
2. Separate the geometry-only singleton deep-split witness from the internal
   cup/cap purity obligation and test whether either factor is independently
   useful.
3. Exhibit a strict decrease in a predeclared measure, rather than move
   predecessor-freeness into a differently worded premise.
4. Hostile-test the factorization against the exact Fin8, Fin10, Fin11, and
   Fin13 fan evidence and against the literal information retained by
   `HasDeepBelowSplit`.
5. Freeze a Lean packet only if all five Ticket 0103 theorem-entry fields pass;
   otherwise close at a bounded route-design stop and reconcile `FP-01`.

## Approved boundary and baseline

The user approved one bounded 60--90 minute information-gathering theorem-entry
block after Ticket 0104.  The checkpoint is commit
`fb101469c89205c9d6f895a806b84b0ada1c7790` on
`codex/state-578-tree-reservoir`; its guarded `make test` had completed all
11,753 Lean jobs and 348 workflow tests before this audit.  This ticket
authorizes no Lean implementation, finite solver work, provider call, service
action, or later execution slate.

The block used only read-only repository inspection.  It opened no run
artifact, solver, proof certificate, provider review, scheduler process, or
idea-generator process.  The scheduler remains intentionally stopped and the
continuous idea generator remains failed/stopped.

## Evidence boundary

The admitted inputs are current compiling theorem signatures and proofs in
`HalfPureSingletonFan.lean`, `InverseSteppingUpKernel.lean`, and
`Decomposable.lean`, together with the already reconciled finite controls in
Experiments 0102 and 0104, `FP-01.A`, `FP-17`, and Ticket 0057.  The
fixed-witness equivalence and candidate factorizations below are a
proposal-level interface audit; this ticket adds no Lean declaration and
claims no new mathematical theorem.

## Structural position reconstructed

The exact consumer ladder already compiles:

```text
HalfPureSingletonFanProducerAboveAt k
  -> predecessorFree_lower_of_cupPure / predecessorFree_upper_of_capPure
  -> PredecessorHalfSubsetAt k
  -> sweepExactUpperAt_of_predecessorHalfSubset
```

At or below `2 * k - 3`, the consumer uses the elementary predecessor
bicoloring theorem.  Above that threshold, the producer must choose a side and
an exterior singleton with three pieces of data:

1. the side has at least half the ambient cardinality;
2. the side and singleton form a deep-below split in one orientation; and
3. every strong `(k-1)`-polygon internal to the side is respectively a cup or
   cap.

The inverse-stepping kernels use the opposite singleton to extend any such
pure predecessor to a forbidden strong `k`-polygon.  They therefore convert
item 3 into predecessor-freeness under the target-free premise.

## Fixed-witness conclusion-erasure audit

For a fixed lower-side witness, abbreviate

```text
CupPure(k, lower) :=
  every strong (k-1)-polygon contained in lower is a cup.
```

Under `1 <= k`, a deep split `HasDeepBelowSplit chi lower upper`, a nonempty
`upper`, and absence of a strong `k`-polygon in the ambient carrier, the current
kernel proves

```text
CupPure(k, lower)
  -> not ContainsStrongPolygonSet chi lower (k - 1).
```

The reverse implication is immediate from the definition of
`ContainsStrongPolygonSet`: if no strong `(k-1)`-polygon is contained in
`lower`, then a polygon satisfying the subset, cardinality, and strong
hypotheses is impossible, so the cup conclusion follows vacuously.  Thus, at
the already selected target-free deep-split witness,

```text
CupPure(k, lower)
  <-> not ContainsStrongPolygonSet chi lower (k - 1).
```

The color-dual statement gives the same equivalence between cap purity on the
upper side and predecessor-freeness there.  Only the forward implications are
existing named Lean theorems; the displayed biconditionals record this
proposal-level logical audit, not new compiled results.

This matters for theorem entry.  Factoring the producer into

```text
half-sized singleton deep split + pure internal predecessors
```

does not factor the hard obligation into independently smaller pieces.  The
first part chooses a structured side but supplies no half-subset consumer.  In
the context supplied by that first part, the second part is exactly equivalent
to saying that the chosen half-sized side is predecessor-free.

## Five-field theorem-entry memo

### 1. Exact producer theorem and model tier

The geometry-only factor can be stated exactly at the sweep-realizable tier:
above `2 * k - 3`, every target-free coloring would admit a half-sized side and
an exterior singleton forming one orientation of `HasDeepBelowSplit`.  This is
a natural witness statement, but it does not imply `PredecessorHalfSubsetAt k`.

Adding the current cup/cap purity clause recovers
`HalfPureSingletonFanProducerAboveAt k` itself.  No intermediate conclusion
strictly between those two statements has been identified.  Field 1 therefore
fails for a smaller theorem-entry producer, even though the existing full
producer and its consumer are precisely stated.

### 2. Existing named downstream consumer

`predecessorHalfSubsetAt_of_halfPureSingletonFanProducerAbove` is a direct,
compiling consumer.  It feeds
`sweepExactUpperAt_of_predecessorHalfSubset`, so the consumer ladder has no
speculative arrow.  Field 2 passes.

### 3. Strict difficulty separation or measure decrease

Before the proposed factorization, the open obligation is to choose a
half-sized predecessor-free support.  Afterwards, it is to choose a half-sized
singleton-split side and prove an internal purity assertion equivalent at that
witness to predecessor-freeness.  No open case, hypothesis strength,
quantifier block, parameter, certificate size, or unresolved dependency depth
decreases.  The geometry clause adds witness structure while the purity clause
retains the original hard conclusion.  Field 3 fails.

### 4. Small hostile neighboring worlds

The factorization was checked against the relevant admitted boundaries:

- `halfPureDeepSplitAtFiveFinEight_of_oneChange` compiles for every exact Fin8
  control, but its fixed scope supplies no arbitrary-size induction or
  selection rule.
- `halfPureSingletonFanAtSixFinTen_of_oneChange` is a nonvacuous exact finite
  theorem, and the synchronized Fin11 fan theorem plus its fixed consumer also
  compile.  Neither is a required base case in an admitted uniform recurrence.
- `FP-17` transports one Fin11 support into an arbitrary window, but a six-point
  support meets the half inequality only through ambient size twelve; audited
  selector/gluing repairs either fail to grow a free support or restore the
  target witness.
- Ticket 0057's abstract Fin13 coloring refutes only the universal rule that an
  arbitrary pure size-six fan extends: one pure fan has all six insertions
  fail.  The weaker rule that some fan extends was not tested, but choosing
  that fan is precisely the missing global selector and is not a smaller
  producer.
- `HasDeepBelowSplit` fixes crossing triple colors and explicitly excludes
  triples lying wholly in either side from its crossing law.  It therefore
  cannot, by itself, determine the internal cup/cap purity needed by the
  consumer.

These controls do not refute a new geometry-specific mechanism.  They do show
that larger finite cases, arbitrary fan extension, window gluing, and the bare
deep-split predicate do not supply the missing strict reduction.  Field 4
passes as a hostile-test inventory.

### 5. Fact expected to produce the theorem

A qualifying successor would need a new sweep-geometric law that selects a
side independently of predecessor-freeness and forces internal purity through
a decreasing statistic, for example a monotone pivot/fan potential whose
minimum excludes every impure predecessor and whose transition is proved to
terminate.  The statistic must see internal triples; the current deep-split
interface sees only crossing triples.

No repository theorem, authenticated source claim, or admitted finite invariant
supplies such a law.  Universal abstract fan extension is already false at its
tested scope, while selective extension has no independent selector.  Field 5
is missing.

## Resolution

`DHALF-FAN-THEOREM-ENTRY-NOT-QUALIFIED__PURITY-RESTATES-PREDECESSOR-FREENESS`.

The existing inverse kernels and the Fin8, Fin10, and Fin11 theorems remain
valid reusable infrastructure at their exact scopes.  The historical use of
“noncircular consumer” remains correct in the narrow syntactic sense that the
consumer assumes neither the same-`k` exact upper bound nor the named
`PredecessorHalfSubsetAt` proposition.  Under Ticket 0103's stricter
proof-distance test, however, its producer premise has no independently
smaller known source: after fixing the singleton split, purity restates the
predecessor-free conclusion.

Do not freeze a geometry-only split adapter, a vacuous purity lemma, a uniform
fan-extension builder, another finite fan certificate, or a proof-producing
label.  Reopen a uniform fan descendant only when a prospective memo supplies
an independently defined internal-triple invariant, a strict decreasing
measure, and a direct selection theorem that does not name the final free
support.

This approved block contains **zero proof-producing slots and one
information-gathering route-design slot**.  It ends at its predeclared honest
stop.  No execution slate is frozen or authorized.

## Proof-distance accounting

- **Net proof movement:** neutral.
- **Evidence:** proposal-level dependency and conclusion-erasure audit against
  compiling Lean kernels/consumers and previously admitted finite controls.
- **Damage scope:** `candidate-local`; only the attempted factorization of the
  existing pure-fan premise as an independently smaller producer is withheld,
  not every geometric fan, pivot, or predecessor-half mechanism.
- **Difficulty displaced:** none.  The uniform half-support selector and
  internal predecessor-freeness obligation remain exactly as hard, and the
  fixed-six domain still first fails at ambient cardinality fifteen.
- **Counterfactual test:** knowing the equivalence before a builder run avoids
  formalizing an adapter whose final premise is the original hard conclusion,
  but does not reduce the estimated remaining proof work or raise the route's
  admitted success probability.
- **Planning consequence:** retain `FP-01` as `gated`, preserve its completed
  finite children, schedule no immediate pure-fan descendant, and return to a
  source-grounded distinct-mechanism allocation under Ticket 0103 before
  reconsidering either load-bearing route.
- **Load-bearing ledger edge changed:** none.

This is not a newly admitted mathematical refutation, so it receives no
failure genome.
