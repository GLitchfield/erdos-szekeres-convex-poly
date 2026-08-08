# Experiment 0061: central cut and the ordered `6+7` cup-block gate

## Question

Can a one-split visible/hidden-adjacency payment eliminate the first open
`(4,8,8)` critical boundary, and, if that payment fails, does the exact
central-cut structure yield a stronger local theorem?

The boundary has ten lower and thirteen upper vertices.  The parent avoids a
four-cap, an eight-cup, and a strong eight-set, and the upper child is
decomposable.  All computational and agent-review evidence in this experiment
is advisory; only the stated Lean theorems count as completed results.

## Payment audit

Lean first makes the proposed payment exact.  Visible lower adjacencies,
hidden lower adjacencies, and one sentinel partition the lower child, and the
hidden adjacencies are equivalent to the canonical hidden-gap pivot seed.  For
a published lower slice, paying every discarded lower vertex with a hidden
pivot is equivalent to bounding the visible adjacencies by the retained-core
threshold.

The central cut refutes that payment at `10+13`.  Around any lower vertex, the
thirteen upper vertices split into two ordered cup blocks of sizes six and
seven.  A hidden lower adjacency must cross the unique six-to-seven change, so
there is at most one hidden lower gap.  Consequently at least eight of the nine
lower adjacencies are visible, whereas the proposed index-four payment permits
at most six.  The discarded lower residual is three, so it is strictly larger
than the hidden count.

A second repair using the two extrema of a predecessor cap is valid but too
weak.  It provides two selected-core vertices disjoint from the pivots and
therefore bounds the hidden count by six, not by the two needed for residual
payment.  The scalar payment route is retired at this boundary.

## Replacement theorem

The same central cut exposes a stronger local target.  Define
`CupBlocks67Force488` to say that two disjoint, ordered cup blocks of sizes
`6+7` or `7+6`, under the one-change law, contain a four-cap, an eight-cup, or
a strong eight-set.

`StructuralChargingCupBlocks67Symbolic.lean` proves this target without an
external oracle.  In the normalized `6+7` orientation, the proof is:

1. Six equal consecutive turns determine all triples on an eight-chain.
2. For each vertex of the six-block, its turn with the first two vertices of
   the seven-block must be right; otherwise those vertices extend to an
   eight-cup.
3. Four-cap avoidance forces the turn on vertices `4,5,6` to be left.
4. Splitting on the turn `4,5,7`, the left case gives two overlapping
   seven-cups and a right fan, hence a strong eight-set.
5. In the right case, four-cap avoidance forces the turn `5,7,8` left.
6. Splitting on the five turns `5,6,k` for `k = 8,...,12`, any left turn gives
   an explicit eight-cup; if all are right, two split seven-cups give a strong
   eight-set.

Lean proves the normalized theorem, derives `7+6` by reversal, and transports
both orientations to arbitrary ordered finite sets.  Applying it at a deep
root proves `upper.card ≤ 12`.  In particular, the `10+13` critical boundary
is impossible.  At total size 23 the exact remaining oriented window is

```text
11 ≤ lower.card     and     upper.card ≤ 12.
```

This is not the full `(4,8,8)` root transition and is not the general
Erdős--Szekeres formula.  It removes one documented boundary and supplies a
reusable local cup-block theorem.

## Advisory finite evidence and review

Before the symbolic proof was found, CaDiCaL and MiniSat both reported the
normalized `6+7` formula UNSAT.  A reduced 540-clause core had a 248-step LRAT
trace that independently replayed as positive-hint RUP.  The retained hashes
are:

- evidence packet:
  `227fec1b05a3fd7dd68d5ce106c83ec15e4351090f983819f740f262bb59aeab`;
- reduced CNF:
  `9e77b66016b04e10649e5c8d71a9001d160ca7ef2801d5b8ca614abcaf2bf385`;
- reduced LRAT:
  `75c408798a7c7cc4401d6bbcfb36d4981a326f2e2f7af89933457cd6dbec7aab`;
- core map:
  `4ae9e1476f4bb13a7f884ff9ee765a7aca19e93bc0d271eee10bb9dd8d6f641b`.

The certificate path was not promoted because the direct symbolic Lean proof
is smaller conceptually and keeps the result independent of a generated
formula bridge.  Sol rated the pre-proof route `partially_supported` with high
confidence and correctly confirmed that the payment contract fails; its
result hash is
`a576fa28b893f55b0cd3701da9a81983897f8190356686e5aba6d61563bc6356`.
Fable produced no mathematical review because its OAuth token had expired;
the raw output hash is
`225a2f1331d4a3c4c1fb3ed4b38b2403abfc568f44087a2999d8f6c31352f77a`.

## Disposition and next gate

The visible/hidden residual-payment contract and the two-extrema reserve are
retired as ways to close this boundary.  The ordered `6+7` cup-block theorem
is promoted and closes every open root with a nonempty lower child and at
least thirteen upper vertices.

The next route-selection task is to classify the residual critical window
`11 ≤ lower.card`, `upper.card ≤ 12` and identify the smallest additional
root-local structural theorem that excludes those splits.  Any proposed
general invariant must be tested first on that window and must preserve the
asymmetry between four-cap and eight-cup avoidance.  The tree-global ledger
remains parked unless a residual case forces descendant aggregation.
