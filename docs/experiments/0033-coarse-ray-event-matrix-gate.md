# Coarse ray-event incidence-matrix gate

## Question

The complete-chain event key of Experiment 0032 is too fine: it makes four
earlier present sets disjoint before an absent set of size three.  The
Innovation Scout proposed a semantic quotient, and Laplace froze it precisely
before implementation.  A key is

    (normalized direction, ordinal chain role, clipped complementary depth).

The direction is the past/future endpoint choice already used by the child-ray
bridge.  The role is the marked vertex's position in an increasing exact-size
active chain.  Complementary depth is the maximum opposite-color one-sided ray
rank inside the same active child, clipped at `k-2`.

This gate asks whether the resulting fiberwise incidence relation supports
fixed local skew set pairs on the frozen `n = 12`, `k = 7` frontier.

## Noncircular contract

For each span, enumerate every exact-size active child-chain witness and map
each marked role to its coarse key.  `CoarseIncident span key` holds when any
fine witness maps to that key.  The present set uses the minimum binary-code
active chain.  A key is absent only when it is **not** coarsely incident; mere
failure to occur in the selected chain is insufficient.

The absent set is local and deterministic: take the first `k-rank-1` absent
keys ordered by direction agreement with the span, then role, then depth.  It
does not inspect earlier spans.  For rank three and `k = 7`, the directed key
space has `2 * 2 * 6 = 24` keys, every present set must have size two, and every
absent set size three.

In addition to testing this fixed choice, the gate computes for every later
span the minimum number of its zero-incidence columns needed to hit all earlier
present sets.  If an earlier present set contains no zero column, no absent
tie-breaking can repair the quotient.

## Frozen result

The fixed local selection already fails for the first ordered pair.  More
decisively, the adjacent spans `(2,5)` and `(4,6)` have identical directed
coarse present keys

    (past, role 0, depth 0),
    (past, role 1, depth 2).

Those keys are also incident to the later span.  Fiberwise absence therefore
forbids both of them from every absent set at `(4,6)`, making its zero-column
hitting number undefined.  Thus the required skew intersection is impossible
regardless of absent-set ordering or capacity.

Forgetting direction does not help: the same adjacent pair still has identical
role/depth keys and fails fiberwise cross-incidence.  Restoring chain or
endpoint identity returns toward the already-refuted fine key.

## Independent replay

The producer uses the cell-mask decomposable-coloring implementation and its
local pair-rank recurrence restricted to the active child.  The checker uses
the independent recursive replay and reconstructs complementary ranks on the
upper-child support.  Both reproduce all active chains, 24 incidence columns,
present and absent sets, 15 ordered-pair intersections, minimum zero-column
hitting rows, and the direction-forgetting diagnostic.

The compact manifest SHA-256 is
`edefca6cd37ba68702d74352a679acecaffd6d559ae74f5cf625d9742f5a080a`.

## Claim boundary and route consequence

This is bounded computational evidence, not a Lean theorem.  It refutes the
exact rank-role-depth quotient and any absent selection respecting its
fiberwise incidence on this frozen root.  It does not refute all conceivable
actual-ray invariants, but it closes both event encodings proposed after the
active-interval theorem failed.

The pending strategic choice is now between the two other Innovation Scout
mechanisms:

1. exact rational independence of the existing reflected endpoint-incidence
   rows; and
2. two-lane meet/join uncrossing inside the existing untagged ideal lattice.

A bounded Sol/Fable review must choose the next falsification gate before
either mechanism is promoted to Lean.

## Reproduction

    python3 scripts/check_coarse_ray_event_matrix.py \
      --output data/derived/e3-coarse-ray-event-matrix-frozen-n12-k7.json
    python3 scripts/replay_coarse_ray_event_matrix.py \
      data/derived/e3-coarse-ray-event-matrix-frozen-n12-k7.json
