# Experiment 0097: Layer-F stratified-rank gate

Date: 2026-08-10

Status: Highest-cardinality rank passes the bounded gate; threshold descent open

## Question

Which ordering of decomposition-prime restrictions is best aligned with a
macro of at most three target-free mutations: the raw number of cores, a
highest-cardinality-first profile, or a minimum-cardinality-first profile?

## Complete seven-point gate

The producer enumerated all 24,698 rank-three signotopes on seven vertices.
Among 22,402 target-free colorings, 13,248 are nondecomposable sources. For
each of the three ranks, every source has a target-free abstract endpoint with
smaller rank within radius three:

| First descent radius | Sources |
| ---: | ---: |
| 1 | 13,098 |
| 2 | 148 |
| 3 | 2 |

Four sources have a smaller endpoint within radius three but no path whose
intermediate ranks are all nonincreasing. This independently confirms the
formal interface choice: only the macro endpoint should be required to
decrease.

## Selected eight-point and spectator gates

The audit tested every target-free nondecomposable eight-point signotope
extending the forty hard seven-point prime-deletion controls. All 2,158 sources
descend for every tested rank: 2,154 at radius one and four at radius two.

A one-uniform-spectator stress test retained 61,872 target-free extensions of
seven-point descending edges. Every retained extension preserved the raw-rank
ordering; 14,516 other extensions became targetful, with no retained tie or
reversal.

The producer and an independent checker agree on all ten validation gates. An
existing kernel-checked rational positive control supplies one exact
realizable edge: changing `(0,5,6)` takes prime profile
`[0,0,0,0,0,0,0,1]` to zero.

## Route disposition

- **GO:** highest-cardinality-first `StratifiedPrimeCoreRank`. It matches the
  compiling locality theorem: arbitrary creation in lower strata cannot undo
  a drop at the highest changed stratum.
- **MODIFY/retain:** raw `PrimeCoreCount`. It remains an exact accounting and
  diagnostic tool, but a descent requires a global destroyed-versus-created
  balance.
- **STOP as primary:** minimum-cardinality-first weighting. It is not
  computationally refuted, but it prioritizes exactly the lower-stratum
  changes that the current macro contract deliberately leaves unconstrained.

The next Lean theorem is the arithmetic bridge

```lean
stratifiedPrimeCoreRank_lt_of_topStratumDrop
```

The subsequent load-bearing geometric contract is
`ThreeStepTopPrimeStratumDropsAboveAt`.

## Evidence boundary and resources

Seven and eight vertices are below the `k = 6` exact threshold of 17. These
results test proposed local machinery; they do not prove or refute the
threshold-scoped Layer-F theorem or the happy-ending conjecture.

- result SHA-256:
  `4f1355980a010c6ec7610813d8f8f6cbf6aa9ce16f4373df2aa2004c9fd35799`
- independent checker SHA-256:
  `801f225c139e3d60cb08a44b7d7d3e12a9f2892218193428b677ee5842c06218`
- producer: 61.26 seconds, 127,032 KiB peak RSS
- checker: 157.39 seconds, 154,316 KiB peak RSS
- packet outputs:
  `runs/agents/20260810-layerf-rank-falsifier/`
