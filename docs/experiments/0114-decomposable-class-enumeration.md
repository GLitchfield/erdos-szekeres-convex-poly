# Experiment 0114: the abstract decomposable class enumerated through nine vertices

Date: 2026-09-04

Status: exact enumeration, validated against an independent checker;
Workstream B step 1 of `docs/plans/workstream-b-self-reliant-plan.md`.  No
Lean theorem is claimed.

## Question

How many colorings on `n ≤ 9` ordered vertices are decomposable in the sense
of `IsDecomposableOn` (`Decomposable.lean`: a singleton, or a disjoint,
possibly interleaving, lower and upper part, both decomposable, with every
crossing triple a left turn exactly when its middle vertex is in the lower
part), and does Baek–Balko's threshold `decomposableThreshold a u k` hold and
bind exactly in this class at every parameter triple whose threshold is at
most nine?  The per-vertex attachment profiles of the extremal colorings are
the input to the invariant search of step 2.

## Predeclared gates

- For `n ≤ 6`, the enumerated class must equal the set of one-change
  colorings accepted by the census checker (`Coloring.decomposable` in
  `scripts/census_order_type_decomposability.py`, validated in experiment
  0107), and every enumerated coloring at `n ≤ 6` must be accepted by it.
- If any enumerated coloring on `n > decomposableThreshold a u k` vertices
  avoids an `a`-cap, a `u`-cup and a strong `k`-set, the abstract theorem is
  false and the kernel-checked cases must be re-examined.
- Resource bound: single core, 12 GiB cap.

## Inputs and provenance

- Git revision: `72599c7` (working tree).
- Enumerator: `scripts/enumerate_decomposable_colorings.py`
  (SHA-256 `a260d12a815196d4a7041960a006bdfdccd82b3e22366b3854ebae17bd1cf1f4`).
- Checker: `scripts/census_order_type_decomposability.py`
  (SHA-256 `ac363cb136a3e919a0f1845482a78d350e1af752a10591066604d8590437de50`).
- Outputs: `data/derived/decomposable-class/summary-n9.json` (counts,
  avoidance counts per `(a,u,k)`, cap/cup/strong histograms, threshold
  table) and `extremal-witnesses-n{6,7,8,9}.json.gz` (for each `(a,u,k)`
  with `a,u,k ≤ 7`, up to 3,000 avoiding colorings as triple bitmasks with
  per-vertex profiles: longest cap ending at and starting from the vertex,
  same for cups).

## Method

Colorings are bitmasks over the increasing triples in lexicographic order.
The class on `n` vertices is generated from the classes on the parts: for
every ordered bipartition into a nonempty lower and upper set, every pair of
decomposable colorings on the parts is transported through the order
isomorphisms and the crossing triples are colored by the side of the middle
vertex; the results are deduplicated.  Caps and cups are longest chains of
consecutive right or left turns (valid in this class because it is sweep
realizable, `IsDecomposable.isSweepRealizable`); strong sets are decided by
the quadruple condition.

## Independent checks

- `n = 3, 4, 5, 6`: enumeration and checker agree exactly (2, 8, 62, 718
  colorings; at `n = 6` these are 718 of the 908 one-change colorings).
- The count 186,888 at `n = 8` coincides with the size of the all-root
  census the research plan cites for `k = 6`, computed by different code.
- Every kernel-checked `DecomposableStateUpper` instance in the tree,
  `(4,5,5)`, `(4,6,6)`, `(5,6,6)`, `(4,8,8)`, is consistent with the table
  where it is testable.

## Results

| n | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|
| decomposable colorings | 2 | 8 | 62 | 718 | 10,596 | 186,888 | 3,816,380 |

Every threshold at most nine is attained and never exceeded (`a, u ≥ 4`
shown; the rows with a 3-cap or 3-cup parameter are trivially tight with one
extremal coloring each):

| (a,u,k) | threshold | largest avoiding n | extremal colorings |
|---|---|---|---|
| (4,4,4) | 4 | 4 | 4 |
| (4,4,5) | 6 | 6 | 20 |
| (4,4,6) | 6 | 6 | 20 |
| (4,4,7) | 6 | 6 | 20 |
| (4,5,5) | 7 | 7 | 193 |
| (5,4,5) | 7 | 7 | 193 |
| (5,5,5) | 8 | 8 | 2,862 |

No enumerated coloring exceeds any threshold.  Extremal counts are symmetric
under swapping `a` and `u` (order reversal with color flip), as they must be.

## Interpretation

Baek–Balko's bound is exact in the abstract decomposable class at every
parameter triple with threshold at most nine, including the `(4,5,5)`
boundary where the literal scalar induction fails, with 193 extremal
colorings there.  This is the evidence base for step 2 of the Workstream B
plan: any candidate profile-carrying bound must be tight on exactly these
extremal colorings and additive across their splits.  The enumeration stops
at nine vertices (the next threshold to test, `(4,5,6) = 10`, needs
`n = 10`, roughly seventy million colorings, feasible in a compiled
implementation but not in this script).

## Reproduction

```console
python3 scripts/enumerate_decomposable_colorings.py --max-n 9 --output runs/experiments/20260903-week1/decomposable/enum-n9.json
python3 scripts/enumerate_decomposable_colorings.py --max-n 6 --validate --output /tmp/enum-n6.json
```
