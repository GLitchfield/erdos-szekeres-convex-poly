# Experiment 0107: decomposability census over extremal order types

Date: 2026-09-03

Status: exact computation, independently replayed at `n = 8`; exact over
all 88,423 hexagon-free types at `n = 9` (4 September; the 2,000-type sample
of 3 September is kept below as a consistency check).  No Lean theorem is
claimed.

## Question

Research-plan questions Q3 and Q10 (`docs/plans/research-plan-2026-09-03.md`):
are the extremal `k`-gon-free point sets decomposable in the sense of
`ErdosSzekeres.IsDecomposable`, in the sweep direction they are given, or in
*some* sweep direction, and do they admit a top-level deep-below split at all?
If every extremal type were decomposable in some direction, a
direction-choosing normalization would be a candidate bridge from the
decomposable theorem to the conjecture; if not, `D-NORMALIZE` cannot be a
direction choice.

## Predeclared gates

- Q10 survives at `k = 5` only if all pentagon-free 8-point order types are
  decomposable in some sweep direction; it survives at `k = 6` only if all
  sampled hexagon-free 9-point types are.
- A single extremal type decomposable in no direction refutes Q10 at that
  `k`.
- Verification threshold: every direction verdict at `n = 8` must be
  reproduced by an independent bottom-up implementation of the literal
  crossing law.
- Resource bound: minutes on one core.

## Inputs and provenance

- Git revision: `c74c737` (branch `codex/state-578-tree-reservoir`).
- Producer: `scripts/census_order_type_decomposability.py`
  (SHA-256 `327fb11ad61ac0c563bc600098d8fee6654e78c607c4135250ae5ed4d3e56ef5`).
- Order-type database (Aichholzer, Aurenhammer, Krasser; realizable order
  types in general position, integer coordinates), downloaded 2026-09-03 from
  `http://www.ist.tugraz.at/aichholzer/research/rp/triangulations/ordertypes/data/`
  into ignored `runs/reference/ordertypes/`:
  `otypes08.b08` (3,315 types, SHA-256
  `d4a5756295a584a57962fca946b4021cbe5c257481b0bc731ef081d1ca2ea0bd`),
  `otypes09.b16` (158,817 types, SHA-256
  `e48faf76c3890ef5481b043bc681b05052b2015092837549b2c53e18626038b4`).
- Outputs: `data/derived/order-type-decomposability-census-n8-k5.json`
  (complete) and
  `data/derived/order-type-decomposability-census-n9-k6-sample2000.json`
  (seed 20260903, compact form of the run output under
  `runs/experiments/20260903-week1/census/`).
- Python 3.12.3, no third-party packages.

## Method

For every order type, keep the sets with no convex `k`-gon (`k = 5` at
`n = 8`, `k = 6` at `n = 9`; convex position of a subset is decided by the
four-point interior test, which is exact in general position).  For each
surviving set enumerate all combinatorially distinct sweep directions: the
critical directions are the normals of the `C(n,2)` pair lines and their
negatives, and one integer direction is taken inside every open arc between
consecutive critical directions.  For each direction the sweep coloring is
formed as in `ErdosSzekeres/Sweep.lean` (vertices ordered by projection; a
triple is a left turn iff the orientation of its points in that order is
positive; orientation signs are invariant under the rotation that carries the
direction to the `x`-axis), and the following are computed:

- `IsDecomposable`, with the crossing law of `HasDeepBelowSplit` in its
  closure form: a split `(L, U)` of `S` is valid iff for every left triple
  `(i, j, k)` in `S` with `j ∈ U` both `i, k ∈ U`, and for every right triple
  with `j ∈ L` both `i, k ∈ L`; recursion on both parts with memoization;
- the number of valid top-level splits of the whole set;
- the longest cap and cup (consecutive-triple chains, valid for realizable
  colorings by `Chains.lean`).

The "database direction" is the sweep by `x` with ties broken by `y`.  Hull
layer sizes are recorded per type.  Mirror images and order reversal are
covered: negating all colors swaps the roles of the two parts of every split,
and the opposite direction is one of the enumerated arcs.

## Independent checks

- Self-test: on random splits the closure form agrees with the literal
  crossing law (`--self-test`).
- The 77 pentagon-free counts and the 88,423 hexagon-free counts reproduce the
  figures quoted in the 3 September review.
- Independent replay (scratch script `verify_census8.py`, bottom-up dynamic
  programme over all subsets with the literal crossing law and no closure
  tables): all 4,296 direction verdicts (decomposable flag and top-split
  count) at `n = 8` agree, zero mismatches.
- The six-point split-pentagon example of the review, points
  `(1,6),(2,44),(3,59),(4,53),(5,50),(6,50)`, is decomposable in the `x`-sweep,
  has no strong 5-set and no convex pentagon, and contains the 4-cap
  `(0,1,2,5)` and 3-cup `(3,4,5)` sharing their right endpoint.

## Results

`n = 8`, `k = 5` (all 77 pentagon-free types; 56 sweep directions each,
except four types with 54 and one with 48 because of parallel pair lines):

| Property | Types |
| --- | ---: |
| decomposable in the database direction | 14 |
| decomposable in some direction | 47 |
| decomposable in no direction | 30 |
| decomposable in every direction | 0 |
| top-level split in the database direction | 35 |
| top-level split in some direction | 77 |
| hull layers `3-4-1` | 61 (all 30 never-decomposable types are here) |
| hull layers `4-4` | 16 (all decomposable in some direction) |

Among the 47 types with a decomposable direction, the fraction of good
directions ranges from `4/56` to `44/56`.  Every type has maximum cap and cup
size exactly 4 in every direction.

`n = 9`, `k = 6` (all 88,423 hexagon-free types of the 158,817
nine-point order types; 72 directions each; run on 4 September in compact
mode, committed gzipped as `data/derived/order-type-decomposability-census-n9-k6.json.gz`):

| Property | Types | Share |
| --- | ---: | ---: |
| decomposable in the database direction | 2,810 | 3.2% |
| decomposable in some direction | 19,727 | 22.3% |
| decomposable in no direction | 68,696 | 77.7% |
| decomposable in every direction | 0 | 0% |
| top-level split in the database direction | 23,117 | 26.1% |
| top-level split in some direction | 87,626 | 99.1% |
| top-level split in no direction | 797 | 0.9% |

The 3 September uniform sample of 2,000 types gave 61 / 475 / 1,525 / 1,988 /
12 for the first, second, third, sixth, and seventh rows, consistent with the
exact shares.  Unlike `n = 8`, where every pentagon-free type has a
top-level split in some direction, 797 hexagon-free nine-point types
have none in any direction; these are not extremal sets (the extremal size
at `k = 6` is sixteen), so they do not bear on the top-split form of Q10.

Never-decomposable types occur in every hull-layer profile
(`3-3-3`, `3-4-2`, `3-5-1`, `4-3-2`, `4-4-1`, `4-5`, `5-3-1`, `5-4`).

## Interpretation

Q10 is false at `k = 5` and `k = 6`: 30 of the 77 pentagon-free 8-point
order types, and about three quarters of the hexagon-free 9-point types, are
decomposable in no sweep direction.  A direction-choosing normalization
therefore cannot be the `D-NORMALIZE` producer, and the plan's Workstream F
candidate "some sweep direction makes a target-free set decomposable" is
retired before any Lean is written.  The decomposable class remains the home
of every known extremal construction (see experiment 0108), but the generic
extremal world is outside it.

Non-claims: nothing here is a theorem; the
census says nothing about whether a *different* coloring on the same vertex
set (a genuine rewriting, as `TargetReflectingDecomposableNormalizationAt`
allows) can be decomposable.

Net proof movement: neutral.  Evidence: checked computation with independent
replay.  Damage scope: `subfamily` (direction-choosing normalizations).
Planning consequence: retire the direction-choice candidate; keep the census
script as the standing instrument for Workstream D.

## Reproduction

```console
python3 scripts/census_order_type_decomposability.py \
  runs/reference/ordertypes/otypes08.b08 --n 8 --k 5 --self-test \
  --output runs/experiments/20260903-week1/census/otypes08-k5.json
python3 scripts/census_order_type_decomposability.py \
  runs/reference/ordertypes/otypes09.b16 --n 9 --k 6 --sample 2000 \
  --output runs/experiments/20260903-week1/census/otypes09-k6-sample2000.json
python3 scripts/census_order_type_decomposability.py \
  runs/reference/ordertypes/otypes09.b16 --n 9 --k 6 --compact \
  --output data/derived/order-type-decomposability-census-n9-k6.json
```
