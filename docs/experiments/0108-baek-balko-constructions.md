# Experiment 0108: Baek–Balko extremal constructions at k = 6, 7

Date: 2026-09-03

Status: exact computation with direct verification; one 32-point result
independently replayed.  No Lean theorem is claimed.

## Question

Research-plan questions Q4 and Q10 and Workstream E: do the known and new
`2^(k-2)`-point sets with no convex `k`-gon (Erdős–Szekeres, Valtr's
blow-ups, and the `x`-blow-ups of Baek–Balko's Theorem 19) have
`(k-1)`-gon-free halves, and are they decomposable in some sweep direction?
A 16-point hexagon-free set with no pentagon-free 8-subset would refute the
Fin16 predecessor-half statement without SAT; a 32-point 7-gon-free set with
no hexagon-free 16-subset would refute the predecessor-half conjecture at
`k = 7`.

## Predeclared gates

- Every produced set must pass the independent checks (general position,
  cardinality `2^(k-2)`, largest convex subset `k-1`); a failure means the
  transcription of the construction is wrong, not a mathematical result.
- The predecessor-half conjecture dies at `k` if any produced set has no
  `⌈n/2⌉`-point `(k-1)`-gon-free subset (decided exactly by SAT with a
  cardinality constraint, model re-checked independently).
- Q10 dies at `k` if any produced extremal set is decomposable in no sweep
  direction.

## Inputs and provenance

- Git revision: `c74c737`.
- Producer: `scripts/baek_balko_constructions.py` (SHA-256
  `8da172762b2510b503675b68fee647c057fce20068207f7f7c6a618f0434fae9`);
  base order types from `runs/reference/ordertypes/otypes08.b08` (see
  experiment 0107 for its hash).
- Solver for the half-support search: CaDiCaL 2.1.2 from the Lean toolchain.
- Outputs: `data/derived/baek-balko-constructions-k6.json`,
  `data/derived/baek-balko-constructions-k7.json` (integer coordinates of
  every set, verification fields, decomposable-direction counts, and the
  half-support witnesses).
- Source: Baek and Balko, *The Erdős–Szekeres Conjecture Revisited*, SoCG
  2025, Section 4 (`P(a,u)`, `P(a,u,k)`), Definition 13 (`(X,Y)`-blow-up),
  Section 6.1 (Valtr's blow-ups), Definitions 17 (the set `M`) and
  Theorem 19 (`x`-blow-ups of `M`).

## Method

Exact rational coordinates.  `P(a,u)` is built by the deep-below recursion
with a translation computed from the slopes involved; `P(a,u,k)` stacks the
clusters `P(k+2-i, i)` (`i = k-a+2, …, u`) on a cup with geometrically
growing heights; the set `M` uses the skeleton `ℓ_i = (-m+i-1, B^(i-1)-1)`,
`r_i = (m-i+1, B^(i-1)-1+ε_i)` with `B = 4m+4` (the combinatorial conditions
of Definition 17 are asserted), with flattened tiny copies of `P(m-i+1, i)`
and `P(m-i, i+1)` at `ℓ_i` and `r_i`; the blow-up places rotated,
horizontally squeezed copies of the prescribed cap/cup-free sets at the base
points and refines the scale until every condition of Definition 13 holds
(orientation preservation across clusters and the vertical-line side
condition).  Each output is then verified without reference to the
construction: general position, cardinality, and the largest convex subset by
the cup/cap chain dynamic programme over a generic sweep order.  The
`s_i` values of `M` reproduce Lemma 18 (`v_1 = 2`, `v_j = 2^(j-1)`).

Decomposability is tested in every combinatorially distinct sweep direction
with the closure-form crossing law (experiment 0107), enumerating the closed
lower parts as unions of vertex closures.  Half supports are found by SAT:
one variable per point, one clause per convex `(k-1)`-gon, a sequential
counter for "at least `⌈n/2⌉` chosen"; every model is re-checked by the
largest-convex-subset routine.

## Independent checks

- Self-test (`--self-test`): 31 checks of `P(a,u)` for `2 ≤ a,u ≤ 6` and of
  `P(k,k,k)` for `3 ≤ k ≤ 6`, `P(4,5,5)`, `P(5,6,6)` (sizes, cap/cup bounds,
  largest convex subset); all pass.
- `k = 5`: `P(5,5,5)` and the Theorem 19 set (`x = 1`, `m = 3`) are
  8-point pentagon-free sets.
- Independent replay (scratch script `verify_t19.py`: closed sets by
  breadth-first union closure, every candidate split checked against the
  literal crossing law): the Theorem 19 set with `x = 1`, `m = 5` at `k = 7`
  has a top-level deep-below split in 398 of its 848 directions and is
  decomposable in none, agreeing with the producer.

## Results

`k = 6` (16 points, all verified extremal):

| Set | decomposable directions | 8-point pentagon-free subset |
| --- | ---: | --- |
| `P(6,6,6)` | 158 / 178 | yes |
| Theorem 19, `x = 1`, `m = 4` | 170 / 208 | yes |
| Valtr blow-up, base = convex pentagon | 158 / 178 | yes |
| Valtr blow-up, base = quadrilateral + interior point | 28 / 178 | yes |
| Valtr blow-up, base = triangle + two interior points | 62 / 178 | yes |

`k = 7` (32 points, all 19 sets verified extremal): the 16 Valtr blow-ups
over all six-point order types are decomposable in between 14 and 628 of
their 722 directions; `P(7,7,7)` in 618 / 722; the Theorem 19 set with
`x = 2`, `m = 3` in 544 / 828; the Theorem 19 set with `x = 1`, `m = 5` in
**0 / 848**.  Every one of the 19 sets contains a 16-point subset with no
convex hexagon.

## Interpretation

- Workstream E survives: on every extremal set built here at `k = 6` and
  `k = 7` the predecessor-half statement holds.  This is evidence about the
  known constructions only.
- Q10 is refuted on a construction, not just on order-type data: the
  Baek–Balko `x = 1` blow-up of `M` for `k = 7` is a 32-point 7-gon-free set
  that is decomposable in no sweep direction, although it is built from
  decomposable clusters.  So even the extremal world reachable by the
  paper's own constructions leaves the decomposable class.  This is the
  "single non-decomposable extremal set" the plan asked for before any
  normalization work, and it is the natural hostile world for any
  `D-NORMALIZE` producer: a target-reflecting decomposable coloring on these
  32 vertices would have to be a genuine rewriting.
- All produced sets have the half property, so the Fin16 endpoint is not
  settled negatively by constructions.

Net proof movement: neutral.  Evidence: checked computation.  Damage scope:
`subfamily` (direction-choosing normalizations; confirms experiment 0107).
Planning consequence: retain E; feed the 32-point non-decomposable set into
Workstream F's hostile-world list.

## Reproduction

```console
python3 scripts/baek_balko_constructions.py --k 6 --self-test \
  --cadical ~/.elan/toolchains/leanprover--lean4---v4.29.1/bin/cadical \
  --base-database runs/reference/ordertypes/otypes08.b08 --base-n 8 \
  --output runs/experiments/20260903-week1/constructions/k6.json
python3 scripts/baek_balko_constructions.py --k 7 \
  --cadical ~/.elan/toolchains/leanprover--lean4---v4.29.1/bin/cadical \
  --base-database runs/reference/ordertypes/otypes08.b08 --base-n 8 \
  --output runs/experiments/20260903-week1/constructions/k7.json
```
