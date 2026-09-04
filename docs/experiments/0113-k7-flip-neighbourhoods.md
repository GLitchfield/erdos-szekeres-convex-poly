# Experiment 0113: single-flip neighbourhoods of the 32-point heptagon-free sets

Date: 2026-09-04

Status: exact computation, every witness independently re-verified; no
counterexample found.  Workstream E falsifier, first form.

## Question

The predecessor-half conjecture (Workstream E) predicts that every 32-point
set with no convex heptagon has 16 points with no convex hexagon.  Experiment
0108 confirmed this on the nineteen known extremal sets.  Do nearby
heptagon-free order types, reached by changing one orientation at a time,
also satisfy it?  A failure would refute the conjecture at `k = 7`.

## Predeclared gates

- Every move must change exactly one orientation of the chirotope and keep
  general position (checked after each move against the full labeled
  orientation vector).
- A move is kept only if the new set is still heptagon-free (all convex
  heptagons enumerated by the chain enumerator of experiment 0111) and its
  labeled orientation vector has not been visited.
- Each kept set gets the SAT half search; a witness half counts only if the
  independent cup/cap programme reports its largest convex subset below 6.
- The conjecture dies at `k = 7` on the first UNSAT; the set is written to
  `data/derived/predecessor-half-k7-counterexamples/`.

## Inputs and provenance

- Git revision: `c74c737` (working tree).
- Base sets: the nineteen verified heptagon-free 32-point sets of
  experiment 0108 (`data/derived/baek-balko-constructions-k7.json`).
- Search: `scripts/predecessor_half_perturbation_search.py`
  (SHA-256 `bc4315072ea2c4821e198d920c5dbb4d53ca86fa41e6f5b0431cf66b6b93b52d`), mode
  `flip`, seed 20260904, 40 accepted moves per base, choosing among the four
  lines nearest the moved point; polygon enumeration and half search from
  `scripts/baek_balko_constructions.py`
  (SHA-256 `eba3f676cc995e4fcc59c156e9632d5e2ee7cd13778dc9831c74f955c26d95a1`).
- Solver: CaDiCaL 2.1.2 (Lean toolchain).
- Output: `data/derived/predecessor-half-k7-flip-search.json` (per-base
  statistics; the walks themselves are reproducible from the seed).

## Method

Random jitter is useless here: the constructions are degenerate at relative
scale `1e-14`, and every one of 2,850 jitters, down to 1% of the
nearest-neighbour distance, created a heptagon.  Instead a move picks a
point and one of the four lines through two other points nearest to it, and
displaces the point along that line's normal by an exact rational amount
that crosses that line and no other (the displacement is chosen strictly
between the nearest and the next threshold, with a small denominator so that
coordinates do not compound along the walk; the set is rescaled to integers
after each move).  The walk is a random walk on the flip graph restricted to
heptagon-free sets, never revisiting a labeled order type.

## Independent checks

- Single-orientation property and general position verified after every
  move by direct recomputation of all 4,960 orientations.
- Every witness half re-checked by `largest_convex_subset`, a different
  algorithm from the SAT clauses.

## Results

| Base set | Flips tried | Heptagon-free | New order types | Halves found | Halves missing |
|---|---|---|---|---|---|
| ES(7,7,7) | 87 | 40 | 40 | 40 | 0 |
| Theorem19(x=1,m=5) | 148 | 45 | 40 | 40 | 0 |
| Theorem19(x=2,m=3) | 118 | 44 | 40 | 40 | 0 |
| Valtr(S#0) | 136 | 52 | 40 | 40 | 0 |
| Valtr(S#1) | 127 | 44 | 40 | 40 | 0 |
| Valtr(S#2) | 125 | 49 | 40 | 40 | 0 |
| Valtr(S#3) | 98 | 42 | 40 | 40 | 0 |
| Valtr(S#4) | 133 | 45 | 40 | 40 | 0 |
| Valtr(S#5) | 112 | 44 | 40 | 40 | 0 |
| Valtr(S#6) | 113 | 42 | 40 | 40 | 0 |
| Valtr(S#7) | 157 | 47 | 40 | 40 | 0 |
| Valtr(S#8) | 118 | 43 | 40 | 40 | 0 |
| Valtr(S#9) | 89 | 42 | 40 | 40 | 0 |
| Valtr(S#10) | 87 | 42 | 40 | 40 | 0 |
| Valtr(S#11) | 135 | 46 | 40 | 40 | 0 |
| Valtr(S#12) | 149 | 47 | 40 | 40 | 0 |
| Valtr(S#13) | 151 | 46 | 40 | 40 | 0 |
| Valtr(S#14) | 138 | 50 | 40 | 40 | 0 |
| Valtr(S#15) | 128 | 50 | 40 | 40 | 0 |

Totals: 2349 flips tried, 860 kept the set
heptagon-free, 760 distinct new order types visited,
760 of them with a verified hexagon-free 16-point half,
0 without.  Whole search: four minutes.

## Interpretation

About 37% of single flips of a point across its nearest lines preserve
heptagon-freeness, so the known extremal sets are not isolated, and the 760
heptagon-free neighbours reached all satisfy the predecessor-half conjecture.
This is the first falsifier the weekly plan asked for and it did not fire.
It says nothing about heptagon-free sets far from the constructions; the
next step is longer walks and walks that also allow moves across
non-nearest lines, which the search supports through its `--keep` and
`--nearest` options at negligible cost.

## Reproduction

```console
python3 scripts/predecessor_half_perturbation_search.py --input data/derived/baek-balko-constructions-k7.json --k 7 --mode flip --keep 40 --nearest 4 --cadical ~/.elan/toolchains/leanprover--lean4---v4.29.1/bin/cadical --output data/derived/predecessor-half-k7-flip-search.json --counterexample-dir data/derived/predecessor-half-k7-counterexamples
```
