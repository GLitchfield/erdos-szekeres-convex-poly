# Experiment 0111: (k−1)-gon-free halves of the 64-point k = 8 extremal sets

Date: 2026-09-04

Status: exact computation with independent verification of every witness.
No Lean theorem is claimed.

## Question

Research-plan Workstream E and Q4 at the next size: do the known
64-point sets with no convex octagon (the Erdős–Szekeres construction and the
two `x`-blow-ups of Baek–Balko's Theorem 19 built in experiment 0108) contain
32 points with no convex heptagon?  A set without such a half would refute the
predecessor-half conjecture at `k = 8`.  Experiment 0108 skipped this search
because the four-point subset test over all 7-subsets of 64 points (621
million) was infeasible.

## Predeclared gates

- Every convex-polygon count produced by the new chain enumeration must agree
  with the recorded four-point-test counts on all 24 sets of experiment 0108
  (five 16-point sets at size 5, nineteen 32-point sets at size 6); a
  mismatch invalidates the method, not the sets.
- A witness half counts only if an independent check (the cup/cap dynamic
  programme `largest_convex_subset`) reports its largest convex subset below
  7, and the index list has 32 distinct valid entries.
- The conjecture dies at `k = 8` if CaDiCaL reports UNSAT for any set.

## Inputs and provenance

- Git revision: `c74c737` (working tree).
- Point sets: `runs/experiments/20260903-week1/constructions/k8.json` from
  experiment 0108 (`scripts/baek_balko_constructions.py`), integer
  coordinates, general position and octagon-freeness verified there.
- Enumerator: `convex_polygons_by_chains` in
  `scripts/baek_balko_constructions.py` (SHA-256 `eba3f676cc995e4fcc59c156e9632d5e2ee7cd13778dc9831c74f955c26d95a1`):
  a convex polygon in general position splits, between its first and last
  vertex along a generic sweep, into a right-turning upper chain and a
  left-turning lower chain, and every such pair with common endpoints is a
  convex polygon; chains are enumerated by depth-first extension.
- Driver: `scripts/k8_half_support.py` (SHA-256 `5ea982d0f907f12d37583401352115e82cc79b08ed9b6eaf67d8a295c15fb02e`).
- Solver: CaDiCaL 2.1.2 (Lean toolchain), sequential-counter cardinality
  encoding as in experiment 0108.
- Output: `data/derived/baek-balko-constructions-k8.json` (points, polygon
  counts, witness halves, verification fields).

## Independent checks

- Chain enumeration versus four-point test: identical counts on all 24 sets
  of experiment 0108 and identical polygon sets on the 32-point
  Erdős–Szekeres set (39,648 hexagons).
- Each witness half re-checked by `largest_convex_subset`, a separate
  algorithm (cup/cap dynamic programme) from the SAT clauses.

## Results

| Set | Points | Largest convex | Convex 7-gons | Enumeration | Solver | Half verified | Largest convex in half |
|---|---|---|---|---|---|---|---|
| ES(8,8,8) | 64 | 7 | 4,720,996 | 5.5 s | 16.7 s | yes | 6 |
| Theorem19(x=1,m=6) | 64 | 7 | 1,588,840 | 2.1 s | 5.6 s | yes | 6 |
| Theorem19(x=2,m=4) | 64 | 7 | 3,846,106 | 2.9 s | 11.6 s | yes | 6 |

All three sets have a 32-point subset with no convex heptagon.  The witness
index lists are in the output file.

## Interpretation

The predecessor-half conjecture (every `n`-point set with no convex `k`-gon
has `⌈n/2⌉` points with no convex `(k−1)`-gon) holds on every known extremal
set at `k = 6, 7, 8`: 5, 19, and 3 sets respectively.  This is evidence for
Workstream E's conjecture at the sizes where a refutation would have been
cheapest; it is not a proof of anything, and the three `k = 8` sets are a
thin sample of octagon-free 64-point sets.  The chain enumerator removes the
size barrier for the next step in the weekly plan, the perturbation search
for a counterexample at `k = 7`.

## Reproduction

```console
python3 scripts/k8_half_support.py --input runs/experiments/20260903-week1/constructions/k8.json --output data/derived/baek-balko-constructions-k8.json --cadical ~/.elan/toolchains/leanprover--lean4---v4.29.1/bin/cadical
```
