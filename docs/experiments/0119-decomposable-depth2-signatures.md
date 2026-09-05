# Experiment 0119: extremal tables of subtrees at depth two and more, by full context signature

Date: 2026-09-06

Status: exact computation over the abstract decomposable class through
eight vertices; no Lean theorem is claimed.  Workstream B, step 2:
continues experiments 0117 (the context rules) and 0118 (depth-one tables).

## Question

Experiment 0117 fixed what a subtree at any depth sees: its list of
ancestor levels with side, sibling positions and sibling chain maximum.
For the subtrees at depth two and more that occur in extremal colorings of
`(4,4,5)`, `(4,5,5)` and `(5,5,5)`, what is the exact extremal size
`E(signature)` of a decomposable coloring with the same run structure under
the constraints the signature induces, is it attained by the subtrees that
occur, and how does it relate to the depth-one pattern?

## Method

`scripts/decomposable_depth2_tables.py`.  For every extremal coloring `T`
of a case and every subtree `S` of every decomposition tree of `T` at depth
at least two, the signature is the sweep-order word of `T` with each
external vertex tagged by its level along `S`'s path and by `S`'s side
there, plus each level's sibling chain maximum.  From the signature alone
the limit matrices `cup_limit[i][j]` and `cap_limit[i][j]` (largest allowed
cup or cap from run `i` to run `j`) are computed by the longest-chain and
join rules of experiment 0117; `E` is the largest decomposable coloring
with the same number of runs meeting those limits, found by the numpy
search of experiment 0118 over the class through `n = 8`.

## Results

| case | threshold | distinct signatures at depth ≥ 2 | depths | `E` values | signatures with `E` attained by an occurring subtree |
|---|---|---|---|---|---|
| (4,4,5) | 6 | 42 | 2: 14, 3: 28 | 3 (32), 4 (10) | 42 of 42 |
| (4,5,5) | 7 | 504 | 2: 114, 3: 138, 4: 252 | 3 (378), 4 (90), 5 (36) | 504 of 504 |
| (5,5,5) | 8 | 8,078 | 2: 780, 3: 1,582, 4: 2,076, 5: 3,640 | 3 (5,924), 4 (1,488), 5 (520), 6 (146) | 8,078 of 8,078 |

**`E` is tight everywhere.**  For every signature the largest subtree that
occurs with it has exactly `E` vertices.  So the context description of
experiment 0117 loses nothing at depth two and beyond: the extremal
colorings realize the exact extremal size of every context they contain.

**Candidate bounds against the tables.**  Three simple formulas were
compared with `E` on every signature (value minus `E`):

| formula | (4,4,5) | (4,5,5) | (5,5,5) |
|---|---|---|---|
| `T(a', u', k)` from the spanning limits (first run to last run) | 0: 16, +2: 10, +3: 16 | 0: 230, +1: 40, +2: 90, +3: 144 | 0: 4,066, +1: 632, +2: 1,300, +3: 2,080 |
| `T(a', u', k)` from the smallest run-internal limits | −2: 34, −3: 8 | 0: 32, −1: 4, −2: 392, −3: 72, −4: 4 | 0: 1,050, −1: 64, −2: 5,732, −3: 1,168, −4: 64 |
| sum over runs of `T(a_i, u_i, k)` with each run's internal limits | 0: 34, +1: 8 | 0: 304, +1: 132, +2: 28, +3: 16, +4: 24 | 0: 3,924, +1: 1,692, +2: 792, +3: 676, +4: 612, +5 to +12: 382 |

The spanning formula is the scalar recursion; it overestimates on most
deep contexts because run-internal cups are shorter than spanning ones.
The internal-minimum formula underestimates (it is not a bound).  The sum
over runs never underestimates on any of the 8,624 signatures and is exact
on 4,262 of them; it is a valid bound for a child by itself but not an
induction bound, since it ignores the spanning constraints and so is not
additive across a split (at `(4,4,5)`, a lower child with two runs around
a singleton upper child would get `3 + 3 + 1 = 7 > 6`).  The right
candidate lies between the spanning and the sum-over-runs formulas: a
window sum that charges each run by its internal parameters and the
spanning cups once.  That is the formula step 3 has to find and prove
additive; the tables here are its test set.

## Reproduction

```console
python3 scripts/decomposable_depth2_tables.py --max-n 8 --cases "4,4,5;4,5,5;5,5,5" --output data/derived/decomposable-depth2-signatures-n8.json
```

Inputs: the class enumerator of experiment 0114, the context rules of
experiment 0117 (`scripts/decomposable_context_functions.py`), numpy 2.4.
