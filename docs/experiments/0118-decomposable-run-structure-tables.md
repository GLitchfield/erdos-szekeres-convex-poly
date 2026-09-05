# Experiment 0118: extremal tables of a depth-1 child by run structure

Date: 2026-09-06

Status: exact computation over the abstract decomposable class through
eight vertices (numpy brute force); no Lean theorem is claimed.  Workstream
B, step 2: the data a closed-form induction bound must match.  Continues
experiments 0116 and 0117.

## Question

By experiment 0117 a lower child `L` of a deep-below split sees of its
sibling `U` only `U`'s longest cap `d` and, for each cup `Q ⊆ L`, whether a
`U`-vertex lies left of `first(Q)` and whether one lies right of `last(Q)`.
Writing the interleaving as runs `L^{r_1} U^{s_1} L^{r_2} …`, that is: the
number `p` of `L`-runs, and whether a `U`-run precedes the first `L`-run
and whether one follows the last (the "outer" flags).  A cup from run `i` to
run `j` may have at most `u − 1 − [i > 1 or before] − [j < p or after]`
vertices and at most `k − 1 − d`; caps of `L` at most `a − 1`; strong sets
of `L` at most `k − 1`.  What is the largest decomposable `L` with `p`
nonempty runs under these constraints, `E_low(a,u,k; p, before, after, d)`,
and its mirror `E_up` for the upper child (caps extended by `L`-vertices,
coupling `c` = longest cup of `L`)?

## Tables

Computed by `scripts/decomposable_run_extremal.py` (`--max-n 8`, 84 s):
per coloring the table of longest cups and caps by first and last vertex,
then for each composition of `m` into `p` runs a numpy check of all
colorings at once.  An entry `0` means no coloring with that run structure
exists at all (for instance two `L`-runs with `U` on both outer sides at
`u = 4`: any two `L`-vertices form a 2-cup that extends to a 4-cup).
Entries for `p = 3` equal those for `p = 2` except where they are `0`.
Full data, including `p = 4`, in `data/derived/decomposable-run-extremal-n8.json`.

`(4,4,5)`, threshold 6:

| child | runs p | outer sibling (before, after) | coupling 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|---|
| low | 1 | (0,0) | 6 | 3 | 1 |  |
| low | 1 | (0,1) | 3 | 3 | 1 |  |
| low | 1 | (1,0) | 3 | 3 | 1 |  |
| low | 1 | (1,1) | 1 | 1 | 1 |  |
| low | 2 | (0,0) | 5 | 3 | 0 |  |
| low | 2 | (0,1) | 3 | 3 | 0 |  |
| low | 2 | (1,0) | 3 | 3 | 0 |  |
| low | 2 | (1,1) | 0 | 0 | 0 |  |
| low | 3 | (0,0) | 5 | 3 | 0 |  |
| low | 3 | (0,1) | 0 | 0 | 0 |  |
| low | 3 | (1,0) | 0 | 0 | 0 |  |
| low | 3 | (1,1) | 0 | 0 | 0 |  |
| up | 1 | (0,0) | 6 | 3 | 1 |  |
| up | 1 | (0,1) | 3 | 3 | 1 |  |
| up | 1 | (1,0) | 3 | 3 | 1 |  |
| up | 1 | (1,1) | 1 | 1 | 1 |  |
| up | 2 | (0,0) | 5 | 3 | 0 |  |
| up | 2 | (0,1) | 3 | 3 | 0 |  |
| up | 2 | (1,0) | 3 | 3 | 0 |  |
| up | 2 | (1,1) | 0 | 0 | 0 |  |
| up | 3 | (0,0) | 5 | 3 | 0 |  |
| up | 3 | (0,1) | 0 | 0 | 0 |  |
| up | 3 | (1,0) | 0 | 0 | 0 |  |
| up | 3 | (1,1) | 0 | 0 | 0 |  |

`(4,5,5)`, threshold 7:

| child | runs p | outer sibling (before, after) | coupling 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|---|
| low | 1 | (0,0) | 6 | 3 | 1 |  |
| low | 1 | (0,1) | 6 | 3 | 1 |  |
| low | 1 | (1,0) | 6 | 3 | 1 |  |
| low | 1 | (1,1) | 3 | 3 | 1 |  |
| low | 2 | (0,0) | 6 | 3 | 0 |  |
| low | 2 | (0,1) | 6 | 3 | 0 |  |
| low | 2 | (1,0) | 6 | 3 | 0 |  |
| low | 2 | (1,1) | 3 | 3 | 0 |  |
| low | 3 | (0,0) | 6 | 3 | 0 |  |
| low | 3 | (0,1) | 6 | 3 | 0 |  |
| low | 3 | (1,0) | 6 | 3 | 0 |  |
| low | 3 | (1,1) | 3 | 3 | 0 |  |
| up | 1 | (0,0) | 7 | 4 | 1 |  |
| up | 1 | (0,1) | 4 | 4 | 1 |  |
| up | 1 | (1,0) | 4 | 4 | 1 |  |
| up | 1 | (1,1) | 1 | 1 | 1 |  |
| up | 2 | (0,0) | 6 | 4 | 0 |  |
| up | 2 | (0,1) | 4 | 4 | 0 |  |
| up | 2 | (1,0) | 4 | 4 | 0 |  |
| up | 2 | (1,1) | 0 | 0 | 0 |  |
| up | 3 | (0,0) | 6 | 4 | 0 |  |
| up | 3 | (0,1) | 0 | 0 | 0 |  |
| up | 3 | (1,0) | 0 | 0 | 0 |  |
| up | 3 | (1,1) | 0 | 0 | 0 |  |

`(5,4,5)`, threshold 7:

| child | runs p | outer sibling (before, after) | coupling 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|---|
| low | 1 | (0,0) | 7 | 4 | 1 |  |
| low | 1 | (0,1) | 4 | 4 | 1 |  |
| low | 1 | (1,0) | 4 | 4 | 1 |  |
| low | 1 | (1,1) | 1 | 1 | 1 |  |
| low | 2 | (0,0) | 6 | 4 | 0 |  |
| low | 2 | (0,1) | 4 | 4 | 0 |  |
| low | 2 | (1,0) | 4 | 4 | 0 |  |
| low | 2 | (1,1) | 0 | 0 | 0 |  |
| low | 3 | (0,0) | 6 | 4 | 0 |  |
| low | 3 | (0,1) | 0 | 0 | 0 |  |
| low | 3 | (1,0) | 0 | 0 | 0 |  |
| low | 3 | (1,1) | 0 | 0 | 0 |  |
| up | 1 | (0,0) | 6 | 3 | 1 |  |
| up | 1 | (0,1) | 6 | 3 | 1 |  |
| up | 1 | (1,0) | 6 | 3 | 1 |  |
| up | 1 | (1,1) | 3 | 3 | 1 |  |
| up | 2 | (0,0) | 6 | 3 | 0 |  |
| up | 2 | (0,1) | 6 | 3 | 0 |  |
| up | 2 | (1,0) | 6 | 3 | 0 |  |
| up | 2 | (1,1) | 3 | 3 | 0 |  |
| up | 3 | (0,0) | 6 | 3 | 0 |  |
| up | 3 | (0,1) | 6 | 3 | 0 |  |
| up | 3 | (1,0) | 6 | 3 | 0 |  |
| up | 3 | (1,1) | 3 | 3 | 0 |  |

`(5,5,5)`, threshold 8:

| child | runs p | outer sibling (before, after) | coupling 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|---|
| low | 1 | (0,0) | 7 | 4 | 1 |  |
| low | 1 | (0,1) | 7 | 4 | 1 |  |
| low | 1 | (1,0) | 7 | 4 | 1 |  |
| low | 1 | (1,1) | 4 | 4 | 1 |  |
| low | 2 | (0,0) | 7 | 4 | 0 |  |
| low | 2 | (0,1) | 7 | 4 | 0 |  |
| low | 2 | (1,0) | 7 | 4 | 0 |  |
| low | 2 | (1,1) | 4 | 4 | 0 |  |
| low | 3 | (0,0) | 7 | 4 | 0 |  |
| low | 3 | (0,1) | 7 | 4 | 0 |  |
| low | 3 | (1,0) | 7 | 4 | 0 |  |
| low | 3 | (1,1) | 4 | 4 | 0 |  |
| up | 1 | (0,0) | 7 | 4 | 1 |  |
| up | 1 | (0,1) | 7 | 4 | 1 |  |
| up | 1 | (1,0) | 7 | 4 | 1 |  |
| up | 1 | (1,1) | 4 | 4 | 1 |  |
| up | 2 | (0,0) | 7 | 4 | 0 |  |
| up | 2 | (0,1) | 7 | 4 | 0 |  |
| up | 2 | (1,0) | 7 | 4 | 0 |  |
| up | 2 | (1,1) | 4 | 4 | 0 |  |
| up | 3 | (0,0) | 7 | 4 | 0 |  |
| up | 3 | (0,1) | 7 | 4 | 0 |  |
| up | 3 | (1,0) | 7 | 4 | 0 |  |
| up | 3 | (1,1) | 4 | 4 | 0 |  |

`(4,4,6)`, threshold 6:

| child | runs p | outer sibling (before, after) | coupling 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|---|
| low | 1 | (0,0) | 6 | 6 | 3 | 1 |
| low | 1 | (0,1) | 3 | 3 | 3 | 1 |
| low | 1 | (1,0) | 3 | 3 | 3 | 1 |
| low | 1 | (1,1) | 1 | 1 | 1 | 1 |
| low | 2 | (0,0) | 5 | 5 | 3 | 0 |
| low | 2 | (0,1) | 3 | 3 | 3 | 0 |
| low | 2 | (1,0) | 3 | 3 | 3 | 0 |
| low | 2 | (1,1) | 0 | 0 | 0 | 0 |
| low | 3 | (0,0) | 5 | 5 | 3 | 0 |
| low | 3 | (0,1) | 0 | 0 | 0 | 0 |
| low | 3 | (1,0) | 0 | 0 | 0 | 0 |
| low | 3 | (1,1) | 0 | 0 | 0 | 0 |
| up | 1 | (0,0) | 6 | 6 | 3 | 1 |
| up | 1 | (0,1) | 3 | 3 | 3 | 1 |
| up | 1 | (1,0) | 3 | 3 | 3 | 1 |
| up | 1 | (1,1) | 1 | 1 | 1 | 1 |
| up | 2 | (0,0) | 5 | 5 | 3 | 0 |
| up | 2 | (0,1) | 3 | 3 | 3 | 0 |
| up | 2 | (1,0) | 3 | 3 | 3 | 0 |
| up | 2 | (1,1) | 0 | 0 | 0 | 0 |
| up | 3 | (0,0) | 5 | 5 | 3 | 0 |
| up | 3 | (0,1) | 0 | 0 | 0 | 0 |
| up | 3 | (1,0) | 0 | 0 | 0 | 0 |
| up | 3 | (1,1) | 0 | 0 | 0 | 0 |


## Reading the tables

Write `T = decomposableThreshold`, `u₁ = u − before − after` (the bound on
cups spanning the whole child) and `κ = k − d` (the coupling bound on cups).
On every entry of the tables:

1. One run (`p = 1`): `E_low = T(a, min(u₁, κ), k)`.  This is the scalar
   recursion of the published proof, and it is exact whenever the sibling
   lies entirely on one side of the child.
2. Two or more runs with an outer sibling on at least one side:
   `E_low = T(a, min(u₁, κ), k)` again, when the structure exists at all.
3. Two or more runs with the sibling strictly inside the child (no outer
   flag): `E_low = T(a, u, k) − 1` when `κ ≥ u` (the coupling does not bind),
   and `T(a, κ, k)` when `κ < u`.  Examples: `(4,4,5)` with `d = 1` gives
   `6 − 1 = 5`; `(5,5,5)` with `d = 1` gives `T(5,4,5) = 7`; `(4,4,6)` gives
   `5, 5, 3` for `d = 1, 2, 3`.
4. `E_up` mirrors `E_low` with `a` and `u` exchanged, as it must.

So at depth 1 the position information enters through exactly two things:
the outer flags, which lower the cup parameter by one per side, and the
"sibling strictly inside" case, which costs one vertex against the
threshold unless the strong coupling already binds.  The `(4,5,5,1,3)`
boundary of the published induction is item 3 at `(4,5,5)`: the child bound
is `T(4,4,5) = 6` there because `κ = 4 < 5` binds, and `6 + 1 = 7`.

The one-vertex loss in item 3 is the quantity a closed-form bound must
explain: the extremal coloring `P(a,u)` cannot be cut into two runs whose
internal cups are one shorter than its spanning cups without losing a
vertex, while a cut with an outer sibling loses nothing beyond the reduced
parameter.  Whether the loss stays one vertex for larger parameters
(`(4,5,6)`, threshold 10, needs `n = 10`) and how it compounds at depth 2
(where the longest-chain rule of experiment 0117 replaces the outer flags
by per-side extension counts) are the next computations.

## Reproduction

```console
python3 scripts/decomposable_run_extremal.py --max-n 8 --output data/derived/decomposable-run-extremal-n8.json
```

Inputs: the class enumerator of experiment 0114; numpy 2.4.
