# Experiment 0120: the recursion is exact on every context computed

Date: 2026-09-06

Status: exact computation over the abstract decomposable class; no Lean
theorem is claimed.  Workstream B, step 3 test: continues experiments 0117
(context rules), 0118 (depth-one closed form) and 0119 (deep signature
tables).

## The recursion

For a context signature (experiment 0119) with runs `0..p−1` and limit
matrices `cup_limit`, `cap_limit` computed by the level rules of experiment
0117:

* one run: `F = T(1 + cap_limit[0][0], 1 + cup_limit[0][0], k)`
  (the classical threshold with the run's internal parameters; 1 or 0 when a
  limit is 1 or 0);
* several runs: `F = max` over cuts `t` (prefix runs `0..t−1`, suffix runs
  `t..p−1`), over both orientations (prefix lower and suffix upper, or the
  reverse), and over `c + d' ≤ k − 1`, of `F(prefix) + F(suffix)`, where the
  prefix's context is its own signature with the suffix added as a new
  level-1 sibling of longest cap `d'` (chain `c` when the suffix is lower),
  the prefix's own cups capped at `c` (caps at `d'`), and symmetrically for
  the suffix.

No "single structure" term for several runs: the spanning thresholds are
not a bound once run-internal limits are tighter than spanning ones, which
is the normal situation at depth two.  At depth one the recursion is the
closed form of experiment 0118, addendum 2.  Implementation:
`scripts/decomposable_recursive_formula.py`.

## Verification

| data set | contexts | `F − E` |
|---|---|---|
| depth ≥ 2 signatures, `(4,4,5)` | 42 | 0 on all |
| depth ≥ 2 signatures, `(4,5,5)` | 504 | 0 on all |
| depth ≥ 2 signatures, `(5,5,5)` | 8,078 | 0 on all |
| depth-one run tables, eight cases `(4,4,5)`…`(4,6,6)`, entries with a placed sibling | 888 | 0 on all |

The 40 depth-one entries with a single run and no outer sibling are not
contexts (a sibling has a vertex somewhere) and were excluded.  Two earlier
versions of the recursion are recorded as falsified: with a spanning-
threshold base term for several runs it overestimates on 2,312 of the
8,624 deep signatures (exactly the scalar-recursion histogram of experiment
0119); with a single cut orientation (prefix lower) it underestimates on
depth-one contexts with an outer sibling, because the lower part of a
deep-below split may lie to the right.

## What this means for the proof

`F` is a candidate for the exact extremal function of every context, and
therefore for the induction hypothesis of Theorem 8: the statement to prove
is that for every subtree `S` of a decomposable coloring avoiding `(a,u,k)`,
`|S| ≤ F(context of S)`, with `F(empty context) = T(a,u,k)`.  The inductive
step is the additivity of `F` across every deep-below split, interleaved or
not, with the child contexts derived by the rules of experiment 0117; on
every split of every extremal coloring examined here it holds with
equality where `E` is attained.  `F` is defined through stacked cuts only,
so the additivity for interleaved splits is the genuine content, and it is
what the paper argument of step 3 has to establish.  The witnesses of
experiment 0118 already show that extremal colorings are not stacked, so
the argument is about values, through the Pascal structure of `T`, not
about reproducing the tree.

## Reproduction

```console
python3 scripts/decomposable_recursive_formula.py data/derived/decomposable-depth2-signatures-n8.json --output data/derived/decomposable-recursive-vs-exact-n8.json
```

A few seconds per case.  Inputs: experiments 0117, 0119.
