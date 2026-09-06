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

## Addendum, 6 September: two advance predictions, and the coupling restated

**The coupling.**  The recursion as first written carried, besides the two
new sibling maxima, an explicit cap on each part's own chains.  The abstract
additivity test (below) found two contexts at `(4,5,5)` where that version
exceeded the parent by one: an explicit cap on a part's cups does not shrink
when the part is cut again and its prefix's cups are extended by its own
suffix.  The correct and simpler form carries the coupling only through the
sibling maxima: the lower part sees a sibling of longest cap `d'`, the upper
part a sibling of longest cup `k − 1 − d'`, and the join rule of experiment
0117 then bounds every chain of each part, including under later cuts.  That
form is still exact on all 8,624 deep signatures and all 870 depth-one
contexts, and the two violations disappear.  In the induction this is the
observation that a part whose own cups are at most `c` satisfies the
constraints of a sibling cap `k − 1 − c`, so the single-parameter form
suffices together with monotonicity of `F` in the sibling maxima.

**`(5,5,6)` at threshold 14.**  The avoiding subclass was enumerated by the
compiled enumerator `tools/decomp_enum/enum_avoid.c` (pair loops bucketed
by chain maxima, finished classes pruned to records whose longest cup or cap
is at most `k − 3`, the only ones the coupling can reuse): 2, 8, 60, 590,
5,974, 54,480, 409,794, 2,335,568, 8,975,214, 19,776,612, 20,071,608,
**11,967,720**, 0 colorings at `n = 3..15`, in 23 minutes at 36 GiB.  The
threshold 14 is exact with 11,967,720 extremal colorings.  The recursion's
predictions for the depth-one tables were committed before the enumeration
(`data/derived/decomposable-recursive-predictions-556-467.json`): all 56
predicted entries match the tables computed from the class
(`data/derived/decomposable-run-extremal-556-n15.json`, 54 min), including
13, 10, 4 for the sibling strictly inside at couplings 1, 2, 3 and
10, 10, 4, 1 for one outer sibling.  With `(4,6,6)` this is the second
advance prediction confirmed, now nine parameter triples in all.

**Abstract additivity.**  `scripts/decomposable_additivity_test.py`: for every
abstract context with up to five child vertices and up to two external
vertices at up to two levels with all sibling maxima, every partition of the
child's vertices into a lower and an upper part that is not a run-boundary
cut, both orientations, every coupling:

| case | contexts | nonzero | interleaved partitions | violations |
|---|---|---|---|---|
| (4,4,5) | 4,168 | 2,124 | 31,708 | 0 |
| (4,5,5) | 4,168 | 2,124 | 31,708 | 0 |
| (5,4,5) | 4,168 | 2,124 | 31,708 | 0 |
| (5,5,5) | 4,168 | 2,124 | 31,708 | 0 |
| (4,5,6) | 7,220 | 4,408 | 66,828 | 0 |
| (5,4,6) | 7,220 | 4,408 | 66,828 | 0 |

ADDITIVITY_MORE

**Monotonicity (lemma 2).**  `scripts/decomposable_monotonicity_test.py`:
raising any one sibling maximum by one never increases `F`, on the same
contexts: 5,272 comparisons each at `(4,4,5)`, `(4,5,5)`, `(5,5,5)` and
10,404 at `(4,5,6)`, no violation.

So on every abstract context in range, the best interleaved split never
beats the best stacked cut.  This is lemma 3 of the induction sketched in
the discussion of 6 September: with the context-transfer lemma (experiment
0117) and monotonicity, it is the inductive step, and it is the one
statement that still needs a proof for all contexts.
