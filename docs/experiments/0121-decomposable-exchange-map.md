# Experiment 0121: the exchange map behind additivity, three-level contexts, and the absence of a closed form

Date: 2026-09-06

Status: exact computations on abstract contexts; no Lean theorem is claimed.
Workstream B, step 3: the three items started on 6 September after
experiment 0120 (the recursion `F`, its induction skeleton, and the
additivity lemma as the one open step).

## 1. Which stacked cut dominates an interleaved split

Additivity says that for every context and every partition of its vertices
into a lower and an upper part, the best stacked cut of the recursion is at
least the value of the partition.  For a hand proof one wants a *rule*: a
cut chosen from the partition that always dominates it.
`scripts/decomposable_exchange_map.py` tests four rule positions, each with
the better of the two orientations and clamped into the valid range:
the run boundary before the first run holding an upper-part letter, the one
after the last run holding a lower-part letter, and the two mirror images.
Contexts with a single run are set aside (no cut exists there; dominance is
the base threshold).

| case | multi-run contexts' interleaved partitions | before first U-run | after last L-run | before first L-run | after last U-run | any of the four |
|---|---|---|---|---|---|---|
| (4,4,5) | 20,736 | 20,736 | 20,736 | 20,736 | 20,736 | 20,736 |
| (4,5,5) | 20,736 | 20,651 | 20,651 | 20,651 | 20,651 | 20,736 |
| (5,5,5) | 20,736 | 20,736 | 20,736 | 20,736 | 20,736 | 20,736 |
| (4,5,6) | 47,224 | 47,174 | 47,174 | 47,174 | 47,174 | 47,224 |
| (5,4,6) | 47,224 | 47,174 | 47,174 | 47,174 | 47,174 | 47,224 |

The rule positions were first tried without clamping and with a fixed
orientation each; then they missed 15 % of the partitions, all of them
partitions taking letters from every run, where the rule position falls off
an end.  Clamped and with the free orientation, one rule alone dominates
every partition at (4,4,5) and (5,5,5) and all but 85 of 20,736 at (4,5,5),
and the four together dominate everything.  This is the exchange argument
in outline: replace an interleaved split by the stacked cut at the first
alternation, in whichever orientation is better, and lose nothing.  The
85 exceptions at (4,5,5) are the cases a proof must treat separately or
with a second rule; they are listed in
`data/derived/decomposable-exchange-455-s5e2.json`.

## 2. No closed form in shifted thresholds

`scripts/decomposable_closed_form_fit.py` fits each depth-one state
(runs, outer flags, coupling) over all nine parameter triples by signed sums
of at most three thresholds `T(a+δa, u+δu, k+δk)` with shifts up to 2 and
coefficients ±1, ±2.  Closed forms exist exactly where the formula of
experiment 0118 is a single threshold: one outer sibling at coupling 1
gives `T(a, u−1, k)`, two give `T(a, u−2, k)`.  Every sibling-inside state
and every coupled state with a flag has no such formula over its 8 to 12
data points.  The reason is visible in the formula itself: those values are
minima and maxima of shifted thresholds (`min(u−1−b−e, k−1−max(b+e,d))`,
and the two-part maximum), which no fixed shift reproduces across the
binomial and window regimes.  So `F` is a recursion, not a window sum, and
additivity has to be proved for the recursion, by the exchange argument of
section 1 rather than by a binomial identity.

## 3. Wider additivity

Three external levels (up to three external vertices, up to four child
vertices), and (5,5,6) at two levels:

| case | contexts | nonzero | interleaved partitions | violations |
|---|---|---|---|---|
| (4,4,5), 3 levels | 101,163 | 24,297 | 179,354 | 0 |
| (4,5,5), 3 levels | 101,163 | 26,033 | 192,510 | 0 |
| (5,5,5), 3 levels | 101,163 | 27,785 | 205,794 | 0 |
| (5,5,6), 2 levels | 7,220 | 4,408 | 66,828 | **624** |

## 4. The (5,5,6) violations: the stacked recursion is not exact at k = 6

The 624 violations at (5,5,6) all have the same shape, for instance the
context `S 1L 2U S S` with sibling maxima (1, 1): one child vertex, then an
external vertex of the level-1 sibling (the child lower there) and one of
the level-2 sibling (the child upper there), then two child vertices.  The
recursion gives 9; the split with the lower part taken from inside the
second run gives 12.  `scripts/decomposable_context_exact.py` computed the
exact extremal value of this context from the compiled (5,5,6) class
(`data/derived/decomposable-context-exact-556-diagnosis.txt`): **12**, and
the two children's exact values equal their recursion values (3 and 9).  So
this is not a failure of additivity of the exact function, which is
tautological, but a failure of `F`: at (5,5,6) the stacked recursion
underestimates some contexts by three.  The extremal structure there has
the lower part strictly inside the upper part's span, a sandwich, which no
cut at a run boundary can produce; at `k = 5` such splits never beat a
stacked cut, at `k = 6` they do.

The repair is to admit interval cuts: one part any contiguous block of the
child's letters, the other the rest, both orientations, all couplings
(`make_F2` in `scripts/decomposable_recursive_formula.py`).  On the two
violating contexts it gives 12; on the smallest 342 deep signatures of the
`k = 5` cases it still agrees with the exact values.  Its full comparison
with the 8,624 deep signatures and its additivity at (5,5,6) and (4,5,6)
are running; see the addendum.

Consequences for the proof.  The induction hypothesis cannot be the
stacked recursion; whatever bound is used must allow sandwich splits at
every level, which is the same phenomenon that defeats the published
scalar induction, now located precisely: it appears first at `k = 6`, at
depth two, in a context with one sibling above and one below.  The exchange
argument of section 1 must then be stated for interval cuts, and the
additivity lemma becomes: the best partition of any context is dominated
by the best interval partition.

## Reproduction

```console
python3 scripts/decomposable_exchange_map.py --case 4,5,5 --s-max 5 --e-max 2 --levels 2 --output data/derived/decomposable-exchange-455-s5e2.json
python3 scripts/decomposable_closed_form_fit.py data/derived/decomposable-run-extremal-*.json --terms 3 --shift 2
python3 scripts/decomposable_additivity_test.py --case 4,4,5 --s-max 4 --e-max 3 --levels 3 --output data/derived/decomposable-additivity-445-s4e3l3.json
```

Inputs: experiments 0117 to 0120.  The k = 6 runs need up to 28 GiB for the
memoization table.

## Addendum, 7 September: interval cuts restore additivity at (5,5,6)

With the interval-cut recursion `F2` in place of `F`, the additivity test
at (5,5,6) on all contexts with up to four child letters and two external
levels, the set that contains every one of the 624 violating contexts of
section 4 (they have three letters), finds **no violation**: 4,315
contexts, 2,747 nonzero, 20,310 interleaved partitions, 17 minutes
(`data/derived/decomposable-additivity-556-s4e2-F2.json`).  `F2` agrees
with the exact values on all 42 and 504 deep signatures of `(4,4,5)` and
`(4,5,5)` and on 150 sampled signatures of `(5,5,5)`; the full `(5,5,5)`
comparison and the five-letter `(5,5,6)` run exceed 28 GiB of memoization
in Python and were not completed.

So the picture after the three items is: the induction hypothesis is the
recursion with interval cuts (a part may be any contiguous block of the
child, in either orientation, coupled through the sibling maxima); it is
exact on every context computed at `k = 5` and on the `k = 6` contexts where
the stacked recursion fails; and its additivity, the one open lemma, holds
on every abstract context tested, including the `k = 6` contexts that
defeat the stacked form.  The exchange map of section 1 says which cut to
take: one of the four boundary positions in the better orientation, and,
by section 4, an interior block when the lower part is sandwiched.

**Addendum 2, 7 September.**  The five-letter (5,5,6) test with interval
cuts, run as four independent shards with bounded memoization tables
(`scripts/decomposable_additivity_test.py --shard`, merged by
`scripts/decomposable_additivity_merge.py`): all 66,828 interleaved
partitions of the 4,408 nonzero contexts, **no violation**, 4.2 h of
shard time at under 2 GiB per shard, where the single process had reached
28 GiB without finishing.  The four-letter interval-cut chain is also clean
at (4,5,6), (5,4,6) and (4,6,6) (20,310 partitions each).  So on every
context tested at `k = 6`, the interval-cut recursion is additive exactly
where the stacked one is not.

**Addendum 3, 7 September.**  Interval cuts, exactness at `k = 5`: the
sharded comparison on all 8,078 deep signatures of `(5,5,5)` (depths two to
five) gives `F2 − E = 0` on every one
(`data/derived/decomposable-recursive-F2-vs-exact-555.json`), so `F2` is
exact on all 8,624 deep contexts at `k = 5`.  Three external levels with
interval cuts at `(4,4,5)`: 179,354 partitions, no violation (sharded).
And at `(4,5,6)`, deep signatures taken from a sample of 50 extremal
colorings of the compiled class (348 signatures, all tight) show the stacked
recursion below the exact value on 4 of them, by one or two, so the sandwich
effect is present at `(4,5,6)` as well as `(5,5,6)`; the full `(4,5,6)`,
`(4,5,7)` and sampled `(5,5,6)` tables with both recursions are running
(`scripts/decomposable_deep_tables_compiled.py`).

**Addendum 4, 7 September: three levels and k = 7.**  Interval-cut
additivity on contexts with up to three external levels (up to three
external vertices, up to four child vertices), sharded:

| case | contexts | nonzero | interleaved partitions | violations |
|---|---|---|---|---|
| (4,4,5), 3 levels | 101,163 | 24,297 | 179,354 | 0 |
| (4,5,5), 3 levels | 101,163 | 26,033 | 192,510 | 0 |
| (5,5,5), 3 levels | 101,163 | 27,785 | 205,794 | 0 |
| (4,5,7), 2 levels | 6,633 | 4,637 | 34,314 | 0 |

The first `k = 7` case passes.  At `(4,5,6)`, the deep signature tables from
all 5,874 extremal colorings of the compiled class contain 12,724 distinct
signatures, every one attained; the stacked recursion is exact on 12,716 and
short on 8 (four by one, four by two), the sandwich contexts; the
interval-cut comparison on the same table is in progress.

**Addendum 5, 7 September: the interval-cut recursion never overestimates
where checked.**  Against the depth-one tables of all nine cases (926
entries with a placed sibling) `F2` equals the exact value on every entry,
never above, never below; and it is monotone in each sibling maximum
(9,444 comparisons at `(4,4,5)`, `(4,5,5)`, `(5,5,5)`, no violation).  So
lemma 2 holds for `F2` as it did for `F`, and `F2` is exact on every
depth-one context of the nine cases and every deep context at `k = 5`.

**Addendum 5, 7 September: `F2` is exact on the real deep `(4,5,6)` contexts.**  The
12,724 deep signatures taken from the compiled `(4,5,6)` class (the `deep-456` table of
`scripts/decomposable_deep_tables_compiled.py`, every subtree context of the extremal
colorings) were compared with the interval-cut recursion on all 12,672 rows with at most
six child letters: **`F2 − E = 0` on every one**
(`data/derived/decomposable-recursive-F2-vs-exact-456-deep.json`; twelve `es job run`
shards at 2 GiB caps, checkpointed every ten rows after the morning's WSL restart lost the
first attempt).  The 52 rows with seven or eight child letters are excluded: the
recursion's interval-cut enumeration stalls on them for over an hour each and needs a
better memoization key before they can be run.  Together with the `k = 5` tables this is
the evidence that `bound` (the Lean transcription of `F2`) is the exact child count on
every real context computed so far, so the additivity conjectures are about the true
extremal function, not about a loose bound.
