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
EXCHANGE_K6

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
ADDITIVITY_MORE

## Reproduction

```console
python3 scripts/decomposable_exchange_map.py --case 4,5,5 --s-max 5 --e-max 2 --levels 2 --output data/derived/decomposable-exchange-455-s5e2.json
python3 scripts/decomposable_closed_form_fit.py data/derived/decomposable-run-extremal-*.json --terms 3 --shift 2
python3 scripts/decomposable_additivity_test.py --case 4,4,5 --s-max 4 --e-max 3 --levels 3 --output data/derived/decomposable-additivity-445-s4e3l3.json
```

Inputs: experiments 0117 to 0120.  The k = 6 runs need up to 28 GiB for the
memoization table.
