# Experiment 0124: boundary domination for two-run contexts — statement, evidence, proof plan

Date: 2026-09-07

Status: node `ctx_bound_two_run_boundary_domination` registered (conjecture, falsifier
`harness/falsifiers/ctx_two_run_boundary.py`); computations exact on abstract contexts; no
Lean proof yet.  Workstream B, the exchange lemma behind the additivity conjectures
(experiments 0121 addendum 6, 0123 §7).

## 1. The statement

For a well-formed context `σ` with exactly two child runs, a nonempty proper partition `K`
of the child positions, an orientation `o` (the kept part is the lower or the upper part)
and an admissible coupling `d` (`1 ≤ d ≤ k − 2`), write

    V_σ(K, o, d) = bound(σ.part K o d) + bound(σ.part (K^c) o' (k − 1 − d))

for the value of the partition (the sum of the two part bounds, `o'` the other side).  The
lemma: there are a nonempty proper prefix or suffix `I` of the child positions and an
admissible `d'` with

    V_σ(K, o, d) ≤ V_σ(I, o, d').

Prefix and suffix cuts are interval cuts, so `V_σ(I, o, d') ≤ bound σ` by
`ctx_bound_cut_le`; the lemma therefore gives `ctx_bound_additive` for every two-run
context.  It was proposed by Gavin and Codex on 7 September after the exhaustive scans of
0121 addendum 6; the same statement without the two-run restriction (any number of runs,
partitions that are not themselves prefix/suffix cuts, sandwiches included) had zero
failures on every case scanned, and would close both additivity conjectures outright.

Changing the coupling is essential: with `d' = d` the statement is false
(`ctx_bound_same_size_exchange_counterexample`, and 8 to 20 failures per case in the
k = 6 scans, thousands when sandwiches are included).

## 2. What the probes say about the dominating cut

`scripts/decomposable_two_run_domination.py` records, for every two-run context and
every partition with a given membership pattern, the set of `(I, d')` that dominate.
At k = 6 with up to four child letters and two external levels (2,496 two-run contexts,
literal Lean recursion):

| partitions | oriented splits | dominated | same `d` works | some end cut works | recoupling needed |
|---|---|---|---|---|---|
| A-B-A-B, (4,5,6) | 19,968 | all | all | all | none |
| A-B-A-B, (5,5,6) | 19,968 | all | all | all | none |
| every crossing (≥ 3 blocks), (4,5,6) | 93,184 | all | 88,420 | all | 4,764, all by exactly one |

So for the four-block pattern the exchange is the simplest possible: the *original
coupling* and a cut that isolates the *first or the last child position* already
dominate.  Recoupling by one is needed only for three-block patterns (a block of one side
strictly inside the other, the two-run sandwich), e.g. `S 1L S S` with maxima (1), keep
{2}, lower, `d = 3`: worth 9, while every end cut at `d = 3` is worth less and the cuts at
`d = 2` are worth 9.  The k = 5 runs with up to five letters and a refined probe (which
end, which sign of the shift) are in `runs/experiments/20260907-exchange/tworun-*.json`.

## 3. Proof plan

Induction on the number of child positions, exchanging one end position at a time.

1. **Milestone A (A-B-A-B).**  Let `p₁` be the first child position and suppose the
   pattern has four blocks.  Claim: `V_σ(K, o, d) ≤ V_σ({p₁}, o, d)` or the same with the
   last position.  The right-hand side is `base(σ.part {p₁} o d) + bound(σ')` where
   `σ' = σ.part (rest) o' (k−1−d)` is again a two-run context with one child position
   fewer and one more external letter at its left end.  The partition `K \ {p₁}` of `σ'`
   has at most four blocks, so by induction (or, when it is an interval cut, by
   `ctx_bound_cut_le`) `bound(σ') ≥ V_{σ'}(K \ {p₁}, o, d)`.  What remains is a comparison
   of cut trees: every cut tree of `σ.part K o d` has a leaf containing `p₁`; splitting
   `p₁` off that leaf costs at most the threshold difference that the new external letter
   at `p₁` charges to the rest, which is the Pascal step of the prefix/suffix node
   (`ctx_bound_additive_prefix_suffix`) applied inside the part.  The data say this never
   needs a change of coupling, so the induction can carry `d` unchanged.
2. **Milestone B (three blocks).**  When one side is an interior block of the other, the
   end cut needs `d' = d ± 1`; the probe's shift-sign statistic will say which, and the
   candidate identity is the window split `T(a,u,k) = T(a,k−d,k) + T(d+1,u,k)` of 0123 §1
   moved by one unit.
3. **Assembly.**  Milestones A and B cover every partition of a two-run context that is
   not itself a prefix/suffix cut (two blocks are exactly those); with `ctx_bound_cut_le`
   this is additivity for two-run contexts.  The general statement (any number of runs)
   should follow the same induction with the number of runs as a secondary measure.

## Reproduction

```console
es falsify ErdosSzekeres.ctx_bound_two_run_boundary_domination
es job run --why "two-run probe" --out runs/experiments/20260907-exchange/tworun-456-s4e2-b4.json --mem 3G -- \
  python3 scripts/decomposable_two_run_domination.py --case 4,5,6 --s-max 4 --e-max 2 --levels 2 --blocks 4 \
  --output runs/experiments/20260907-exchange/tworun-456-s4e2-b4.json
```
