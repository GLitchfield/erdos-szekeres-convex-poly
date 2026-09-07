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

## 2b. The stripping step, tested (same day, later)

`scripts/decomposable_strip_end_test.py` tests the induction step directly: cut the first
or last child position `p` off as a singleton, on the side its membership gives it (the
kept side if `p ∈ K`, the other side otherwise) or on the opposite side, at some coupling
`d₂`, and compare `V_σ(K, o, d)` with `base({p}) + V_{σ'}(K ∖ {p}, o, d₃)`, the value of
the *same* partition in the reduced context `σ'`.  At (4,4,5) with up to four letters and
one level, with `p` on its membership side:

| pattern | splits | step holds | with `d₂ = d₃ = d` |
|---|---|---|---|
| A-B-A-B (4 blocks) | 216 | 216 | 216 |
| 3 blocks (a sandwich) | 792 | 784 | 620 |

So for A-B-A-B the induction step is exactly as hoped, with the original coupling on both
sides (a first version that put `p` on the kept side regardless of membership failed 4
times: membership decides the side).  For three blocks it fails in eight cases, e.g.
`S S 1L S S` with maxima (1), keep {1}, upper, `d = 1`: the partition is worth 5, the
whole bound of `σ`, while every end-singleton cut on the membership side is worth at most
4 = 1 + 3.  Two things can rescue such a case: the cut at the run boundary `{0, 1} | {3, 4}`
(both parts single runs), or the end singleton on the *opposite* side, which the
exhaustive scans say always exists in one of the four end-cut forms.  Probe v3 (queued)
and the strip test with both sides decide which move the induction should take.

## 2c. The bound is attained by an end cut (same day, evening)

`scripts/decomposable_end_cut_normal_form.py` asks a question about the recursion alone:
is `bound σ`, the maximum over *all* interval cuts, always attained by a cut that isolates
the first or the last child position (either side, some coupling)?  At k = 6 on (4,5,6)
and (5,5,6) with up to four child letters and two external levels, every context with two
or three runs and a nonzero bound, 2,600 of them, has its bound attained by such an end
cut (interior blocks never win).  If this holds in general, every cut tree normalizes to a
sequence of end strips, `bound` has a recursion over end cuts only, and the exchange lemma
becomes a commutation of two end strips: the partition tree strips an end of one part,
the exchanged tree strips the same position at the root.  The k = 5 runs with up to five
letters and the three-run contexts at larger sizes are queued.

Whether one strip at the *global* end always suffices for the induction of §3 is what the
both-sides strip test (v3) measures; with the end position confined to its membership
side and two external levels it fails on 112 to 324 four-block splits per case, so the
side has to be free.

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
   needs a change of coupling, so the induction can carry `d` unchanged, provided the
   stripped position keeps its own side (§2b).  Stripping an end of a four-block pattern
   whose end block is a singleton produces a three-block pattern, so milestone A rests on
   milestone B.
2. **Milestone B (three blocks).**  When one side is an interior block of the other, the
   single strip on the membership side is not always enough (§2b); the run-boundary cut,
   whose parts are single runs, or the end singleton on the opposite side rescues the
   failures.  The step to prove there is a comparison of leaf values, the three-way base
   allocation (`ctx_bound_three_way_base_allocation`, closed) composed with the
   prefix/suffix Pascal step, once the leaves' limits under the sandwich tree are shown to
   be no better than under the exchanged tree; that monotonicity of limits under
   re-rooting a cut tree is the lemma still missing.  The shift statistics show recoupling
   by one in both directions, so the coupling has to be chosen from the leaves, not by a
   fixed rule.
3. **Assembly.**  Milestones A and B cover every partition of a two-run context that is
   not itself a prefix/suffix cut (two blocks are exactly those); with `ctx_bound_cut_le`
   this is additivity for two-run contexts.  The general statement (any number of runs)
   should follow the same induction with the number of runs as a secondary measure.

4. **Dependency structure after the strip tests (evening).**  With the stripped end free
   to take either side (v3, k = 5 and 6, up to four letters, two levels), the step
   `V_σ(K, o, d) ≤ base({p}) + V_{σ'}(K ∖ {p}, o, d₃)` holds for every four-block split
   in all four cases and for every three-block split except 64 at (5,5,6), all of the form
   `S 1L 2U S S S` with the kept block strictly inside the second run.  There the
   dominating cut is the run cut `{0} | {3, 4, 5}`, whose residual is a *single* run: what
   continues the induction is `bound(σ') = base(σ') ≥ V_{σ'}(K ∖ {p})`, single-run
   additivity for a sandwich, not the same partition.  So the two-run lemma decomposes as

   - the **strip lemma** for residuals with two runs (a level-swap comparison between
     "cut K first, strip p inside a part" and "strip p first, cut K inside the rest"),
   - **single-run sandwich additivity** (`ctx_bound_additive_single_run` restricted to
     interior blocks; Codex's singleton-ended draft is the first case),
   - induction on the number of child positions, with `ctx_bound_cut_le` and the closed
     prefix/suffix node at the bottom;

   and the end-cut normal form (`ctx_bound_attained_by_end_cut`) is the same strip lemma
   applied to interval partitions.  The strip lemma is where the Lean work starts: its two
   sides differ only in the levels of two letter groups (the stripped position and the
   other part) and in the maxima the couplings assign, which is a finite comparison of
   `leftExt`/`rightExt`/`joinExt` values that the existing `part_*` and `withMaximum`
   lemmas of `DecomposableContextLemmas` can express.

## Reproduction

```console
es falsify ErdosSzekeres.ctx_bound_two_run_boundary_domination
es job run --why "two-run probe" --out runs/experiments/20260907-exchange/tworun-456-s4e2-b4.json --mem 3G -- \
  python3 scripts/decomposable_two_run_domination.py --case 4,5,6 --s-max 4 --e-max 2 --levels 2 --blocks 4 \
  --output runs/experiments/20260907-exchange/tworun-456-s4e2-b4.json
```
