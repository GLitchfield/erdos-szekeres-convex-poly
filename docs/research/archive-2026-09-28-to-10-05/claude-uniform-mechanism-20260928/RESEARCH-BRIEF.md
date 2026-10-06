# Claude run: a uniform mechanism for context-bound additivity

Run: `claude-uniform-mechanism-20260928`. Coordinator: Claude Code session
`claude-code:17de3bb4-f81b-48a5-b73d-2d86b781322f`, which also plays Astra (direction and review).
Research window `window-e252a09356f64a79`; coordinator-monitoring window
`window-b24d4ed9d4484de5` (observational 10,000-output-token target).
Claim: `ErdosSzekeres.ctx_bound_prefix_suffix_domination`, until 2026-09-29 02:08 EDT.
Run directory: `runs/claude-uniform-mechanism-20260928/` in the primary checkout.

## Why this run exists

The B chain is `decomposableStateUpper_all ← ctx_card_le_bound ← ctx_bound_additive`.
`ctx_bound_prefix_suffix_domination` together with three closed lemmas
(`ctx_bound_cut_le`, `ctx_bound_additive_prefix_suffix`,
`ctx_bound_interval_or_complement_le`) gives `ctx_bound_additive` outright.

Since 8 September the Codex route has closed single-run additivity one capacity band at a time:
`ctx_bound_additive_single_run_min_capacity_three`,
`..._min_capacity_four_below_saturation`, and now capacity five at k = 6
(`ctx_two_actual_marker_small_history_internal_chosen_kept_cut_six_bound`, still partial).
Each band uses bespoke fixed-k charge accounting, and no lemma takes band c to band c + 1.
That approach cannot reach all k. Every route is missing a **uniform mechanism**. This run
looks for one. It works mathematics-first and computation-guided, and every conjecture is
falsified at k ≤ 7 before anyone writes a proof. No Lean is written in this phase.

## Seed finding (coordinator, 28 Sept, diagnostic only)

Define two reductions of a context σ at `(a, u, k)`:

- σ↓cap: parameters `(a−1, min(u, k−1), k−1)`; every level where the child is **lower**
  (so its sibling maximum is a cap) has its maximum decreased by 1.
- σ↓cup: parameters `(min(a, k−1), u−1, k−1)`; every level where the child is **upper**
  has its maximum decreased by 1.

**Conjecture P (Pascal exactness).** For well-formed σ with every sibling maximum in `[2, k−3]`
and `4 ≤ a, u ≤ k−1`: `bound_k(σ) = bound_{k−1}(σ↓cap) + bound_{k−1}(σ↓cup)`.

Evidence so far: exact on all 606 non-extreme contexts at each of (4,4,6), (4,5,6) and (5,5,6)
(s ≤ 3, e ≤ 2, two levels). Outputs are `pascal/probe-keep_letters.txt`, jobs
`20260928-140829-258402` and `-2c50e6`. Larger probes (k = 6 with s ≤ 4 or three levels,
k = 7) run as jobs `20260928-141019-*` and `20260928-141020-*`, with outputs
`pascal/pk-*.txt`. The script is `pascal/pascal_probe_keep_letters.py`.

Failures seen so far:
- extreme maxima: 1, a singleton sibling or "marker"; and k−2;
- a = 3 (60 contexts at (3,4,5));
- u = k (2 at (4,5,5), 4 at (5,5,5)).

The direction `bound_k ≥ sum` failed only on 4 extreme contexts at (5,5,6).
Deleting the letters of a level whose maximum reduces to 0 is the wrong normalization:
it overshoots (`pascal/probe-delete_empty.txt`).

**Why P matters.** Take a partition with coupling d in `[2, k−3]` of a non-extreme σ, with parts
A and B. Then `A↓cap`, `B↓cap` are the parts of `σ↓cap` at couplings `(d−1, c)`, and
`A↓cup`, `B↓cup` are the parts of `σ↓cup` at `(d, c−1)`. So
`F(A)+F(B) = [F(A↓cap)+F(B↓cap)] + [F(A↓cup)+F(B↓cup)] ≤ F(σ↓cap) + F(σ↓cup) = F(σ)`,
using additivity at k − 1. **Additivity then descends in k uniformly.** What remains are extreme
couplings (d = 1 or d = k − 2, i.e. a singleton part or a maximal-chain sibling), contexts
whose history contains extreme levels, and the parameter boundary (a or u equal to 3 or k).
These are the configurations where the Codex k = 6 analysis is stuck.

Proof sketch for the two directions. It is unverified and part of Track B's job.
- **Leaves.** For a single run, when `u ≤ k−1` the cap reduction lowers the cap limit by exactly
  one and leaves the cup limit unchanged. The cup reduction is symmetric when `a ≤ k−1`. So
  the leaf values obey Pascal for the threshold, `T(p+1,c+1,k) = T(p,c+1,k−1) + T(p+1,c,k−1)`,
  except at (1,1) leaves.
- **Descent (≤).** Follows by structural induction on the recursion, because a maximum of sums
  is at most the sum of the maxima, at least for non-extreme cuts.
- **Ascent (≥).** Needs the cap-world optimal cut and the cup-world optimal cut to combine.
  This is the real content; find out what makes it true.

## Ground rules (every track)

- Export `ES_AGENT=claude-code:17de3bb4-f81b-48a5-b73d-2d86b781322f/<track>` in each Bash
  call. Run `es` as `tools/es/bin/es` from `/home/gavin/git/erdos-szekeres-convex-poly`.
- Anything longer than about a minute goes through
  `es job run --why "..." --out runs/claude-uniform-mechanism-20260928/<track>/... --node ErdosSzekeres.ctx_bound_prefix_suffix_domination --mem 3G -- <cmd>`.
  Caps are 3 GiB, 4 GiB at most; run at most two jobs per track at once. Wait with
  `es job wait <id> --timeout 55` in a loop. Codex holds a 2 GiB host job and the shared budget
  is 30 GiB. Use bounded evaluator caches (`cache_size` ≤ 400000). Historical k = 6 memo tables
  reached 28 GiB, so shard instead of growing a cache.
- Record every finding **as it arises** with
  `es log --node ErdosSzekeres.ctx_bound_prefix_suffix_domination "<claim, hypotheses, probe semantics, result, why, job id / path>"`.
  This includes failed conjectures and counterexamples. Say explicitly that computational
  evidence is diagnostic, not Lean-certified.
- Before writing Python, run `es lib search "<task>"` and `es lib show <id>`. The evaluator is
  `harness.research.recursive.evaluator(a,u,k, semantics='context-bound-zero-children-v1', cache_size=...)`,
  which returns `F(word, maxima)`. The word is a tuple of `'S'` or `(level, 'lower'|'upper')`.
  The maxima are indexed by level − 1 and hold a cap when the child is lower there and a cup
  when it is upper. The context enumerator is
  `scripts/decomposable_additivity_test.contexts(s_max, e_max, levels, k)`, and
  `...child(word, maxima, keep, side, sibling_max)` builds a part.
- Write only under `runs/claude-uniform-mechanism-20260928/<track>/`. Do not touch git, branches,
  worktrees, `ESBlueprint`, statements, or other agents' claims. Codex's live work is
  `runs/worktrees/sol-12h-20260916` (Sol research on
  `ctx_two_actual_marker_small_history_internal_chosen_kept_cut_six_bound`) and
  `runs/worktrees/main-integration-20260928`. Treat them as read-only.
- Current Lean sources, to read only, are at the chain tip:
  `runs/worktrees/older-exterior-small-opposite-20260924/ErdosSzekeres/DecomposableContext.lean`,
  `.../DecomposableContextLemmas.lean` and `.../ESBlueprint/B/*.lean`. Closed general lemmas
  worth knowing:
  - `ctx_single_run_descendant_bound_normalize`: old history absorbs into the run parameters,
    so single-run questions reduce to root contexts.
  - `ctx_single_run_part_limits_exact`
  - `ctx_erase_level_bound_mono`: erasing a level can only raise the bound.
  - `ctx_part_limits_le`
  - `ctx_mixed_exchange_of_ordered_limits`
  - `ctx_sandwich_middle_block_contraction`
  - `ctx_bound_three_way_base_allocation`
  - `ctx_point_limits_eq_of_child_interval`
  - `ctx_reverse_extension_transport`

  Search more with `es search "<identifier-like tokens>"`.
- Background notes: `docs/experiments/0120` to `0124`; 0121 addendum 6 and 0124 cover the
  exchange rule and strip tests. `runs/sol-12h-20260923/GOAL-OPTIONS.md` and `REPORT.md`
  describe Codex's current leaf.

## Track B (primary): Pascal descent

1. **Falsify P broadly.** Cover k = 6 with s ≤ 4 and three levels, k = 7 (several `(a,u)`), and
   k = 8 if affordable. Read the coordinator's queued `pascal/pk-*.txt` first, and do not rerun
   them. Record exact counts. If P fails on a non-extreme context, stop and characterize the
   failure family before anything else.
2. **Separate the directions.** Find where descent (≤) and ascent (≥) each hold, including on
   extreme contexts. Test ascent on the parts produced by extreme cuts specifically.
3. **Find the correct statement at the boundary.** Handle extreme maxima (marker levels), a = 3
   and u = k. Candidates: a normalization of marker levels that makes P exact (compare Codex's
   `*_marker_erase_normalize` lemmas); a refined reduction that sends a singleton sibling into
   exactly one world; or a weaker inequality that is still enough for the induction.
4. **Write the induction.** State exactly which additivity cases P reduces to smaller k, which
   residual family is left (it should be extreme-coupling or marker cuts), and whether that
   residual is itself uniform in k. Test the residual statement computationally.
5. **Attempt a paper proof** of P, or of whichever direction survives, for general k: leaves
   first, then the recursion.

## Track A (secondary): deterministic exchange rule

The goal is a *deterministic* rule for the prefix/suffix cut and coupling that dominates each
partition (0124: "same end, side mirrored or swapped, couplings (m,d) or (m+1,d−1)" was only
existential).

1. Using and extending `scripts/decomposable_exchange_test.py`,
   `decomposable_strip_rule.py`, `decomposable_strip_numeric.py`,
   `decomposable_two_run_domination.py` and `harness/falsifiers/ctx_prefix_suffix_domination.py`,
   find a selector from partition data (membership pattern, end limits) to `(I, d')` with zero
   failures at k = 5 (s ≤ 5) and k = 6 (s ≤ 4), then test it at k = 7.
2. Split the rule's inequality into separately testable general lemmas: a leaf numeric
   inequality on thresholds and a residual (level-swap) monotonicity. Falsify each at k ≤ 7.
3. **Coordinate with Track B.** Check whether P already disposes of non-extreme couplings. If so,
   restrict the exchange rule to extreme-coupling or marker partitions and report whether the
   rule becomes simpler there.

## Decision gate and deliverables

Each track ends with `runs/claude-uniform-mechanism-20260928/<track>/FINDINGS.md` containing:
- the exact conjecture statements (as Lean-style formulas over `Ctx.Context` where possible);
- evidence tables with job ids and output paths;
- failures and counterexamples;
- the proof status: a paper proof, a partial proof with the precise gap, or a refutation;
- the recommended next step.

Log the path with `es log`. The coordinator reviews both and decides whether a general
conjecture has survived k = 7 and has a credible proof path. If so, the next window registers
it (`es node add`, on a `node/<Name>` branch) and starts Lean. If not, the run records the
obstruction and stops. No theorem credit is claimed for computational evidence.
