# Handoff: Claude run `claude-uniform-mechanism-20260928` (closed 28 Sept 2026)

Coordinator: `claude-code:17de3bb4-f81b-48a5-b73d-2d86b781322f`. Brief: `RESEARCH-BRIEF.md`.
Tracks ran as background subagents: B = Pascal descent, A = deterministic exchange rule.
All track findings are in `es journal` on `ErdosSzekeres.ctx_bound_prefix_suffix_domination`.
The harness blocked the subagents from writing `descent/FINDINGS.md` and `exchange/FINDINGS.md`. The
coordinator saved their full texts there with Gavin's approval. Scripts and outputs are in `descent/` and
`exchange/`.

## Open obligation

`ErdosSzekeres.ctx_bound_prefix_suffix_domination` is unchanged: still open, with no counterexample. It
held on every partition tested up to k = 7 (s ≤ 4, two levels, including boundary parameters). This run
earns no theorem credit. Nothing was written in Lean except the certification `#eval` below.

## Certified finding

**`ErdosSzekeres.ctx_bound_attained_by_end_cut` is false as stated.**
- Context: (a,u,k) = (3,4,5), word `[ext 1 lower, child, child, ext 2 upper, child, child]`, maxima
  `[3,1]`.
- A Lean `#eval` of the real definitions (`certify/EndCutCounterexample.lean`, output `.out`, job
  `20260928-153807-8b8ad8`) gives child positions `[1,2,4,5]`, `numRuns = 2`, `bound = 1`, and best end cut
  `0`.
- Track A lists 24 such contexts at (3,4,5) and 36 at (3,5,6)
  (`exchange/verify/endcut-cex-345-s4e2l2.txt`). All have a = 3, and the node's falsifier never ran a = 3.
- **Next step:** register a refutation node with a `decide`/`rfl` proof, or `es node restate` with
  `4 ≤ σ.a`. Then re-check the consumer `ctx_bound_two_run_boundary_domination` at a = 3.
- **Update (Gavin approved "handle the false conjecture").** The kernel-checked refutation
  `ctx_bound_attained_by_end_cut_counterexample` compiles, using only `propext`, `Classical.choice` and
  `Quot.sound` (`certify/EndCutRefutation3.lean`, job `20260928-165722-8b2e28`). It avoids deciding the
  full 4-letter bound: `bound ≥ 1` comes from `ctx_bound_cut_le` at the run-boundary cut {1,2}, and the
  twelve end-cut values of 0 are separate `decide +kernel` lemmas (peak 4.5 GiB). Deciding the whole bound
  was OOM-killed at 8 and 16 GiB. The harness reported those as `rc=-15` with `oom_kills=0`, although
  systemd logged `oom-kill`.
  - Registration is in progress on branch `node/CtxBoundAttainedByEndCutCounterexample`, worktree
    `runs/worktrees/claude-endcut-refutation`.

## Results with paper proofs (not in Lean)

- **Tree identity (Track B).** For a, u ≤ k−1 and every interval-cut tree t:
  `val_k(t) = val_{k−1}(t↓cap) + val_{k−1}(t↓cup) + N11(t)`. Here ↓cap lowers a and k and every
  lower-level maximum by 1, ↓cup is the mirror, and N11 counts leaves with both limits 1. 214,677 random
  trees gave 0 violations.
  - Corollary: single-run bounds obey Pascal exactly, up to the (1,1) term.
- **MERGE (Track A).** Relabelling an adjacent same-side level into its neighbour, with the merged maximum
  any of inner, outer, max or min, never lowers the bound. 758k checks at k = 5–7 gave 0 failures. The
  proof: extensions and joins do not grow, the limits are monotone, and `part` commutes with merging, so
  induction on fuel finishes it. `es search` found no existing equivalent.
- **Orientation reduction (Track A).** The node is equivalent to `∀ K d, V_σ(K,d) ≤ M(σ)`, where M is the
  best prefix/suffix cut.

## Refuted (diagnostic)

- **Conjecture P (Pascal descent of the bound in k on non-extreme contexts) fails in both directions.**
  Counterexamples, rechecked by the coordinator:
  - (5,5,6) `1L2US1L2US` (2,2): 5 vs 3+3;
  - (7,7,8), same word: 45 vs 24+24;
  - (6,6,8) `S1L2US` (2,2): 30 vs 16+16;
  - (4,4,6) `2U1US3L4L` (2,2,2,2): 1 vs 0+0.

  Causes: (1,1) leaves, and different optimal trees in the cap world and the cup world. The P-induction
  leaves bulk residuals (13–38% of steps), not just marker cuts. P misled the coordinator at first because
  the early probes used at most two external letters.
- **Deterministic dominating-cut selectors fail in every family tried.** The needed coupling shift reaches 3
  at (5,6,7), and the working choice depends on part values.
- **PAIR, STRIP, END (at a = 3), and leaf-by-leaf limit domination are refuted.**

## Reusable observations and leads

- **Three-world domination.** For every partition tested, some prefix/suffix-rooted interval tree dominates
  every k-optimal partition tree in the k world and both reduced worlds at once. But it cannot also carry
  the partition tree's N11 count. A k-uniform proof would need a lemma that absorbs each (1,1) leaf into
  reduced-world slack. That lemma is untested.
- **The common obstruction in every approach is the low-value corner:**
  - (1,1) leaves;
  - the 1→0 PAIR losses;
  - the a = 3 end-cut failures.

  This is also where Codex's k = 6 analysis sits (singleton "marker" siblings). A direct attack on the
  corner is the recommended next research target.
- **Formal assets worth registering if a consumer appears:** MERGE; Lemmas 1–2 of Track B (reductions
  commute with `part`; exact limit transport); the single-run Pascal corollary.

## Evidence

- `pascal/`: coordinator probes; jobs `20260928-140829-*`, `-141019-*`, `-141020-*`.
- `descent/`: Track B; `pascal_lib.py`, `*_probe.py`, and outputs.
- `exchange/`: Track A; `tables/`, `lemmas/`, `leafdom/`, `verify/`, and `lean_literal.py`.
- `certify/`: the Lean `#eval` certification.

## Evening follow-ups (28 Sept, after the run closed)

- **MERGE proved.** `ErdosSzekeres.ctx_bound_le_merge_same_side_levels` (merging two adjacent
  same-side levels with the larger maximum never lowers the bound). Targeted `es check` job
  `20260928-192323-6d2d8a`: closed, sorry-free, standard axioms, type hash `3db6cc13c593f0b0`.
  - Branch `node/CtxBoundLeMergeSameSideLevels` (worktree `runs/worktrees/claude-merge-levels`),
    uncommitted.
  - Proof development: `merge/MergeScratch.lean` (compile jobs `20260928-191300-*`, `-192051-*`,
    `-192109-*`).
- **Restated conjecture.** `ErdosSzekeres.ctx_bound_attained_by_end_cut_of_four_le`:
  - It needs both 4 ≤ a and 4 ≤ u; the mirror (4,3,5) of the counterexample also fails.
  - Falsifier `ctx_end_cut_normal_form_four.py` passed all 6 cases (job `20260928-190547-471d23`).
  - Branch `node/CtxBoundAttainedByEndCutOfFourLe` (worktree `runs/worktrees/claude-endcut-four`),
    uncommitted.
- **Refutation branch.** The falsifier now runs a = 3 first; job `20260928-183635-012d12`
  recorded `counterexample`.
- **Harness branch.** `harness/incremental-index` (5648ad25 and fa937551; the nightly unit now
  forces a full re-extraction). Cutover steps: `CUTOVER-RUNBOOK.md`.
- **Track C** (brief `TRACK-C-BRIEF.md`, output `rewrite/`) is running. It tests whether a
  value-independent, reduction-equivariant, N11-monotone rewriting from partition trees to
  interval trees exists; by Track B's Theorem 4 that would prove additivity by induction on k.
- **Housekeeping, needs a decision.** `ErdosSzekeres/CommonAnchorPermutationOrder.lean:130` uses
  `native_decide` with no allowlist entry. The theorem ranges over all 256 maps Fin 4 → Fin 4
  times 1,024 states, so a kernel `decide` is impractical; it has no user besides the root import.
  Options: an allowlist entry, or dropping it from `ErdosSzekeres.lean`. Either rebuilds the root.

## Track C result (28 Sept, evening)

**Refuted.** The equivariant-rewriting route: a value-independent rewriting R from partition trees
to interval trees, commuting with the reductions and never decreasing N11, closed by Track B's
Theorem 4.
- **N11 monotonicity is impossible for any R, even at the top world.** Example: (4,4,5), word
  `1L S 1L S S S`, maxima (2), root K = child vertices 0 and 2 upper, d = 2. The k-optimal tree
  (value 3 = bound) has three isolated-vertex leaves; interval trees have at most two.
  Rechecked by the coordinator with `rewrite/explain.py` and the shared evaluator.
- **The δ and "route" strengthenings fail in the bulk:** non-extreme contexts, in-domain couplings,
  k = 5–7.
- **Structural obstruction (paper argument).** Theorem 4 needs a, u ≤ k−1, and the boundary
  {a = k} ∪ {u = k} is absorbing under both reductions. So no Pascal-in-k induction reaches
  a = u = k, the diagonal case `decomposableStateUpper_all` must cover.

**Surviving, evidence only: conjecture W.** One interval tree dominates the partition tree's value
in every Pascal world at once, with 0 failures on all tested ranges. W is stronger than additivity
and has no known mechanism; do not register it.

**Overall reading of Tracks A–C.** Every uniform-in-k mechanism tried breaks at the isolated-vertex
corner: (1,1) leaves, 1→0 losses, the a = 3 end-cut failures. That corner is exactly what Codex's
fixed-k charge accounting handles locally. This tempers the coordinator's earlier critique of the
fixed-k route: local accounting may be necessary rather than a detour. Evidence is in `rewrite/`.
The FINDINGS text is held pending Gavin's approval to save it.
