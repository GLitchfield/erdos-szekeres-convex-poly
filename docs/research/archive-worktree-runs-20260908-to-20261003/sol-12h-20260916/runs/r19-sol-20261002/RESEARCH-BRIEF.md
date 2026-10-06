# R19: singleton attainment (PEEL) and its two exact tools (one Sol trial, gpt-6.1-sol)

**Approval and roles.** Approved by Gavin on 2026-10-02 ("let's see what proof work we can get
done today advancing things").
- Coordinator: `claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude).
- Callbacks are not verified, so never wait for replies; keep `PROGRESS.md` here current.
- This is one trial. Never reset the host deadline.

**Worktree and branches.**
- Worktree `runs/worktrees/sol-12h-20260916`, branch `research/r19-peel-20261002` from main
  e3c87197.
- R18's branches in this worktree must be preserved. Do not modify them; create your own `node/*`
  branches from e3c87197.

**Integration in parallel.** In parallel the coordinator integrates the closed helpers of
R16/R17/R18 into main. Do not touch their nodes. Their handoffs are useful reading:
- `runs/worktrees/sol-12h-20260913/runs/r17-sol-20261001/MATHEMATICAL-HANDOFF.md`
- `runs/worktrees/sol-12h-20260916/runs/r18-sol-20261001/MATHEMATICAL-HANDOFF.md`

## Background (read first)

Read `/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-residue-20261001/NOTE.md`, including
its CORRECTION, and `HANDOFF.md` in that directory. All evidence there is diagnostic, from the
compiled evaluator.

- **One-level roots are explained.** The Lean bound equals the depth-one closed form
  (`scripts/decomposable_depth1_formula.py`) on all non-degenerate cases. It depends only on the
  limit profile: a run type path of length <= 3.
- **The common obstacle.** R16, R17 and R18 all stalled at the same step, the *sibling penalty*.
  When a part is split off, its sibling sees two nested same-side levels instead of one merged
  level, and one side/coupling choice must pay for it:
  - R18: "same-side merge loses marker-thread data";
  - R17: "bound the complement together with the leaf gain".

  Per AGENTS.md, do NOT commission another narrowing on that route. Work from the mechanism below.
- **PEEL** (singleton attainment for ALL contexts, any child) holds on every family tested:
  - two-level contexts at k=5 and k=6;
  - three-level four-child contexts at k=5 (all (a,u)) and at k=6, (4,5,6), (5,5,6), (6,6,6).
- **Peeling only an end is not enough.** EXTREME-PEEL (first/last child only) and END-PEEL (the
  four run-end children) are REFUTED at k=6, three levels: 68 and 24 non-degenerate failures.
  Example: `SSS1L3L2LS`, maxima (1,1,1), (a,u,k) = (5,5,6), bound 8. The ONLY optimal first peel
  is the middle child of the three-child run (upper side, d=2): leaf 2 + rest 6.
- **Mechanism.**
  - The peeled child becomes the OLDEST level for everything else. It costs the remainder an
    extension only on chains to which it can be appended as the outermost link.
  - A flank (end) child always can, so it costs every chain on its side.
  - An interior child only extends chains lying wholly on one side of it. It is free for chains
    spanning across it.
  - In `SSS1L3L2LS` the value lives on spanning cups (within-run cup limit 2, run1->run2 cup
    limit 4), so the middle peel wins.
  - Hypothesis to test and prove: **the optimal first child is the one whose letter costs the
    remainder least.**

## Work items, in priority order

### 1. Splitting identity (arithmetic, about 100 lines; close it first)

For 3 <= a, 3 <= u, a,u <= k:

    max_{1<=d<=k-2} [ T(a, min(u-1,k-d), k) + T(min(a-1,d+1), u, k) ] = T(a,u,k),

where T = decomposableThreshold. Register both halves with `es node add` (kind formalization):
- the witness half, with explicit d;
- the "every d gives <= T" half, if convenient.

Proof, checked by hand:
- **Classic regime (a+u <= k+3).** Take any d in [a-2, k+1-u]. Both terms are classic, and Pascal
  gives C(a+u-5,a-2) + C(a+u-5,a-3) = C(a+u-4,a-2).
- **Window regime (a+u >= k+4).** Take d in [k-u+1, a-2]. The terms are the size windows
  [k-a, k-d-2] and [k-d-1, u-2] of row k-2. These tile [k-a, u-2]. The window formula is valid at
  the classic boundary, since a+(k-d) in {k+2,k+3} and (d+1)+u = k+2 give coinciding classic and
  window values.
- Tools: `decomposableThreshold_eq_choose`, `_eq_window`, `decomposableBinomialWindow_pair_le`
  (ErdosSzekeres/Decomposable.lean), `Nat.choose_succ_succ`, Finset.Icc splitting.

Meaning: splitting a single run into two adjacent singletons (left lower, right upper) loses
nothing.

### 2. FLANK-SWAP (formalization, MERGE-sized, about 500 lines)

**Statement.** Suppose level 1's letters all lie left of every child and level 2's all lie right
of every child, or the mirror. Swapping the two level labels preserves `σ.bound` when:
- the two sides differ: each letter keeps its maximum (maxima [m2, m1] after the swap);
- the two sides agree: the maxima become (M, M-1), with M = max(m1, 1+m2), assuming 1 <= M-1 and
  M <= k-2.

**Why it holds.** A flank letter is always usable on its side, so extension counts do not depend
on level order. A chain using both flanks has strong term alpha + max(m_first, 1+m_second) in
either order, and every other chain type sees one flank only. So every descendant's limits are
identical; finish by induction on fuel exactly as `ctx_bound_le_merge_same_side_levels`
(ESBlueprint/B/CtxBoundLeMergeSameSideLevels.lean) does.

**Evidence.** Verified exactly: 12,672 same-side and 19,008 different-side contexts, k=5
(`runs/claude-labels-20261001/flank_swap.py`, job 20261001-171623-44dbc9).

### 3. PEEL: register, falsify, and work on the proof

- **Register.** Use `es node add`, kind conjecture. Domain: 4 <= a, 4 <= u, a,u <= k, legal
  maxima, numRuns >= 2, bound >= 2. Conclusion: some child p (any position), side s and coupling
  1 <= c <= k-2 satisfy
  σ.bound = (σ.part [p] s c).bound + (σ.part rest (opp s) (k-1-c)).bound.
  This generalizes the closed <= 3 children case and N_root. Falsifier: adapt
  `runs/claude-labels-20261001/peel_nf.py` (mode all) or `peel3_fail.py`.
- **First mathematical step.** Explain `SSS1L3L2LS` and the other k=6 middle-child cases exactly.
  Compute the leaf and remainder limits for each candidate child. Show that the remainder's loss
  equals the number of its binding chains extended by the child's letter as the oldest level.
- **Then try a proof** by induction on children with a cost-based choice. Take an optimal interval
  cut. Choose p in the part where its letter, as the oldest level, binds no chain of the other
  part, or binds only coupling-limited chains, where re-choosing the coupling pays: the pure-T scan
  closed all 87,804 coupling-limited cases. Use FLANK-SWAP where p is outermost.
- **Done for this item:** PEEL proved, or refuted by a counterexample, or a written proof idea that
  survives the k=6 examples. A narrowing alone is bookkeeping; say why its pieces are easier, or
  don't do it.

## Constraints

- es job run for anything over a minute; no self-chosen timeouts; `es log` every finding; a
  handoff at the end.
- New statements only via `es node add`; one node per branch; no merge or push. The coordinator
  integrates your pinned commits.
- Your sandbox cannot write `.git-data`: commit through the guarded es job path, as R17/R18 did.
- Keep memory caps modest. `es node add`/`es check` reserve 20G; two build slots are available.
- When items 1 and 2 are closed and committed, say so in PROGRESS.md immediately.
