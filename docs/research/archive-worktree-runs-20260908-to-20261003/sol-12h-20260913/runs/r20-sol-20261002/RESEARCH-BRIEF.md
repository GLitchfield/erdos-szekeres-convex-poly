# R20: formalize the uniform two-cup-block lemma (one Sol trial, gpt-6.1-sol)

**Approval and roles.** Approved by Gavin on 2026-10-02 ("Yes, go ahead with R20. Let's see what we can learn to
help us prove the other cases.").
- Coordinator: `claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude).
- Callbacks are not verified, so never wait for replies; keep `PROGRESS.md` here current.
- This is one trial. Never reset the host deadline.

**Worktree and branches.**
- Worktree `runs/worktrees/sol-12h-20260913`, branch `research/r20-cupblock-20261002`, from main `6e4d0e66`.
- Create your `node/*` branches from `6e4d0e66`.
- R17's leftover untracked files were archived under `runs/r17-sol-20261001/untracked-leftovers-20261002/`. Do not
  restore them.
- **In parallel**, R19 (Sol) runs in `runs/worktrees/sol-12h-20260916` until 2026-10-03T00:25Z. Do not touch its
  branches or nodes.

## Background (read first)

**The core of workstream B.**
- `decomposableStateUpper_all` (Baek–Balko Theorem 8) reduces, by experiment 0081
  (`StructuralChargingPascalTails.lean`, `StructuralChargingPascalTailGates.lean`), to strict predecessors plus two
  singleton Pascal-tail gates per active state (a,u,k).
- Each gate follows from the two-side bound `PascalTailTwoSideBound a u k`.
- For the diagonal a=4 family the two-side bound is exactly the two-cup-block contract
  `DiagonalCupBlocksForce4kk k` (`ErdosSzekeres/StructuralChargingPascalCupBlocks.lean`). It was known only for
  k <= 8 (hand-built theorems) and k = 9 (a large CNF certificate).

**New today.** A uniform hand proof for every k >= 5, valid for every OneChange coloring (decomposability is not
used). It is in `CUPBLOCK-PROOF.md` in this directory, written by a Claude subagent and verified line by line by
the coordinator.
- Exhaustive replays: n <= 10, including 319,312 tight k=7 splits.
- Random replays: n <= 12.

**Mechanism.**
- With no 4-cap, a strong set is a cup plus at most one apex.
- Every strong set of size >= 5 that avoids D = {2nd point of the left cup, 2nd-to-last point of the right cup}
  extends by one point (Claim D).
- So deleting D lowers the largest strong set, giving induction on k.

## Work items, in priority order

### 1. The uniform theorem (close it first)

Follow `FORMALIZATION-PLAN.md` in this directory. The target node (`es node add`, kind formalization):

    theorem diagonalCupBlocksForce4kk_of_five_le {k : ℕ} (hk : 5 ≤ k) : DiagonalCupBlocksForce4kk k

Suggested route:
- **Strengthened card bound, by induction on k** (`TwoCupBlockBound k`: ordered cup sides, OneChangeOn, no 4-cap,
  no strong k-set => |left| + |right| <= 2k - 4).
- **Base k = 5:** from `diagonalCupBlocksForce4kk_five` via `diagonal_cup_block_card_add_le`.
- **General helpers H1–H3**, with `es search` before each:
  - H1: consecutive-triple cups are cup sets under OneChangeOn;
  - H2: under no 4-cap, a middle-determined set has at most one cap-middle interior point. Use
    `isStrongPolygonSet_iff_isMiddleDeterminedOn`;
  - H3: a cup plus an apex (l,x,r) cap is middle-determined.
- **Claim D:** the case split in `CUPBLOCK-PROOF.md`, Step 1.
- **Induction step:** delete D.

Also derive `SingletonLowerPascalTailGate 4 k k` for all k >= 5 from `singletonLowerPascalTailGate_four_diagonal_of_cupBlocks`.
Make it a separate node if the one-node-per-branch rule requires it.

**Done for item 1:**
- the theorem is CLOSED with an original-source receipt (standard axioms, no sorry, no certificates, no
  `native_decide`);
- or the exact blocking lemma is identified, logged and stated.

### 2. Reusable tools for the next cases (a = 5 and up)

Gavin's aim is to learn what helps the other cases. The two-side bound is open for a >= 5: (5,6,7), (5,7,8), ...;
(5,5,6) is certified.

Read:
- `/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-twoside-a5-20261002/NOTES.md`;
- `/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-twoside-a5b-20261002/NOTES.md`, if present (a second
  attempt may still be running).

As time allows, formalize the general, reusable pieces:
- the strong-set shape lemma generalized: under no (j+1)-cap, a middle-determined set has at most j-2 cap-middle
  interior points;
- the layer lemma L1: in a 4-cap-free set, the points whose longest ending cup has j points form a cup with <= j
  points;
- the cup-extension moves (M1/M2) as standalone lemmas.

Do NOT commission narrowing for a >= 5 without a stated proof idea. If you see a proof idea for a = 5, write it in
PROGRESS.md before formalizing anything.

## Constraints
- `es job run` for anything over a minute; no self-chosen timeouts.
- `es log` every finding and every meaningful compiler failure.
- Write a mathematical handoff (`MATHEMATICAL-HANDOFF.md`) before the deadline.
- New statements only via `es node add`; one node per branch; no merge or push. The coordinator integrates pinned
  commits after review.
- Your sandbox cannot write `.git-data`: commit through the guarded es job path, as R17–R19 did.
- Keep memory caps modest: `es node add`/`es check` reserve 20G and two build slots are shared with R19.
- This worktree's build cache predates the R16–R18 integration, so expect a rebuild of changed modules on the first
  check.
