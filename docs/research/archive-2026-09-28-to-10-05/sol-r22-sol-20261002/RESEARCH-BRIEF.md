# R22: formalize the decomposable (5,k-1,k) Pascal-tail gate (one Sol trial, gpt-6.1-sol)

**Approval and roles.** Approved by Gavin on 2026-10-02:
- "I approve all", for formalizing the audited (5,k-1,k) proof;
- "yes, yes, and yes, all items approved", for running it in R21's worktree and adding the audited (5,k,k) gate as
  priority 2.
- Coordinator: `claude-code:f3e0818a-9388-430b-9c32-aeb7dc5d297b (resumed from 22c8132f)` (Claude).
- Callbacks are not verified, so never wait for replies; keep `PROGRESS.md` here current.
- This is one trial. Never reset the host deadline.

**Worktree.** `runs/worktrees/sol-12h-20261002` (R21's, which has a warm build cache), on a new branch
`research/r22-gate5-20261002` from main `6e4d0e66`. R21's branches in this worktree must be preserved.

**In parallel.** R19 ends at 00:25Z (`runs/worktrees/sol-12h-20260916`); do not touch it. During the night the
coordinator integrates R19/R20/R21 into main. Keep your baseline at `6e4d0e66` regardless.

## Mathematics

`AUDITED-PROOF-5k1k.md` (this directory) is a self-contained, independently audited paper proof. The coordinator has
read all its lemmas and cases. No step rests on computation.

**Theorem.** Let k >= 6, and let U be decomposable with sides L|R split at a gap. Suppose:
- each side has no 4-cap;
- U has no 5-cap, no (k-1)-cup and no strong k-set.

Then |U| <= C(k-1,2) + C(k-3,2).

**Lean target** (register via `es node add`, kind formalization):

    theorem singletonLowerPascalTailGate_five_pred_of_six_le {k : ℕ} (hk : 6 ≤ k) :
      SingletonLowerPascalTailGate 5 (k - 1) k

`SingletonLowerPascalTailGate` is in `ErdosSzekeres/StructuralChargingPascalTails.lean`.
- Its reservoir equals H + 1: lowerPascalTailReservoir 5 (k-1) k = T(5,k-1,k) + 1 - C(k-3,3), and
  T(5,k-1,k) - C(k-3,3) = C(k-1,2) + C(k-3,2). Prove this arithmetic first.
- The gate's singleton q, deep below `upper`, is the gap marker. The side conditions (H1)-(H2) follow from the gate's
  no-5-cap hypothesis via `containsCapSet_succ_of_lower_endpoint`, as in the existing (4,8,8) proof.

**Proof structure** (sections of `AUDITED-PROOF-5k1k.md`).

Facts already available in `ErdosSzekeres/Decomposable.lean`:
- the root split (`exists_split`, `HasDeepBelowSplit`);
- the cup/cap gain lemma (C) (`insert_upper_isCupSet_of_*`, `containsCupSet_succ_of_upper_endpoint`);
- the coupling (P) (`containsStrongPolygonSet_of_cup_cap`);
- signotope-ness (`turnSequenceAllowed`).

Lemmas:
- **Lemma 1**, layered Erdős–Szekeres for 4-cap-free sets. Only the count C(v,2) is needed, except in Lemma 6,
  which needs the row structure. The count is available via `containsCapSet_or_containsCupSet_of_choose_lt` and
  `IsDecomposable.isSweepRealizable`. For general OneChange sets, prove the layer lemma directly (it is short).
- **Lemma 2:** Z bound (v-1)^2.
- **Lemma 3:** two cups, at most 2u-3.
- **Lemma 4:** three cups, at most 3u-6.
- **Lemma 5:** marker lemma (WE plus bound).
- **Lemma 6:** R2 for u=k-1 (Lemma C). Its rows and cells are the most intricate part.

Case analysis: 11 cases (NN1-3, BN by reflection, N1a/b, N2a-e, one-sided).
- Reflection (reversing the x-order) is needed; check whether the project has a reversal/mirror lemma for
  colourings and decomposability. `es search` first.
- If not, avoid reflection by proving the mirror cases directly.

**Reuse.** R20 closed a local cup-plus-apex/middle-determined toolkit on branch
`node/DiagonalCupBlocksForce4kkOfFiveLe` (c89df0e8); it is not on main. Its H1-H3 helpers are relevant, but you may
NOT cherry-pick it. Re-prove whatever you need locally, or reference it only after integration.

## Priorities
1. **The (5,k-1,k) gate above:** closed with an original-source receipt (standard axioms, no sorry, no
   certificates, no `native_decide`).
2. **The (5,k,k) gate.** Use the audited proof `AUDITED-PROOF-5kk.md` in this directory (an independent audit,
   COMPLETE-WITH-REPAIRS).
   - It reuses Lemmas 1-6 above. It adds:
     - Theorem A: it applies the (5,k-1,k) theorem at the same k, so priority 1 feeds it;
     - R1-dec: three decomposable cups, at most 3k-8;
     - R2-dec: decomposable cup | 4-cap-free side, at most T(4,k,k)+k-4;
     - Z';
     - Lemma B: cup + cap with common endpoints is strong.
   - It also needs two results that are closed in Lean but NOT on your baseline:
     - the uniform two-cup-block lemma `diagonalCupBlocksForce4kk_of_five_le` (R20, branch
       `node/DiagonalCupBlocksForce4kkOfFiveLe`, `c89df0e8`);
     - Baek's single-set bound `card_le_choose_of_oneChange_no_capFour_no_strong` (R21, `adf3b2f1`, source
       `ESBlueprint/C/CardLeChooseOfOneChangeNoCapFourNoStrong.lean` on branch `node/...` in this worktree's history).

     For the exact statements, read their sources (read-only) in the integration worktree:
     - `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/integration-r20-20261002/ESBlueprint/B/DiagonalCupBlocksForce4kkOfFiveLe.lean`;
     - `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/integration-r20-20261002/ESBlueprint/C/CardLeChooseOfOneChangeNoCapFourNoStrong.lean`.

     State the (5,k,k) gate with those two results as EXPLICIT HYPOTHESES (copy their exact statement shapes), so it
     closes on baseline `6e4d0e66`; the coordinator instantiates it after integration. Do not cherry-pick them.
   - Target:

         theorem singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs
           (hblocks : ∀ k, 5 ≤ k → DiagonalCupBlocksForce4kk k)
           (hbaek : <exact statement of card_le_choose_of_oneChange_no_capFour_no_strong>)
           {k : ℕ} (hk : 6 ≤ k) : SingletonLowerPascalTailGate 5 k k
3. **If time allows:** the colour-dual upper gates via `singletonUpperPascalTailGate_iff_lower_dual`.

## Constraints
- Each lemma may be its own node, if that helps parallel checking (one node per branch).
- `es job run` for anything over a minute; no self-chosen timeouts.
- `es log` every finding and every meaningful compiler failure.
- New statements only via `es node add`; no merge or push.
- Commit through the guarded es job path.
- Write `MATHEMATICAL-HANDOFF.md` before the deadline.
