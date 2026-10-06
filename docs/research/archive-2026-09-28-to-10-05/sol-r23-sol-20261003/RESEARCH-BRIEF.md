# R23: formalize the decomposable (6,k-2,k) Pascal-tail gate (one Sol trial, gpt-6.1-sol)

**Approval and roles.**
- Approved by Gavin on 2026-10-02 ("okay, approve those items", on the proposal: "R23 — formalize the audited
  (6,k-2,k) gate, in R22's worktree once R22 ends").
- Coordinator: `claude-code:f3e0818a-9388-430b-9c32-aeb7dc5d297b` (Claude).
- Callbacks are not verified, so never wait for replies. Keep `PROGRESS.md` here current.
- This is one trial. Never reset the host deadline.

**Worktree.** `runs/worktrees/sol-12h-20261002` (R21's and R22's, with a warm build cache), on a new branch
`research/r23-gate6-20261003` from main `6ae26b5d`. Preserve R21's and R22's branches in this worktree.
- `6ae26b5d` is main after the coordinator integrates R22; the coordinator fills it in at launch.
- Two build slots are shared; keep memory caps modest. Checks of modules that import the Pascal-tail closure need
  about 28G (R21 used `es check --force` at 28G, ~17 min).

## Mathematics

`AUDITED-PROOF-6k2k.md` (this directory) is a self-contained, independently audited paper proof (verdict
COMPLETE-WITH-REPAIRS; every repair is already folded into the text). No step rests on computation, and nothing
external is cited: no Baek, no cup-block lemma, no a=5 gate.

**Theorem (§0).** Let k >= 7, and let U be decomposable, split at a gap into U = L|R (either side may be empty).
Suppose:
- (H1) L and R have no 5-cap;
- (H2) U has no 6-cap;
- (H3) U has no (k-2)-cup;
- (H4) U has no strong k-set.

Then |U| <= C(k-1,3) + C(k-3,3).

**Lean target** (register via `es node add`, kind formalization):

    theorem singletonLowerPascalTailGate_six_pred_pred_of_seven_le {k : ℕ} (hk : 7 ≤ k) :
      SingletonLowerPascalTailGate 6 (k - 2) k

- The reservoir identity is in §0.1: lowerPascalTailReservoir 6 (k-2) k - 1 = C(k-1,3) + C(k-3,3). T(6,k-2,k) is in
  the window regime with no truncation for k >= 7; T(5,k-2,k) is classic. Prove this arithmetic first.
- §0.2 is the gate reduction. The singleton q deep below `upper` is the gap. (H1) follows from the gate's no-6-cap
  hypothesis, because a crossing triple is a cup iff its middle point is q. R22 did the same reduction at a=5;
  reuse its code.

**Proof structure.** The dependency order (§7) has no induction on |U|:
1. Basic facts (M), (F0), (F1), (C), (P). Several exist in Lean:
   - `IsDecomposableOn.turnSequenceAllowed` = (F0);
   - `HasDeepBelowSplit.containsStrongPolygonSet_of_cup_cap` = (P);
   - the cup/cap gain lemmas in `ErdosSzekeres/Decomposable.lean`.
2. Z-lemmas, valid in every signotope:
   - Lemma 1 (Erdős–Szekeres);
   - Lemma 2 (classic5);
   - Lemma 3 (Z6);
   - Lemma 4 (ZR);
   - Lemma 5 (Θ and Θ_cup);
   - Lemma 6 (L3 and L3_cup).

   Each is an iterated "first points of caps" peel. Factor out ONE generic peel lemma first: the first points of
   j-caps of a j'cf set form a set with smaller cap number, and the rest is (j-1)cf. Then derive Lemmas 2–6 from it.
3. Marker lemmas: Lemma 7 (the abstract straddle core), then Lemmas 8 (Marker6) and 9 (Lemma M).
4. Lemma 10 (R₃) and Lemma 11 (R2-6 at u=k-2).
5. The Theorem: the 13-row root-split case analysis (§5, tables §6).

**Reuse (search first; do not re-prove what is on main).**
- R22's toolkit, integrated into main at `6ae26b5d` (modules under `ESBlueprint/B/`; `es search` for exact signatures):
  - `isMonochromaticSet_of_oneChange_consecutive`: consecutive-triple chains are monochromatic sets;
  - `monochromaticSet_insert_min_of_oneChange` / `monochromaticSet_insert_max_of_oneChange`;
  - `exists_cupStartLayers_of_oneChange_no_capFour` and `card_le_choose_of_oneChange_no_capFour_no_cup`: cup-start
    layers and the triangular C(v,2) bound for 4-cap-free sets. Your generic peel lemma generalizes these to
    j-cap-free sets;
  - `card_le_square_of_oneChange_gap_no_capFive_no_cup`: the square bound across a cap-free gap (template Lemma 2);
  - `twoCupBlocks_card_and_extensions_of_oneChange_no_capFour_no_cup`,
    `threeCupBlocks_card_le_of_oneChange_no_capFour_no_cup`;
  - `isCupSet_iff_not_containsCapSet_three`, `isStrongPolygonSet_union_of_cup_cap_common_extremes`;
  - `markerCupEndpoints_no_capThree_on_one_side`, `card_le_mul_of_oneChange_gap_no_capFive_straddled_cups`: the a=5
    marker lemma, the template for Lemma 7 and Marker6;
  - `deepSplit_two_endpoint_extensions`: simultaneous cup and cap endpoint gains at a deep split, i.e. (C);
  - `reverseColor_set_invariants`: order reversal, for the "by reflection" rows;
  - `card_le_two_choose_of_oneChange_gap_deepSplit_no_capFive_no_cup_no_strong` and
    `singletonLowerPascalTailGate_five_pred_of_six_le`: the a=5 root bound and its gate wrapper. They are the
    templates for the a=6 root case analysis and for the §0.2 wrapper.
- `IsDecomposableOn.subset` (`ErdosSzekeres/Decomposable.lean`): nonempty subsets of decomposable sets are
  decomposable.
- Reflection (reversing the x-order) appears in N-rows "by reflection". Check what R22 used; if there is no
  reversal lemma for colourings and decomposability, prove the mirror cases directly.
- The new assembly `decomposableStateUpper_of_lower_gates_at` (main, `1d689375`) consumes exactly this gate. With
  it, (6,5,7) becomes a k=7 input.

## Priorities
1. **The (6,k-2,k) gate above**, closed with an original-source receipt: standard axioms, no sorry, no
   certificates, no `native_decide`.
   - If the full gate does not close, close the lemma layer as separate nodes (generic peel, Z6, ZR, Θ/Θ_cup,
     L3/L3_cup, Lemma 7, Marker6, Lemma M). Then log the exact remaining rows.
2. **The colour-dual upper gate** via `singletonUpperPascalTailGate_iff_lower_dual`, if cheap.

## Constraints
- Each lemma may be its own node (one node per branch), if that helps parallel checking.
- `es job run` for anything over a minute; no self-chosen timeouts.
- `es log` every finding and every meaningful compiler failure.
- New statements only via `es node add`. No merge or push.
- Commit through the guarded es job path.
- Write `MATHEMATICAL-HANDOFF.md` before the deadline.
