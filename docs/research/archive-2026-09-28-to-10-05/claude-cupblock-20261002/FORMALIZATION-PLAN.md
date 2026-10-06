# Formalization plan: uniform two-cup-block lemma (draft for an R20 brief)

**Target.** One theorem closing the existing contract (Lean names as on main):

    theorem diagonalCupBlocksForce4kk_of_five_le {k : ℕ} (hk : 5 ≤ k) : DiagonalCupBlocksForce4kk k

`DiagonalCupBlocksForce4kk` is defined in `StructuralChargingPascalCupBlocks.lean`. Register the theorem with
`es node add`, kind formalization.

**Payoff.** Combined with `singletonLowerPascalTailGate_four_diagonal_of_cupBlocks`, it gives
`SingletonLowerPascalTailGate 4 k k` for every k >= 5. That replaces the k <= 8 theorems and the k = 9 CNF
certificate.

**Paper proof.** `NOTES.md` in this directory, verified by the coordinator.

## Structure

1. **Strengthened statement, by induction on k >= 5.** Call it `TwoCupBlockBound k`.

       left | right ordered, IsCupSet left, IsCupSet right, OneChangeOn (left ∪ right),
       ¬ContainsCapSet (left ∪ right) 4, ¬ContainsStrongPolygonSet (left ∪ right) k
         → left.card + right.card ≤ 2k - 4

   `DiagonalCupBlocksForce4kk k` follows by cardinality, the converse of `diagonal_cup_block_card_add_le`.

2. **Base k = 5.**
   - Reduce to (4,3) and (3,4) sub-blocks: the existing `cupBlocks34Force455` already covers sizes (3,4)/(4,3).
   - So the base case is `diagonalCupBlocksForce4kk_five` plus the counting step. No new geometry is needed.

3. **Signotope helpers** (new; general, reusable):
   - (H1) Consecutive-triple chain lemma. If a finite set's consecutive triples (in sorted order) are cups and
     OneChangeOn holds, it is a cup set. Same for caps.
     - Search first: `es search "consecutive triples cup set one change"`.
     - `isCupSet_insert_two_of_extreme_cup_extensions` is a special case.
   - (H2) Strong-set shape under no 4-cap. Use `isStrongPolygonSet_iff_isMiddleDeterminedOn`.
     - In a middle-determined set S with no 4-cap, at most one interior point has cap colour (two would give a
       4-cap l,x,x',r).
     - Every other interior point has cup colour. So S = cup C plus at most one apex x.
   - (H3) Converse of H2. A cup C from l to r plus x (l < x < r, x ∉ C) with (l,x,r) a cap is middle-determined,
     given OneChangeOn. The check is mixed triples via the one-change law.

4. **Claim D (core).** Let p2 be the second element of left and q be the second-to-last element of right, when
   they exist. If S ⊆ U is strong, p2 ∉ S, q ∉ S and 5 <= |S|, then some strong S' ⊆ U has |S'| = |S| + 1.
   Cases, as in NOTES.md:
   - A: S is a cup. If it has >= 3 left points, insert p2 (H1: the new consecutive triples lie in `left`).
     Mirror for right.
   - B: S is a cup plus an apex.
     - c >= 2 with s1 >= p3: prepend p1, p2.
     - c >= 3: insert p2 (H3 keeps the apex).
     - Mirror cases for right.
     - The residual case {p1, s, t, q_b} + apex uses the no-4-cap condition at (p2, s, t, q).

5. **Induction step.** If no strong (k-1)-set exists, apply the induction hypothesis directly. Otherwise
   maxconv = k-1 >= 5, and Claim D shows U \ {p2, q} has no strong (k-1)-set. Then apply the induction
   hypothesis to (left \ {p2}) | (right \ {q}): subsets of cups are cups, and OneChangeOn and no-4-cap are
   monotone.

## Estimate and risks

- About 800–1500 lines. Most of the work is Finset order bookkeeping for "second element" and the case split.
- Keep the helpers general: H1–H3 are useful beyond this lemma.
- No certificates and no `native_decide`.
