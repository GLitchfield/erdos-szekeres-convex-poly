# R20 (draft, needs Gavin's approval): formalize the uniform two-cup-block lemma

**Roles.** Coordinator `claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f`. One Sol trial (gpt-6.1-sol, xhigh).
Starts after R19's deadline. Never reset the host deadline.

**Target node** (register with `es node add`, kind formalization; one node per branch, based on main):

    theorem diagonalCupBlocksForce4kk_of_five_le {k : ℕ} (hk : 5 ≤ k) : DiagonalCupBlocksForce4kk k

`DiagonalCupBlocksForce4kk` is defined in `ErdosSzekeres/StructuralChargingPascalCupBlocks.lean`.

**Corollary** (a second node, or the same module if the harness allows):
`SingletonLowerPascalTailGate 4 k k` for all k >= 5, through `singletonLowerPascalTailGate_four_diagonal_of_cupBlocks`.

**Mathematics.** `runs/claude-cupblock-20261002/NOTES.md` is a hand proof, verified by the coordinator, with replay
scripts. `FORMALIZATION-PLAN.md` in the same directory gives the Lean structure:
- the strengthened statement, a card bound, proved by induction on k;
- the base case from `diagonalCupBlocksForce4kk_five` and `diagonal_cup_block_card_add_le`;
- helpers H1–H3:
  - H1: consecutive-triple cups are cup sets under OneChangeOn;
  - H2: with no 4-cap, a strong set is a cup plus at most one apex, via `isStrongPolygonSet_iff_isMiddleDeterminedOn`;
  - H3: the converse of H2;
- Claim D, which is the core;
- the induction step.

**Rules.**
- Run `es search` before each helper.
- Keep H1–H3 general (OneChangeOn colorings), since they are reusable.
- No certificates, no `native_decide`, no axioms.
- `es log` every meaningful compiler failure and every finding.
- No merge or push. The coordinator integrates pinned commits after review.
- Keep memory caps modest; `es check` reserves 20G and there are two build slots.

**Done.** The theorem is closed with a receipt, or the precise blocking lemma is identified (with its failure mode)
and logged.

**Second priority** (only if the first closes early): read `runs/claude-twoside-a5-20261002/NOTES.md` and
`runs/claude-twoside-a5b-20261002/NOTES.md`. Formalize any proved a=5 lemmas (L1 layer lemma, L3 cup-killing) as
reusable helpers. Do not commission narrowing on a=5 without a stated proof idea.
