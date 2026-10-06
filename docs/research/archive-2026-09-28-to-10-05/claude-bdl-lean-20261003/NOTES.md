# BDL implies Theorem 8 (decomposable): Lean scratch, 2026-10-03

Status: `BdlScratch.lean` compiles against main daf3e6a6 (job 20261003-222711-a295f2,
log `compile1.log`, rc=0, no errors or warnings). Both theorems depend only on
`[propext, Classical.choice, Quot.sound]`. This is a scratch file, not a registered node.

## Final statement

    theorem decomposableStateUpper_all_of_bands
      (hBDL : ∀ {n k α β : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)},
        IsDecomposableOn χ s → ¬ContainsStrongPolygonSet χ s k →
        ¬ContainsCupSet χ s (α + 1) → ¬ContainsCapSet χ s (β + 1) → k ≤ α + β →
        ∃ b : Fin n → ℕ, (∀ x ∈ s, k - 1 - β ≤ b x ∧ b x ≤ α - 1) ∧
          ∀ j, j < k →
            ¬ContainsCupSet χ (s.filter (fun x => b x = j)) (j + 2) ∧
            ¬ContainsCapSet χ (s.filter (fun x => b x = j)) (k - j))
      (a u k : ℕ) (ha : 1 ≤ a) (hu : 1 ≤ u) (hak : a ≤ k) (huk : u ≤ k) :
      DecomposableStateUpper a u k

## Hypothesis change: `∀ j` became `∀ j, j < k →`

With the band conditions required for every `j`, the hypothesis is false. At `j = k`
we get `k - j = 0`, and every set contains a 0-cap (the empty set). So that version
proves `False`, and the theorem would hold vacuously. `bdl_unguarded_refutable` proves
this in Lean using one point, `k = 2`, `α = β = 1`, `j = 2`.

The guarded version follows from BDL:
- If `j` lies outside the band range, the band `X_j` is empty. An empty set has no
  `(j+2)`-cup, and no `(k-j)`-cap because `k - j ≥ 1`.
- If `j` lies inside the range and `j < k`, the natural-number subtraction `k - j`
  equals the integer `k - j`.

A related integer edge case: BDL with upper bounds `α ≥ k+1` is false if read literally,
because the empty band `j = k` would need `cap ≤ -1`. The fix is to derive it from
exact BDL, where `α' = cup(S) ≤ k-1` and `β' = cap(S) ≤ k-1`:
- If `α' + β' ≥ k`, the bands `[k-1-β', α'-1]` lie inside `[k-1-β, α-1]`.
- If `α' + β' < k`, a single band `j` works for any `j` in the nonempty intersection of
  `[α'-1, k-1-β']` and `[k-1-β, α-1]`.

Natural-number truncation in the range bounds `k-1-β` and `α-1` only weakens the
conclusion, so it is harmless. An equivalent alternative is to state the conditions
only for occupied bands (`∀ x ∈ s`, with `j = b x`).

## Proof

- **`a = 1` or `u = 1`:** use `containsCapSet_one` or `containsCupSet_one` on
  `hdec.nonempty`.
- **Classic regime (`a + u ≤ k + 3`):** apply `card_le_choose_of_oneChange_no_cap_no_cup`
  with `c = a`, `v = u`. `OneChangeOn` comes from `IsDecomposableOn.turnSequenceAllowed`.
- **Window regime (`k + 4 ≤ a + u`):**
  1. Apply hBDL with `α = u-1`, `β = a-1`. Then `b` maps `s` into `Icc (k-a) (u-2)`.
  2. Split the cardinality with `Finset.card_eq_sum_card_fiberwise`.
  3. Bound each band `j` with the classical bound at `c = k-j ≥ 2` (this uses `u ≤ k`)
     and `v = j+2`. Then `c+v-4 = k-2`, and `C(k-2, k-2-j) = C(k-2, j)` by
     `Nat.choose_symm`.
  4. Apply `Finset.sum_le_sum` and `omega`.
- `hak : a ≤ k` is not needed mathematically. `huk` is needed: it ensures every band used
  has `j ≤ k-2`.

## Mathematical content

Once BDL is given, the reduction is routine. The whole difficulty of Theorem 8 for
decomposable sets is BDL itself: the band partition with the cup/cap trade-off
`cup(X_j) ≤ j+1`, `cap(X_j) ≤ k-1-j`. This file does not address BDL.
