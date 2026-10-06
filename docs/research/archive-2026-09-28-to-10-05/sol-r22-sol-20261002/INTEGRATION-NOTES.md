# Coordinator input instantiation

2026-10-03T05:14Z. Source-level interface review only. No integration
build was run in this fixed-baseline worktree.

Read-only source recheck:

- R20 `diagonalCupBlocksForce4kk_of_five_le` has implicit `{k : ℕ}` and
  explicit `(hk : 5 ≤ k)` (integration source line11).
- R21 `card_le_choose_of_oneChange_no_capFour_no_strong` has implicit
  `{n k : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}` followed by
  `3 ≤ k`, one-change, no four-cap and no strong k-set (line2449).

After their accepted proof modules and the R22 chain are integrated,
the following proof-body expression instantiates the accepted diagonal
lower gate in an existing context `hk : 6 ≤ k`:

```lean
exact singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs
  (fun k hk ↦ diagonalCupBlocksForce4kk_of_five_le (k := k) hk)
  card_le_choose_of_oneChange_no_capFour_no_strong hk
```

This expression is an integration sketch, not a new registered theorem
or a compiled receipt. Its lambda makes R20's implicit k into the gate's
explicit universal k; R21's entire statement shape already matches.
The upper diagonal gate will take the same two inputs because they are
uniform over every colouring. Neither input needs a separate dual proof.

The lower predecessor gate is unconditional. The conditional lower
diagonal gate is accepted with its exact original-source receipt and
standard axioms; it does not claim the external inputs are proved on
baseline6e4d0e66. Preserve this boundary when reporting the result.

Safest next consumer action: review the accepted R22 proof receipts and
dependency chain, integrate through the coordinator's authorized workflow,
then compile the actual input instantiation on that integrated baseline.
No merge, push, reset or cherry-pick was performed in R22.
