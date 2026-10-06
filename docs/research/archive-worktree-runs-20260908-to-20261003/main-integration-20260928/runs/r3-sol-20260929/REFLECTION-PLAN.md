# Reflection proof plan (not a proof receipt)

Exact target to register, unchanged:

```lean
theorem ctx_bound_reverse (σ : Ctx.Context) (hwf : σ.WellFormed) :
    ({ σ with word := σ.word.reverse } : Ctx.Context).bound = σ.bound
```

Search `reversing context word preserves bound` and `ctx_bound_reverse` found no duplicate.
Search `ctx_reverse_extension_transport` found the closed node in
`ESBlueprint/B/CtxReverseExtensionTransport.lean`, type hash `4d6c2aaed124fffe`,
standard axioms only. It supplies reversed well-formedness and all extension/capacity
transport. Reuse it rather than reprove `sideAt` and the greedy folds under reflection.

Develop local facts within one scratch example/theorem, with no admissions:

1. `reverse` is involutive. On valid positions `flip p = word.length-1-p` is an
   involution and reversed `letterAt (flip p)` is original `letterAt p`.
2. Use the existing reverse-range identity to get
   `reverse.childPositions = childPositions.reverse.map flip`; lengths agree.
3. At most one run implies convex child positions. Reuse the checked local predecessor
   argument in `CtxBoundAdditiveSingleRunBoundary` / run-group-pruning proofs.
   Convexity transports by `flip`, and convex child positions imply at most one run
   because every start equals the least child. Empty children are separate.
4. On a convex child interval, each external letter is wholly outside the interval.
   Therefore every external-position filter at two child endpoints agrees. Fold
   induction gives equal left/right extension counts and point capacities within that
   interval. This supplies the requested single-run constant-limit lemma.
5. Compare original and reversed first-child bases with the capacity transport theorem
   and constant point capacities. Do not assert base equality for arbitrary multirun words.
6. A proper nonempty block is an infix of child positions. Reverse and map the infix,
   then reconstruct membership in `blocks` from its prefix/block/suffix witness.
7. For bounded keep positions, `part` commutes with reversal and reflected keep;
   the complement filter transports too. Prove word equality using reverse-range/map
   and pointwise letter transport. Maxima and parameters agree by construction.
8. Induct on fuel, uniformly over well-formed contexts, proving the bound inequality
   into the reflected context. Use `WellFormed.part` with both admissible coupled maxima.
   Transport each cut to a reflected cut and apply the fuel induction to its parts.
9. Reflect again for the opposite inequality; child count equality supplies full-bound equality.

All compilation must be guarded jobs with a 4 GiB cap for scratch work. Registration
and targeted check use 20 GiB guarded admission. No full extraction, root theorem
weakening, unrelated statement edits, merging, pushing, or delegation.

This plan is reusable evidence for a handoff, not accepted theorem credit.
