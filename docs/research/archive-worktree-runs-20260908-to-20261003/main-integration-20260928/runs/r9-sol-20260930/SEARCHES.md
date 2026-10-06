# R9 searches

All searches use the primary es launcher with this worktree as `--root`.

- `alternating single run contraction deletion childPositions range isolated part`:
  only the registered R9 reduction node.
- `child positions contiguous interval one run`: no indexed results.
- `context word external letters deletion preserves WellFormed`: no indexed results.
- `alternating parity list paint contraction separator isolated children`: no indexed results.

Source search found R6's local glue in
`ESBlueprint/B/CtxBoundAdditiveSingleRunOfRunContractionAndAlternating.lean`:
context equality, one-run interval reconstruction, preservation of WellFormed,
child-block position and base transport, Boolean painting and parity/complement
bookkeeping. R9 reuses those local proofs within the fixed theorem body.

Library searches: `guarded Lean scratch compile proof` returned
`workflow.proof` and `workflow.jobs`; both API contracts were read.
