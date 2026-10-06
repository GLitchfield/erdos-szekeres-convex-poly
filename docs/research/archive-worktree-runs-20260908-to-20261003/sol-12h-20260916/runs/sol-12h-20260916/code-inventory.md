# Code inventory

## Reused

- Existing exported Lean theorems named in `checkpoint.md`.
- Repository `es` claim, search, job, proof, check, extraction, and finalization workflows.
- Catalogued `decomposable.context-enumeration` and `research.recursive-bounds` implementations via
  `scripts/decomposable_additivity_test.py`, with Lean-aligned zero-child semantics, for the bounded
  diagnostic recorded as job `20260916-233503-c02de0`.

## Introduced

- One run-local diagnostic, `probe_two_marker_overlap.py`. It composes the catalogued context
  enumeration, context-limit, and recursive-bound APIs; it adds only filtering, explicit pure
  extension reconstruction, canonical low/high pair-set accounting for the exact residual, and a
  bounded `--s-max` option.
- Run-local ledger files and diagnostic JSON outputs, including
  `additivity-5-5-6-two-level-s4-lean.json` and `two-marker-overlap-final-s4-lean.json`.

## Deferred

- The filtered probe is deliberately not promoted: it is one-off mathematics tied to this exact
  residual, carries no equivalence certificate to Lean, and does not justify a generic workflow API.
- The five-child extension job `20260917-000224-ed58a0` was cancelled before consolidation and
  left an empty output placeholder; no conclusion is drawn from it.
