# Code inventory

## Tracked mathematical code

- `ESBlueprint/B/CtxTwoActualMarkerOppositeBoundaryCompanionNineBound.lean`
  — new theorem module, created only through `es node add`, proof edited with
  `apply_patch`.  Reuses the checked triangular-linear two-marker potential
  and part-history transport lemmas; no new axiom, `native_decide`, or `sorry`.
- `ESBlueprint.lean` and `harness/statements.lock` — generated registration
  changes from `es node add`.

## Research artifacts

- `probe_companion_group_charges.py` — small diagnostic derived from the prior
  reviewed overlap probe.  Reuses catalogued APIs
  `research.recursive-bounds`, `research.context-extension`, and
  `decomposable.context-enumeration`; explicit semantics are
  `context-bound-zero-children-v1`.  It has no proof credit and awaits its
  first run/review.
- `checkpoint.md`, `mathematical-analysis.md`, `code-inventory.md` — handoff
  and review records.

No reusable workflow helper was added.  The new diagnostic is intentionally
kept run-local until its mathematical utility is established.
