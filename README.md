# Erdős--Szekeres convex-polygon formal research

This project attacks the exact Erdős--Szekeres happy-ending conjecture. Its
standard of completion is intentionally strict: a mathematical result counts
as complete only when the exact statement has a compiling Lean 4 proof.

For every `n ≥ 3`, let `ES(n)` be the least number such that every set of
`ES(n)` planar points in general position contains `n` points in convex
position. The target is

```text
ES(n) = 2^(n - 2) + 1.
```

The repository does not assume this conjecture. Stronger, relaxed, and abstract
variants are supporting material only when they advance this exact target. The
first strategic task is to choose the canonical formal model and the first
attack milestone without losing the connection to realizable planar point
sets.

## Current state

- Lean 4 and mathlib are pinned at `v4.29.1`.
- `ErdosSzekeres/Basic.lean` defines orientation, planar general position,
  convex position via convex hull, the forcing predicate, and the classical
  conjecture as an unproved proposition.
- `ErdosSzekeres/Sweep.lean` formalizes the sweep ordering, ordered triple
  coloring, cups/caps, and the bridge from left/right turns to slope changes.
- `ErdosSzekeres/Presentation.lean` constructs a generic determinant-one shear
  and sorted sweep presentation for every finite general-position point set.
- `ErdosSzekeres/Convexity.lean` proves the orientation-sign triangle test and
  a purely sign-based convexity certificate for four points.
- `docs/formalization_plan.md` records the intermediary lemma ladder from the
  sweep model to the exact conjecture.
- `docs/literature_review.md` records the initial research synthesis.
- `docs/bibliography.md` is the living source ledger.
- `docs/wayfinder/tickets/0001-choose-formal-model.md` is the first open
  strategic decision.

## Build

```console
lake update
lake build
make test
python3 scripts/wayfinder_status.py
```

No theorem containing `sorry` or `admit` is accepted by the test gate.

## Layout

```text
ErdosSzekeres/              Lean source
docs/formalization_plan.md intermediary lemma ladder and proof boundaries
docs/literature_review.md  research synthesis and candidate directions
docs/bibliography.md       primary-source ledger
docs/wayfinder/            durable strategic map and tickets
docs/experiments/          designed computational experiments
data/reference/            metadata for authenticated external inputs
data/derived/              compact certificates and verified results
runs/                      ignored machine-local work
```

This repository was initialized from `open-math-research-template` and is MIT
licensed; see `LICENSE` and `NOTICE`.
