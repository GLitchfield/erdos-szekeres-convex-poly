# Mathematical handoff: exact older-exterior companion

## Outcome and trust status

The native target
`ErdosSzekeres.ctx_two_actual_marker_small_history_internal_chosen_kept_cut_six_bound`
is **not proved**. The preserved Lean scaffold compiles, but it contains exactly
two explicit `sorry` terms and therefore still depends on `sorryAx`. This run
produced no accepted theorem and the research window ended with
`accepted_results = 0`.

The terminal targeted check was job `20260929-010130-71d5cc`, exit code zero,
with detail artifact
`d8cc704edf7ffb3cf4ec5c97e849c84b18f29a0ec0ee0fc4874d79e3775b7418`.
This is only a receipt that the partial scaffold typechecks. The exact whole
declaration was captured as proof fixture
`82e1af28fe183aa37968dfd613a5cc9083f9809f978280a1c99a5da1fc6da54a`,
source hash
`abaa1c5473e79e36ffe2198f5e004fde43ca20aeb37bf65c1e3d6a1fc8fe3403`,
and unchanged type hash `afc74d2efdb0115f`.

The only tracked source change is
`ESBlueprint/B/CtxTwoActualMarkerSmallHistoryInternalChosenKeptCutSixBound.lean`.
It expands the former final admission into a checked recursive proof tree and
leaves the two narrow obligations below.

## Exact open obligations

### 1. Middle cut: incompatible endpoint values

At the first `sorry` (around line 3605), write
`C := B.part R s 2` and `D := B.part K t 3`. The surrounding checked proof has
already established:

- for every fuel and in full, `D <= 3`;
- in the outer geometry, `D <= 2` and `C <= 10`;
- in the inner geometry, `C <= 9`;
- all other positional branches of this cut are closed.

The exact missing statement is the following fuel-specific endpoint saving:

```text
outer geometry -> (boundFuel f C <= 9 or boundFuel g D <= 1)
or
inner geometry -> (boundFuel f C <= 8 or boundFuel g D <= 2).
```

Equivalently, exclude simultaneous endpoint pairs `(C,D) = (10,2)` in the
outer geometry and `(C,D) = (9,3)` in the inner geometry. Once supplied,
the checked `hCoupledEleven` immediately gives `boundFuel f C + boundFuel g D
<= 11`.

Do not try to prove either standalone `C <= 8` or outer `D <= 1`: both are
false in the diagnostic semantics described below.

### 2. Swapped extreme cut: mixed-capacity companion ten

At the second `sorry` (around line 4024), the own part
`B.part K s 4` is already bounded by one, so the exact goal is
`boundFuel g C <= 10` for `C := B.part R t 1`.

The checked context available at that point includes:

- actual `t`-markers `p` at level one and `q_0` at level two;
- actual `s`-markers `x,y` at the transported levels `N+2,M+2`;
- both globals at most five and exact chosen-axis marker occurrence transport;
- no younger actual `s` history;
- two nonempty arms of `R` around the convex block `K`, while all of `K` lies
  on one side of `q_0`;
- an active `s`-capacity-at-least-three witness `highS` and an active
  `s`-capacity-at-most-two witness `lowS`;
- the checked separation
  `(x<y and lowS<y and y<highS) or
   (y<x and highS<y and y<lowS)`;
- an active `t`-capacity-at-most-two witness `low`.

The all-active capacity-three cases on either axis already give `C <= 10`, and
the source cut is already closed when every active companion child has chosen
capacity at most two. The residual must use the simultaneous two-axis mixed
capacities and their spatial collision to save one unit.

## Compiling reductions preserved in the source

The following are local facts inside the sorry-bearing declaration. They have
no standalone theorem credit, but they passed guarded targeted checks:

- `hDThree`, `hDTwoOfOuter`, `hCNineOfInner`, and `hCTenOfOuter` establish the
  four middle envelopes above.
- `hCoupledEleven` is completely proved from the missing endpoint disjunction.
- The swapped branch transports all four actual markers and exact chosen
  occurrences into `C`.
- `ctx_extreme_cut_six_eleven_of_small_chosen_maxima_capacity_two` closes the
  all-chosen-low source cut; its negation supplies `highS`.
- `ctx_all_active_capacity_three_two_marker_triangle_bound` closes the
  all-active-high case on each axis; their negations supply `lowS` and `low`.
- `ctx_mixed_capacity_children_separated_by_older_marker_global_five` supplies
  the exact separation of `highS` and `lowS` by `y`.

The successful incremental check receipts were:

- `20260928-231828-9aa108`: inner `C <= 9`;
- `20260928-233417-5938d4`: outer `C <= 10`;
- `20260928-233908-0ad5cb`: middle coupling scaffold;
- `20260928-235354-93f09e`: all-active opposite-axis branch, artifact
  `ce1bcd3e...`;
- `20260929-000034-b2e63b`: explicit active opposite-low witness, artifact
  `39cd250...`;
- `20260929-000725-eaf104`: all-chosen-low source closure/high witness,
  artifact `bbf77acc3055695331e534dd67ecfecc9112f1573132da60d925a73676a6f56f`;
- `20260929-001258-00c926`: all-chosen-high companion closure/low witness,
  artifact `f4de47c02dce1ef52577654b242237b5ad85f68a9eec25b85f59bdbb5381e1d7`;
- `20260929-001824-22195d`: checked separation, artifact
  `b85c2dead33364a86be7a5e307a1d2a77a7282acb032d92fa56942e582cb02f7`.

The final check `20260929-010130-71d5cc` supersedes them for the terminal
source bytes.

## Diagnostic evidence and failed routes

All items in this section are exploratory Python-evaluator evidence with no
Lean-equivalence certificate and no theorem credit.

### Middle branch

- `probe-middle-k-left-length9.json` (job `20260928-222538-a1239f`) gives a
  companion word of exact bound nine, refuting a blanket improvement below
  nine in that configuration.
- `probe-middle-counterexample-companion.json` and
  `probe-middle-counterexample-source.json` reconstruct an outer example with
  the relevant companion endpoint and source bound eleven.
- `probe-middle-outer-d-two.json` (job `20260928-232458-892ca1`) finds an outer
  case with `D = 2`, refuting outer `D <= 1`.
- `probe-middle-tight-companion.json` records an inner tight sample with
  `(C,D) = (8,3)` and sum eleven.
- `probe-middle-coupled-length10.json` records a length-ten sample with sum ten.
- `sweep-middle-inner-rectangle-cover.json` gives minimum rectangle-cover cost
  nine while its exact witness has `C=7,D=1`; the proposed rectangle cover does
  not encode the needed endpoint incompatibility.
- The broad coupled sweep job `20260928-232553-087c2f` was canceled after
  485.4 seconds with exit `-15` and produced no artifact. It is inconclusive.

### Swapped branch

- `diagnose-middle-cuts-swapped.json` contains the representative tight
  companion of exact bound ten and source total eleven.
- `probe-swapped-k7-rectangles.json` (job `20260928-234524-8b8cb5`, 42.6 s,
  275 MiB) finds minimum rectangle-partition cost ten on either axis, but
  `all_chosen_intervals_thin=false`; therefore the thin-cover theorem cannot be
  applied.
- `probe-swapped-upper-capacity.json` (job `20260928-235907-eacb61`, 43.0 s,
  289 MiB) gives ordinary upper-axis capacity pruning charges `8+3=11` while
  the source bound is ten. The pair supports have sizes eight and six with
  intersection six, so a generic support-overlap estimate is far too weak.
- The representative maximizing cut uses a singleton block. Repeating the
  block-versus-singleton split may expose the missing reservation, but this is
  only a suggested classification, not a checked fact.

Final exact `es search` queries found no packaged theorem for the mixed-axis
companion-ten statement or the middle endpoint incompatibility. The broad
earlier exhaustive job `20260928-212806-cf524e` was canceled after about 99
minutes with no output and is likewise inconclusive.

## Code and artifact review

The bounded run-review artifact is
`f16b94b3710edd78232ee901698b98ab2ad8e5bd5fe5e28006f8fd722fc8a2f2`.
It reports 135 jobs, no pending or unknown jobs, and does not infer theorem
credit.

`diagnose_middle_cuts.py` was manually reviewed. It is a specialized
exploratory driver that reuses the registered context evaluator/primitives.
Its new modes and JSON outputs have explicit diagnostic semantics, but no Lean
equivalence or stable regression fixture. Promotion to `harness/research/` was
therefore deferred. No tracked workflow helper, generic library code, or
generated certificate module changed. The target Lean file and inline guarded
commands were also reviewed; the only trust gaps are the two visible admissions.
Because this was an explicitly Sol-only/no-delegation trial, independent Astra
review remains the coordinator's responsibility.

## Safest next work

Resume from one admission, not from the original outer branch. The most useful
new reusable theorem would expose a strict one-unit shared endpoint/collision
charge:

1. either prove the middle endpoint incompatibility under its exact outer/inner
   marker geometry; or
2. prove a two-axis mixed-capacity bound `C <= 10` using the separated
   `s`-high/low witnesses and the active `t`-low witness.

Avoid independent component bounds: the diagnostics show that they overpay by
exactly one. Any finite search must retain recursive cut legality and run
witnesses; witness compression is still unproved.

The active claim belongs to coordinator
`codex:01a0e90e-755d-75d0-a9d8-15eadb32fd28` and was intentionally not
released or impersonated by this researcher. Nothing was committed, pushed,
published, or marked closed.
