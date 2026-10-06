# Sol/xhigh research report

## Outcome

Window `window-c8d65fe03ead46dd` ran under agent
`codex:agent-run-0ce68047e38845f0`, with baseline `8ae570bb` and frozen deadline
`2026-09-16T02:41:07Z`. It closed `complete` at `02:41:31Z` with 24 accepted results.

This window produced 24 locally reviewed, compiling Lean theorems on the single claimed parent
`ctx_bound_additive_sandwich_one_singleton_end`. The authoritative frontier moved from 227 closed,
12 open, one refuted to 251 closed, 12 open, one refuted after the parent claim was released
partial. The parent remains open: this run did not claim a proof of sandwich additivity or of the
Erdős–Szekeres conjecture.

The mathematical path first closed every exact two-marker endpoint cut at `k = 6`, then classified
internal complement cuts. Lower opposite widths, younger surrounds, between-marker intervals, and
older-exterior intervals are closed. At saturated opposite global five, the surviving internal-cut
geometry is now explicit:

- an opposite kept interval surrounds the older marker, with complement maximum `m = 2` or `m = 3`;
- or the kept interval lies exterior to the younger marker, away from the older marker.

The last classifier is
`ctx_two_marker_internal_complement_cut_six_top_width_middle_residual_classification`.

## Reviewed commits

1. `29f32cfc` — Sharpen the six-point older-exterior cut
2. `89d40558` — Normalize large sibling maxima to width three
3. `10118339` — Sharpen the six-point older-exterior endpoint
4. `0bcc5b13` — Sharpen the six-point younger-exterior endpoint
5. `94a2d319` — Classify the six-point endpoint obstruction
6. `8b238564` — Extract nested boundary marker rank budget
7. `50e2da14` — Bound an older-surrounded endpoint complement
8. `8fea7aa5` — Sharpen the older-surrounding endpoint at six
9. `90d64159` — Extract retained-boundary doubled rank budget
10. `a4aeddab` — Extract three-marker exterior unit bound
11. `245d1155` — Bound a younger-surrounded endpoint complement
12. `ef6ebc81` — Close the younger-only endpoint cut at ten
13. `b1fde93c` — Close every two-marker endpoint cut at six
14. `0edb4ffd` — Close low-width internal cuts at six
15. `3a2ad60d` — Sharpen younger-surrounding internal cuts
16. `c7bfd4e3` — Extract middle-marker doubled-width bound
17. `72e7ee72` — Sharpen between-marker internal cuts
18. `3d74615c` — Isolate two saturated internal cut residuals
19. `b454c8b4` — Extract older-surround complement bound
20. `67d0847c` — Close extreme older-surround maxima
21. `337e20db` — Narrow internal cuts to middle residuals
22. `8bda993d` — Extract three-marker triangular-plus-one bound
23. `f71a4cd3` — Extract active separating-marker rank wrapper
24. `031229ca` — Isolate saturated internal cut residuals

Nothing was pushed or published.

No tracked scripts, workflow helpers, generated certificate modules, or ad hoc research programs
changed; the tracked delta consists of theorem modules, the blueprint root, and harness metadata.
Consequently there is no algorithm or workflow code to promote into `harness/research/` or
`tools/es/es/`. Under the explicit Sol-only/no-delegation constraint, this session did not perform
the prescribed external Astra post-run maintenance review; this report records the delta for that
review. No Astra mathematical hint was requested.

## Verification

Every result passed a guarded targeted check and a guarded full extraction before commit. The last
theorem extraction was job `20260915-214530-3c3b53`: 484.8 seconds, 5,393 MiB peak, tree hash
`46400e9f4f7a0708`. The final changed-declaration axiom audit covered 239 declarations with no
failures; import layering and `git diff --check` passed. Closed theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.

A post-commit full refresh, job `20260915-215942-c30717`, passed in 496.1 seconds at 10,770 MiB,
produced tree hash `ea7bef4ca32b0635`, and anchored the 251/11/1 frontier to theorem commit
`031229ca`. Metadata-only commit `bec4c12d` records that provenance refresh and is not a
mathematical result. After releasing the sole parent claim, final status is 251 closed, 12 open,
one refuted. Parent context reports `frontier_fresh=true`; the tracked worktree is clean.

The durable outer host job `20260915-150549-609c48` ended rc 1 at `02:23:44Z`, 1,042 seconds before
the frozen deadline, after its native-goal monitor classified the intentional verified hold as
`goal_blocked`. This was not an OOM or budget overrun (`budget_exceeded=false`, 520 MiB peak), and
no repository work was active or lost. It emitted handoff artifact
`21fa6ac58f8fe1ade0cbc37b6f6bae7407c5fc7f290db8171918cd4eb89ecbb6`; the existing window resumed
for the permitted finalization turn without restarting the host or extending the deadline.

Final reconciled usage contains 1,861 records through `02:41:26Z`: 269,471,305 input tokens
(266,068,608 cached; 3,402,697 uncached), 516,572 output tokens, and 134,835 reasoning-output
tokens, with zero reconciliation delta. Job resource totals are absent from the window report
because the guarded jobs were not operation-linked; their individual IDs, durations, caps, and
peaks are preserved in the checkpoint and harness journal.

## Next exact target

The saturated younger-exterior estimate currently decomposes into a triangular-plus-one complement
charge `11` and an exterior retained charge `2`, one above the required total `12`. The legal
`k = 6` coupling should close both extreme complement maxima:

- `m = 1` forces retained maximum `n = 4`, so the retained part has bound at most one and `11 + 1 = 12`;
- `m = 4` makes the complement part have bound at most one, while the retained rank-union charge is
  at most two.

The clean implementation route is to expose a componentwise version of
`ctx_two_marker_younger_exterior_internal_complement_cut_potential_bound`, using the newly exported
`ctx_three_ordered_markers_triangular_plus_one_bound` and
`ctx_active_separating_marker_retained_boundary_rank_union_bound`. A short coupled corollary can
then reuse `ctx_part_positive_letters` and `ctx_bound_le_one_of_large_sibling_maximum` to close
`m = 1` and `m = 4`, refining the younger-exterior residual to `m = 2 ∨ m = 3` just as the
older-surround branch already is. The component proof is the post-helper portion around lines
438–618 of the existing potential theorem. Exact searches found neither a componentwise theorem
nor a younger-exterior extreme-maximum theorem.

Its intended conclusion, under the existing potential theorem's hypotheses, is:

```text
let w := oppositeGlobal - 1
let rest := σ.childPositions.filter (· ∉ keep)
((∀ f, boundFuel f (σ.part rest s m) ≤ (w + 1).choose 2 + 1) ∧
  (σ.part rest s m).bound ≤ (w + 1).choose 2 + 1) ∧
((∀ g, boundFuel g (σ.part keep t n) ≤ w - 2) ∧
  (σ.part keep t n).bound ≤ w - 2)
```

The projected sequence is therefore: componentwise charges; an exact `k = 6` extreme-maximum
corollary; then a short classifier composition attaching `m = 2 ∨ m = 3` to both surviving
positional families at opposite global five. The final residual can be factored as
`oppositeGlobal = 5 ∧ (m = 2 ∨ m = 3) ∧ (older-surround ∨ younger-exterior)`.

The detailed chronological receipts, proof fixture IDs, job IDs, extraction hashes, and decisions
are in `checkpoint.md` beside this report.
