# Handoff: R7, C3 via root normalization and deletion monotonicity (Claude, 30 Sept 2026)

Run `claude-comb-closedform-20260930`, coordinator `claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f`.
- Claim: `ErdosSzekeres.ctx_bound_additive_single_run_alternating` (C3).
- Research window: `window-943327fe28674eea`.
- Journal: `es journal --node ErdosSzekeres.ctx_bound_additive_single_run_alternating --since 2026-09-30`.

Everything numerical below is diagnostic evaluation of the recursion (`Ctx.Context.bound`) with the
compiled evaluator (`context-bound-zero-children-c-v1`). Nothing here earns theorem credit until the
Lean nodes named below close.

## Open obligation

**Formal state (30 Sept, afternoon).** Single-run additivity now depends only on C1
(`ctx_bound_child_run_contraction_of_level_one_span`). Two Sol trials closed their nodes the same day,
each with a targeted-check receipt: `sorry=False`, standard axioms.

- **R8, DelMono.** `ctx_bound_ext_letter_deletion_mono_of_isolated_children`.
  - Branch `node/CtxBoundExtLetterDeletionMonoOfIsolatedChildren`, commit bf243a39, worktree
    `runs/worktrees/sol-12h-20260916`.
  - Evidence: `runs/r8-sol-20260930/`.
- **R9, C3 ⟸ C1 + DelMono.** `ctx_bound_additive_single_run_alternating_of_run_contraction_and_deletion`.
  - Branch `node/CtxBoundAdditiveSingleRunAlternatingOfRunContractionAndDeletion`, commit 4cf96422,
    worktree `runs/worktrees/main-integration-20260928`.
  - Evidence: `runs/r9-sol-20260930/`.
- **Already on main:** R6's glue, single_run ⟸ C1 + C3.
- **Neither branch is on main.** Integrating them was denied by the session's permission classifier
  and awaits Gavin.
- **After integration**, C3's own module can be closed modulo C1 by applying R9's theorem to C1 and
  DelMono. Its status then shows the C1 dependency.
- **Still open:** C1, and multi_run.

## Results

1. **Older letters are irrelevant for single-run parts.** This is already a Lean theorem:
   `ctx_single_run_descendant_bound_normalize` (closed).
   - Every part of a single-run σ has the bound of a context with parameters
     (capLimit + 1, cupLimit + 1, k) of σ's run and only the new level.
   - So C3 is equivalent to C3 on root contexts ⟨a′, u′, k, Sⁿ, []⟩.
   - The glue uses C1 only on one-level contexts over a root.
   - Cross-check: 8,712 alternating parts, 0 mismatches (`normalize-check.json`).
2. **The reduction.** Proved on paper; see the journal entry "R7 REDUCTION" and the R9 brief.
   - Base cases: n = 2 is prefix/suffix and n = 3 is the singleton-ended sandwich, both closed.
   - Step for n ≥ 4: remove the 2nd and 3rd children. In each comb, delete the separator (DelMono),
     then contract the doubled tooth (C1). This gives the alternating partition of a run of length
     n − 2, with the same base (`ctx_base_child_letter_contraction`).
3. **P10, root tables** (`p10/`). k = 5..8, all 1 ≤ a′, u′ ≤ k, teeth ≤ 4, n ≤ 8, plus n = 9 at k = 5 and 6.
   - 0 C3 violations.
   - V(n) ≤ V(n − 2) in all 7,040 comparisons.
   - Comb values are constant from teeth 1 (4,913 cases), 2 (701) or 3 (18).
   - The only increases occur when a 1-tooth comb without ends has an empty level (sideAt defaults to
     lower). That is the last-letter case DelMono excludes.
4. **D1, DelMono** (`d1/`, `d1c5/`).
   - With 2–4 children: 0 violations in 82,512 singleton-run deletions and in about 23,000
     general-run deletions over eight triples.
   - Deleting the last letter of a level does violate it, so the hypothesis is necessary.
   - Five-child shards: see `d1c5/`.
5. **P9 slice.** Peeling one end tooth attains every plain-comb bound at (5,5,6) and (6,6,6).
   - This is open at scale, and no longer needed.
   - At (5,5,6) with m = 1 the comb bound drops 14 → 13, which makes C3 tight: 13 + 1 = 14 = T(5,5,6).
6. **M1, multi_run scoping** (`m1/`, six jobs, about 4–5 h each for k = 6). Question: does deleting
   a doubled kept letter inside a run of a multi-run context keep V_σ(K) ≤ V_σ′(K′)? Results pending.
7. **C1R, root-level cross-cut domination for C1** (`c1r/`, 15 shards for k = 5, 6, 7).
   - Setting: one-level root contexts, a doubled pair y y′, at most 5 children.
   - **Separating cuts.** Every cut separating y and y′ is dominated in ρ′ by one of the two moved
     partitions, (B, R−y′) or (B−y, R−y′+y).
     - Usually this works at the same coupling. About 1–7% need re-optimized orientation or coupling.
     - Example: S x S S at (5,5,6), m = 1, cut {y} upper 4 with V = 13 needs upper 3 in ρ′.
   - **Non-separating cuts.** Dominated by the same partition in ρ′, essentially always at the same
     coupling (58,751 of 58,752 at k = 5).
   - So far 0 exceptions and 0 C1 violations.
   - If this holds at scale, it is an explicit rule for the value argument. A proof would still have
     to show the re-optimized domination, which needs a local exchange inequality between a gained
     external letter and a lost child.
8. **Tooling.** The compiled evaluator gained `persistent=True`: one C memo across calls, the same
   values, and 27× faster on part-heavy probes (main 2d9b5ec3).

## Failed or stopped work (none is a negative result)

- P8 (t ≤ 7) and the first P10 smoke were stopped for cost. At t = 6 a comb takes 81 s; the cost
  explodes with depth.
- P8 and P9 were later made redundant by the normalization lemma.
- Early foreground smoke tests were killed by `timeout` wrappers. That practice is now forbidden by
  the rule change in c53fb41d. The dropped coverage was relaunched: D1 with 5 children, and P10 at n = 9.

## Reusable observations

- Before any single-run probe, normalize: root parameters (a′, u′) replace the history.
- A comb's limits have 4 classes: first/other × last/other.
- The compiled evaluator is exponential in recursion depth. Keep combs to ≤ 5 teeth, and time a
  small instance first.
- `ctx_bound_mono_of_marker_inclusion` and `ctx_single_level_occurrence_prune_bound_mono` (closed)
  give "replace a letter by an inert one" for free. Only run merging needs work.

## Next steps

1. **Integration.** On Gavin's approval, integrate the R8 and R9 branches into main. Then close C3's
   module modulo C1, as the composition of R9's theorem, C1 and DelMono.
2. **C1**, now the only open piece of single_run.
   - Read the C1R shards.
   - If domination by moved partitions holds throughout, isolate the exchange inequality it needs:
     "adding back the external letter gains at least what deleting the adjacent child loses, after
     re-optimizing the coupling".
   - Test that inequality directly on parts, which are 2-level contexts.
3. **multi_run:** read M1.


## Update (30 Sept evening, second round)

**Formal state (main f55e3b92, pushed).** Single-run additivity now rests on one conjecture, the root
form C1r (`ctx_bound_child_run_contraction_one_level_root`). All of the following are closed:

| Node | What it says | Run |
|---|---|---|
| DelMono `ctx_bound_ext_letter_deletion_mono_of_isolated_children` | deleting an external letter never lowers the bound | R8 |
| Bridge `ctx_bound_part_run_contraction_of_one_level_root` | C1 on parts of single runs, from C1r | R10 |
| R9′ `ctx_bound_additive_single_run_alternating_of_part_contraction_and_deletion` | C3 from part contraction and DelMono | R11 |
| R6′ `ctx_bound_additive_single_run_of_part_contraction_and_alternating` | single_run from part contraction and C3 | R11 |

- **Composition.** C3's module is being re-composed as R9′(bridge(C1r), DelMono) in
  `runs/worktrees/sol-12h-20260916` on branch `node/CtxBoundAdditiveSingleRunAlternating`. Its
  targeted check is waiting for the build slot.
- **single_run.** It becomes R6′(bridge(C1r), C3). This needs a full `es extract` first, because its
  import change makes `CtxBoundAdditive`..`DecomposableStateUpperAll` stale.
  - Branch `node/CtxBoundAdditiveSingleRun` has an older composition (b698329e, through general C1).
    Redo it with R6′.
- **General C1** (`ctx_bound_child_run_contraction_of_level_one_span`) stays open but is off the
  critical path.
- **Sol R12** (`runs/worktrees/main-integration-20260928/runs/r12-sol-20260930/`) is composing three
  special cases:
  - `sandwich_one_singleton_end` and `three_blocks`, from single_run;
  - `uniform_separator_contraction`, from the bridge applied to C1r.

**Evidence for C1r.**
- C1R: 0 exceptions and 0 C1 violations over k = 5..7.
- Its falsifier: 0 violations in 2,628 contexts; the `es falsify` job is running.

**P11: how the value argument for C1r would have to look.**
- Cuts not dominated at their own coupling:
  - k = 5: 2,382 separating, 2 non-separating;
  - k = 6: 9,294 separating, 38 non-separating.
- All of them are rescued by the same partitions at another orientation or coupling.
- The needed coupling shift grows with k: ±1 at k = 5, down to −2 at k = 6; k = 7 is running. So
  there is no fixed-shift rule.
- The hard cases concentrate where the separated block is the single child {y}, i.e. one part is
  single-run with an explicit base value. A proof would pair that with threshold/Pascal allocation
  (`ctx_base_pascal_combine`, `ctx_bound_three_way_base_allocation`).

**Workstream C.** Adaptive cube-and-conquer runs in `runs/etv-cc-20260930/`.
- 908 six-point cubes; about 80% are UNSAT in about 5 s each.
- The hard cubes did not finish 2M conflicts in 32 minutes, so the run was resumed at 100k conflicts
  with 5 workers.

**Harness (main).**
- 15f36571: `es run finish`, which worked for R10 in 12 s; a stale-MCP warning; `es falsify --mem`.
- 8744c564: the sandbox dependency check.
- Backlog: a build-slot refusal is misreported as "20G cannot fit".

## Running jobs at handoff (check first on resume)

- M1: 20260930-083201-6b6330 and five more (`m1/`); reviewed with an estimate of about 4–5 h.
- C1R: 20260930-094404-984340 .. 20260930-094407-a7ce68 (`c1r/`).
- Sol hosts R8 (20260930-090312-6e9550) and R9 (20260930-090758-d1f606). Both results are already
  committed and reviewed. The hosts wait for their native deadlines (R9 21:08Z, R8 23:03Z) and then
  finalize.

## Update (30 Sept, night): M2, the multi_run reduction routes

Setting: jobs 20260930-160620-9d4ab3 and 20260930-160620-bb82e4, `m2/m2-{A,B}.json`, script
`m2_multirun_domination.py`. Diagnostic only.

**Correction to M1.** The step "V_σ(K) ≤ bound(σ′)" after deleting a doubled child is false for
*interval* partitions.
- Example: [S,1L,2U,S,1L,2U,S,S], maxima (1,1), 9 → 8.
- This is the C1 failure with a level-2 letter in the span.
- Interval partitions are handled by `ctx_bound_cut_le` anyway, so the routes below are tested on
  interleaved partitions only.

**Results.** Scope: 2–3 runs, ≤ 5 children, six (a,u,k) cases, 32,688 interleaved partitions.

| Check | Result |
|---|---|
| multi_run violations | 0 |
| **Route X** (inside σ): flipping some maximal same-side segment keeps V ≥ V_σ(K) | 32,688 / 32,688 |
| **Route D** (deletion), 12,672 steps: DOM, V_σ(K) ≤ bound(σ′) | 0 failures |
| Route D: DEL, bound(σ′) ≤ bound(σ) | 0 failures |
| Route D: natural transport | 139 failures |

- **Route X.** A *singleton* segment flip always works. End segments are not always enough.
  - This gives an induction on the segment count that ends at interval partitions.
  - It needs neither C1 nor C1r.
- **Route D.** The 139 transport failures are dominated at distance 1 (checked in 5,5,6 and 6,6,6).
- **Link to R13.** Both routes point the same way as R13's singleton normal form: the bound is
  attained by a singleton cut when numRuns ≥ 2.

**n = 6: stopped, no result.** Jobs 20260930-180304-ad6dbe and 20260930-185353-5b7035.
- Heavy contexts, with 5–6-child runs over 2 levels, take far longer than an hour.
- This is the evaluator's exponential depth cost. I scaled the estimate from partition counts
  without timing a heavy context first.
- Follow-up: time single contexts first, then run a restricted family, or attempt a direct proof of
  the singleton-flip exchange.
