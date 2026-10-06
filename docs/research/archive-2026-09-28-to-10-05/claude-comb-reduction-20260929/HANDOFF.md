# Handoff: R1, reducing single-run additivity to combs (Claude, 29 Sept 2026)

Run `claude-comb-reduction-20260929`, coordinator `claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f`.
- Claim: `ErdosSzekeres.ctx_bound_additive_single_run`.
- Research window: `window-f12ebdc29b9f446e`.
- Brief: `RESEARCH-BRIEF.md`. Proposal: `runs/next-round-proposal-20260929/PROPOSAL.md` §4 R1.

Everything below is diagnostic evaluation of the recursion (`Ctx.Context.bound`). None of it is
Lean-certified. Two evaluators were used:
- Python, `harness.research.recursive`, semantics `context-bound-zero-children-v1`.
- The compiled evaluator from R5's unmerged branch: `harness/fixes-20260929` at 3dc338b3,
  `harness/research/context_bound.c`, semantics `context-bound-zero-children-c-v1`. It was loaded
  read-only from the worktree. It agreed with Python on 600/600 random contexts at six triples
  (`crosscheck-compiled.json`, job 20260929-171127-1edbf5).

## Open obligation

`ctx_bound_additive_single_run` is still open, and this run earns no theorem credit. It reduces it,
diagnostically, to two general-k statements plus a Lean-derivable glue step:

- **C1, run contraction under level-one spans.** Suppose every letter strictly inside the child
  span of a well-formed σ is a child or `ext 1 s`, for one fixed side s. Then deleting one of two
  adjacent child letters leaves `σ.bound` unchanged.
  - Repeated, this shortens every run to one letter.
  - The two-run case is `ctx_bound_uniform_separator_contraction`.
  - The ≥ direction is the closed `ctx_bound_child_letter_expansion`.
- **C3, comb inequality.** Single-run additivity restricted to alternating singleton partitions:
  every second child letter, starting at the first or at the second letter.
- **C2, glue (Lean-derivable, not yet written).** Take a single-run σ and any keep set K.
  - Both parts of the partition have the C1 shape: the other part's letters become level-1
    letters, and σ's own letters lie outside the run.
  - So C1, applied to both parts, plus `ctx_bound_external_letter_contraction` for the level-1
    blocks, rewrites the partition value into the value of the alternating partition of a
    shorter single run with the same outside letters.
  - That shorter run has the same base value, because the base reads only the first child's
    limits.
  - Then C3 finishes.

## Results

**C1** (`p1c.json`, job 20260929-171128-49e79e, compiled; `p1-k5.json`, `p1-k67.json`, Python sampled).
- The family: `OLDER_L (1,s)^e1 S^r1 (1,s)^m1 … S^rj (1,s)^e2 OLDER_R`.
  - j = 2 or 3 runs; run patterns up to (3,2) or (2,2,1); separators of 1 or 2 letters.
  - Optional level-1 letters outside the span; 12 templates of older letters (levels 2–3).
  - Maxima: all 1, all k−2, and seeded random.
  - 10,944 contexts per triple.
- **Complete, 0 mismatches:** (4,4,5), (3,4,5), (4,5,5), (5,5,5).
- **Capped at 600 s, 0 mismatches:** (4,5,6) 9,502; (5,5,6) 9,544; (4,6,6) 9,890; (3,5,6) 9,491;
  (6,6,6) 8,115; (4,5,7) 2,226; (5,6,7) 2,458; (7,7,7) 2,485.
- **Total: 97,487 contexts, 0 mismatches.**
- Expansion monotonicity never failed.
- Caveat: `p1c.json` was written by the pre-label version of the script. Its `semantics` field
  reads the Python name, but the job command line shows `--evaluator-root`, i.e. the compiled
  evaluator.

**C3** (`p2/`, jobs 20260929-154436-324885 and -155707-c3512b, Python).
- 0 violations on every alternating partition, both start patterns, both orientations, every d.
- Coverage: run lengths n ≤ 8 at k = 5, 6; n ≤ 7 at k = 7; n ≤ 6 at k = 8. Parameters:
  (4,4,5), (3,4,5), (4,5,5), (5,5,5), (4,5,6), (5,5,6), (4,6,6), (3,5,6), (6,6,6), (4,5,7),
  (5,6,7), (7,7,7), (5,6,8), (8,8,8). Partial coverage at n = 9 for k ≤ 6.
- The outside templates have 0–2 of σ's own letters on each side, at levels 1–2.
- The P2 saturation statistics are invalid: that table mixed the two end patterns. See P6 below.
  The Python evaluator's cost explodes past n = 8 (34 s per configuration at n = 9).

**Toward a proof of C1: the run-length laws**
- P3 (`p3/`, job 20260929-171206-a8fc44, compiled): "a run can be shortened to the number of
  distinct interior levels" is **false**. Example: (5,5,6), `[S,3U,1U,3U,S^r]`, maxima (1,1,1);
  bound 7, 7, 8, 8 for r = 1..4.
- The refined **adjacent-gap law** was consistent on 25,726 random contexts: a run can be
  shortened to the larger contracted length of its two adjacent gaps.
- It is **false** as well (`p5/undominated-556.json`, confirmed in the foreground):
  - (5,5,6), `[S,2L,1L,2L,S,1L,1L,S^r]`, maxima (1,1): bound 7 at r = 1 and 8 at r = 2.
  - The same holds for `[S,1L,2L,S,1L,1L,S^r]`: 9 then 10.
  - A composite gap that is not adjacent to the run still matters.
- The remaining candidate, "shorten to the longest contracted gap anywhere in the span", has not
  been refuted. It has the same closure problem.
- C1 itself is unaffected: its contexts have no level ≥ 2 inside the span.

**Inductive structure** (P4 `p4/`, P5 `p5/`).
- Suppose we prove C1 or a law by induction on child letters. Call a cut *good* when a run letter
  can be removed using the law on the smaller part plus external contraction on the other part.
- P4 (job 20260929-174848-5e8d5c, `p4/`) covered 4,353 contexts over ten triples ((3,4,5),
  (3,5,6), (4,4,5), (4,5,5), (4,5,6), (4,5,7), (4,6,6), (5,5,5), (5,5,6), (6,6,6); ≤ 6 child
  letters at k = 5, ≤ 5 at k ≥ 6).
  - Every context had a good optimal cut, except one at (5,5,6):
    `[S,2U,1U,2U,S,2U,S,S]`, maxima (1,1).
  - That same context is the only failure of the adjacent-gap law in P4.
- But bad cuts exist in essentially every context:
  - *split* cuts: the block boundary lies inside the long run;
  - *rest* cuts: the run lies in the complement, next to a merged composite gap.
- Under the adjacent-gap law, a few bad cuts are dominated by no good cut. This is how that law
  was refuted.
- Structural dominators (P5, job 20260929-175818-bf42c6, `p5/`; ≤ 5 child letters, one run of
  length h + 1). "Split" is a boundary move to a run end, any orientation; "rest" is block ∪ run,
  any orientation. Each cell is the share of bad cuts dominated by that move / by any good cut.

  | case | contexts | bad split | split move / any good | bad rest | rest move / any good |
  |---|---:|---:|---|---:|---|
  | (5,5,6) | 493 | 17,056 | 98.2% / 17,054 | 2,384 | 99.4% / 2,383 |
  | (4,4,5) | 619 | 16,326 | 99.8% / all | 2,418 | 99.4% / all |
  | (4,5,6) | 363 | 12,320 | 99.9% / all | 1,648 | 99.6% / all |
  | (3,4,5) | 703 | 18,576 | 99.8% / all | 2,754 | 97.7% / all |
  | (6,6,6) | 432 | 14,856 | 99.9% / all | 2,040 | 100% / all |
  | (5,5,5) | 670 | 17,646 | 99.98% / all | 2,598 | 99.8% / all |
  | (4,5,7) | 332 | 14,050 | 99.9% / all | 1,960 | 99.4% / all |

  - The only bad cuts dominated by no good cut are the three at (5,5,6), in the adjacent-gap-law
    counterexamples.
  - Neither move is a complete rule.

**C1′, a single interior level of any height** (job 20260929-184203-39c2de, `p1prime-opposite.json`,
`p1prime-same.json`, compiled).
- Question: does C1 hold with level-2 separators inside the span and level-1 letters only outside,
  on the same side as the separators or the opposite side? That is the shape of interval parts in an
  induction on C1.
- Result: 104,855 contexts, 0 mismatches. The family is complete (10,944) at (4,4,5), (3,4,5),
  (4,5,5) and (5,5,5), and has about 4,200–4,450 contexts at (4,5,6) and (5,5,6), in each variant.

**Parts of C1 contexts** (P7, job 20260929-194842-bc30e5, `p7/`).
- Question: does run contraction survive in the descendants of C1 contexts?
- (4,4,5): 0 failures in 71,244 depth-1 and depth-2 parts of 300 contexts.
- (5,5,6): failures in the depth-1 parts of 5 of 300 contexts and in the depth-2 parts of 1.
- (6,6,6): failures in the depth-1 parts of 4 of 300 contexts.
- Example: the C1 context `[2L,S,1U,S,1U,S,S]`, maxima (1,1), at (5,5,6). Cutting out the middle
  child gives the complement part `[3L,S,2U,1U,2U,S,S]`, maxima (1,1,1), whose final run cannot be
  shortened (bound 6 → 5).
- So contraction is not closed under cuts even within C1's descendants. C1 holds only because another
  cut recovers the value. A proof of C1 has to compare different cuts by value.

**Comb saturation** (P6, jobs 20260929-194615-338576 and 20260929-205244-43757b, `p6/`, compiled).
- Correction first: the comb tables were initially keyed by tooth count, which mixed the two end
  patterns. That invalidates the P2 saturation statistics. The three affected P6 outputs are kept
  in `p6/old-keying/` and were re-run.
- With tables keyed by run length n, and comparing only lengths of equal parity (the same end
  pattern), all 10 cases are clean:

  | parameters | max n | configurations |
  |---|---:|---|
  | (4,4,5), (3,4,5), (5,5,5) | 10 | 620 each |
  | (4,5,6), (5,5,6), (6,6,6), (3,5,6) | 10 | 684 each |
  | (4,5,7) | 9 | 630/638 |
  | (7,7,7) | 9 | 634/638 |
  | (5,6,8) | 8 | 576 |

- C3 has 0 violations in every case.
- Every comb-bound sequence is constant from run length ≤ 6: ≤ 5 at k = 6, 7, 8, and ≤ 6 at k = 5.
  No sequence changes at its last recorded length.
- If this saturation holds in general, C3 for all run lengths follows from C3 for n ≤ 6 or 7, and
  the saturation length does not grow with k. A k-uniform target then is a closed form for the
  bounds of small combs, in terms of thresholds.

## Failed approaches and why

- **The level-count law and the adjacent-gap law are false.** The needed run length depends on
  composite gaps anywhere in the span.
- **Purely combinatorial induction fails.** Not every cut admits a removable letter, so any proof
  of C1 needs a domination (value) argument for split and rest cuts. This is the same kind of
  obstruction as the general exchange problem, but now localized to one run and one cut.
- **Python-evaluator scale.** P3 in Python processed fewer than 50 contexts in 56 min before it was
  cancelled.

## Reusable observations

- The compiled evaluator, once merged, makes exhaustive small-family checks cheap: 10,944
  contexts in about 135 s at k = 5. Blocks with 5–6 child letters and 2–3 levels still take tens
  of seconds each.
- The single-run reduction C2 is sound structurally. Parts of single-run contexts contain only
  level-1 interior letters, so C1 is exactly the class C2 needs, and C1 is much narrower than the
  general run-contraction question.

## Formal state and next steps

- **C1 node, pending.** The module `ESBlueprint/B/CtxBoundChildRunContractionOfLevelOneSpan.lean`
  is on branch `node/CtxBoundChildRunContractionOfLevelOneSpan` in the primary checkout, with the
  falsifier `harness/falsifiers/ctx_level_one_span_run_contraction.py`.
  - The statement quantifies the span over `σ.childPositions`. An earlier draft over raw indices
    was wrong, because `letterAt` returns `child` past the end of the word.
  - `es node add --targeted` was refused: elaboration reserves 20 GiB against the shared 30 GiB,
    beside the R2 solver job and the two Sol hosts. The falsifier run likewise needs 24 GiB.
  - Rerun the exact `es node add` from this branch with `--force` once capacity allows (after R5
    ends and the N=27 job's 07:00Z cutoff), then `es falsify`.
  - Type-check job: 20260929-181410-e2a0a2, queued.
- **Next research.**
  1. Prove C1 by a value argument. Every cut of the long context must be dominated by a cut of the
     contracted one. The data says moving the boundary to a run end, plus block ∪ run, covers
     about 98%; the residue needs a characterization.
  2. Register C3 and the C2 glue theorem (Sol).
  3. Settle comb saturation in the tooth count with the compiled evaluator.
- **Multi-run additivity is untouched by R1.**

## Code review and library disposition (end of run)

- **Reused:** `harness.research.recursive` (Python evaluator), `scripts/decomposable_additivity_test.child`,
  and R5's compiled `harness/research/context_bound.py` from the unmerged branch, loaded by file path.
- **Promoted:** `harness/falsifiers/ctx_level_one_span_run_contraction.py`, the C1 family as a
  self-contained falsifier on the Python evaluator. It is on branch
  `node/CtxBoundChildRunContractionOfLevelOneSpan` and not yet committed.
- **Deferred:**
  - `p1`–`p7` and the analysis scripts are one-off probes with explicit semantics in their
    docstrings.
  - The compiled-evaluator loader shim becomes unnecessary once R5 lands; switch to
    `evaluator(..., semantics='context-bound-zero-children-c-v1')` then.
  - No shared helper is worth extracting yet.
- **Found and fixed in this run:** a comb-table keying bug (P2/P6) and a raw-index span hypothesis
  in the first C1 statement draft.

## Evidence index

- Scripts:
  - `p1_multirun_usc.py`, `p2_comb_c3.py`, `p2_driver.sh`
  - `p3_run_saturation.py`, `p3_driver.sh`
  - `p4_rl_induction.py`, `p4_driver.sh`
  - `p5_bad_cut_domination.py`, `p5_driver.sh`, `p5_find_undominated.py`
  - `crosscheck_compiled.py`, `analyze_p2.py`, `analyze_p3.py`
- Outputs:
  - `p1-k5.json`, `p1-k67.json`, `p1c.json`
  - `p2/`, `p3/`, `p4/`, `p5/`, `crosscheck-compiled.json`
- Journal: `es journal --node ErdosSzekeres.ctx_bound_additive_single_run --since 2026-09-29`.
