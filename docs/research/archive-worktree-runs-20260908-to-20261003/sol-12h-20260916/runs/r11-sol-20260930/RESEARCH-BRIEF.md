# R11: re-prove the two single-run reductions with run contraction on parts only (one Sol trial, gpt-6.1-sol)

Approved by Gavin on 30 Sept 2026 (evening round). Coordinator:
`claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f` (Claude). Callbacks are not verified: never wait
for replies; keep `PROGRESS.md` here current. One trial, two nodes in order; never reset the host
deadline. When both nodes are closed and committed, say so in PROGRESS.md: the coordinator reviews
the receipts and ends the run early with `es run finish` (you then get the finalization turn).

## Why

Two closed theorems on main take general run contraction (C1) as the hypothesis `hcontract`:
- R9 `ctx_bound_additive_single_run_alternating_of_run_contraction_and_deletion` (C3 ⟸ C1 + DelMono),
  module `ESBlueprint/B/CtxBoundAdditiveSingleRunAlternatingOfRunContractionAndDeletion.lean`;
- R6 `ctx_bound_additive_single_run_of_run_contraction_and_alternating` (single_run ⟸ C1 + C3),
  module `ESBlueprint/B/CtxBoundAdditiveSingleRunOfRunContractionAndAlternating.lean`.
Both apply `hcontract` only to parts of well-formed single-run contexts. General C1 is stronger than
needed; the new target is C1 on parts (C1p), which follows from a root-form conjecture through a
bridge being proved in parallel (R10). This trial proves both reductions from C1p.

## Checkout and scope

- **Worktree:** `runs/worktrees/sol-12h-20260916` (Lake build cache). Two registered nodes, one
  branch each (base main 15f36571):
  1. `node/CtxBoundAdditiveSingleRunAlternatingOfPartContractionAndDeletion`:
     `ErdosSzekeres.ctx_bound_additive_single_run_alternating_of_part_contraction_and_deletion` (R9').
  2. `node/CtxBoundAdditiveSingleRunOfPartContractionAndAlternating`:
     `ErdosSzekeres.ctx_bound_additive_single_run_of_part_contraction_and_alternating` (R6').
  The worktree is currently on another branch (`node/CtxBoundAdditiveSingleRun`, a coordinator
  commit that must stay untouched): `git -c gc.auto=0 -c maintenance.auto=false checkout <branch>`
  switches (the tree is clean). Do R9' first, commit, then switch to R6'.
- **Harness:** `/home/gavin/git/erdos-szekeres-convex-poly/tools/es/bin/es --root /home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916`.
- **Commit** each with `es node commit <node> --message-file <file>` on its branch (queued for
  `es worker` from your sandbox; then `es job wait <id>`).
- **Checks:** `es check <node> --targeted` (sized, ~4-5 GiB); scratch compiles as
  `es job run --mem 4G ... -- lake env lean <file>`. Never kill a job at a self-chosen time; at
  `review_due` record `es job review <id> --note ...`.
- **Forbidden:** merging, pushing, touching the primary checkout, editing other statements, a full
  `es extract`, delegating.

## The change

Each new statement equals the old one with `hcontract` replaced by
`(hpart : ∀ τ, τ.WellFormed → τ.numRuns ≤ 1 → ∀ keep s m, 1 ≤ m → m ≤ τ.k - 2 → ∀ left right,
(τ.part keep s m).word = left ++ [child, child] ++ right → (τ.part keep s m).bound =
({ τ.part keep s m with word := left ++ [child] ++ right }).bound)`.

Start from the existing proofs (copy them). At each place they apply `hcontract` to a context ρ,
show instead ρ = `τ.part keep' s m` for a WellFormed single-run τ, and apply `hpart`:
- in R9: ρ is the K-part (or complement part) of σ after deleting one separator letter y; this is
  `(σ with the child at y deleted).part keep' s d` (deleting a non-kept child of σ deletes the
  corresponding external letter of the part). σ minus a child is WellFormed (no condition on children)
  and single-run (a child removed from a contiguous run);
- in R6: ρ is a part of σ after deleting doubled kept letters one at a time; the same argument.
Both theorems already contain the word/part bookkeeping (R6's `hCtxEq`, `hInterval`, deletion lemmas);
the new obligation is the representation of ρ as a part of a single-run context. Consider proving
that once as a local lemma and reusing it in both.

## Procedure and stop criteria

- For each node: scratch development in `runs/r11-sol-20260930/`, `es check <node> --targeted`,
  `es node commit`, note in PROGRESS.md.
- **Closed (both):** stop and report. **Stuck:** two consecutive attempts fail at the same obligation:
  write the exact missing lemma in the handoff and stop (report which node closed, if any).
- **Rules:** AGENTS.md; `es log` every finding with job IDs; at the end `MATHEMATICAL-HANDOFF.md` and
  `REPORT.sol.md` here; claim each node before working on it and release it at the end.

## Addendum (coordinator, 30 Sept ~11:35Z): register node 2 yourself

The coordinator's registration of node 2 failed on a parse error (a `let` inside `halternating`
lost its line break; the corrected statement is in `R6P-TYPE.txt` here, with `;` after the `let`
value). The branch `node/CtxBoundAdditiveSingleRunOfPartContractionAndAlternating` exists at main
15f36571 with no node yet. After node 1, check out that branch and register exactly this statement:

```bash
es --root <this worktree> node add --targeted --ws B --kind formalization \
  --name ctx_bound_additive_single_run_of_part_contraction_and_alternating \
  --import ErdosSzekeres.DecomposableContext \
  --consumer ErdosSzekeres.ctx_bound_additive_single_run \
  --depends ErdosSzekeres.ctx_bound_external_letter_contraction,ErdosSzekeres.ctx_base_child_letter_contraction \
  --type "$(cat runs/r11-sol-20260930/R6P-TYPE.txt)" \
  --description "Single-run additivity from run contraction on parts of single-run contexts (hpart, C1p) and alternating additivity (halternating, C3): the closed R6 glue with its general-C1 hypothesis narrowed to what it uses (R7/R11)."
```

Commit the registration with `es node commit`, then prove it as briefed. The type text must not be
edited: it is R6's signature with `hcontract` replaced by `hpart` (the same `hpart` as node 1).
