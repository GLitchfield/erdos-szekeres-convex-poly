# Final handoff: partial small-history chosen-kept cut

## Outcome

The primary theorem
`ErdosSzekeres.ctx_two_actual_marker_small_history_internal_chosen_kept_cut_six_bound`
was **not proved**. Its checked Lean scaffold still ends in `sorry` in the
older-exterior branch, so the native goal remains paused and receives no
primary theorem credit.

The run did prove the authorized fallback
`ErdosSzekeres.ctx_two_actual_marker_opposite_younger_exterior_companion_eleven_bound`.
It is sorry-free, compiled, audited, reviewed, and committed at `4f2b56fa`
(`Prove younger-exterior actual companion bound eleven`). Its extracted type
hash is `659c2ef5b137dd59`.

## Exact receipts

- Fallback targeted check: job `20260923-025536-950d52`, rc 0. Receipt says
  `proof_accepted=true`, `sorry=false`, and only `propext`,
  `Classical.choice`, and `Quot.sound`; there are no uncovered axioms.
- Fallback audit/layers: job `20260923-030536-da12d8`, rc 0; 337 declarations
  audited with no failures, and no layer violations.
- Fallback review: job `20260923-030545-412494`, rc 0,
  `proof_accepted=true`, `frontier_fresh=true`, source hash
  `987c9411311b46dec56654f3828b3ab93ebf2df01a8bc9b77998afe162f9aa96`.
- Primary node registration: job `20260923-091340-05a2c1`, rc 0; registered
  type hash `afc74d2efdb0115f`.
- Primary scaffold check: job `20260923-092853-ba4c4c`, rc 0, 141.6 seconds,
  peak 3449 MiB. The check explicitly reports `sorry=True`, `sorryAx`, and
  status `claimed`; it is only a typechecking receipt for the partial scaffold.
- Window `window-38e46bc18a80431b` ended complete with one accepted result
  (the fallback). Usage sync recorded 1,892 responses and 1,138,009 output
  tokens. Both the primary-node claim and its umbrella consumer claim were
  released `partial`.

## Preserved primary progress and obstruction

The scaffold derives `m=4`, `n=1`, proves `A.bound≤1`, handles the global
chosen-axis-at-most-four case, consumes the residual classifier, and closes
the classifier-done, between-marker, and younger-exterior placements. It also
proves that the remaining retained placement is older-exterior.

That last branch still lacks one strict unit of coupled accounting at global
five. The attempted local three-band triple-face count was invalid: the static
support can be `3+9=12`, not `3+4+4=11`. A later capacity route was also
corrected: a high child between the older marker and the retained block need
not force the retained part to zero. The diagnostic tight word
`[S,1L,S,3U,2U,S]` has companion source 11 and raw high/low charges `9+3=12`;
this suggests the missing lemma must charge a shared marker/run or otherwise
couple the companion saving to the retained part. This probe is exploratory,
not Lean-equivalent, and is not theorem evidence.

Run-local diagnostic code and outputs remain under this directory. They reuse
the existing evaluator/limits workflows; no recurring algorithm warranted
promotion. There are no queued, starting, or running proof/check jobs. The
only live job observed at finalization was `20260923-085022-a10063`, the host
process executing this final turn, not a child research job.

The fallback commit is `4f2b56fa`. The primary checkpoint could not be
committed from this sandbox: Git failed while creating `.git-data/index.lock`
with `Read-only file system`, before changing the index. The remaining working
tree changes are exactly `ESBlueprint.lean`, `harness/statements.lock`, and the
new `ESBlueprint/B/CtxTwoActualMarkerSmallHistoryInternalChosenKeptCutSixBound.lean`.
The harness index is intentionally stale by this one newly registered,
incomplete node; no full extraction was started during deadline finalization.

## Safest next action

Resume only in a fresh authorized research turn. Start from the preserved
older-exterior branch and seek a formally stated one-unit shared charge at
global five; do not revive either corrected counting claim. Re-run a targeted
check only after replacing the final `sorry`. From a Git-writable shell,
commit the preserved partial checkpoint (without presenting it as closed),
then perform full extraction, audit, review, and a final proof commit before
claiming the primary theorem.
