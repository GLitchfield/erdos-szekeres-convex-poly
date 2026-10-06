# Older-exterior chosen-kept cut, 2026-09-24

Target: `ErdosSzekeres.ctx_two_actual_marker_small_history_internal_chosen_kept_cut_six_bound`.
The only remaining `sorry` is the older-exterior branch with chosen global five.
The retained part is bounded by one, so the exact remaining obligation is to
bound the opposite companion by eleven, for all fuels and at full recursion.

The checked older-exterior interval lemma bounds the companion by twelve. It
splits physical child runs at the younger chosen marker: the far group costs
at most three and the near group at most nine. These are independent charges;
the missing fact is that the two group maxima cannot be realized together in
the recursive context. Splitting at the retained opposite marker is weaker:
for the clean three-child witness its original-history pruning charges are
eight and six.

The registered Python evaluator (`context-bound-zero-children-v1`) ran in es
job `20260924-182140-c135a6` on the clean six-child companion
`[S,S,2L,3L,S,S,1U,S,S]`, maxima `[1,1,1]`. It returned companion 11 and
retained part 1 (total 12), in 820.4 seconds at 195 MiB peak. This is only
diagnostic: no Lean equivalence certificate is asserted. Zero chosen maxima,
one unindexed barrier in the four-child family, and selected larger patterns
also returned at most eleven. None is a proof for arbitrary child-run lengths.

Checked `ctx_two_actual_marker_companion_maximum_bound` bounds a recursive
opposite-side part with new sibling maximum 2, 3, or 4 by 8, 4, or 1. At
maximum 2 the chosen-side part may attain 4 when it straddles the original
opposite marker. The needed conditional is that an opposite part attaining 8
forces that chosen part to be at most 3 (or an equivalent one-unit collision).
Analogous coupled charges are needed for maximum 3 and for the maximum-1
branch. Existing rank/pruning lemmas bound the parts separately and do not
establish these implications.

Finite witness compression is unproved. Removing unused children can destroy
the `numRuns > 1` condition that made a recursive cut legal; keeping a run
witness can alter a positive child part. No finite negative sweep is theorem
credit. The exact target file remains sorry-bearing and has not passed the
requested closure gate.
