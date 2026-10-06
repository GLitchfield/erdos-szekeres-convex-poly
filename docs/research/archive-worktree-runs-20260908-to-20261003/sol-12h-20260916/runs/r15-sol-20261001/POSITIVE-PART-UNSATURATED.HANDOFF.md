# Positive proper parts force a strict source-history ceiling

Kernel-closed ctx_positive_part_forces_unsaturated_same_side_history,
locked typeb4e207f3ada8ea51. Exact hypotheses: rawσ with positive actual
external labels,3<=σ.k, arbitrary keep/axis/freshmaximum m, one actual
removed source childr∉keep, and0<(σ.partkeep s m).bound. Conclusion:
every N∈σ.levelsOn s0 has maximumAtN<=σ.k-3. Includes unused declared
levels, duplicate/noncanonical keeps, arbitrary runs/globals/m. NoWF or
legal coupling is needed. It is a necessary condition, never a sufficiency
or lower-bound comparison. κ4 plus positive legal old maxima would force
the selected source history to unit maxima; that specialized corollary is
not separately kernel-registered yet.

Proof is six lines: a violated ceiling implies max>=k-2 usingk>=3,
closed SameSat gives the full proper partbound0, contradict positivity.
SourcePOSITIVE-PART-UNSATURATED.candidate-v1.txt SHA
7d11710fcafaf217bf927d069528be8b1b43b42cc6f157b4f1436bc92cc578d1
matches checked module. Fixturef6485acdb500719ca5562e70aaf4ab009eee2f33525c17ff363bf915b1b41884
(10121B) preceded proof. Registration072336-73fcd9,105.9s2353MiB, is
proposed-before-lock output; normalready/claim establishes later locked state.

Accepted check073315-7ecc5b:rc0/38.5s2335MiB/OOM0/budgetfalse,
build2.961813927s. Full receiptCHECK.positive-part-unsaturated-v1-retry-a.json,
FILE SHA2fd8a70a8d889a505eb250ad7e654fa86deca6288b76fc5e868a0518f958fa4b:
closed/Std/noSorry/locktrue/blocks[]/errors[]/targeted+incrementaltrue.
Initialcheck072759-e0d71c failed before Lean: nestedstage20G exceeded
outer8G (8.1s82MiB/built0). Failure receipt retained. Read-only config
confirmsdefaultbuild20G; core-only targets previously fit lower overrides.
Same source retried24G after singlecompiler slot cleared. No config,
worker/cache lease, statement or proof changed for retry; no time kill.

Dependency SameSat commit705bdaf03ec87d94e6c4f4285ee717005eaea554,
receipt39bcb5e5c1f656e1f3248f6d5f206427fa20204d048a99ca2b1724eafd0a82a5,
type d913167a30e72df3/Std/noSorry. Exact temporary overlay source
SAME-SIDE-ZERO.candidate-v1.txt SHA66f233e9ca91de1867eb8d3cea16eda899e9ef44dd5ee4402ee42904178dac79
is excluded from this node's commit and removed after terminal commit.
Integration needs that separate dependency commit, no merge performed here.

Open: positive-k>=4 paired whole-segment uncrossing. Point-positive and
stable-surviving-point shortcuts are refuted (some already kernel-certified),
so this history ceiling only removes impossible saturated positive branches.
Proposed next general estimate: if an old indexed max and the fresh max
are both>=k-3, any-axis proper part has everyfuel/fullbound<=2, by same-axis
near bound or opposite-axis both-near bound. Atκ4 alllegal fresh maxima meet
that threshold, enabling a proposed critical-value3 unit-history reduction.
Neither next statement is registered or certified at this checkpoint.

Commitfc33578a09d63832a3d1d6a00345d2b910eb561a completed by073614-0e3cf5
on node/CtxPositivePartForcesUnsaturatedSameSideHistory. Exactly ownnode
module/rootimport/lock/index/status; SameSat overlay excluded. Full receipt3461B.
