# What the k=6 examples say about singleton selection

## Current verdict, 2026-10-02 21:49 UTC

Full PEEL is refuted in Lean by `ctx_bound_singleton_attainment_counterexample`,
check20261002-101239-d357fa. At(4,4,5), word3U4LSS1L2USS, maxima1111,
WellFormed holds, bound>=2, and all24 legal singleton sums are1. Exact bound2
remains diagnostic. The exact witness is also proved not Satisfies any coloring,
check20261002-110525-546700: its first pair has cup limit1, below the vacuous
two-point cup requirement2. Neither fact resolves singleton attainment on
actual feasible histories or the one-level root target.

The effective-parameter explanation is now reusable mathematics:
`ctx_oldest_singleton_flank_normalize`, check20261002-112036-dd5454, proves
equality of all child limits, fuel bounds and the full bound after truncating
a genuine singleton oldest flank and changing its selected global parameter
G to min(G-1,k-m). Its normalized context retains an unindexed marker and need
not be WellFormed. `ctx_satisfies_of_limits_le`, check20261002-113919-10c1db,
transports coloring constraints under unchanged child positions and monotone
limits/k; two applications logically give constraint equivalence for exact
normalization. No combined independent-branch corollary receipt is claimed.

The k6 context below is now a Lean-certified positive Satisfies witness whose
global-end cuts are all strictly smaller than its bound:
ctx_k6_satisfied_end_cut_counterexample, check20261002-122611-18dca1,
receipt37353e1f739a6742ee72aa641913fdcf267f1bdadc569e67d87be88a4f097f51,
commit8e2f72ce9b0ae129609f051661313b7bee767dcf. It certifies WF, constant-right
Satisfies, bound>=8 and all16 p0/p6 cut sums<=7. Exact parent bound8, middle
attainment2+6 and failure of every other child including p2 are now certified
by ctx_k6_unique_middle_singleton_attainment, check20261002-145508-8b2f02,
receiptf2d86d2b78a2888f86ed602b7adc5c32e04d850e5616102b720b5348c4a89c38,
commit1cd0281b18dddb1177d47d876c1e6b87f15fc741. Complement symmetry and56
numeric certificates cover all72 parent cuts and24 nonmiddle singleton cuts.
Uniqueness of the side/coupling remains diagnostic. Full external history is
accepted as ctx_k6_actual_history_witness, type80c84048681897f7,
commitd3b81e384ff288237fbef7fa380c985dd0ded1ca,
check20261002-160456-155bf5,
receiptd882dc65055b3a1af3920b833c3e518df688494e481c51e80b25075ff88f965d.
Its seven-vertex coloring has actual singleton ancestors and root profile
upper bounds(4,4,5), with a four-vertex child. It does not prove sharp child
cardinality8 or a stronger coordinate deep-below tree. The independent exact
bound and history receipts have no separate compiled conjunction. None of
these proposes general feasible PEEL.

The budget-cost comparison is separately certified by
ctx_k6_remaining_budget_cost_counterexample, check20261002-135814-128f53,
receipt2dd0090dbe57f57267bf19742af8237b234cfe0dc227eb628513887a1a909677,
commitc0094d67eaf0247835dcb62b4720328896c815ba. Its locked statement gives
end upper3 leaf2/rest4 with every remaining cup/cap limit unchanged, middle
upper3 leaf2/rest>=6 with positive cup loss, and all end-child cuts<=7.
Pointwise remaining-budget-loss minimization can therefore prefer an inferior
child. This refutes that particular cost surrogate under the already certified
Satisfies witness, rather than every possible definition of net capacity cost.

Exterior-unindexed-padding and ordinal-Satisfies transport are also accepted
(checks20261002-130548-84659e and20261002-133225-571382). Together with exact
oldest-flank normalization, they explain how effective raw contexts can be
renumbered while preserving bounds and coloring constraints. Independent-branch
composition has no separately compiled corollary receipt.

The additional tables and exact equalities below remain diagnostic outside
the certified scope above. Source:
`PEEL.cost-profiles.json`, job `20261002-093908-bcbe7b`, shared C recurrence
`context-bound-zero-children-c-v1`. Every endpoint limit was cross-checked against
the existing `limits_from_signature(..., lean=True)` run matrices.

## The middle of `SSS1L3L2LS`

Globals `(5,5,6)`, maxima `(1,1,1)`, child positions `0,1,2,6`. The full bound is
8. All parent cap limits are 4. Cup limits within the first run are 2, across
the two runs 4, and at the last child 2.

The unique attaining child is 1 (Lean-certified). The diagnostic table also
identifies a unique attaining side/coupling: upper with its sibling maximum
`c=3`, and the complementary lower maximum 2. The brief's `d=2` describes that
lower coupling, not `c=2` for the upper leaf.

| Peeled child, upper `c=3` | Leaf | Remainder | Sum |
| --- | ---: | ---: | ---: |
| 0 | 2 | 5 | 7 |
| 1 | 2 | 6 | 8 |
| 2 | 2 | 5 | 7 |
| 6 | 2 | 4 | 6 |

Each leaf has cup and cap limit 2, hence value `T(3,3,6)=2`.
In the middle remainder, children 0 and 2 have cup limit 1 separately, but the
cup spanning them retains limit 2: the new marker at position 1 lies between
its endpoints and cannot extend it. The two neighbors are separate runs; with
the old last child there are three surviving runs in total. The last singleton
run has limits(cup2,cap4), hence recursive capacity T(5,3,6)=4. Together with
the two unit runs this explains remainder6. Bound measures recursive capacity,
not the number of child letters: this context has four children and bound8.
In an end remainder the two surviving neighbors form one contiguous run with
cup limit 1, including their spanning cup. The remainder capacities are 6 and
5 respectively. This accounts for the missing unit in the end-only cuts.

Spanning does not remove every new constraint. In the middle remainder the
cup from 0 to 6 keeps extension count zero, but its join term increases from
1 to 2, so its limit falls from 4 to 3. A proof must retain the coupling term
even for intervals that cannot use the new marker as an extension.

## Why raw marker costs do not give the selection theorem

The formal part operation inserts the new sibling at level 1 and shifts all
old levels up. In repository indexing the new sibling is the nearest level,
not the largest/oldest indexed level handled by oldest-flank normalization.
The brief's "oldest" wording must not be used to reverse this walk order.
A spanning interval cannot use its marker in either direction.
An exterior marker is usable, but need not increase the maximum extension:
choosing it first may block older markers, while omitting it preserves all old
walks. The profiles contain exterior intervals with zero extension change.

More decisively, the last-child cut above has **zero loss of every remaining
lower limit**, but yields remainder 4. The middle-child cut has positive losses
on some limits yet yields remainder 6, with the same leaf value 2. Consequently,
pointwise limit loss, or a count of tightened endpoint constraints, cannot by
itself measure the loss of the recursive bound or identify the optimal child.
Removing a whole run and splitting a surviving run affect capacity as well.

The needed quantity is a net capacity trade: leaf gain, changes to surviving
run capacities, and coupling/threading constraints together. The certified
splitting identity explains how a single-run threshold can be allocated among
adjacent pieces; certified FLANK-SWAP handles the exact outer-flank rotation.
Neither yet proves that a paying child exists in an arbitrary optimal cut tree.

FLANK-SWAP also requires actual presence of both flanks. The accepted
ctx_absent_flank_swap_counterexample, check20261002-164625-6c030a, receipt
b6b07830e79402c133ded8f19180ce85d5a8135d5b24280d4866dbc435346e84, certifies
SS/maxima1,2 at(5,5,6) versus the exact same-side normalization to3,2.
Both are WellFormed, all positional flank predicates hold vacuously and M3 is
legal, but their bounds are10 and4. Empty levels have no extension walks yet
their declared maxima still enter strong joins under the default side. Thus
positional predicates alone are insufficient. The witness does not classify
all absent-level swaps or prove each presence premise independently necessary.

Feasibility is also not inherited by arbitrary legal formal cuts. The accepted
ctx_satisfies_arbitrary_part_counterexample, check20261002-172857-7ed08e,
receipt739ee383947782d1c2d2ebb2bb7f19e20f6f804fd1d5834ccf1a2ac4e252ce81,
pin6b5dce7e7d26dc99172f89b72e9b4bebcefd51fc, uses the same k6 parent.
It certifies parent WellFormed/Satisfies and a legal p0 upper3 cut whose leaf
and lower2 remainder are both WellFormed. The remaining children1,2,6 have
cupLimit1,2=1, excluding every coloring/ambient set by the two-point cup
argument. Thus the raw recursive recurrence can evaluate infeasible parts
even from a feasible parent. This cut is nonoptimal by the independent exact
k6 receipt; the example does not refute feasible PEEL or all optimal cuts.
An induction restricted to feasible histories needs a cut-selection argument
that preserves feasibility or a stronger invariant, rather than assuming it
for every formal recursive part. No such argument is established here.

## A zero-valued optimal leaf

At `(4,5,6)`, `SS1L2US3US`, maxima `(1,3,1)`, the full bound is 4. Only child 1,
upper side, `c=4` attains: leaf 0 plus remainder 4. Other children peak at 3.
Thus an all-context PEEL induction cannot insist that the first optimal leaf
has positive value. Zero-valued parts are retained by the Lean recurrence and
by the registered direct singleton falsifier.

This example is outside the feasible scope too: its first pair has caplimit1
in the recorded profile. Upper markers2 then3 give chain extension2, leaving
4-1-2=1. The certified pair-limits necessary condition excludes such a profile
from Satisfies. The extra literal infeasibility has no separate Lean receipt;
ZERO-LEAF.scope-diagnostic.json preserves the diagnostic values. Consequently
this example supplies no evidence against positive-leaf selection on feasible
histories. The accepted arbitrary-part counterexample above rules out generic
feasibility preservation, so this observation does not establish an inductive selector.

## Historical rotation idea, rejected on the raw domain

Start with an optimal interval cut, use the induction hypothesis on each part,
and compare a first singleton rotation. Preserve the local threshold capacity
by the splitting identity, while matching full descendant limits where
FLANK-SWAP applies. For an interior child, keep the two residual runs and their
spanning constraints rather than charging a uniform one-unit extension loss.
Re-optimize the coupling to pay for new strong terms. Zero-value leaves are an
allowed case and can discharge a dead child without losing value.

The proposed step was a structural selection/rotation inequality asserting that
some child and coupling make the combined net capacity trade nonnegative.
It is false on the stated raw-context domain, by the accepted PEEL refutation.
The pointwise-cost minimization formulation above
has been rejected by the certified finite comparison, and it must not be used as an
inductive premise. A further narrowing without an invariant for this combined
capacity is bookkeeping, not progress. The present open question is whether an
actual-history invariant, beyond merely imposing higher global parameters,
supports a valid selection principle. No such invariant or proof is established
here, and no narrowing on the stalled sibling-penalty route was commissioned.
