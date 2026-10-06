# Mathematical analysis ledger

## Component extraction

The existing younger-exterior internal-complement proof already establishes the two desired
components separately. After defining

- `w := oppositeGlobal - 1`,
- `rest := σ.childPositions.filter (· ∉ keep)`,
- `α := σ.part rest s m`, and
- `β := σ.part keep t n`,

its `hOwn` is the triangular-plus-one estimate for `α`, and its `hOther` is the `w-2`
retained-boundary estimate for `β`. The exported replacements for local copies are sufficient.

## Legal extreme maxima

For `σ.k = 6`, positive `m,n`, and `m+n=σ.k-1`:

- `m=1` implies `n=4`; level `1` in `β` has maximum `n`, so
  `ctx_bound_le_one_of_large_sibling_maximum` gives `β≤1`. The component theorem gives `α≤11`
  at opposite global five.
- `m=4` gives `α≤1`; the component theorem gives `β≤2`.

Both arguments preserve independent fuels. No informal inference about a source level is needed:
the indexed witness is the synthetic part level `1`, and its maximum equality is exactly
`part_maximumAt_one`.

## Position-independent maximum-three reduction

There is a stronger legal reduction not recorded in the prior handoff. When `m=3`, coupling gives
`n=2`.

1. For `α := σ.part rest s m`, level `1` lies on `s` with maximum `m=3`. Thus
   `ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three` gives `α≤4` from opposite
   global at most five.
2. Apply `ctx_two_actual_marker_companion_maximum_bound` to the source with selected list `rest`,
   a retained child `l∈rest`, and removed child `q₀∈keep`. Its companion is definitionally the
   double complement of `rest`, hence equal as a part to `β := σ.part keep t n`. With `k=6,n=2`,
   its budget is `k-n-1=3`, so the triangular-linear charge is
   `choose(4,2)+3-1=8`.
3. Therefore every independent-fuel sum and the full sum are at most `4+8=12`.

This argument does not use the positional family, empty opposite history, convexity, exact chosen
occurrence classification, or opposite-width lower bound. Once compiled, it removes `m=3` from
both older-surround and younger-exterior residuals.

Searches before drafting:

- `es search "two marker internal complement maximum three bound twelve"` found no theorem.
- `es search "two actual marker companion maximum m three internal cut"` found no matching
  theorem.

## Remaining maximum-two obstruction

At the saturated width `w=4`, current unconditional component charges are:

- younger-exterior: `α≤11`, `β≤2`;
- older-surround: `α≤8`, `β≤5`.

The older-surround entry above was only the coarse two-loss triangular estimate. Applying
`ctx_two_actual_marker_companion_maximum_bound` to the double complement is sharper here:
`m=2` forces `n=3`, hence companion budget `6-3-1=2` and charge
`choose(3,2)+2-1=4`. Therefore the older-surround case closes as `8+4=12` and is no longer an
obstruction.

The new maximum values are `m=2,n=3`. The easy sibling-maximum lemmas do not save the missing
unit: `m=2` is below the `k-3` threshold for `α`, while `n=3` is below the `k-2` threshold for a
unit bound on `β`.

For the remaining younger-exterior `β`, the two complementary level-one markers `l,r` give left and right
pure losses one. With opposite global five and level-one maximum three, both the pure and strong
constraints allow capacity two, so a direct unit-bound claim is not justified. The existing
`w-2=2` estimate can therefore be sharp at the component level. Any final saving is likely a
coupled activity/rank reservation or a sharpening of the `α` triangular-plus-one charge, not an
immediate application of the large-sibling theorem.

## Maximum-two normalization closure

The paragraph above overlooked the more general upper-normalization theorem. In the unique
residual, the complement `α` has a synthetic chosen-side level `1` with
`α.maximumAt 1 = m = 2`, while `α.k = 6`; its maximum is exactly `α.k-4`.

`ctx_sibling_maximum_upper_normalize` at that level bounds every fuel approximation and the full
bound by a context whose chosen global is at most four, while preserving the opposite global.
The checked `ctx_small_global_axis_rank_pair_potential` bounds the normalized context by its
active opposite ordered-rank-pair union. That union lies in the full opposite-rank triangle and
therefore has cardinality `choose(oppositeGlobal,2)`. At opposite global five the complement
charge is ten. The already extracted retained component is at most `w-2=2`, closing the residual
as `10+2=12`.

This route needs neither convexity nor younger-exterior geometry for the complement charge. The
compiled mixed-capacity separation theorem remains reusable but is unnecessary for this exact
maximum-two closure.

## Opposite-kept block-cut closure

A proper member `keep ∈ σ.blocks` is an infix of the pairwise-increasing child-position list.
Consequently it is convex: any child position lying between two kept positions is itself kept.
Fixing one kept position then classifies each removed child as lying strictly before every kept
position or strictly after every kept position.

This yields an exhaustive three-way split for the backward/opposite-kept recurrence orientation:

- a removed child exists on each side, giving the internal-complement hypotheses;
- all removed children lie before the block, giving the left endpoint hypotheses; or
- all removed children lie after the block, giving the right endpoint hypotheses.

The compiled endpoint and internal-complement `k=6` theorems therefore compose into a uniform
twelve bound for every recurrence block, with both independent fuels and the full bound retained.
The remaining parent-facing work is the other recurrence orientation, where the chosen-side part
keeps the block.

## Extreme chosen-kept cut: large old maximum

For the chosen-kept extreme `k=6`, coupling forces the chosen new maximum to be `m=4` and the
opposite new maximum to be `n=1`. The synthetic chosen level therefore bounds the chosen part by
one through `ctx_bound_le_one_of_large_sibling_maximum`.

If an old chosen-axis level has maximum at least two, transport that level into the companion and
upper-normalize there. Its chosen global becomes at most `6-2=4`, while the opposite global stays
at most five. The saturated triangle estimate is then
`choose(6-2,2)+(6-1)=6+5=11`. Together with the unit chosen part, this gives twelve. The proof
does not depend on endpoint/internal geometry or on the opposite new maximum.

Hence the only remaining extreme branch has every old chosen-history maximum at most one. The
existing `ctx_extreme_next_cut_of_small_chosen_maxima_capacity_two` already identifies an active
companion child of chosen capacity at least three as the next residual condition (for its generic
13 target); the two-marker positional hypotheses must now be used to sharpen or eliminate that
witness for the exact twelve target.

## Extreme chosen-kept cut: small maxima and low capacities

The generic small-maxima wrapper also loses exact slack. At `k=6` and opposite global at most
five, the transported companion has opposite width at most four. If every active companion child
has chosen capacity at most two, `ctx_small_maxima_active_capacity_two_linear_potential` gives
the companion charge `3*4-2=10`. The chosen part is still at most one, so the full cut is at most
eleven.

Thus failure of the exact twelve conclusion in the all-small-history branch requires an active
companion child of chosen capacity exactly three. If active low-capacity children also occur, the
checked two-marker separation theorem places every high/low pair on opposite sides of the older
marker. If they do not, the checked all-active-capacity-three triangle theorem gives companion
charge ten. What remains is to formalize a mixed-support charge that uses the marker separation
without paying the high and low prunings independently.

## Exact mixed-support residual and low-arm normalization

The compiled residual classifier now makes the prior paragraph exact. The low-only branch is
bounded by ten through the small-maxima thin-rectangle potential. The high-only branch is bounded
by ten through the active boundary rank-pair triangle. Thus only simultaneous active high and low
support remains, and any such pair is separated by the older selected marker.

There is a useful nonfinal numerical consequence. Prune to all children whose chosen point
capacity is at most two. A fixed capacity-three witness and the universal older-marker separation
put every child of this pruning on the younger marker's side of the older marker. The exact
two-occurrence hypothesis puts all younger chosen positions there as well. Absorbing the older
marker therefore gives a context with chosen global at most four while retaining the younger
actual marker. The refined one-level exterior potential bounds that normalized context, and hence
the low-support pruning, by `2 * (oppositeGlobal - 1) - 1 <= 7`.

This does not close the mixed context by independent pruning addition—the high capacity-three
pruning can still cost ten—but it reduces the low arm from ten to seven and presents the precise
shared-charge problem for the next coupled potential.

## Exact disjoint-support closure

The low numerical bound is not the right invariant for coupling. The stronger compiled theorem
bounds the low pruning by its exact union of active opposite ordered-rank pairs. The high pruning
admits the same kind of exact charge: every high child lies beyond the older selected marker, and
there is no selected occurrence below that marker, so the active boundary pair theorem applies to
the high pruning at the older marker.

Both pair unions use the original opposite-axis history and therefore lie in the same ordered-pair
triangle on ranks `1,...,global-1`. Binary run decomposition bounds the source context by the sum
of the two pruning bounds. If their exact pair unions are disjoint, cardinalities add without loss
inside that triangle, giving `choose(global,2) <= choose(5,2)=10` for every fuel and the full
context.

Consequently the residual mixed case is no longer merely “both capacities occur.” Failure of the
ten bound forces a shared ordered rank pair: some active low child and some active high child have
two common opposite-rank interval values. Unpacking and exploiting that overlap is the next
mathematical obstruction.

## Exact pair-overlap excess

The disjointness hypothesis can be removed without weakening the pair charge. For the low and
high pair unions `P₀,P₁`, binary pruning and the two boundary arguments give

`bound <= |P₀| + |P₁|`.

Their union is contained in the complete opposite ordered-rank triangle, so
`|P₀ ∪ P₁| <= choose(global,2)`. The exact finite-set identity

`|P₀ ∪ P₁| + |P₀ ∩ P₁| = |P₀| + |P₁|`

therefore yields the compiled every-fuel and full bound

`bound <= choose(global,2) + |P₀ ∩ P₁|`.

At opposite global five, an intersection of cardinality zero gives the earlier ten bound, while
cardinality one gives eleven, exactly enough after adding the unit extreme chosen part. Thus any
remaining failure of the target cut bound must exhibit at least two distinct low/high shared
ordered rank pairs. This is the current sharp residual.

## One-collision companion closure

Specializing the exact excess theorem at opposite global at most five gives a reusable sharp
corollary. If the canonical low/high pair intersection has cardinality at most one, then every
fuel approximation and the full companion context are at most eleven:

`bound <= choose(global,2) + intersectionCard <= 10 + 1 = 11`.

This is exactly the companion budget needed beside the extreme chosen part of cost one. The next
composition should lift it into the actual `k=6`, `m=4` cut, after which the cut-level residual is
formally “at least two distinct pair collisions in the companion.”

## Cut-level one-collision closure

The companion corollary now composes with the actual extreme cut. A kept child produces the
companion's synthetic opposite-axis level one. The original two chosen markers transport to
levels `N+1,M+1`, with their positions and exact chosen history unchanged. Thus the companion
satisfies the hypotheses of the one-collision eleven-bound theorem.

Independently, `m+2=k=6` makes the synthetic chosen maximum of the kept part equal to `k-2`, so
the large-sibling-maximum theorem bounds that part by one. Therefore companion intersection
cardinality at most one gives the exact cut total `1+11=12`, for independent fuels and full
bounds, without assuming all old chosen maxima are small.

The remaining extreme-cut obstruction is now precise: at least two distinct ordered rank pairs
must be shared by the canonical active low- and high-capacity companion pair unions.

## Explicit two-collision cut residual

The cardinal obstruction is now exposed as witnesses. For every extreme cut satisfying the same
two-marker and high-witness hypotheses, either all independent-fuel and full sums are at most
twelve, or there are distinct ordered pairs `z != w` with both

`z,w ∈ P₀ ∩ P₁`.

Here `P₀` and `P₁` are exactly the canonical active low/high companion pair unions used by the
overlap-excess theorem. The next abstraction boundary is to unpack each membership into active
source children of capacity at most two and at least three, respectively, together with the four
common interval-membership facts for the pair coordinates.

## Source witnesses for a shared pair

The pruning abstraction has now been eliminated from an individual collision. Membership
`z ∈ P₀ ∩ P₁` yields source children `low` and `high` such that both are active in the
original context, their chosen capacities lie on opposite sides of the binary threshold,

`capacity low <= 2` and `3 <= capacity high`,

and both coordinates of `z` lie in each child's original-history opposite-rank interval. The proof
uses exact child-support, point-limit, and pure-history transport from the pruning theorem, so no
information is lost when returning from the low/high pruned contexts to the source.

This makes the two-collision residual geometric: each shared pair has a low/high source-child
witness pair. Under the exact two-marker assumptions, the existing mixed-capacity separator should
place those children on opposite sides of the older marker while preserving the four interval
memberships. That is the next reusable composition.

## Marker-separated collision geometry

The reusable composition is now compiled. Under the exact two-marker history and chosen global at
most five, every shared pair `z` has active source children `low,high` with low chosen capacity at
most two, high chosen capacity at least three, and one of the two orientations

`low < y < high` or `high < y < low`,

with the orientation determined by the order of the selected marker positions `x,y`. Both
coordinates of `z` still lie in the original-history opposite-rank intervals of both children.

Thus the unresolved cut branch is no longer an opaque finite-set overlap: it contains at least two
distinct ordered opposite-rank pairs, and each pair is realized by active children on opposite
sides of the older marker. A closing argument must exploit the distinctness of those pairs to force
extra rank spread or incompatible interval endpoints; cardinality bookkeeping alone is already
sharp at this stage.

## Actual-cut two-collision geometry

The two collision packages are now lifted through the real extreme recurrence cut. For `k=6` and
`m+2=k`, the compiled theorem gives the exact alternative

- all independently fueled and full cut sums are at most twelve; or
- there are distinct pairs `z != w` in the canonical low/high intersection, and both `z` and `w`
  have active low/high companion witnesses straddling the older marker, with each pair's two
  coordinates lying in both witness intervals.

No small-history-maximum assumption is used. The companion's synthetic opposite marker and both
original chosen markers are transported exactly, so this is a statement about the actual residual
of the target recurrence rather than a detached pruning model.

The remaining obstruction is therefore sharply geometric. A closure must show that two distinct
ordered rank pairs cannot both be realized across the older-marker split without either creating
additional rank spread (which can be charged) or forcing incompatible left/right extension
endpoints. Future work should operate on this explicit two-pair witness package, not return to the
coarser mixed-capacity or cardinality classifications.

## Pure-extension position monotonicity

The extension-fold monotonicity used locally throughout the rank-potential development is now an
exported theorem. If `p <= q`, then on every side and at every history cutoff

`leftExt(p) <= leftExt(q)` and `rightExt(q) <= rightExt(p)`.

Consequently both endpoints of the available rank interval move weakly right as the physical child
moves right. For two marker-separated collision packages, choose the later low child and the
earlier high child. Monotonicity then shows that both distinct collision pairs lie in both of these
selected intervals: the high witnesses control all lower endpoints, while the low witnesses
control all upper endpoints. This is the next formal composition and turns two separately
supported collisions into a common interval containing at least two distinct ranks.

## Common intervals for two straddling collisions

That composition is now compiled in both marker orientations. In the forward orientation the
selected endpoints are the later low witness and the earlier high witness; in the reverse
orientation they are the earlier low witness and the later high witness. Interval convexity under
physical position follows from pure-extension monotonicity, so every coordinate of both collision
pairs belongs to both selected source intervals.

Because the two ordered pairs are distinct, either their first coordinates differ or their second
coordinates differ. Thus the selected low and high intervals contain two named distinct ranks.
The theorem also records that each selected endpoint is one of the original collision witnesses.
This matters for the next charge theorem: activity and the low/high capacity split can be recovered
by cases on those identities instead of reproving any pruning transport.

The remaining obstruction has consequently narrowed again. It is no longer necessary to compare
four unrelated witness intervals. One must show that a marker-straddling active low/high source
pair whose two intervals share at least two distinct ranks forces an additional unit of budget or
an incompatible extension configuration. Such a theorem would compose directly with the actual
extreme-cut geometric residual.

## Two-rank triangle amplification

Two distinct common ranks generate three, not merely two, common nondecreasing ordered pairs: the
two diagonals and their sorted cross-pair. This elementary quadratic amplification is now a
standalone compiled lemma. Once source/pruning interval equality is reinstated, the two-collision
geometric residual therefore cannot have pair-intersection cardinality exactly two; it jumps to at
least three. The remaining contextual composition is transport rather than new counting.

## Cardinality-two collision overlap is impossible

The contextual transport is now compiled. Under the exact two-marker chosen-global-five
hypotheses, two distinct elements of the canonical low/high pair intersection produce
marker-separated source witnesses. Monotonicity selects one low and one high source interval
containing two distinct common ranks. The selected endpoint identities recover source activity and
the two capacity colors, while pruning transport identifies the selected source intervals with
their group intervals. Triangle amplification therefore places three pairs in the original
canonical intersection.

Thus the residual overlap spectrum has a genuine gap: `card <= 1` is already bounded by eleven,
while any failure of that case has `card >= 3`; `card = 2` cannot occur. The next proof must exploit
the common three-pair triangle to recover at least two units of slack from the separate low/high
pair-potential bounds. Pure inclusion-exclusion still overcounts this regime.

## Actual-cut three-pair residual

The cardinality gap is now exposed at the real recurrence cut. For `k=6` and `m+2=k`, with the
same chosen-capacity-three companion witness, the compiled alternative is:

- every independently fueled and full cut sum is at most twelve; or
- the companion's canonical low/high ordered-rank-pair intersection has cardinality at least
  three.

The proof reuses the companion transport of the original chosen markers and history, then invokes
the source-level gap theorem. This removes the intermediate existential collision packages from
the next consumer's interface. The remaining work is not another residual classification: it is
the strict pair-potential estimate needed when at least a full two-rank triangle is duplicated.

## Bounded check of the remaining strict-charge direction

The repository's retained abstract-context enumerator was run with the Lean-aligned recurrence
semantics at `(a,u,k)=(5,5,6)`, up to four children and two indexed external markers. Across 7,127
well-formed signatures and 64,062 tested partitions it found no additivity violation. This does not
certify the evaluator against Lean and does not isolate the exact pair-overlap premise, so it is
only negative evidence against an immediate small counterexample.

The proof audit also explains why the current library does not close the branch by composition.
The overlap-excess theorem gives `bound <= 10 + intersectionCard`, so `intersectionCard >= 3`
makes the coarse estimate worse, not better. The existing low-capacity seven-bound leaves the
high group eligible for the full ten-pair triangle. The separating-marker linear theorem requires
the active children and the older retained marker to lie on opposite sides of the younger marker;
the known capacity-three exterior geometry puts the high support on the same exterior side instead.
Thus the next useful result must couple the two pruning recursions or strengthen one boundary
potential using a collision witness. Pure finite-set inclusion-exclusion and the present one-group
bounds cannot recover the required two units of slack.

## Why the synthetic companion marker must remain in the theorem

A filtered bounded probe sharpened the preceding conclusion. In the retained Lean-aligned
semantics, the unconditional exact-two-marker statement is false: among signatures with at most
four children and no opposite history, forty mixed signatures have pair overlap at least three but
context value twelve. A minimal shape is

`S, 1L, 2L, S`, with sibling maxima `(1,1)`.

Both pruning pair sets are the full ten-pair triangle there. Therefore no Lean theorem of the form
"the hypotheses of `ctx_two_marker_two_pair_collision_intersection_three` plus overlap at least
three imply bound at most eleven" should be attempted without an additional premise.

The real extreme companion has exactly the missing structure: the selected part becomes an
opposite-axis level-one marker, and in the `m=4,n=1,k=6` case its sibling maximum is one. Repeating
the filtered probe with this mandatory marker, followed by the two shifted chosen-axis markers,
found 824 mixed residuals and no value above eleven. Overlap cardinalities were only three and six,
never ten. Yet extremal value-eleven signatures still have separate pair-set sizes `6+6` or
`6+9`, so endpoint exclusion alone plus inclusion-exclusion remains too weak.

The next formal target should consequently stay at the actual-cut interface (or state an explicit
level-one opposite-marker/max-one hypothesis) and prove a coupled recursion charge. The synthetic
marker forces every child interval to lose a left or right extreme rank according to its side of
that marker; the difficult equality cases then require sharing one charge across the two capacity
groups. Forgetting the synthetic marker recreates the bounded value-twelve counterexamples.

## Compiled synthetic-marker endpoint loss

The basic interval consequence is now exported in Lean. For an actual marker `x` on rank axis
`t` and any child `p`, child/marker disjointness gives exactly one of `x<p` and `p<x`. In the first
case the singleton marker level contributes one left extension, so every rank in the child's
interval is at least two. In the second it contributes one right extension, so every interval rank
`r` satisfies `r+2<=global`.

This theorem is intentionally structural rather than a claimed eleven-bound: the bounded extremal
examples show pair-set sizes `6+6` and `6+9`, so one-sided endpoint loss does not by itself pay the
sum of the two pruned group bounds. The next theorem must use this endpoint partition inside the
recursion, retaining the level-one maximum-one hypothesis and sharing the missing charge between
the low- and high-capacity groups.
