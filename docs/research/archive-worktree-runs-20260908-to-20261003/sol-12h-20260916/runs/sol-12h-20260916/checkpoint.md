# Sol/xhigh twelve-hour checkpoint

## Frozen run identity

- Worktree: `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916`
- Agent: `codex:agent-run-87535a41ec804a72`
- Thread: `01a0ab2e-b3cd-7e22-86e7-9ea28ebc6efb`
- Research deadline: `2026-09-17T05:05:59.810844Z`
- Consolidation begins: `2026-09-17T04:35:59.810844Z`
- Finalization hard stop: `2026-09-17T05:35:59.810844Z`
- Baseline source: `433d1b33`; prepared HEAD: `52e48fa2`
- Initial frontier: 251 closed, 12 open, one refuted; indexed tree `ea7bef4ca32b0635`

## Startup and ownership

- Read `RESEARCH-BRIEF.md`, `previous-mathematical-handoff.md`, `parent-context.json`, and the
  relevant declarations before proof work.
- Cache bootstrap job `20260916-125101-e0cb90` was still running at startup. Per the brief, no
  statement registration, tracked Lean edit, or compilation was attempted before its readiness
  receipt. Its transfer completed before an `rg` PATH failure; guarded recovery and validation are
  documented in `../setup-20260916/READY.md`.
- `es node show --json --full` reported the parent node's status as `claimed` but its authoritative
  `claim` field was null. This mismatch was logged. The parent was force-claimed for this exact host
  as agent `codex:agent-run-87535a41ec804a72`, expiring after the frozen research deadline.

## Search receipts

Before drafting the first component lemma:

- `es search "younger exterior internal complement cut component bound"` returned no result.
- `es search "younger exterior extreme maximum six"` returned no matching theorem (the only
  ranked result was the existing middle-residual classifier).
- Source search confirmed the intended facts exist only as local `hOwn` and `hOther` inside
  `ctx_two_marker_younger_exterior_internal_complement_cut_potential_bound`.

## First proof plan (source-verified)

Expose the two local estimates under exactly the potential theorem's hypotheses. Reuse:

- `ctx_part_positive_letters` for positivity of both `part` contexts;
- `ctx_three_ordered_markers_triangular_plus_one_bound` for the complement estimate;
- `ctx_active_separating_marker_retained_boundary_rank_union_bound` for the retained estimate.

The proof tail needed is lines 438--614 of
`CtxTwoMarkerYoungerExteriorInternalComplementCutPotentialBound.lean`. The older local copies of
the exported bounds at the start of that file are not needed. The intended theorem preserves
independent fuel quantification and both full-context bounds.

For the next legal `k = 6` corollary, the extreme reductions are source-valid in shape: level `1`
belongs to both part contexts, `part_maximumAt_one` gives maxima `m` and `n`, and
`ctx_bound_le_one_of_large_sibling_maximum` applies when `part.k - 2` is below that maximum.
With `σ.k = 6` and `m+n=5`, `m=1` gives `n=4` and a unit retained bound; `m=4` gives a unit
complement bound. Compilation remains to be checked after bootstrap readiness.

## Jobs

- `20260916-125101-e0cb90`: physical cache copy completed, then wrapper failed at missing `rg`.
- `20260916-131638-85c157`, `20260916-131714-6db7ab`: failed pre-mutation recovery attempts.
- `20260916-131744-a65e2f`: cache isolation/identity validation passed.
- `20260916-131802-18727d`: targeted baseline theorem check passed.
- `20260916-130525-4020c1`: durable native-goal host for this thread; running.

## Accepted results

### `ctx_two_marker_younger_exterior_internal_complement_cut_component_bounds`

- Type hash: `78de34c4f7fa181a` (matches the registered lock).
- Targeted check: job `20260916-132433-e4bbf5`, passed; build 3.69 seconds and 608 MiB
  peak in the check artifact `3bd88a217988225c4baf3e49bdc2e0505532be4d49c00dcfb310309d4408a693`.
- The targeted result is sorry-free, lock-valid, and has no nonstandard axioms.
- First full extraction attempt `20260916-132614-f88e9e` scanned all 15,608 modules but
  exceeded its undersized 30-minute/20G envelope before writing the index (1,824.9 seconds,
  20,480 MiB peak). It did not count as acceptance.
- Full extraction retry `20260916-135701-379475` passed on the unchanged tree in 502.9 seconds,
  with a 28,672 MiB peak, no problems, 265 nodes, 12,910 declarations, 17 destinations, and tree
  hash `664c20d92a701753`.
- Full-index state: theorem closed, sorry-free, lock-valid, and axioms exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- Mathematical content: exposes both the complement `choose(w+1,2)+1` component and retained
  `w-2` component, for every independent fuel and full bound, under exactly the original combined
  theorem's hypotheses.
- Commit: `e75b479d` (`Expose younger-exterior component bounds`). Claim released closed.

### `ctx_two_marker_younger_exterior_internal_complement_cut_six_bound_of_extreme_maximum`

- Type hash: `199744e9319d718b` (matches the registered lock).
- Targeted check: job `20260916-140958-8de097`, passed on the first implementation; check
  artifact `52f1620ee9d6b2e7d0f46f07d3a80173b5d8e6e3f52c80c23b176744eb506af8`.
- Full extraction: job `20260916-141133-ca1bf7`, passed with no problems, 266 nodes, 12,910
  declarations, 17 destinations, and tree hash `048f0c3f2d8ad09c`.
- Full-index state: theorem closed and lock-valid. The proof uses only the standard project axioms.
- Mathematical content: at `k=6`, the legal endpoint maxima `m=1` and `m=4` force the combined
  independent-fuel and full bounds to be at most twelve. The proof reuses the exposed component
  bounds and the large-sibling unit-bound lemma.
- Commit: `21d89b6d` (`Close younger-exterior extreme maxima`). Claim released closed.

### `ctx_two_marker_internal_complement_cut_six_top_width_both_middle_residual_classification`

- Search receipts: `es search "internal complement cut six top width both middle residual
  classification"` returned no result; `es search "younger exterior middle maximum
  classification m two m three"` returned only the strictly weaker existing classifier.
- Type hash: `77e9003bb7c320ec` (matches the registered lock).
- Targeted check: job `20260916-142346-d4354d`, passed on the first implementation; check
  artifact `50c8f40207843876c698cbc02e2eff29c5cfe3bc1f9a27c7bb866d073db19ef4`.
- Full extraction: job `20260916-142554-c7aed8`, passed with no problems, 267 nodes, 12,910
  declarations, 17 destinations, and tree hash `27304a692b0534f9`.
- Mathematical content: composes the previous saturated-width classifier with the new endpoint
  theorem, so both the older-surround and younger-exterior residuals now require `m=2` or `m=3`.
- Commit: `4162fc7f` (`Narrow internal-complement residual maxima`). Claim released closed; a
  journal correction records that the commit hash in the original release note was mistyped.

### `ctx_two_marker_internal_complement_cut_six_bound_of_maximum_three`

- Search receipts (before drafting): `es search "two marker internal complement maximum three
  bound twelve"` and `es search "two actual marker companion maximum m three internal cut"`
  returned no matching theorem.
- Type hash: `1e0176e552bc3606` (matches the registered lock).
- First targeted check `20260916-143801-9298a5` failed only because `omega` did not unfold a
  constructor-specialized opposite-global `match`; explicit simplification repaired it.
- Targeted check `20260916-143839-50652f` then passed; check artifact
  `2306d60243e812bcc8922b2c2250d34da0c824845911cad3d830a9789a37a87e`.
- Full extraction: job `20260916-144106-bf5e46`, passed with no problems, 268 nodes, 12,910
  declarations, 17 destinations, and tree hash `bfb63e3b0135c473`.
- Mathematical content: with no positional, convexity, or clear-history hypothesis, `m=3`
  gives a complement charge at most four and, through double-complement companion transport,
  a retained charge at most eight. Both full and independently fueled sums are at most twelve.
- Commit: `0e7d7135` (`Close maximum-three internal cut`). Claim released closed.

### `ctx_two_marker_internal_complement_cut_six_top_width_maximum_two_residual_classification`

- Search receipts: `es search "internal complement cut six top width maximum two residual
  classification"` returned only the two weaker classifiers; `es search "two marker only m two
  residual both geometries"` returned no result.
- Type hash: `c1d28097e95b14` (matches the registered lock).
- Targeted check: job `20260916-145250-e0ddba`, passed on the first implementation; check
  artifact `cf5cd7942eb97dabde154b1b490e2b7d2eac4b3eb6390db4afb2a555f23b48bb`.
- Full extraction: job `20260916-145522-1e453f`, passed with no problems, 269 nodes, 12,910
  declarations, 17 destinations, and tree hash `26fd5e9031643557`.
- Mathematical content: every legal internal-complement cut is now discharged unless the opposite
  global is exactly five and `m=2`; the remaining geometry is explicitly older-surround or
  younger-exterior. Thus the residual also has `n=3` by legal coupling.
- Commit: `e320d72b` (`Isolate maximum-two internal residual`). Claim released closed.

### `ctx_two_marker_older_surrounding_internal_complement_cut_six_bound_of_maximum_two`

- Search receipts: `es search "older surrounding internal complement cut maximum two bound
  twelve"` returned only the older extreme theorem and the new residual classifier;
  `es search "surrounded older marker complement doubled width component companion maximum
  three"` returned no result.
- Type hash: `13c696a8e38eba0c` (matches the registered lock).
- Targeted check: job `20260916-150756-9d2087`, passed on the first implementation; check
  artifact `72fdab44f0c56e1ad31b00a47d4fc29dcc4a7b264c85006d870808ac3d3fc65f`.
- Full extraction: job `20260916-150957-6ba730`, passed with no problems, 270 nodes, 12,910
  declarations, 17 destinations, and tree hash `70b5ce22320c82a9`.
- Mathematical content: the older-surround `m=2`, `n=3` case is closed exactly. The complement
  doubled-width theorem gives at most eight, and the sharp double-complement companion theorem
  gives the retained part at most four. No clear-history, width-lower-bound, or second-boundary
  hypothesis is needed.
- Commit: `b6f27203` (`Close older-surround maximum-two cut`). Claim released closed.

### `ctx_two_marker_internal_complement_cut_six_top_width_younger_exterior_maximum_two_residual_classification`

- Search receipts: `es search "top width younger exterior maximum two residual classification
  internal complement"` returned only the weaker classifiers; `es search "only younger exterior
  m two residual"` returned no result.
- Type hash: `e830354adea68bd3` (matches the registered lock).
- Targeted check: job `20260916-152210-de216b`, passed on the first implementation; check
  artifact `d53d3119af49039e6d1d583dc5e6123d604cdd45c81b38455ace6b67491cd611`.
- Full extraction: job `20260916-152443-b1be37`, passed with no problems, 271 nodes, 12,910
  declarations, 17 destinations, and tree hash `e71a9c5a5aa2df3a`.
- Mathematical content: the formal internal-complement residual is now unique: opposite global
  exactly five, complement maximum `m=2` (hence retained maximum `n=3`), and the kept block
  exterior to the younger marker away from the older marker.

### `ctx_two_marker_younger_exterior_complement_mixed_capacities_separated_by_older_marker`

- Search receipts: the three pre-draft searches for younger-exterior mixed-capacity separation
  returned no matching theorem.
- Type hash: `b864427f6fae914b` (matches the registered lock).
- Targeted check: job `20260916-155348-fff097`, passed.
- Full extraction: job `20260916-155524-f2a4ab`, passed in 478.1 seconds at 5,387 MiB peak, with
  no problems, 272 nodes, 12,910 declarations, 17 destinations, and tree hash
  `03615506ffc40f3d`.
- Full-index state: theorem closed and lock-valid, with only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Mathematical content: in the unique younger-exterior complement, the transported older marker
  separates every chosen-capacity-three child from every chosen-capacity-at-most-two child, even
  though the new level-one marker block has arbitrary size.
- Commit: `4ccf71da` (`Separate younger-exterior mixed capacities`). Claim released closed.

### `ctx_small_global_axis_opposite_binomial_bound`

- Type hash: `c10151b63dae762f`; targeted check `20260916-160642-75bf19` passed.
- Full extraction `20260916-160803-809a48` passed with no problems and tree hash
  `b8a2b36bd6e4ab70`.
- Mathematical content: chosen global at most four bounds every fuel and the full context by the
  full opposite rank-pair triangle `choose(oppositeGlobal,2)`.
- Commit: `602f2541` (`Export global-four opposite triangle bound`).

### `ctx_chosen_sibling_maximum_opposite_binomial_bound`

- Type hash: `75543650732252e9`; targeted check `20260916-161820-c15010` passed.
- Full extraction `20260916-161938-bd0c38` passed with no problems, 274 nodes, and tree hash
  `c0970b159a5bc122`.
- Mathematical content: a chosen-side sibling maximum at least `k-4` normalizes the chosen global
  to at most four without changing the opposite global, giving the opposite-binomial bound.
- Commit: `1611b971` (`Normalize chosen sibling maximum to triangle`).

### `ctx_two_marker_younger_exterior_internal_complement_cut_six_bound_of_maximum_two`

- Searches for a maximum-two younger-exterior bound and the normalization composition found no
  matching theorem.
- Type hash: `802c9ab1deb9ab8e`; targeted check `20260916-163135-a5e97f` passed.
- Full extraction `20260916-163317-dd4907` passed with no problems, 275 nodes, and tree hash
  `3e4df07f9d1de569`.
- Mathematical content: at the synthetic complement level, `m=2=k-4` gives `α≤10`; the existing
  younger-exterior component theorem gives `β≤2`. Hence both independently fueled and full sums
  are at most twelve.
- Commit: `c3d2e235` (`Close younger-exterior maximum-two residual`).

### `ctx_two_marker_internal_complement_cut_six_bound`

- Search receipts: `es search "uniform two marker internal complement cut six bound twelve"`
  returned no results; `es search "internal complement cut six no residual"` found only the
  distinct older-exterior theorem.
- Type hash: `c8bc6115d3a530e6`; targeted check `20260916-164528-5443c6` passed on the first proof.
- Full extraction `20260916-164816-b9fbbb` passed with no problems, 276 nodes, and tree hash
  `b1e9764e740a199a`.
- Mathematical content: the complete residual classifier and maximum-two closure yield a uniform
  bound of twelve for every legal two-marker internal-complement cut at `k=6`, both globals at
  most five, and opposite width at least two.
- Commit: `0ab8709d` (`Close all two-marker internal k-six cuts`).

### `ctx_two_marker_opposite_kept_block_cut_six_bound`

- Search receipts: `es search "two marker opposite kept block cut six bound"` found only the
  constituent internal residual theorems; `es search "block endpoint internal complement k
  six"` found no matching package theorem.
- Type hash: `9d6e22634a9072a4`; targeted check `20260916-170402-b35869` passed on the
  first implementation.
- Full extraction `20260916-170648-5450b5` passed in 477.0 seconds at 6,011 MiB peak, with no
  problems, 277 nodes, 12,910 declarations, 17 destinations, and tree hash
  `b1fd038c400f8351`.
- Mathematical content: a proper contiguous recurrence block is convex in the sorted child
  positions. Its complement is therefore wholly on the left, wholly on the right, or has
  witnesses on both sides. The two endpoint cases are discharged by
  `ctx_two_marker_endpoint_cut_six_bound`; the two-sided case is discharged by
  `ctx_two_marker_internal_complement_cut_six_bound`. Thus every opposite-kept block cut at
  `k=6` has independently fueled and full sums at most twelve.
- Commit: `fe1a819f` (`Prove two-marker opposite-kept block cuts at k=6`).

### `ctx_extreme_cut_six_twelve_of_large_chosen_history_maximum`

- Search receipts: `es search "extreme cut six twelve large chosen history maximum"` and
  `es search "k six large chosen maximum one plus eleven cut"` found no matching theorem.
- Type hash: `96a33cf8c8959a7d`; targeted check `20260916-172204-669034` passed on the
  first implementation.
- Full extraction `20260916-172443-57c484` passed with no problems, 278 nodes, 12,910
  declarations, 17 destinations, and tree hash `16a8f0199e0374da`.
- Mathematical content: at `k=6`, an extreme new chosen maximum `m=4` bounds its part by one.
  If any old chosen-axis maximum is at least two, normalizing the companion at that level gives
  chosen global at most four; the saturated triangle theorem bounds the companion by
  `choose(4,2)+5=11`. Thus every independent-fuel and full sum is at most twelve, for arbitrary
  kept lists and arbitrary opposite new maximum.
- Commit: `9a9c5df2` (`Sharpen large-history k-six extreme cut`).

### `ctx_extreme_cut_six_eleven_of_small_chosen_maxima_capacity_two`

- Search receipts: `es search "extreme cut six eleven small chosen maxima capacity two"` and
  `es search "k six all maxima one active companion capacity two eleven"` found no matching
  theorem.
- Type hash: `dcee70109f1baf50`; the first targeted check
  `20260916-173702-e08a2d` found one definitional `B.k` rewrite issue. After routing the bound
  through `σ.k-5`, targeted check `20260916-173720-aba3a1` passed.
- Full extraction `20260916-174004-00216e` passed with no problems, 279 nodes, 12,910
  declarations, 17 destinations, and tree hash `e4a64b071007dea9`.
- Mathematical content: the extreme chosen part costs one. When every old chosen maximum is at
  most one and every active companion child has chosen capacity at most two, the checked
  small-maxima linear potential costs at most `3*(5-1)-2=10`; the exact cut total is therefore
  eleven, one below the required twelve.
- Commit: `1e18fa9b` (`Sharpen small-history capacity-two extreme cut`).

### `ctx_extreme_cut_six_small_history_mixed_capacity_residual_classification`

- Search receipts: `es search "extreme cut six small history mixed capacity residual
  classification"` and `es search "companion high low separated older marker extreme eleven"`
  returned no results.
- Type hash: `8cf6c47b88eb7a22`; targeted check `20260916-175347-87cff4` passed on
  the first implementation.
- Full extraction `20260916-175630-57e5b1` passed with no problems, 280 nodes, 12,910
  declarations, 17 destinations, and tree hash `38019e0265a2b504`.
- Mathematical content: the low-only companion branch closes at ten, and the all-high branch
  closes at the opposite rank triangle, also at ten. Therefore failure of the stronger cut
  bound eleven requires both an active chosen-capacity-at-least-three child and an active
  chosen-capacity-at-most-two child. The older selected marker separates those witnesses in the
  orientation forced by the two selected marker positions.
- Commit: `85392b3c` (`Classify mixed-capacity extreme residual`).

### `ctx_two_marker_low_capacity_pruning_seven_bound_of_high_witness`

- Searches for a low-capacity pruning seven bound, an older-boundary normalization version, and
  an exact pair-support version found no matching theorem.
- Type hash: `fff13a04ee44a52d`. Initial targeted check `20260916-181640-ef633a`
  exposed only a substituted-name error and an unexpanded record projection; targeted check
  `20260916-181715-590953` passed after those local repairs.
- Full extraction `20260916-181854-927555` passed with no problems, 281 nodes, 12,910
  declarations, 17 destinations, and tree hash `4e408b8812aae02f`.
- Mathematical content: canonically prune to every source child of chosen capacity at most two.
  A fixed capacity-three witness forces that entire pruning to the younger-marker side of the
  older marker. The retained-boundary doubled-rank theorem then normalizes the chosen global to
  four while retaining the younger actual marker, giving
  `2*(oppositeGlobal-1)-1 <= 7`. No `k`, maximum, or activity hypotheses are needed.
- Commit: `b35292cd` (`Bound low-capacity two-marker pruning by seven`).

### `ctx_two_marker_low_capacity_pruning_rank_pair_bound_of_high_witness`

- Exact searches for the low-capacity pruning pair bound and mixed pair-overlap obstruction found
  no matching theorem.
- Type hash: `c202af6df437385a`; targeted check `20260916-183819-b4c7a3` passed on
  the first proof.
- Full extraction `20260916-183954-5c88e7` passed with no problems, 282 nodes, 12,910
  declarations, 17 destinations, and tree hash `37044820aaf9fe35`.
- Mathematical content: the same high-witness/older-marker geometry bounds the canonical low
  pruning by its exact union of active opposite ordered-rank pairs. Unlike the numerical-seven
  corollary, this theorem requires no opposite-global bound and retains the original active set,
  so pair overlap with the high pruning remains visible.
- Commit: `b445cf15` (`Expose exact low-support pair bound`).

### `ctx_two_marker_mixed_capacity_disjoint_pair_support_ten_bound`

- Exact searches for a mixed-capacity disjoint pair-support bound and binary-capacity ordered-pair
  union found no matching theorem.
- Type hash: `eec51e0372ffecb2`. The first two targeted checks
  (`20260916-185946-85b130`, `20260916-190043-c6a528`) exposed only local elaboration issues;
  targeted check `20260916-190138-b1c17b` then passed.
- Full extraction `20260916-190313-12956a` passed in 477.1 seconds at 5,454 MiB peak, with
  no problems, 283 nodes, 12,910 declarations, 17 destinations, and tree hash
  `a3279486f7188a62`.
- Mathematical content: split physical child runs at chosen capacity two. The exact low-support
  pair theorem bounds the low pruning, while the capacity-three exterior geometry makes the high
  pruning boundary-ready at the older marker and bounds it by its own exact opposite ordered-pair
  union. If those two unions are disjoint, their cardinalities add inside the single global
  opposite-rank triangle, of size at most `choose(5,2)=10`. Hence every fuel approximation and
  the full companion context are at most ten.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
- Commit: `b55e1455` (`Bound disjoint mixed-capacity pair supports`).

### `ctx_two_marker_mixed_capacity_pair_overlap_excess_bound`

- Exact searches for a mixed-capacity overlap-excess theorem and a binary-pruning intersection
  cardinality bound found no matching theorem.
- Type hash: `331b9ab5270a6fd0`; targeted check `20260916-192331-b83058` passed on
  the first proof.
- Full extraction `20260916-192506-24fc3a` passed in 482.1 seconds at 5,385 MiB peak, with
  no problems, 284 nodes, 12,910 declarations, 17 destinations, and tree hash
  `ad12f9fb2c1283e0`.
- Mathematical content: without any opposite-global cap, binary low/high pruning bounds the
  source by the sum of the two exact active pair-union cardinalities. Their union lies in the
  complete opposite ordered-rank triangle; `card_union_add_card_inter` then shows that the only
  excess over `choose(oppositeGlobal,2)` is exactly the cardinality of the low/high pair
  intersection. At opposite global five, exceeding companion bound eleven therefore requires at
  least two distinct shared ordered pairs.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
- Commit: `ac94fa0b` (`Measure mixed-capacity pair overlap excess`).

### `ctx_two_marker_mixed_capacity_pair_intersection_one_eleven_bound`

- Exact searches for a two-marker mixed-capacity intersection-one eleven bound found no matching
  theorem.
- Type hash: `ef07e35c4a17a2ba`; targeted check `20260916-193629-f77421` passed on
  the first proof.
- Full extraction `20260916-193807-7ef8cd` passed in 479.2 seconds at 5,380 MiB peak, with
  no problems, 285 nodes, 12,910 declarations, 17 destinations, and tree hash
  `eded9d358dea8a47`.
- Mathematical content: at opposite global at most five, the exact overlap-excess theorem gives
  `bound <= choose(global,2)+intersectionCard <= 10+1=11` whenever the canonical low/high
  active ordered-pair unions intersect in at most one pair. Every fuel approximation and the full
  context satisfy the bound, so any remaining failure has at least two distinct pair collisions.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
- Commit: `2d1497d6` (`Close one-pair mixed-capacity overlap`).

### `ctx_extreme_cut_six_twelve_of_pair_intersection_one`

- Exact searches for an extreme-cut pair-intersection-one closure and a unit-part/companion-eleven
  composition found no matching theorem.
- Type hash: `f7274db185e85743`. Two registration attempts failed only because the nested
  statement `let`s needed explicit function types. Targeted checks
  `20260916-195038-fad3f5` and `20260916-195412-35c3a4` exposed local proof-dependent match
  conversion issues; targeted check `20260916-195757-8c8c11` passed after side normalization.
- Full extraction `20260916-195938-3eee7a` passed in 480.4 seconds at 5,589 MiB peak, with
  no problems, 286 nodes, 12,910 declarations, 17 destinations, and tree hash
  `73d86820828a186d`.
- Mathematical content: transport the exact two chosen markers and chosen history into the
  companion part `B`. Its canonical low/high pair intersection of cardinality at most one gives
  `B<=11`. The extreme relation `m+2=k=6` makes the chosen part `A<=1`, so every independent-fuel
  and full cut sum is at most twelve. No old-history-maximum assumption is required.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
- Commit: `627c262c` (`Lift one-pair closure to extreme cut`).

### `ctx_extreme_cut_six_two_pair_collision_residual_classification`

- Exact searches for an extreme-cut two-distinct-pair residual classifier found no matching
  theorem.
- Type hash: `83f6df93418c5513`; targeted check `20260916-201221-2cff30` passed on
  the first proof.
- Full extraction `20260916-201400-920aaa` passed in 476.7 seconds at 5,372 MiB peak, with
  no problems, 287 nodes, 12,910 declarations, 17 destinations, and tree hash
  `c78a2766e75439a1`.
- Mathematical content: split on whether the companion low/high active ordered-pair intersection
  has cardinality at most one. The small branch is the accepted twelve-bound cut theorem. In the
  residual, `Finset.one_lt_card` produces two named, distinct pairs belonging to both exact pair
  unions. This converts the numeric overlap obstruction into concrete witnesses.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
- Commit: `c6ca74b3` (`Expose two-pair extreme-cut residual`).

### `ctx_binary_capacity_pair_intersection_source_witnesses`

- Exact searches for binary-capacity pair-intersection source witnesses and shared ordered-rank
  pair witnesses returned no matching theorem.
- Type hash: `82273b794f7a6210`; targeted check `20260916-202532-139225` passed on the
  first proof.
- Full extraction `20260916-202619-c4f9b2` passed with no problems, 288 nodes, 12,910
  declarations, 17 destinations, and tree hash `2bab74337da12f58`.
- Mathematical content: every ordered pair shared by the canonical low/high active pair unions
  has explicit source-active witnesses `low` and `high`. Their chosen capacities satisfy
  `capacity low <= 2` and `3 <= capacity high`, and both coordinates of the shared pair lie in
  both original-history opposite-rank intervals. This removes the pruning abstraction from the
  collision residual.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
- Commit: `92a77dc6` (`Expose source witnesses for pair collisions`).

### `ctx_two_marker_pair_collision_source_separated`

- Exact searches for two-marker collision witnesses separated by the older marker returned no
  matching theorem.
- Type hash: `b214b659b655ebf9`. Targeted checks `20260916-203739-705358` and
  `20260916-203835-dd0913` exposed dependent-match normalization and heartbeat costs;
  `20260916-203903-a60429` timed out under broad context normalization. After replacing that
  tactic with explicit lower/upper branches, check `20260916-204318-4582ca` passed.
- Full extraction `20260916-204450-a2debe` passed with no problems, 289 nodes, 12,910
  declarations, 17 destinations, and tree hash `bffadf00ca01e935`.
- Mathematical content: under exact two-marker chosen history and chosen global at most five,
  each low/high pair collision has source-active capacity witnesses straddling the older marker.
  The same result retains both shared pair coordinates in both original-history opposite-rank
  intervals, exposing positional and rank geometry simultaneously.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
- Commit: `c3a6b225` (`Separate source witnesses for pair collisions`).

### `ctx_extreme_cut_six_two_pair_geometric_residual_classification`

- Exact searches for an extreme-cut two-pair geometric residual and two marker-separated
  collision packages returned no matching theorem.
- Type hash: `e75a7360b8f792be`. Several targeted checks exposed only elaboration issues at
  the large nested-`let` interface: `20260916-205658-718f81`,
  `20260916-210154-8d6332`, `20260916-210736-6cc338`,
  `20260916-211501-a64fd1`, `20260916-212641-d75b7e`,
  `20260916-213349-89aa4c`, and `20260916-214111-833569`. The decisive repair was to
  split the opposite side before normalizing collision memberships, reducing the successful
  check `20260916-215002-439e4f` to about 75 seconds.
- Full extraction `20260916-215140-9ad749` passed with no problems, 290 nodes, 12,910
  declarations, 17 destinations, and tree hash `4c91e90adbacb417`.
- Mathematical content: the actual extreme `k=6` cut now has a complete geometric dichotomy.
  Either all independent-fuel and full cut sums are at most twelve, or the companion contains two
  distinct shared ordered-rank pairs, each realized by active source children of chosen capacities
  at most two and at least three that straddle the older marker, with both coordinates in both
  original-history intervals.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
- Commit: `8c0ed5bb` (`Expose geometric two-collision cut residual`).

### `ctx_pure_extensions_position_monotone`

- Exact searches for pure-extension monotonicity in physical position returned no exported
  theorem, although the fold argument was duplicated locally in several potential modules.
- Type hash: `5152d30fbad865d6`; targeted check `20260916-220409-ccc189` passed on
  the first proof.
- Full extraction `20260916-220508-3b2f2f` passed with no problems, 291 nodes, 12,910
  declarations, 17 destinations, and tree hash `968898656d9dae1a`.
- Mathematical content: for every context, side, history cutoff, and positions `p<=q`,
  `leftExt p <= leftExt q` while `rightExt q <= rightExt p`. This exports the fold
  monotonicity needed to compare and cross-combine collision intervals supported by different
  marker-separated witness children.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
- Commit: `135fac25` (`Export pure extension position monotonicity`).

### `CtxTwoStraddlingPairCollisionsCommonWitnessIntervals`

- Exact searches for two straddling pair collisions with common witness intervals and for
  cross-combining collision intervals with distinct ranks returned no matching theorem.
- Type hash: `de0b0cca7b251438`; targeted check `20260916-222053-0bc83c` passed on
  the first proof.
- Full extraction `20260916-222148-f9354b` passed in 482.7 seconds at 5,415 MiB peak,
  with no problems, 292 nodes, 12,910 declarations, 17 destinations, and tree hash
  `9c8935e0d68ca7a6`.
- Mathematical content: if two distinct ordered-rank collisions each have source intervals whose
  endpoints straddle the same marker in the same orientation, extension monotonicity selects one
  low and one high endpoint from the original witnesses so that all four collision coordinates
  lie in both selected intervals. Pair distinctness supplies two distinct ranks common to both
  selected intervals. Endpoint identities are retained for later transfer of activity and
  capacity facts.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
- Commit: `71b7db83` (`Cross-combine two straddling pair collisions`).

### `rank_pair_triangle_intersection_card_ge_three_of_two_common_ranks`

- Exact searches for two common ranks forcing three shared ordered pairs returned no matching
  theorem.
- Type hash: `b3f8d57c2f89ac3a`. Check `20260916-223419-c51795` exposed only a
  reversed-orientation pair-distinctness simplification; targeted check
  `20260916-223441-59ed83` passed after supplying the oriented inequality.
- Full extraction `20260916-223522-fd980e` passed in 477.0 seconds at 5,904 MiB peak,
  with no problems, 293 nodes, 12,910 declarations, 17 destinations, and tree hash
  `b19a271e6f60f766`.
- Mathematical content: if two finite rank sets share distinct ranks `r,r'`, their
  nondecreasing ordered-pair triangles share the two diagonal pairs and the sorted cross-pair.
  Hence their pair-intersection cardinality is at least three.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
- Commit: `9e00e6e3` (`Amplify two common ranks to three pairs`).

### `ctx_two_marker_two_pair_collision_intersection_three`

- Exact searches for a two-marker theorem ruling out canonical pair-intersection cardinality two
  returned only the existing intersection-at-most-one eleven-bound, not this structural converse.
- Type hash: `a7cc2bb327b83ca5`. Checks `20260916-224716-59487f`,
  `20260916-224745-4b689d`, `20260916-225001-24622b`, and
  `20260916-225328-e0f3cc` exposed first a heartbeat ceiling and then proof-dependent `match`
  normalization at the nested pruning interface. Using a non-generalizing side match produced the
  successful check `20260916-225757-dc63fb`.
- Full extraction `20260916-225934-da5cf1` passed in 480.6 seconds at 5,383 MiB peak,
  with no problems, 294 nodes, 12,910 declarations, 17 destinations, and tree hash
  `e22813c0ab208878`.
- Mathematical content: in the exact two-marker chosen-global-five context, any two distinct
  members of the canonical low/high capacity-pruning pair intersection cross-combine to two
  distinct ranks in one low and one high source interval. Exact pruning transport and triangle
  amplification put three distinct ordered pairs back in the canonical intersection. Therefore
  intersection cardinality two is impossible.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
- Commit: `c201c0c1` (`Rule out two-pair marker collisions`).

### `ctx_extreme_cut_six_pair_intersection_three_residual_classification`

- Exact searches for an extreme-cut overlap-at-least-three residual found only the prior theorem
  exposing two distinct collisions, not the sharpened cardinal conclusion.
- Type hash: `b609724c42011c14`; targeted check `20260916-231128-4cd541` passed on
  the first proof.
- Full extraction `20260916-231308-5f6b3b` passed in 478.3 seconds at 5,388 MiB peak,
  with no problems, 295 nodes, 12,910 declarations, 17 destinations, and tree hash
  `4796b829e57e30d2`.
- Mathematical content: the actual extreme chosen-kept `k=6` cut now has the direct dichotomy
  that all independent-fuel and full sums are at most twelve, or the companion's canonical
  low/high pair intersection has cardinality at least three. The proof transports the two-marker
  hypotheses into the companion and applies the source-level impossibility of cardinality two.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
- Commit: `12fdc631` (`Lift three-pair residual to extreme cut`).

## Open work

The full opposite-kept recurrence orientation is packaged. In the chosen-kept `k=6` extreme
`m=4,n=1`, sources with an old chosen maximum at least two close at twelve. In the all-small-maxima
branch, the low-only and high-only companions both close at cut total eleven. The remaining branch
has both active chosen-capacity-three and chosen-capacity-at-most-two support, separated by the
older marker. Binary capacity pruning now closes the whole companion at ten whenever the exact
low/high active opposite ordered-pair unions are disjoint. Thus pair overlap is the sole remaining
mixed-support obstruction. More sharply, the exact excess theorem bounds the companion by ten
plus the pair-intersection cardinality, and the intersection-at-most-one case is now lifted to the
actual extreme cut: the companion costs eleven and the chosen part costs one. Thus any remaining
failure of the twelve bound requires at least two distinct shared ordered pairs in the companion.
The actual extreme-cut residual now supplies two distinct collision values together with both full
geometric witness packages. Each collision has source-active low/high companion children, common
original-history rank intervals, and children on opposite sides of the older marker. The remaining
mathematical target is an incompatibility or strengthened charge showing that two distinct ordered
pairs inside these common intervals force enough endpoint/rank spread to close the cut at twelve.
The two collision packages can now be cross-combined into a single selected low/high interval
pair containing at least two distinct ranks, and this geometry has been transported back to the
canonical pruned pair sets. Consequently the overlap cardinality jumps from the closed range
`<=1` directly to `>=3`; the value two is impossible. The remaining mathematical target is a
strict pair-potential saving in the `>=3` overlap regime, strong enough to bound the companion by
eleven despite the duplicated triangle pairs. This sharpened residual is now lifted through the
actual extreme cut, so subsequent work can begin directly from the `>=3` companion overlap.

## Bounded recurrence diagnostic after the three-pair reduction

- Reused the catalogued abstract-context enumeration and Lean-aligned recursive evaluator; no new
  script or workflow glue was written.
- An initially admitted five-child run, `20260916-232614-4001ee`, was cancelled cleanly after the
  retained benchmark showed that the comparable historical sweep required about four hours and
  could not finish before the frozen consolidation deadline.
- The deadline-sized replacement, `20260916-233503-c02de0`, exhaustively tested `(a,u,k)=(5,5,6)`
  with at most four children, two external positions, two indexed levels, unused levels included,
  and Lean-aligned zero-child arithmetic. It completed in 337.7 seconds at 34 MiB peak.
- The resulting 7,127 well-formed contexts and 64,062 nontrivial partitions had zero additivity
  violations. The slack histogram was `0:62170, 1:1156, 2:132, 3:592, 4:12`.
- This is falsification evidence only, not kernel proof credit and not an equivalence theorem for
  Lean `Context.bound`. It supports continuing to seek a coupled strict charge; it does not justify
  asserting the missing `>=3`-overlap-to-eleven theorem.

## Filtered overlap falsifier and corrected next target

- A run-local probe composed the catalogued context enumerator, limit matrices, and Lean-aligned
  recursive evaluator to test the exact canonical capacity split and pair-overlap predicate. The
  final audited run was `20260916-234719-bc184a` (78.8 seconds, 35 MiB); its output is
  `two-marker-overlap-final-s4-lean.json`.
- On 1,984 bare exact two-marker signatures with at most four children, all 128 mixed signatures
  had overlap at least three. Forty had recursive value twelve (maximum twelve), refuting the
  proposed unconditional implication `overlap >= 3 -> bound <= 11` in the retained semantics.
  The smallest recorded shape is `S,1L,2L,S` with maxima `(1,1)` and full ten-pair overlap.
- The actual extreme companion necessarily retains a synthetic opposite-axis level-one marker of
  maximum `n=1`. On 12,480 minimal signatures with that marker plus the two shifted chosen-axis
  markers, all 824 mixed/overlap residuals had recursive value at most eleven. Their overlaps were
  exactly three or six; the bound histogram was `6:224, 7:52, 8:80, 9:416, 11:52`.
- Extremal value-eleven examples show why separate pair-cardinality bounds still do not suffice:
  their low/high pair-set sizes include `6+6` with overlap three and `6+9` with overlap six.
- These are diagnostic model results, not Lean theorem credit. They nevertheless falsify the broad
  research direction and isolate the safest next statement: a cut-specific coupled bound that
  preserves the synthetic level-one opposite marker and `maximumAt 1 = 1`, rather than applying a
  theorem to the companion after forgetting its construction.
- A requested extension of the filtered domain to five children, job
  `20260917-000224-ed58a0`, was cancelled at the predeclared 00:25 EDT stop after remaining
  nonterminal for about twenty-three minutes. Its output file is empty and carries no result; the
  completed four-child run remains the audited diagnostic boundary.

### `ctx_actual_marker_opposite_rank_interval_endpoint_exclusion`

- Exact search for an actual opposite marker forcing rank-interval endpoint exclusion returned no
  exported theorem.
- Type hash: `a5cecb39bcbadb6d`. Checks `20260916-235052-8f9ecb`,
  `20260916-235109-3d3741`, and `20260916-235136-52c963` exposed only dependent-match and
  simplifier normalization issues; targeted check `20260916-235158-9a1fd5` passed.
- Full extraction `20260916-235247-bb4e2b` passed in 478.9 seconds at 5,862 MiB peak, with
  no problems, 296 nodes, 12,910 declarations, 17 destinations, and tree hash
  `acd8e08828fb7257`.
- Mathematical content: relative to any actual marker on the rank axis, every child lies strictly
  to one side. A child to the marker's right has left extension at least one, so every available
  rank is at least two. A child to its left has right extension at least one, so every available
  rank `r` satisfies `r+2 <= global`. This is the exact endpoint loss contributed by the actual
  extreme companion's synthetic marker.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.
- Commit: `13bf3cd8` (`Export actual-marker rank endpoint exclusion`).

## Finalization

- Research admission stopped at the frozen `2026-09-17T05:05:59.810844Z` deadline; no research
  was started afterward.
- Consolidation review artifact:
  `9e0334a07915ba705b6496701822b4aa9984b91b641444881f8011c919806779`.
- Paused-goal finalization review artifact:
  `4be31e0952d1f142f426d4ea97db972af5d550428f0b2b213cd505527b7f01db`.
  It inventories 249 jobs, the prepared-head-to-`13bf3cd8` tracked boundary, the run-local probe,
  and the final successful check/extract lifecycle entries. Its explicit-proof list is empty
  because this run used `es check` plus guarded extraction rather than `es proof`; theorem credit
  is supplied by `verified-results.json` and the checks/extracts above.
- Usage synced through `2026-09-17T05:08:31.839Z`: 345,701,715 input tokens (342,451,584
  cached), 731,517 output tokens, and 181,146 reasoning-output tokens across 2,414 records, with
  zero reconciliation delta.
- The parent claim was released `partial`. Final frontier: 283 closed, 12 open, one refuted, no
  claims. Queued and starting job lists are empty; durable observer `20260916-130525-4020c1`
  remains live only until native-goal completion.
- Compact handoff: `REPORT.sol.md`.
