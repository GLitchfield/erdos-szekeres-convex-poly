# Coordinator note (Claude, 2026-10-01 ~16:00Z): a mechanism for C1r. Read before your next attempt.

This is diagnostic understanding, not a proof. Details are in the es journal on
ctx_bound_child_run_contraction_one_level_root, entries "Understanding, revised" and earlier.

1. **Limits come from chain extensions.** In decomposable_depth2_tables.limits_from_signature, the
   function `extension` threads the grow-side levels IN ORDER and takes AT MOST ONE external letter per
   level on each side, each further out than the previous one. So every cup or cap limit is
   `min(param - 1 - e, k - 1 - es)`, where e counts levels threaded on the two sides.
2. **One level means no gain from extra runs or doubled children.** With a single separator level,
   e <= 1 per side however many separators or runs exist. Extra runs and doubled children change no
   limit, which gives run-count saturation and C1r (sep_side_test.py: single level, 100/100 for both).
   With >= 2 levels, extra positions allow nested multi-level threading and can raise the bound; this
   is exactly where general C1 fails (the [S,1L,2U,S,S] counterexample, and P7's parts with two levels
   inside the span).
3. **One-level root facts:**
   - single run: bound = T(a, min(u - e, k - m), k), e = number of end markers;
   - with >= 1 end marker, the internal separators are invisible;
   - with no end markers, the two-run value is a one-sided Pascal loss (k=6, a=u=4, m=1: 6 = 3+3
     becomes 3+2 = 5);
   - the bound is the same for 2..5 runs (a, u >= 3).
4. **Suggested proof shape.** Compare cut values through EXTENSION COUNTS (small integers fixed by which
   levels occur on each side and in what nesting), not through recursive values. Parts of a one-level
   root have exactly two levels: the cut-created level 1 and the old separators at level 2. A cut of σ
   that splits or contains the doubled pair, and the moved cut of ρ seen in the C1R and X rescue data,
   should differ by a computable change in e on one side. The re-optimized coupling (side change, or
   shift -1/-2) is the T-Pascal compensation for that change. If this holds, X and N_root become finite
   case analyses over level-presence patterns plus T-inequalities (ctx_base_pascal_combine,
   ctx_single_level_limits_exact).

## Update (~16:45Z): X rescue mechanisms

X rescue mechanisms (x_mech.py; jobs 20261001-114324-70390a, 20261001-114443-0dd02c, 20261001-114443-0bdefe, 20261001-114850-7e58d3; one-level roots with <=3 runs around a doubled pair, all m and sides; diagnostic). Same-(side, coupling) transport fails: k=5 (a,u>=3) 282 of 25,272 cuts, ALL with p in the pair; k=5 (a,u>=4) 186 of 11,232, all in pair; k=6 (a,u>=4) 994 in pair + 2 outside, of 44,928. (A) p in the pair = PASCAL REBALANCING: sigma's cut uses a lopsided coupling, the leaf copy has limits like (3,1) worth T(4,2)=1, and the twin adds +1 in the complement; rho's rescue uses a balanced coupling, limits (2,2), worth T(3,3)=2 = T(3,2)+T(2,3). The pair splits one child's T-value across two cuts; the single child recovers it balanced. (B) p outside the pair (k=6, (5,5,6), m=1, S1LSSS, p just before the pair, s=l c=4): sigma's complement [S 2L 1U S S] has separator levels on OPPOSITE sides and gains from the pair (12 vs 9 contracted); rho's rescue flips orientation so the complement is [S 2L 1L S] (same sides), already 12 with one child = SIDE FLIP. Proof shape for X: (A) a Pascal inequality for twins, plus (B) a side-flip inequality for two-level parts with a doubled run.
