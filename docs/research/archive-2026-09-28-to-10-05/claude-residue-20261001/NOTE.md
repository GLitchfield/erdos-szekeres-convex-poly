# Structure of the context bound near one-level roots (Claude, 2026-10-01 afternoon)

All evidence below is diagnostic, from the compiled evaluator (`context-bound-zero-children-c-v1`,
the Lean `bound` convention), and was produced by the jobs named. None of it is Lean-certified.

## What the bound of a one-level root is

1. **Closed form = bound.** On non-degenerate one-level roots, the Lean bound equals the depth-one
   closed form of experiment 0118 (`scripts/decomposable_depth1_formula.py`), which was fitted to
   true-extremal E tables (k=5, a,u in 3..5, 1-4 runs of length 1-2, flags, both sides, all m;
   2278 matches; jobs `20261001-162958-751677`, `-163845-43b040`).
   - `plain`: one run, or any outer flag.
   - `inside`: two or more runs and no flag. This is a two-block staircase: the first run sits
     deep below the rest.

   All mismatches are conventions:
   - limit < 1: the E tables count a lone point; Lean counts 0;
   - unflagged multi-run with m = k-2: E says the structure is nonexistent; Lean keeps a dead run;
   - a word with no letters has level-1 side *lower* in Lean, whatever side the caller names.
2. **LIM for one-level contexts.** The bound is a function of the canonical limit profile: the
   cup/cap limit matrices, with adjacent runs of identical limits merged (`lim-k5-l1.txt`: 120
   groups, 0 conflicts).
   - Mechanism: with one level, a run's extension is
     [letter left of it] + [letter right of it]. So runs have three types: before the first
     letter, between, after the last.
   - A one-level root is determined by (a,u,k,m), a type path of length <= 3 and the end flags.
   - This is *why* the bound saturates at 3 runs and *why* C1r holds: deleting one of two
     adjacent children preserves the profile.
3. **LIM on parts.** Interval-cut parts of one-level roots also have bounds that depend only on
   their profiles (job `20261001-162802-60f285`: 739 groups, 21 live conflicts).
   - At a,u >= 4 the only conflict is the limit-<=1 nonemptiness degeneracy: 1U2LS vs S2LS1U at
     maxima (k-2,k-2).
   - The rest are at a=3 or u=3. This agrees with the run-length part table (`part-table-k6.txt`:
     82 conflicts, all at a=3/u=3).
4. **LIM fails in general at two levels**, but only through dead runs (job
   `20261001-161332-cea2fe`).
   - A run whose limit is 0 after threading can be cut off, and then its length matters
     (SS2L1LS1L: 3 vs S2L1LS1L: 2 at a=u=4).
   - So bound != E exactly where runs are infeasible.

## What does not work (refuted relaxations)

5. **Bilateral/MERGE closure.** Merge all same-side levels of each part into one level. MERGE
   (proved) makes this an upper bound, but the max over cuts overshoots the bound at
   (4,4,5) on 382/384 one-level roots (jobs `20261001-160928-ac9c63`/`-c4781b`, cancelled once
   decisive).
6. **Plain part bounds.** T(1+max cap limit, 1+max cup limit, k) per part overshoots on
   360/384 at (4,4,5) and (5,5,5) (job `20261001-161853-42f4bd`).
7. **Why both fail.** Optimal cuts use *nested two-letter threading*: a newer sibling child, then
   an older separator further out, on the same side. Merging levels is not even geometrically
   sound: a newer-sibling point and an older-sibling point span a near-vertical line that the part
   straddles. Any induction for the one-level closed form must treat two-level parts exactly.

## The residue colorings (user's suggestion)

8. All 5 no-singleton-split extremal colorings at (4,5,5) have one shape: a 3-cap L strictly
   inside the x-range of a 4-cup U, deep below it, coupling 2, context values 3 + 4 = 7 = T
   (`anatomy-455.txt`).
   - The split is tight with *plain* parameters, so these equality cases stress additivity only
     at the bare root, where 93 interval cuts attain T.
   - They are not where FLIP or N_root are hard.

## A candidate universal normal form

9. **PEEL (all-context singleton attainment).** Every context's bound equals its best
   caterpillar: peel one child (any child, orientation, coupling), its singleton part valued by
   its own bound, then recurse on the rest.
   - Two-level contexts (<=6 letters, <=4 children, k=5): equal everywhere except 16 cases at
     a=u=3 (job `20261001-163935-b3689f`).
   - One-level and k=6 runs: jobs `20261001-163934-fea352`, `20261001-164842-fedeb6`.
   - Only <= 3 children is closed (`ctx_bound_attained_by_singleton_cut_of_le_three_children`,
     where it is trivial).
   - PEEL is the all-context form of N_root. Unlike N_root, it can serve as its own inductive
     hypothesis on parts.
   - The inductive step (rotate an optimal non-singleton cut) reduces to level-swap
     inequalities. MERGE helps the leaves that gain a merged level and hurts the sibling that
     loses one, so a coupling re-optimization must pay for the difference. This is the same local
     obstacle the R13-R16 exchange trials met.

## Infrastructure found on the way

- **es worker** (pid 4531) started 09-30 15:01 and caches config, so it admitted against the old
  30G budget. An aged 30G extract blocked every younger queued job for ~5h. I cancelled the
  extract; a worker restart is needed to apply 40G.
- **`harness/statements.lock` on local main is invalid JSON** since R15 commit 76a1b269: a missing
  `},` after the `ctx_bound_maximal_segment_flip_exchange_of_zero_value` entry, at line 910.
  Hand repair needs the user's decision.

## Open questions, in the order I would pursue them

1. Does PEEL hold at k=6 and for one-level roots with flags (jobs above)? If yes, register it as
   a conjecture generalizing N_root, with falsifier `runs/claude-labels-20261001/peel_nf.py`.
2. Is the bound of a two-level part given by a closed form generalizing plain/inside, e.g. a
   staircase of blocks with nested-threading flags of weight up to 2? Part-LIM says it is a
   function of finitely many profile data.
3. Can a staircase description at every depth make additivity an identity of T-sums? This is the
   correlated-inequality program, now with the knowledge that two-level threading must be kept
   exactly.

## Evening update: deque normal form and the exact shape of the hard case

**EXTREME-PEEL.** Every context's bound is attained by peeling only the first or the last child,
repeatedly. This is a deque: the extremal filling is built from the outside in.
- **Evidence:** all 102k two-level contexts at k=5 with a,u >= 4 (job 20261001-170417-f3b4a7);
  failures only at a=3/u=3.
- **Weaker variants, also holding at a,u >= 4:** END-PEEL (the four N_ends candidates at every
  step; job -165459-f274b9) and PEEL (any child; job -163935-b3689f).
- **Stress tests:** jobs -170928-3c1dc1 (5-6 children) and -170928-cc14a5 (three levels);
  PEEL at k=6 is job -165930-b61766.
- **Meaning:** each peel makes the peeled child a flag that costs every remaining chain one cap
  (lower peel) or one cup (upper peel). So the bound is a sum of T's along a lattice path, the
  classic ES cup-cap recursion. The depth-one closed form is a two-step peel.

**Splitting identity.** For a,u >= 3:
max_d [T(a, min(u-1,k-d), k) + T(min(a-1,d+1), u, k)] = T(a,u,k).
Splitting a run into two adjacent children loses nothing, in both regimes.

**FLANK-SWAP.** If level l's letters are all left of every child and level l+1's are all right,
swapping the two levels leaves every limit of every descendant unchanged.
- Different sides: keep the maxima.
- Same side: new maxima (M, M-1) with M = max(m_l, 1+m_{l+1}).
- Verified on 12,672 (same side) and 19,008 (different sides) contexts (job -171623-44dbc9).

**The residual trade.** With FLANK-SWAP, EXTREME-PEEL's inductive step is one trade: the
cross-polygon constraint (p's cup + 1 + Y's cap <= k-1) is charged to p or to Y.
- Coupling-limited Y: the reroute is never worse.
- Threading-limited Y: the reroute fails about half the time, and a side flip or the last-child
  route must rescue. This is precisely the X rescue-mechanism split, now as one explicit
  inequality family.

**Proposed next trial (needs user OK):**
1. Register EXTREME-PEEL (all contexts, a,u >= 4) and FLANK-SWAP.
2. Prove FLANK-SWAP in the style of MERGE.
3. Prove the coupling-limited case.
4. Classify the threading-limited case: which alternative route works, and prove it.

## Idea (untested): multi_run via deque merging

If bound = D (the deque value), then for a non-interval partition (L,U) of sigma's children,
bound(sigma_L) + bound(sigma_U) = D(sigma_L) + D(sigma_U). Interleave the two optimal deque
sequences into one deque sequence of sigma: at each step, pop sigma's current first or last
child from the part it belongs to.
- **Why it might work.** In sigma's merged sequence, each leaf sees all remaining children (L and
  U) as ONE level. In sigma_L's sequence it saw remaining L as level 1 and U as an older level.
  MERGE (proved) says merging two same-side levels never lowers the bound. Different-side levels
  do not interact, though the two must be ordered consistently (FLANK-SWAP-type
  reorderings). So leaf values can only go up.
- **Obstruction: a deadlock.** The interleaving fails exactly when L's next pop is blocked by a
  pending U child and U's next pop by a pending L child. Example: sigma = L1 U2 L3 U4, where
  sigma_L pops L3 first and sigma_U pops U2 first.
- **Consequence.** FLIP/multi_run would reduce to one exchange lemma at deadlocks. Test plan: on
  two-level contexts, compute both optimal deque sequences; check whether a non-deadlocked optimal
  pair always exists, and how often merging is strict.

## Draft statements for the proposed route (not registered)

The context is the published Baek-Balko induction. It is plain-parameter and fails at the
boundary (`published_induction_boundary_regression`, (4,5,5,u'=1,a'=3)), where a part falls
below the active Pascal window. The context recursion exists to supply the missing positional
information. The deque normal form says what that information buys: optimal decompositions
peel from the ends.

1. **FLANK-SWAP** (formalization; MERGE-sized, ~500 lines).
   - Hypotheses: sigma.WellFormed, 2 <= sigma.maxima.length. Every level-1 letter position is
     < every child position, and every level-2 letter position is > every child position (or
     the mirror).
   - Define sigma' by relabelling ext 1 <-> ext 2 in the word and setting maxima
     [m1', m2'] ++ drop 2, where:
     - sideAt 1 != sideAt 2: (m1', m2') = (m2, m1), each letter keeps its maximum;
     - sideAt 1 = sideAt 2: (m1', m2') = (M, M-1) with M = max(m1, 1+m2).
   - Conclusion: sigma.bound = sigma'.bound (or <= in the needed direction).
   - Evidence: job 20261001-171623-44dbc9.
2. **EXTREME-PEEL2** (conjecture). For 4 <= a, 4 <= u, 2 <= sigma.numRuns and 2 <= sigma.bound,
   some p in {first child, last child}, side s and coupling c with 1 <= c <= k-2 satisfy
   sigma.bound = (sigma.part [p] s c).bound + (sigma.part rest s' (k-1-c)).bound.
   - Evidence: two-level 102k contexts, three-level 40,176 (all failures have bound 1); 5-6
     children and k=6 running.
   - Generalizes N_ends and implies the registered end-cut conjecture for a,u >= 4 on contexts
     with bound >= 2.
3. **The three local lemmas of EXTREME-PEEL2's induction** (optimal interval cut (X,Y)):
   - (A) X is optimally peeled at sigma's extreme child p. Reroute: peel p from sigma, then cut
     (X-p,Y). X-p is unchanged by FLANK-SWAP. When Y is coupling-limited the reroute closes by
     a coupling choice (pure-T scan: 87,804/87,804). When Y is threading-limited, rescue by the
     other side or the other end: 12,532 rescues in data, none missing.
   - (B) X is a single run: splitting identity in context.
   - (C) X is optimally peeled at its interface child q: the boundary move to (X-q, Y+q) keeps
     the optimum in ~94% of instances; the rest need a further move.

## Rotation step, by hand (evening)

Blocks A=[p] < B < C.
- **H1** = ((A,B),C): X = A∪B has side s against C; within X, A has side t against B.
- **H2** = (A,(B,C)): A takes side t' = t; within B∪C, B has side r = s against C.

B is invariant by FLANK-SWAP, using the stated maxima rule. The A/C trade then splits into two
cases:
- **t = s.** A is below C in both trees.
  - A: two nested extensions (B, then C further right) become one merged extension, so A
    **gains one** extension on chain type t.
  - C: one merged extension (X) becomes two nested ones (B, then A further left), so C **loses
    one** extension on the opposite chain type.
  - The strong terms shift by one (M-rule).
- **t ≠ s.** The rotation flips A and C vertically: in H1, A ∪ B is below C; in H2, A is above
  B ∪ C. The single extension on their shared chain type moves from A's chains (extended by C)
  to C's chains (extended by A), and the cross-polygon changes from (A cup + C cap) to
  (C cup + A cap).

Both are marginal trades: T(A with one more) - T(A) against bound(C) - bound(C with one less).
Optimality of H1, meaning its couplings are optimal, gives first-order inequalities on these
marginals. They are the natural tool for proving that, among the reroutes (this one, A's other
side, the mirror rotation at C's far end), one always wins. Data: always.

## Late update: a rescue-free induction candidate (foreground scans, small family)

- **RR.** Every context has an optimal *run-respecting* interval cut, one whose block is a union
  of whole runs. 864/864 at (4,5,5) and (5,5,5).
- **Where the failures come from.** Non-degenerate reroute failures (case A) occur only when the
  chosen cut splits a run, or when a part is dead. With X a genuine multi-run block and both
  parts alive, no failure was found.
- **GOOD-CUT (deterministic).** Take, among optimal run-respecting cuts, the one whose part
  containing an extreme child is smallest. Then peeling that extreme child from sigma, on the side
  of its optimal peel within the part, attains the bound.
  - Results: 360/360 at (4,4,5), (4,5,5) and (5,5,5); 90 and 88 of these are nontrivial (part
    >= 2 children).
- **Proposed induction for EXTREME-PEEL2.** RR + smallest-extreme-part choice + same-side
  reroute, using FLANK-SWAP and the splitting identity. Unit/dead cases go through the existing
  zero lemmas.
- **To do at scale (when the queue is free):**
  1. RR and GOOD-CUT on longer words (7-8 letters), three levels, k=6.
  2. Look for a minimal-counterexample argument: if the reroute fails at the smallest extreme
     part, derive a smaller optimal cut.

## CORRECTION (20:05 local): the deque normal form is not universal

EXTREME-PEEL2 and END-PEEL fail on three-level four-child contexts at k=6 (job
20261001-191322-86bf03).
- **Size of the failure.** At (5,5,6), 56 non-degenerate failures (bounds 4..11); the extreme
  caterpillar is always short by exactly 1.
- **Example.** SSS1L3L2LS mx (1,1,1) has bound 8, and its only optimal first peel is the
  *middle* child of the three-child run.
- **What survives.** PEEL (some singleton, possibly interior) attains the bound in every case
  tested.
- **What the deque held on.** Two levels (k=5,6) and three levels at k=5.

Consequences for this note:
- The organizing conjecture should be **PEEL**: singleton attainment for all contexts, interior
  children allowed.
- The deque picture (extremal fillings built from the outside in) is only a low-depth
  phenomenon.
- The rotation analysis still applies, but the peeled child need not be extreme, so FLANK-SWAP
  (which needs flank letters) covers only part of the step.
- The registered N_ends (one-level roots) is unaffected.

**Why the middle of a run** (SSS1L3L2LS, (5,5,6)).
- The value is carried by spanning cups: within-run cups 2, run1 -> run2 cups 4.
- Peeling the middle child leaves an interior letter that only extends one-sided chains; the
  remainder keeps 6 and the leaf gets 2, total 8.
- Peeling an extreme child leaves a flank letter that extends every chain on its side, so the
  best total is 7.
- Selector principle: peel the child whose letter costs the remainder least. Position alone does
  not decide this.
