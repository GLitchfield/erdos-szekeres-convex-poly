# General picture: Theorem 8 for decomposable sets

Coordinator's working document. Update it after every result. A specific case or computation is commissioned only
to answer one of the open questions below, and its result is recorded here as what it taught about the general
mechanism.

Last updated: 2026-10-03 10:00 (Claude, coordinator). Running: Q1/Q2 (runs/claude-uniform-20261003), Q3/Q4 (Sol R24), Q6 (runs/claude-kfree-20261003).

> Note (17:45 real time): the parenthesised times on entries after about 12:00 today were estimated and run up to
> about 2.5 h ahead of the real clock. Use the es journal timestamps as the authority.

## Target

For all a, u, k: a decomposable X with no a-cap, no u-cup and no strong k-set has |X| <= T(a,u,k). In the window
regime, T(a,u,k) counts the words w in {U,D}^{k-2} with #U <= u-2 and #D <= a-2.

## Why the obvious induction fails

Split X at its root, X = L << U. Each child's constraints are not just smaller (a',u',k'): they depend on WHERE the
sibling's points sit (nested root splits). The published Baek–Balko proof has a gap exactly here.

So the statement that can be proved by induction must be about sets in a *context*. Finding the right
context-indexed bound is the whole problem.

## What is now known structurally (proved, all parameters)

**Lemma DS** (audited). For X = A << B:
- a cap of X meeting B is a cap D of B, optionally extended by one A-point before it and one A-point after it;
- a cup of X meeting A is a cup of A, optionally extended by one B-point on each side;
- strong(X) = max(strong A, strong B, cup A + cap B).

**Consequences** (immediate from DS by induction over the tree):
1. "No strong k-set" is a LOCAL tree condition: at every internal node A << B, cup(A) + cap(B) <= k-1.
2. A child sees its ancestors only through the extreme points of the siblings along its root path, i.e. through a
   finite set of cut positions (zones). Its cup and cap limits depend only on the zones where a chain starts and
   ends.

So Theorem 8 is equivalent to a finite recursive optimisation. Let
- N(P; α, β) = the maximum size of a decomposable set with zone profile P, cup number <= α and cap number <= β;
- the recursion = a split into A << B with an interleaving pattern, child profiles induced by DS, and the
  constraint cup(A) + cap(B) <= k-1.

**The general conjecture should be a closed form for N(P; α, β).**

## Partial answers

- **Iterated endpoint split.** It proves the classic (no-k) part for block profiles (killset run).
- **Kill-set rule.** N = (window words) − (monotone kill family) is exact on all single-gate block profiles. It fails
  on multi-gate profiles: nested blocks need deficiencies on unions of blocks.
- **Absorption.** A point lying only in 3-caps kills exactly one label.
- **Labels (Sept SAT study).** A valid injective labelling exists, but a point's label must depend on the positions
  of external points, not only on maxima. This is consistent with consequence 2: labels should depend on the zone
  profile.
- **Context route (R1–R19).** It used a guessed bound function on contexts and stalled at additivity (the sibling
  penalty). The guessed function may simply be the wrong N. That has never been tested against exact values.

## CURRENT GENERAL CONJECTURE (10-03 ~11:45): the Band Decomposition Lemma (BDL)

Source: runs/claude-uniform-20261003/NOTES.md. Not yet audited.

> **BDL.** Let X be decomposable with no strong k-set, α = cup X, β = cap X, α + β >= k. Then X is a disjoint
> union of bands X_j, k-1-β <= j <= α-1, with cup X_j <= j+1 and cap X_j <= k-1-j.

**BDL ⇒ Theorem 8 for all (a,u,k), with no gates.** Classical Erdős–Szekeres gives |X_j| <= C(k-2, j), and the
sum over j in [k-a, u-2] is T. The coordinator re-checked the band sums for every window state with k <= 15.
- The injective labelling is: a point maps to (its band j, its classical Erdős–Szekeres lattice path inside the
  band), which is a window word.
- The Erdős–Szekeres lower-bound construction is literally a chain of bands.
- With no cup or cap limits the bands give 2^(k-2), so BDL for all signotopes would be the Erdős–Szekeres
  conjecture. Any proof must therefore use decomposability.

**Evidence (diagnostic).**
- Exhaustive over all decomposable colourings with n <= 8 and every k: 442,930 cases, 0 failures.
- Nested and random samples at k = 6, 7, 8: 0 failures.
- The stronger "peel" form is false.

**Why it composes.** At X = A << B, A's bands lie below cup A and B's bands start at k-1-cap B. These index
ranges are disjoint by the node condition, so the partitions concatenate. This is the window identity made
structural.

**The ONE gap: case R**, i.e. the tight nested split, cap B = cap X = β and cup A = k-1-β. This is exactly the
Baek–Balko gap.
- It closes if B's bottom band lies on one side of A.
- Candidate invariant P (diagnostic, 0 failures): if the β-caps of B share a core, B has a band partition with
  its bottom band entirely left of the core, and another with it entirely right.
- BDL + P ⇒ gap bound (paper).
- Missing: carry P through root splits. The likely induction hypothesis is BDL in a context, with the sibling's
  letters tagged by band.

**Answers recorded.**
- Q1: no single kill family. N(G; α, β) = T(β, α+1, k) + C(k-3, β-2) on the gap profile.
- Q2: N is adjacent-band Markov on one-sided contexts; the exceptions are two-sided contexts and multi-gate
  non-contexts.
- Q3: kill families add on disjoint bands, except in case R.

**Running on BDL (10-03 ~12:50):** Sol R25 (rigorous proof, host 20261003-104816-63f404); subagent bdl-induct (Q7, invariant search, runs/claude-bdl-induct-20261003); subagent audit-bdl (Q8, runs/claude-audit-bdl-20261003); Sol R24 (Q3/Q4, context bound vs truth); subagent kfree (Q6).

**END OF DAY 10-03 (23:45). Current exact state.**
- **Lean (main 701ff379):** Theorem 8 ⇐ BDL (decomposableStateUpper_all_of_bands). Also on main: Lemma DS, the
  classical bound, the lower construction for all parameters, gluing and pushforward, and the a=4, a=5 gates.
- **Paper:**
  - BDL ⟺ MIXED ROOT (R25; the audit confirms it as a conditional reduction);
  - the case-R lock splits by lo: ZLOCK at lo = 1 (single point; true in all tests; lift needed only at tight
    two-sided-mixed z) and P at lo >= 2 (true in all tests).
  - BRL+ and P fail only at lo = 1.
- **Running overnight:** Sol R26 (MIXED ROOT, single point first; until about 10:55) and a P-at-lo>=2 hand-proof
  subagent.

**R25 DONE (22:55).**
- **BRL+ REFUTED at n = 24** (and with it P/G_core on both sides).
- **Paper81 [paper]** closes every hard root with no MIXED max β-cap.
- **The exact BDL residue is MIXED ROOT:** a tight root where a max β-cap meets both children. BDL ⟺ MIXED ROOT.
  See LOCK.md.

**Q25 ANSWERED, NEGATIVE (22:20).**
- Bottom-up attainable context sets have no closed form: they are near-injective and not self-inductive.
- Always attainable: P on both sides (not inductive).
- Every failure is a SINGLE SIBLING POINT near the core, which supports the ZLOCK focus (LOCK.md; test running).

**R24 DONE (21:55 real).**
- **Q4 negative:** the context bound is not the true maximum (two-cap obstruction, true maximum 2p, never at an
  interval root).
- **Q3:** an exact hand composition identity, not a closed form.
- **12 Lean theorems accepted on branches,** including:
  - Lemma DS (strong-avoidance iff; endpoint-constraint iff);
  - colour gluing and pushforward;
  - the UNIVERSAL THRESHOLD LOWER CONSTRUCTION (T attained for all parameters, built from successive classical bands,
    i.e. BDL's shape).
- These are general, reusable foundations, and integration candidates along with R23's general lemmas and node A.

**Q23 ANSWERED.**
- The local frame lemmas L4₀ and L2₀ HOLD for decomposable sets (s = 5 complete); L2₀ is false for general
  signotopes.
- **Q14's conjecture (a) is FALSE** (N = 11).
- **Partial hand proof:** Lemma D (a gon in a child forces that child's cap or cup to be larger by 2) closes most
  cases.
- **Open:** the case where a 1–2 point sibling ANCHORS near-maximal chains of the big child, i.e. the lock in its
  smallest form.

**Q17 RESOLVED (20:00).**
- **The determined rule fails from n = 10.**
- **But the TWO-SIDED TOWER LANGUAGE suffices:** broad backtracking finds a proof inside it on EVERY instance and
  tree tested (7,996 roots up to n = 41; 22,529 roots over 12,358 trees). The language is finite (bounded by k).
- **Proved:** single-point absorption, so two-sided towers are needed exactly at degenerate cores.
- **PROOF-DRAFT.md** has a sound induction schema plus the proved step lemmas.
- **Open:** an intrinsic family of contexts (containing the root, closed, non-empty at base nodes). The choice is
  non-local, so top-down selection fails.
- **Next: Q25, BOTTOM-UP.** Compute each node's set of attainable signatures (the Pareto frontier) in the finite
  language and look for a closed form that composes. If found, it removes the lookahead, since bottom-up DP needs
  none.

**Q17 PARTIAL (19:17 real time; runs/claude-tower-20261003/NOTES.md). The most promising BDL result.**
- **Tower Closure Lemma [P].**
- The tower plus a neighbour cut closes Q9f's regrowth, and NO unbounded parameter appears.
- **A fully DETERMINED recursive rule** (keep → reserve → lift, side inheritance, no oracle) has 0 failures on all
  n <= 7; the n = 8 run in progress shows 0 failures so far.
- **Reduction:** BDL ⇐ "the rule delivers only satisfiable contexts to the 2-band and classic base nodes", a
  near-classical 2-band statement that is partly proved.
- Relaunched to finish n = 8, prove the 2-band base truth, and write PROOF-DRAFT.md.

**Q24 ANSWERED, NEGATIVE.**
- Rectification has no local monotone move lemma. Monotone paths exist (n <= 8, with single-point moves), but
  every potential plateaus.
- **PROVED Lemma S:** the strong number is INDEPENDENT of the interleaving; cup and cap depend only on the
  children's four extreme points.
- A nested root un-nests monotonically unless LOCKED: the inner child sits strictly inside the core of the outer
  child's max caps (or cups), and the outer child carries that number. Theorem 8 reduces at best to one-defect
  sets, whose core is the lock.

**OVERALL (evening 10-03).** Every approach tried localises the difficulty to the same LOCKED NESTED SPLIT:
partitions, colourings, frames, lattices, width, LLL, polyhedra and moves. The lock is: a part inside the common
core of the other part's longest caps, with the longest-cap number carried by the outer part.

**Q24 (running, runs/claude-rectify-20261003; from Gavin's algebraic-object idea).**
- RECTIFICATION instead of partition, by analogy with the plactic monoid and jeu de taquin.
- Use local moves that keep |X| and never increase cup, cap or strong number: adjacent x-swaps (S_n generators
  acting on interleavings), free re-rootings, and block moves.
- Drive X to a NON-INTERLEAVED set, where every split is non-nested and Theorem 8 is already proved (R19 split_le).
- The nested split, the obstruction everywhere, is purely an interleaving phenomenon. So a LOCAL monotone move
  lemma would prove Theorem 8.

**Q22 ANSWERED, NEGATIVE.** The probabilistic route is ruled out:
- the slack decays toward extremal size;
- the Local Lemma misses by a factor that grows with k, because gons are dense (about 250 per point at k=6, n=16);
- the residual polytope is not integral.

**META-INSIGHT (end of 10-03 afternoon).**
- Statements true for GENERAL signotopes (PSL, CORE, the frame lemmas) are ES-HARD if proved without
  decomposability: PSL for all signotopes implies the ES conjecture for signotopes.
- So their decomposable proofs must use decomposability ESSENTIALLY. Every local, lattice, LLL or polyhedral
  failure today is what ES-strength statements predict.
- BDL is false for general signotopes, so it has decomposability built in; its kernel is BRL+ (R25).
- Our only use of decomposability so far is Lemma DS / tree induction, and it regrows.
- **Next direction:** a NEW GLOBAL use of decomposability. The candidate is the binary-label + x-order encoding,
  a permutation-like object. Or focus on the decomposable-specific BRL+.

**Q21 ANSWERED.**
- PSL width is NOT chain-bounded; it grows with n (the n <= 8 result was an artifact).
- **Survives: W = "width <= α+β−3".** W ⇒ PSL [P], and W is equivalent to a one-step pinning lemma [P]. No proof
  idea for W.
- **Frames:** each frame lemma splits into a local part (no forced monochromatic gon in all frames; looks
  provable) and the global hitting set E.

**Q20 ANSWERED, NEGATIVE (20:00).**
- There is no Hex-type dichotomy mechanism: the extending frame's extensions are free and unrelated to the other
  frame's obstruction. Existence comes from slack.
- The residual LP was exact on the small nontrivial failures.
- The only remaining lead on the CORE line is polyhedral: is the residual hitting-set polytope integral?

**Q16 ANSWERED (19:40).**
- **No polymorphisms** (lone β-cap ⇒ the 1-in-β relation), so lifting to sets of possibilities alone does not
  localize the choice. Inside the classical frame, AND-closure holds except through strong (k−1)-sets.
- **NEW POSITIVE SIGNAL: PSL has width <= A−1** (chain scale) on ALL decomposable instances with n <= 8, while BDL's
  width grows (pigeonhole).
- Bounded width without polymorphisms must come from INSTANCE structure, i.e. a bounded-bag (tree-decomposition)
  lift. That is Gavin's idea made precise.
- **Next: Q21.** Does PSL width stay <= A−1 at larger n, why, and is chain-scale consistency of the list-free
  instance provable?

**Q18 ANSWERED (19:15): CORE unproved and unrefuted. Its residue is precisely a GLOBAL HITTING-SET dichotomy.**
- **Proved:** cored-set structure, i.e. the F/L frames satisfy all conditions except the (k−1)-gon one.
- **Open:** a set E of newly blue points hitting every red gon of B∖F, with F ∪ E free of α-cups, β-caps and gons.
- **No local rule works.**
- **Two-frame lemma:** EITHER the F-frame OR the L-frame extends. It holds everywhere; a single fixed frame does not
  (FEL is false at n = 12).
- **Proposed new abstraction:** an either/or existence statement is the shape of HEX/Sperner-type (topological)
  dichotomies, where failure of one side is witnessed by a blocking structure that builds the other. Alternatively,
  LP integrality of the residual hitting-set problem (the conv-hull LP was exact on frame instances in Q12).

**Q19 ANSWERED (18:45): CORE is not inductive without context.** It composes everywhere except at double-carrier
splits, where it regrows exactly as before.

**DECISION.** Every tree induction regrows at the same nested split. No more composition tests. The frontier is
NON-inductive:
- a direct proof of CORE on signotopes (Q18). This is plausible, since CORE holds on general signotopes, so the
  tree should not be needed;
- the finite tower (Q17);
- lattice/width structure (Q16);
- Sol R25.

**Q9h ANSWERED (18:20).**
- 3-band validity ⟺ (i) L∪T hits every max cup and cap, (ii) cup L <= α−2, (iii) cap T <= β−2 (PROVED). This is a
  2-colouring-type problem.
- The one-swap lemma holds in all tests but is only half proved (max caps done; the strong bound must enter for
  cups).
- Chain induction on the number of bands is refuted: realignments are bottom "stars" plus repairs.
- **The BDL exchange route is stalled. The lead is now CORE (PSL route):** Q18 attempts a direct proof, and Q19
  (Q9 agent) tests whether CORE/HIT compose under DS splits.

**Q9g ANSWERED (17:55).**
- There is no monotone realignment, and the distance from an arbitrary partition is unbounded.
- Optimal realignments are chains of swaps between band pairs (augmenting-chain structure).
- 3 bands: a single swap (up + refill) always works (6.9M partitions at n = 8).
- **Next: Q9h.** A hand proof of 3-band BRL+ as the base of an augmenting-chain induction on the number of
  bands, and whether chain length is <= #bands − 1.

**Two lead targets now:** (BDL route) BRL+ via augmenting chains; (PSL route) CORE + HIT. CORE is context-free and
holds even on general signotopes, which makes it currently the most promising.

**Q15 ANSWERED (17:40): PSL's case R reduces EXACTLY [P] to a CONTEXT-FREE conjecture, CORE.**
- **CORE:** every "cored" decomposable window set B (its max caps share a common core) has a 2-colouring with:
  - every β-cap bichromatic;
  - every α-cup containing a red point;
  - every (k−1)-gon bichromatic.
- **Evidence:** 0 failures on 228,819 cored sets with n <= 8 and 2,121 large instances. It holds even on GENERAL
  signotopes (396 cored instances, including the BDL counterexample X14).
- **Relief mechanism:** a MONOCHROMATIC child (A all blue), not overlap.
- **Cored-frame lemma [P]:** blue = the first points of the β-caps already satisfies everything except the gon
  condition.
- **Proof shape for PSL ⇒ Theorem 8:** uniform rules [P] everywhere except R, R1 and mirrors; R ⇐ CORE [P]; R1 ⇐ HIT
  (with A's cup context) [C].
- **CORE is the first target.** It is context-free and plausibly a general signotope fact. Its obstacle is that the
  gon condition couples a cup and a cap.

**Q17 (running, runs/claude-tower-20261003; Gavin: "multiple lifts").**
- Q9f's regrowth adds pairs of DECREASING cap length, so it is a FINITE tower of at most β levels.
- Test whether the tower context (a full monotone cap-length profile on band lo+1, more bands if needed, with size
  bounded by f(k)) closes. If it does, the proof is a double induction over the tree and the profile level.
- Q16 also measures the consistency width as a function of k.

**Q16 (running, runs/claude-lattice-20261003; from Gavin's lifting idea).**
- Lift to SETS of possibilities. This helps iff the solution sets have lattice or majority polymorphisms, which by
  constraint-satisfaction theory give bounded width: local consistency implies a global solution, and canonical
  extreme solutions compose.
- Tests: meet/join/majority closure of BDL partitions, PSL colourings and FULL hypercube labellings; whether the
  extreme solutions compose; whether the extreme BDL partition gives BRL+.

**Q9f ANSWERED, NEGATIVE (17:10).**
- The bounded positional context family closes to n = 6 but fails at n = 7.
- Each nested lift level adds a (cap length, cut) pair, so the context regrows into the DS zone profile.
- **All tree-induction strengthenings are now exhausted.**
- **Target: BRL+ by a direct realignment/exchange argument.**
- The cap-length profile is the invariant that a cascade of upward band moves must keep. **Next: Q9g**, measuring
  realignment distance and whether monotone upward cascades always work.

**CONVERGENCE (16:45).** Sol R25 independently reduced BDL, by a SIZE induction (paper, unaudited), to one lemma:
- **BRL+ (bottom realignment).** Given a valid band partition of a decomposable Y (>= 3 bands, open max-cap core),
  there is another valid partition whose bottom band lies entirely on ONE side of the core, either side.
- R25 closes every other case. Case R closes with BRL+ applied to B, then absorbing A by DS.
- This is the same missing lemma as the Q9 line's G_core / LL. Q9f tests an inductive strengthening (J + LL),
  and R25 attacks BRL+ directly.
- **THE target is now BRL+.**

**Q9e ANSWERED (16:35).**
- LL is TRUE at every core cut for >= 3-band W (exhaustive n <= 8), with the orientation chosen from t.
- LL composes at wide–wide splits (proved).
- The context is BOUNDED and does not regrow: per side, a floor, a position cut, an LL cut and an orientation.
- Open steps: a cut-aware classic-block split; an orientation rule when t and the sibling disagree; floor
  lowering for 2-band children.
- **Next: Q9f**, closure of the bounded context family at those three steps.

**Q12 ANSWERED (16:20).**
- **BDL is false on general signotopes** (X14 at k=6; tight k=7 sets). **PSL never failed.** Decomposability
  excludes the BDL obstructions.
- **Generic tools fail for BDL:**
  - Hall at all subsets is insufficient;
  - the band families are not matroids;
  - there is no Greene–Kleitman shape;
  - fractional BDL is false on general signotopes.
- **New CHOICE-FREE targets.** Each implies Theorem 8 [P] and survived every test:
  - Φ(X) = Σ_j r_j(X) − |X| ≥ 0, i.e. Hall at X only;
  - the per-band density r_j(X) ≥ |X|·C(k−2,j)/T;
  - numeric PSL, |X| ≤ ρ_R + ρ_B with overlap allowed.
- **Why these may escape the obstruction.** The obstruction everywhere was COORDINATION: a core point must go to
  exactly one band or colour. Choice-free statements let each band take its own maximum set, and overlaps are
  allowed.
- Φ composes everywhere except case R (sketch). **Next: Q15**, does overlap close case R?

**Q9d ANSWERED (16:00): the BDL route is down to ONE lemma with a ONE-CUT context.**
- **Concatenation splits:** classic-block insertion holds for EVERY joint of W. The canonical lift rule is PROVED
  in the main case.
- **Absorption splits (Z nested in W's core):** an exact lift criterion is PROVED: lifting works iff W's next band
  has no (cap−1)-cap entirely left of a lifted point.
- **Open: the LIFT LEMMA.** For a nested classic Z at position t, W has a joint (orientation chosen from t) whose
  next band avoids such caps.
- With the Lift Lemma, J composes at every split, and J ⇒ BDL ⇒ Theorem 8.
- **Next: Q9e.** Is the Lift Lemma (one cut point plus orientation) closed under W's own splits?

**Q14 ANSWERED (15:30).**
- There is no canonical, lookup or sweep rule for PSL (SAT-UNSAT cores). The classical split is a sweep; PSL is
  provably not.
- Why: a strong set is a cup plus a cap with shared ends. Colouring it needs coordination between two chains,
  while the classical obstruction completes at one point.
- **Surviving conjectures (n <= 9):**
  - (a) Fp and Lu never both contain a strong (k-1)-set;
  - (b) FRAME LEMMA: one of four one-sided frames extends to a PSL split.
- **Missing step:** a transversal E of the strong (k-1)-sets of X∖Fp that stays independent (no α-cup, no strong
  (k-1)-set) together with Fp. This is a matroid-intersection / Hall-type problem; see Q12.

**Q13 ANSWERED, NEGATIVE (15:00).** PSL under separable profiles is false and not closed: a first-child split can
saturate both colours at one later point. This happens even WITHOUT k, where PSL is just the classical
Erdős–Szekeres split.

**META-INSIGHT (Q7c, Q9b, Q11, Q13):**
- Tree-order induction is the WRONG ORDER. The classical Erdős–Szekeres split is proved by a global canonical rule
  (first points of max caps / last points of max cups, i.e. a sweep), not by induction over the decomposition tree
  with contexts.
- So the window statements (PSL/BDL) should be sought as a strong-aware extension of the classical canonical rule,
  or as a global existence theorem (Q12).
- The decomposition tree then enters only through Lemma DS facts about chains, not as the induction order.
- Next: **Q14**, a strong-aware canonical/sweep rule for PSL, or a proof that no such rule exists.

**Q9c ANSWERED (14:45).**
- **Counterexample (n = 25, tight (5,6,7)):** G as stated for all t is FALSE. This X has empty cores, so the form
  needed in case R (a cut inside a nonempty core) and P are not refuted.
- **Positive:** J = "a joint in SOME orientation" (bottom band one-sided w.r.t. the cap core, top band w.r.t. the
  cup core) held everywhere with >= 3 bands.
- **Proved:** wide–wide splits compose.

**THE SINGLE OPEN STEP on the BDL route is now CLASSIC-BLOCK INSERTION (CBI):** a classic block Z (one band; an
Erdős–Szekeres-type set) placed as the sibling of a wide set W with a joint. CBI contains case R. Z's classical
structure (iterated endpoint peel) is fully understood, and W's joint may be chosen.

**Q11 ANSWERED, NEGATIVE (14:30).** Point insertion has no local repair: the repair distance is unbounded (7 for
every point of a tight 14-point set). Tight sets are rigid, deleting a point opens many partitions, and undoing
that is global.

**Coordinator synthesis (Q6 + Q10) → Q13.**
- PSL's obstruction is ONE-coloured: red points of lower siblings extend caps.
- By Lemma DS, each ancestor level adds at most one extension on each side, so the accumulated context is a
  SEPARABLE cap profile (limit β − P_i − Q_j, with P, Q monotone).
- Q6 proved separable profiles are closed under the DS recursion.
- Candidate hypothesis **PSL-sep**: PSL holds under every realisable separable cap profile, mirrored for cups. If
  it is closed, the only remaining issue is the child-order dependence.

**Q10 ANSWERED (14:20).**
- PSL is the structurally stronger form: every PSL split extends to a full word labelling (FULL) at n <= 8, and
  FULL ⇒ BDL.
- PSL's tree induction fails only at tight nodes, and the failing condition is ONE-COLOURED: R-points of A must
  not extend B's caps past β-1.
- "Split A first, then B in A's context" always works to n = 9.
- Missing: PSL in a realisable one-coloured context, with a child-order rule. The same sibling penalty, now in its
  simplest form.

**Coordinator observation.** PSL is a hypergraph 2-colouring: every β-cap needs a Bl point, every α-cup an R
point, and every strong (k-1)-set both colours. This is a cleaner global problem than BDL's list colouring;
forwarded to Q12.

**Q9b ANSWERED (13:40).**
- U holds against EVERY tested sibling, including interleaving ones.
- Proved: G ⇒ U; U for 2-band sets; U + U′ (all decomposable sets) ⇒ BDL.
- But U does not compose: a universal partition of X cannot be built from arbitrary universal partitions of the
  children. Compatible choices always exist, i.e. some universal partition of X restricts to universal ones of both
  children.
- In the failures, X's universal partitions are POSITIONAL: bottom band left of the cap core and top band right of
  the cup core (opposite-side joint, OSJ).
- Next (Q9c): is OSJ always achievable, and does it compose?

**Q12 (running, runs/claude-hypergraph-20261003):** BDL as hypergraph list colouring. Covers obstructions on
general signotopes, a Hall/matroid-partition characterization, the fractional relaxation and its dual, and the
global theorem that would give BDL.

**Pattern across Q7, Q7b, Q7c, Q9, Q9b.** Every inductive route meets ONE obstruction: the parent's partition needs
child choices that depend on the parent's maximal chains (lookahead). The information is bounded (Q7b) and
compatible choices exist (Q9b), but no local rule makes them.

**Q7c ANSWERED, NEGATIVE (13:10).**
- There is no intrinsic admissibility in the DS context shape. Adm_DS is inherited and holds at the root, but is
  false on contexts the induction generates.
- Cause: LOOKAHEAD. How to split a merged classic child across bands lo/lo+1 depends on the sibling's deeper
  structure, which the parent cannot see.
- So top-down DS induction with bounded intrinsic contexts is ruled out.

**Remaining routes.**
- **(U)** Bottom-up: every node's set of achievable signatures contains a universal element that works against
  every sibling (Q9b).
- **(PSL)** Induct on k instead of on the tree (Q10).
- Non-DS decompositions, in particular **(Q11) induction on points**: repair a BDL partition of X−x by augmenting
  band moves (runs/claude-insert-20261003).
- Sol R25.

**Q9 ANSWERED (12:50).**
- There is no canonical band rule: partitions are massively non-unique and the freedom is global. TDF (explicit
  top-down) is proved when every case-R sibling has <= 2 bands, and fails from n = 12 when B has 3 bands.
- Two leads:
  - **(U) universal partition.** B has ONE band partition that works against EVERY case-R sibling. It is
    context-free, so if it composes under root splits it IS the induction hypothesis. Next: Q9b, testing U against
    all siblings (including interleaving) and its composition.
  - **(PSL) Pascal split with strong number.** X = R ∪ Bl, with cap R <= β-1, cup Bl <= α-1, and both with
    strong <= k-2. It is exhaustive to n = 8 and proves Theorem 8 by plain induction on k with no context. It is the
    10-02 PASCAL-SPLIT. Its tree induction hits a case-R analogue.
- Three candidate induction hypotheses are now on the table: H* with admissible bounded contexts (Q7c, running),
  the universal partition U (Q9b), and PSL.

**Q7b ANSWERED (12:25).**
- The context a node needs is BOUNDED: at most 4 band-tagged sibling pieces, saturating along deep paths.
- But no positional rule selects those pieces; root-most or nearest selection regrows.
- So the induction hypothesis should quantify over contexts: "for every ADMISSIBLE context of <= 4 tagged pieces,
  v has a compatible BDL partition". The missing ingredient is an intrinsic admissibility condition, local to v
  and its tagged pieces.
- This is the sibling penalty in a bounded form. It is the first time the context has been shown to stay finite.

**Q8 ANSWERED (audit, 10-03 ~14:30; runs/claude-audit-bdl-20261003/AUDIT.md).**
- BDL is verified exhaustively to n = 9 (9.7M decomposable cases), and P/P′ likewise. The paper claims are
  correct (two repairs).
- BDL, P and P′ also hold on ALL 8-point signotopes, decomposable or not. This is weak evidence, since n = 8 is far
  from extremal, but decomposability may matter only for the PROOF route (Lemma DS), not for truth.
- Refined obstacle: whenever a whole child sits in band j0, it must be split by the F-rule (first points of its max
  caps into j0, the rest into j0+1). That needs band j0+1 to be free in context. The difficulty lives entirely in
  the two bottom bands j0, j0+1, which matches Lemma M.

**Q7 progress (10-03 ~13:50, runs/claude-bdl-induct-20261003).**
- Proved: BDL ⇐ G (with reflections and duals). G(X,t): if cap(X∩(t,∞)) <= a-2, there is a BDL partition with the
  bottom band left of t.
- G's proof closes except S1/S2, which need Lemma M: the lifted piece E goes wholly into band k-a+1. M held in every
  test, but it is a CONTEXT statement with band-tagged sibling pieces.
- Obstacle: liftability into the second band depends on that band's maximal caps.
- Rotation rarely removes case R.

**Coordinator judgement.** This is the context-regrowth (sibling penalty) pattern in band language. Two questions
were commissioned:
- **Q7b:** is M's context form closed under B's splits with bounded tags, or do the tags regrow?
- **Q9 (step back):** is there a CANONICAL band rule (band = function of tree address plus sibling events), proved
  non-inductively? Uniqueness of band partitions on tight sets shows what the rule must be.

**Q6 consequence for BDL.** Case R has A nested in the core of B's β-caps. If A lies within a single gap of B
and B's tree splits there, the rotation lemma re-roots X into a non-nested split, where BDL closes. So the hard
residue of case R should be B-points inside A's span (interleaving). This is to be checked.

**New open questions.**
- **Q7 (THE target).** Find an induction hypothesis H, BDL in context, that implies BDL and is preserved at
  every DS root split, including case R. Prove it.
- **Q8.** Independent audit: re-verify BDL and P (n <= 9 exhaustive), and the paper claims (the DS-induction
  cases, BDL + P ⇒ gap).

## Open questions, and the specific computations that answer them

| # | Question | How to answer | Status |
|---|---|---|---|
| Q1 | Is N(P; α, β) always (window words) − (a monotone kill family K(P))? Is the extremal structure always a labelling? | Exact N for multi-gate and nested profiles, k=5..8, via the pure DS recursion | subagent runs/claude-uniform-20261003 |
| Q2 | What is K(P) for nested profiles, and what exactly is a union deficiency? | Same data, plus which words the extremal sets realise | same |
| Q3 | How do K(P_A), K(P_B) combine at a split (the recursion step)? | Child profiles of extremal sets; check whether K(P) is determined by K(P_A) and K(P_B) | subagent (kill-set form) and R24 (composition law of the true N) |
| Q4 | Was the context route's bound function wrong, and is its additivity failure explained by union deficiencies? | Compare the Lean Context bound with exact N | Sol R24 (host 20261003-095244-5d6c47), together with Q3 |
| Q5 | What is the injective map from points to words, as a rule on the tree? | Once K is known: test candidate rules (root-path letters filtered by zone events) | after Q2 |
| Q6 | Without the strong-set condition (k = infinity), is the zone-profile maximum N∞(P) a clean closed form proved by iterated endpoint splits? If yes, the window difficulty is purely the coupling cup(A)+cap(B) <= k-1; if no, union deficiencies are a classic phenomenon to understand first | Exact N∞ by the DS recursion on nested and multi-gate profiles (incl. kill-set failures 22, 122, 222, 1122/2112) | subagent runs/claude-kfree-20261003 | **ANSWERED 10-03:** separable profiles (all that k=∞ produces) have non-interleaved optima and a Pascal-type cut recursion; gated profiles (created by the coupling) show nesting and union deficiencies already at k=∞, and the kill-set window failures are classical effects. Rotation lemma: nesting in a single gap can be re-rooted away. |

**Computations that would NOT help** (do not commission): more gate instances at larger k; SAT certification of
k=7 states; Lean formalization of individual (a,u,k) gates. The exception is a structural lemma that any general
proof needs, such as Lemma DS itself or the generic peel.

## Earlier proof idea (superseded by BDL above)

If Q1–Q3 come out right, the proof is: by induction over the tree, every point gets a word in W(P) = (window words)
minus K(P), injectively, and the DS recursion maps W(P_A) and W(P_B) disjointly into W(P). There is no proof of
that step yet; it is exactly what Q3 must reveal.

## Obstacle

We do not yet know N for multi-gate profiles, and the union deficiencies are not understood.

## 2026-10-04 (morning): survey of combinatorial tools (runs/claude-survey-20261004/SURVEY.md)

Six area surveys (A–F), plus coordinator probes.

**Result.** No known tool proves MIXED ROOT, and the survey produced no proof idea for it.

**What the survey learned about the obstacle.**
- **A: the canonical layering fails only at overfull points [P + C].** The layering puts v in band cupEnd(v) − 1. It
  is valid unless some point has cupEnd(v) + capEnd(v) >= k + 2.
  - Overfull points come from mixed caps (Lemma DS).
  - Repairs are not confined to them.
  - Baek–Balko's split-gon theorem is this argument.
- **B: a root split cuts the window at one level [P, identity checked for k <= 12].** At p = cup A,
  T(a,p+1,k) + T(k−p,u,k) = T, so induction works whenever k−a < p < u−1.
  - The lock is the single degenerate level p = k−a. In Boolean terms, A must displace a star of level p of B_{k−2}.
  - Test (star_flow.py, cex40): relative to the best partition of B, ZERO B-points need to move; A is lifted to
    p+1. So the content is choosing B's partition knowing A's cuts (ZLOCK / tower), not flow through bands.
- **D: the A-side keep/lift choice is cheap and locally forced.** Every generic existence tool (Scarf, kernels,
  deferred acceptance, topological Hall, Nullstellensatz) works on B and fails at the mixed root.
- **F: the chain type τ is an exact k-free composition congruence;** Theorem 8 is a τ-statement. The witness
  (band) side does not compress.
- **SH [C, n <= 8 exhaustive + hard corpora + X14 + general signotopes].** Overfull Moshkovitz–Shapira labels
  inject into the unused window labels by sub-down-sets. SH is choice-free and implies Theorem 8, but it holds for
  general signotopes, so it is ES-strength. The gap between staircase and box is the ES difficulty itself.

**Refuted or closed.**
- Mirsky window (fails at n = 21, configH).
- Greene–Kleitman saturation (n = 8 witness).
- Kernel bottom-peel at mixed roots.
- One-band star exchange.
- Baek's ETV technique: a canonical peel, which the author says stops at a = 4.

**Purity, easy half [C, |X| <= 8 exhaustive].** Every constrained decomposable set below T extends by one point.
Point sets do not have this property (Damásdi–Dong–Scheucher–Zeng). The other half is Theorem 8 itself, so this
is not a route.

**Open leads.**
- Deficiency counting at the lock (submodularity of the deficiency over gap sets).
- τ-potential / learned all-k invariants (costly).

**Common obstacle (unchanged).** At the degenerate level, B's partition must be chosen in view of A's cut
positions. That choice needs global information about B, and no generic tool supplies it.
