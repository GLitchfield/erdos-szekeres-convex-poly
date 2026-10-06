# Claude research handoff: context-free routes to Theorem 8 (2026-10-02)

Coordinator session `claude-code:22c8132f-fa67-40ab-90d0-f8255f87797f`. All evidence is diagnostic (Python, plus
CaDiCaL via pysat). Nothing here is Lean-certified.

## Target and why

**Target.** Theorem 8 (`decomposableStateUpper_all`): a decomposable set X with no a-cap, no u-cup and no k-gon has
|X| <= T(a,u,k).

**Why this route.** The context route stalls at `ctx_bound_additive`, at the sibling penalty. This run looked for a
proof by *plain* strong induction on |X|, with no contexts.

## What is proved (on paper, checked exhaustively n <= 7)

Let X = L << U be a decomposable split: L lies far below U, with any horizontal interleaving, and every mixed triple
is a cup iff its middle point is in L. Checked by `verify_structure.py` on 14,988 splits.

- **(P)** Any cap of U together with any cup of L is in convex position, whatever the interleaving. Hence
  conv(X) = max(conv L, conv U, cap U + cup L). These are plain lengths: there is no positional condition.
- **(C)** cup(X) = max(cup U, max over cups C of L of |C| + [some U point left of C] + [some U point right of C]).
- **(A)** caps: the same as (C) with the roles of L and U swapped.

So positions enter only through the extensions of cups (of L) and caps (of U), and only through the extreme points
of the other part.

**Non-nested roots are easy.** Suppose the leftmost and rightmost points of X lie in different parts. Then every
L-cup gets at least one extension and every U-cap gets at least one, so:
- cup L <= u-2 and cap U <= a-2;
- by (P), cup L + cap U <= k-1.

Plain induction then gives |L| <= T(a, min(u-1, k-d), k) and |U| <= T(min(a-1, d+1), u, k) with d = cap U. The
splitting inequality closes the step; R19 has closed it in Lean (commit e2902639). No contexts are needed.

**The only hard root configuration is a NESTED split.** Both extremes of X lie in the same part, e.g. L lies inside
the span of U. Then U's caps get extensions only when they do not span L. This is exactly the one-level root
context problem (C1r etc.), now isolated.

## Refuted today

- **Lemma G** (job 20261002-102306-bf7f8c, `random-sp.txt`, `analyze_fail.py`).
  - Statement: if every c-cap of U crosses a gap, the left- or right-endpoint set F of the c-caps has
    cup(F) + cap(U-F) <= max(conv U, c+1).
  - It held on all signotopes n <= 7 (84,556 cases) but fails for a decomposable U with 9 points: X = {4} << U,
    (5,5,6).
  - It also fails without the gap condition, already at n = 6 (`lemma_g2.py`).
- **SP'** (job 20261002-103023-610177, `sp-sat/`; checked by brute force in `verify_sp_fail.py` and
  `general_split.py`).
  - Statement: a partition with cup A <= u-2, cap E <= a-2 and cup A + cap E <= k-1, i.e. a two-part plain
    induction that keeps k.
  - It held on all decomposable n <= 7 and on all extremal sets with T <= 8.
  - It fails on two random maximal (5,5,6)-free sets with n = 13: the best value of cup A + cap E is 6.
  - **Lesson:** at nested splits, any two-part induction must lower the polygon bound in both parts.
- **Explicit splitting rules** for the Pascal split:
  - greedy sweeps fail in one orientation (n <= 7);
  - tree-endpoint rules fail at n = 6 (`tree_rule.py`, 8 cases);
  - vertical cuts fail (`sp_cut.py`);
  - a hereditary Pascal split (restriction to every tree node is again a Pascal split) fails (`pascal_restrict.py`).

## Still alive

**PASCAL-SPLIT.** X = A + E where:
- A has no a-cap, no (u-1)-cup and no (k-1)-gon;
- E has no (a-1)-cap, no u-cup and no (k-1)-gon.

With Pascal-with-k, T(a,u,k) = T(a,u-1,k-1) + T(a-1,u,k-1), this gives Theorem 8 by plain induction.

Evidence:
- all decomposable n <= 7;
- all extremal sets with T <= 8;
- the two SP' counterexamples (64 and 86 splits; the minimum T-sum is 13 <= 14);
- all signotopes n <= 7. This last fact is weak evidence: a Pascal split for general sets would imply the
  Erdős–Szekeres conjecture.

A large SAT sweep on near-extremal sets (k = 6, 7, 8) is running: job 20261002-103504-6d9fb6, output `pascal-sat/`.

**No proof idea yet for nested splits.** Splitting the parts independently and pessimistically (`CPS` in the session
log) composes trivially. It fails only at points that are "doubly tight": cup-tight through context extensions and
cap-tight. Those points need the sibling's actual colouring, through the colours of the extreme points of each
level. This is the sibling penalty in split language.

## Open obligation

Prove or refute PASCAL-SPLIT for decomposable sets, or find a different two-part plain induction that handles
nested root splits.

## Evidence paths

All scripts are in this directory, each with a docstring. Two shared helpers:
- `chains.py`: polynomial chain statistics;
- `sp_sat.py`, `pascal_sat.py`: SAT checks with random maximal-set growth.

## Afternoon update (2026-10-02, ~11:10 local)

### Relation to the published proof and to August work

**Diagnosis.** The Baek–Balko step (child index from |L|, coupling a'+u' <= k-1) is sound at non-nested roots. The
documented boundary defect is exactly the nested case: L inside span U with U containing a spanning (a-1)-cap, or
the mirror. In the window regime this case is equivalent to:

    GAP BOUND  |U| <= G(a,u,k) := T(a-1,u,k) + C(k-3,a-3)

for U whose (a-1)-caps all cross a common gap. This is true, since it follows from Theorem 8.

**This equals existing work.**
- Experiment 0081 (`StructuralChargingPascalTails.lean`) already reduced E3 to two singleton-tail gates.
- Experiment 0086 isolated the diagonal a=4 family as "two cup blocks" (`DiagonalCupBlocksForce4kk`):
  - proved for k <= 8 by small theorems;
  - proved for k = 9 by a large CNF certificate;
  - open uniformly.

My "formalize the reduction" proposal (R20-PROPOSAL.md) is therefore withdrawn; see its correction section.

### New today (diagnostic)

- **The gates matter only for nested roots.** Non-nested roots close with R19's `split_le`.
- **G obeys the Pascal recurrence** G = G(a,u-1,k-1) + G(a-1,u,k-1).
  - The gap class is closed under Pascal splits: E must have no (a-2)-cap on either side of the gap.
  - Gap-compatible splits exist in every hard nested case tested: job 20261002-104722-230b99, about 2.5k cases
    incl. about 750 tight, plus all decomposable n <= 7.
  - So do double-cap splits (double_cap.py).
- **DELETION LEMMA (a=4).** This is the gap-compatible split for two cup blocks P|Q with no 4-cap, no k-cup and no
  k-gon: delete at most one point per block so that no (k-1)-cup and no (k-1)-gon remain.
  - It implies the uniform two-cup-block lemma by induction on k.
  - It holds on ALL signotopes up to n=8 (cupblock_general_dfs.py: 6,301 signotopes, 12,607 splits incl. 3,816
    tight), so decomposability is not needed.
  - No fixed rule chooses the deleted points (cupblock_delete.py).
  - n=9,10: job 20261002-110426-e6862c.
  - A Claude subagent is attempting a uniform proof, working in runs/claude-cupblock-20261002/.
- **PASCAL-SPLIT sweep** (job 20261002-103504-6d9fb6): no failure on 13,860 near-extremal sets at k=6,7,8.

### Current proof idea and obstacle

**Idea.** Prove the tail gates by induction on k through gap-compatible Pascal splits. For a=4 this is the deletion
lemma; general a would follow by induction in a, with E being (a-2)-cap-free per side.

**Obstacle.** No canonical choice of the deleted points / E-set is known, even at a=4. Any canonical rule must use
global cup/gon structure; the junction and extreme points are not enough.

## Late-morning update (~12:30): a=4 family closed on paper; a=5 open

- **PROVED (paper, verified by the coordinator):** the uniform two-cup-block lemma = `DiagonalCupBlocksForce4kk k`
  for all k >= 5, on general signotopes.
  - Mechanism: every maximum strong set meets D = {2nd point of left cup, 2nd-to-last of right cup}, and induction
    on k.
  - Write-up: runs/claude-cupblock-20261002/NOTES.md.
  - Formalization plan: runs/claude-cupblock-20261002/FORMALIZATION-PLAN.md.
  - Via existing Lean reductions this gives `SingletonLowerPascalTailGate 4 k k` for all k >= 5. Not yet in Lean.
- **a=5** (runs/claude-twoside-a5-20261002/NOTES.md). The two-side bound holds by SAT on general signotopes
  through (5,6,7). Gap-compatible splits exist, but in tight cases E must be a whole tight a=4 block chosen jointly
  across the gap. No canonical/pointwise rule exists (SAT-UNSAT over 13 statistics). Hand lemmas:
  - L1: layer lemma;
  - L2: u=k-1 reduction;
  - L3: E0 cup-killing.
- **Remaining gates for diagonal k=7:** TwoSide(5,6,7), (5,7,7), (6,5,7), (6,6,7), (6,7,7). The (4,7,7) lower gate
  and its dual are now covered.

**Current idea for a>=5.** The step k -> k-1 is a 2-colouring: E is two cups (per side) with no 4-cap and contains
no strong (k-1)-set, and every strong (k-1)-set of U meets E. Then |E| <= 2k-6 by the a=4 lemma, and induction
handles U-E.

**Obstacle.** The existence of such an E is unproved. It is not canonical, and E depends on both sides of the gap.

## Afternoon update (~15:45): a=4 in Lean; decomposable a=5 rests on R2

### Lean (R20, closed on branches, not yet on main)
- `diagonalCupBlocksForce4kk_of_five_le`: c89df0e8.
- `singletonLowerPascalTailGate_four_diagonal_of_five_le`: 82a57072.
- Integration prepared on `integration/r19-r20-20261002` (runs/claude-integration-r19-r20-20261002/PLAN.md).

### R21 (Sol, launched 15:20)
Port Baek's ETV (n,4,n) theorem, which is (S), and assemble `DecomposableStateUpper 4 k k` for all k from the gate.

### Decomposable a=5 two-side bound (paper, plus SAT where marked)
- Root-split case analysis: runs/claude-twoside-a5c-20261002.
- Tools, all proved by hand:
  - the Z bound (v-1)^2;
  - two cups <= 2u-3; three cups <= 3u-6;
  - R1 (three cups with no strong k-set <= 3k-8): k>=8 by hand, base k<=7 by SAT;
  - MARKER LEMMA (runs/claude-h1-20261002): if every max cup straddles a gap, |A| <= m(m-1). This closes H1 and the
    singleton chains.
- **Only R2 remains open** (cup | 4-cap-free side <= T(4,u,k)+k-4). It is SAT-checked; a second attempt is running
  (runs/claude-r2b-20261002).
- (S) is Baek's Theorem 2.7, with a Lean 4 source.

### Current idea / obstacle (a=5)
- **Idea.** The polygon coupling puts the low part in the classic regime, where endpoint arguments are exact. The
  k-gon condition only acts on a=4 objects (cups, cup blocks, 4-cap-free sets).
- **Obstacle.** R2: 4-caps starting in the cup P interact with Q's cup layers. No invariant is known that both
  forces a gon and survives a deletion.

## Evening update (~20:50): kill-set rule; a=6 u=k-1 attack launched

### Kill-set rule (runs/claude-killset-20261002/NOTES.md; SAT diagnostic)
- **KS (single gate).** Take blocks with cap deficiencies: q blocks with d=1 (one is the hub), at most one gate with
  d=s, and p point blocks with d=a-2. Unions satisfy only the global bound a-1. Then
  max = T(a-1,u,k) + sum_{i<=q-2} C(k-3-i,a-3) + C(k-1-q-s,a-2-s) + p.
  - This is T minus an explicit monotone kill family of bottom labels.
  - It specializes to TS, R_s, Theta_s and the four-cup bound.
- **Evidence.** Exact on 92 in-class profiles (261 instances), including a=6 and general signotopes.
- **Failures.** It fails with two or more gates (profiles 22, 122, 222 at a=5; the block order matters there). The
  extremal examples nest a cup block between upper points, so a multi-gate rule needs union deficiencies.
- **Proof idea (classic part), a hand sketch.** Iterated endpoint split: E_{j+1} = first points of (a-1)-caps in
  E_j. Each D_j = E_j \ E_{j+1} has no (a-1)-cap and no (m-j)-cup, and E_j lies in the first q+1-j blocks. Summing
  gives exactly the classic part. The labels D_j <-> U^j D are the kill-set labels.
- **Window part.** KS obeys V(a,u,k) = V(a,k-beta,k) + T(beta+1,u,k) for medium beta, so those root splits close by
  induction. Still open: A meeting the hub, and small beta.

### Consequence
The block lemmas have one closed form, and its classic part has a natural proof. Beyond one gate, the a=6 u=k-1 core
N2d is a three-gate profile (222), where no rule is known yet.

### Launched
A Claude subagent on the a=6 u=k-1 cores (runs/claude-a6u1-20261002): the N1c marker case, N2d and N2f. Two runs
stalled at the marker-case F-branch, so the brief requires stepping back first: say why the bound holds, then test
explanations, not case splits.

## 21:20 update: (6,k-2,k) audited; integration pushed
- **Audited:** runs/claude-audit-6k2k-20261002/AUDITED-PROOF-6k2k.md (COMPLETE-WITH-REPAIRS). The decomposable
  two-side gate at (6,k-2,k) has a paper proof for all k >= 7; (6,5,7) is paper-done.
  - It needs no external input: every T at u=k-2 is classical.
  - The reservoir C(k-3,3) is carried by Z6 or by R2-6's extra C(k-4,2).
  - Six repairs, none changing a statement. The notable one is Theta_cup, needed in R_3.
- **Main = fd27c532 (pushed):** the a=4 gate (R20), Baek's bound and the (4,k,k) assembly (R21), and R19's 16 results.
- **k=7 milestone, remaining paper work:** (6,6,7) and (6,7,7), i.e. the a=6 cores at u=k-1 (N1c marker, N2d
  three 4cf blocks, N2f R2-6(k-1)), under attack in runs/claude-a6u1-20261002.
- **Lean:** R22 is on (5,k-1,k), with helpers closed; (5,k,k) is its priority 2.

## 21:45 update: a=6 u=k-1 reduced at k=7; gate assembly in Lean
- **runs/claude-a6u1-20261002 (hand proofs, unaudited; SAT diagnostic).**
  - The marker case H1-6 is a double gate: q is the cap gate and b the cup gate.
  - Mechanism: ABSORPTION. A marker point lies only in 3-caps or 3-cups, so absorbing it into a block-cap-free part
    saves one point.
  - Theorem P (all k) closes every row except R1 and R2.
  - Theorem D (k=7 only, by bit-flip self-duality) sends R1 and R2 to N2d(7) and R2-6(6,7).
  - Theorem N reduces N2d to its marker case N2d-M; N2d-M(7) is SAT-UNSAT at 24.
  - => (6,6,7) now rests on R2-6(6,7) (binding core) plus hand proofs of N2d-M.
  - Next run: runs/claude-r26u1-20261002 (sharded SAT decision plus a hand proof of R2-6 at u=k-1).
- **Lean.** `decomposableStateUpper_of_lower_gates_at` compiles (scratch; node registration running on branch
  node/DecomposableStateUpperOfLowerGatesAt, merge approved by Gavin).
  - It says: Theorem 8 for all (a,u) at fixed k follows from the lower gates at k.
  - Corollaries compile: Theorem 8 at k=5 unconditionally, and Theorem 8 at k=7 from exactly five gates (5,6,7),
    (5,7,7), (6,5,7), (6,6,7), (6,7,7).

## 00:45 (10-03) update: R2-6(6,7) settled by SAT; k=7 status
- **runs/claude-r26u1-20261002.**
  - New hand lemma DS: caps meeting B are a+D+a′, so each part sees only the extreme points of the other per zone.
    This gives an exact zone-profile recursion, which makes the k=7 SAT instances decidable.
  - R2-6(6,7) max is exactly 28 (29 UNSAT, all 272 root pairs); the marker case max is 27; N2d(7) max is 24.
  - Hand Theorem R (all k) closes the R2-6 u=k-1 table, given sub-lemmas MC, N2d, ThC5, R3, L3S. MC reduces to
    leaves DM and L2 (tight at k=7) plus L6/L7.
- **k=7 milestone status** (five lower gates needed beyond (4,7,7), which is in Lean):
  - (5,6,7) and (5,7,7): audited paper; R22 is formalizing them (R1, R2, extremal deficit closed overnight).
  - (6,5,7): audited paper, all k; R23 will formalize it.
  - (6,6,7): hand rows plus unaudited Theorems P/D/N/R plus SAT at k=7. Needs an audit.
  - (6,7,7): u=k cores N2d(u=k) [25] and R2-6(u=k) [29] are open.

## 01:10 (10-03) update: all five k=7 gates supported
- **Values at k=7.** G(5,6,7)=21, G(5,7,7)=22, G(6,5,7)=24, G(6,6,7)=29, G(6,7,7)=30. A log entry once wrote 28 for
  G(6,6,7); that was a slip, since 28 is the R2-6(6,7) and H1-6 bound.
- **runs/claude-a6uk-20261003.**
  - Decomposable SAT through the Lemma DS recursion: G(6,7,7) <= 30 and G(6,6,7) <= 29 directly, both attained.
  - Hand: Lemma U0 (no marker core at u=k, by (P)) and Theorem U (the u=k table reduces to the u=k-1 results plus
    the u=k block lemmas). N2e reduces to L3S.
- **Status.** (5,6,7), (5,7,7) and (6,5,7) have audited hand proofs. (6,6,7) and (6,7,7) are SAT-verified at k=7
  (decomposable, diagnostic, no DRAT), with unaudited hand reductions. The audit of (6,6,7) is running
  (runs/claude-audit-667-20261003).
- **General-k obstacle** (the next research target after k=7): the self-similar marker leaves (H1-6 R1/R2, N2d-M,
  DM, L2) and the three-block a=6 lemmas ThC5, R3, L3S. Each needs the reservoir C(k-3,3) carried through several
  blocks, and no fixed structure is known to do that. The kill-set rule predicts the losses but is unproved in the
  window.
- **For Lean at k=7:** the two a=6 gates (6,6,7) and (6,7,7) currently rest on SAT. Either formalize the hand proofs
  once audited and completed for all k, or certify k=7 by a DRAT/LRAT certificate route; the latter needs the
  certificate pipeline and a decision from Gavin.

## 01:50 (10-03): (6,6,7) audited
- runs/claude-audit-667-20261003/AUDITED-PROOF-667.md (COMPLETE-WITH-REPAIRS): G(6,6,7) <= 29 by hand, from:
  - T(5,6,7), H(7) <= 21 and G(6,5,7) <= 24;
  - two SAT verdicts at k=7, N2d(7) <= 24 and R2-6(6,7) <= 28.
  29 is attained.
- Theorem D (duality) is valid at k=7 only. Theorems P, N, R and Lemma DS hold for all k.
- Lean note: "subsets of decomposable sets are decomposable" = IsDecomposableOn.subset (exists).
- **k=7 gate evidence summary.**
  - (5,6,7), (5,7,7), (6,5,7): audited hand proofs.
  - (6,6,7): audited hand proof, modulo 2 SAT verdicts.
  - (6,7,7): SAT plus unaudited hand reduction (Theorem U).

## 10-03 generalization effort (to ~15:30). Living document: runs/claude-general-picture/GENERAL-PICTURE.md

**Method change (Gavin).** Specific cases are tools for finding the general statement, never progress in
themselves. The rule is in CLAUDE.md/AGENTS.md (d63b3fb8).

**General conjectures found.** All are diagnostic; none is proved.
- **BDL (Band Decomposition Lemma).** A decomposable X with no strong k-set splits into bands X_j with
  cup <= j+1 and cap <= k-1-j. ES per band then gives T(a,u,k) for ALL parameters.
  - Verified exhaustively to n = 9 by independent audit; holds on all 8-point signotopes.
  - Its bands are the blocks of the ES lower-bound construction.
- **PSL (Pascal split with strong number).** X = R ∪ Bl with cap R <= β-1, cup Bl <= α-1, both strong <= k-2.
  - Proves Theorem 8 by induction on k.
  - Structurally stronger than BDL: every PSL split extends to a full word labelling, which implies BDL.
  - Exhaustive to n = 9.
- **J (one-sided joints).** The bottom band is one-sided w.r.t. the cap core and the top band w.r.t. the cup core,
  in some orientation. Exhaustive to n = 8.
- **Frame lemma (PSL).** One of four one-sided classical frames extends to a PSL split. Exhaustive to n = 9.

**Proved on paper (unaudited unless noted).**
- Lemma DS (audited): "no strong k-set" is local at each tree node.
- BDL => Theorem 8.
- BDL <= G, with G restated with the core hypothesis.
- U + U′ => BDL.
- The wide–wide composition lemma for J.
- TDF is correct when case-R siblings have <= 2 bands.
- Rotation lemma.
- Separable profiles are closed under DS (k=∞).

**Refuted proof strategies, each with its mechanism.**
- Single kill families (Q1).
- Top-down DS induction with bounded intrinsic contexts. The needed context is bounded (<= 4 pieces) but is
  chosen globally, i.e. lookahead (Q7b, Q7c).
- Canonical band rules: partitions are massively non-unique (Q9).
- Composition of universal partitions (Q9b).
- G for all cuts (counterexample n = 25, empty cores) (Q9c).
- Point insertion: unbounded repair distance (Q11).
- PSL under separable profiles: the double-saturation squeeze, which already occurs at k = ∞ (Q13).
- Every lookup or sweep rule for PSL (SAT-UNSAT) (Q14).

**Understanding.**
- The only obstruction, in every formalism, is the tight nested split (= the Baek–Balko gap).
- Its precise form: a strong set is a cup plus a cap with shared ends, so placing a point requires coordination
  between two chains. No local, sweep or tree-order rule can provide it.
- Tree-order induction is the wrong order; even the classical split is proved globally.

**Current proof idea.** A global existence theorem (Hall- or matroid-type) for the band list-colouring (BDL) or the
2-colouring (PSL). In the frame form, PSL is a transversal problem: E meets all strong (k-1)-sets of X∖Fp and
stays independent with Fp. This is Q12, in progress. Also running: classic-block insertion (Q9d), Sol R25 (BDL
proof), Sol R24 (context bound vs truth).

**Open obligation.** Prove BDL or PSL for decomposable sets, or find the global theorem that implies them.

## 10-03 evening (to 19:15; session stopped at usage limit)
- **Added since 15:30 (all diagnostic unless noted):**
  - Q9d–Q9h: J + LL induction, closure fails at n=7 by regrowth; realignment needs swap "stars".
  - Q15/Q18/Q20/Q22: PSL's case R reduces EXACTLY [P] to the context-free CORE. Its cap and cup parts are proved
    by hand; the gon repair is a global hitting set (no local rule, no Hex dichotomy, LLL fails, polytope not
    integral).
  - Q16/Q21: no polymorphisms; PSL width grows; W (width <= α+β−3) ⇒ PSL [P].
  - Q24: rectification has no local move lemma. Lemma S [P]: the strong number is interleaving-invariant; the
    obstruction is the "locked" nested split.
- **Meta-insight.** PSL, CORE and the frame lemmas hold for general signotopes, so any proof of them must use
  decomposability essentially, or it would prove ES for signotopes.
- **Open obligations:** BRL+ (Sol R25), or CORE + HIT.
- **Evidence:** the run directories named in GENERAL-PICTURE.md. Stopped subagents: Q17, Q23 (partial).

## 10-03 late evening (to 23:45)
- **Lean, main 701ff379:**
  - Theorem 8 ⇐ BDL (decomposableStateUpper_all_of_bands, checked, standard axioms);
  - integrated general foundations: Lemma DS, the classical bound, the cap-start peel, the lower construction,
    gluing and pushforward;
  - the library promotion.
- **Sol R24 (done):** the context-route bound is not the true maximum (two-cap obstruction); 12 general Lean lemmas,
  of which the general ones are integrated.
- **Sol R25 (done):**
  - BRL+ is refuted at n = 24;
  - paper81 closes all non-mixed hard roots;
  - BDL ⟺ MIXED ROOT (audited as a conditional reduction).
- **Tower (Q17):** a two-sided tower language always admits a proof (n <= 41), but there is no local or bottom-up
  closed form (Q25).
- **ZLOCK:**
  - true everywhere tested;
  - the case-R lock splits as ZLOCK(lo = 1) + P(lo >= 2);
  - every P/BRL+ failure has lo = 1.
- **Audit:** two step-lemma repairs (single-point absorption at lo = 0; reserve with lifts); everything else
  correct.
- **Open obligations:** ZLOCK at lo = 1 (tight, two-sided mixed z) and P at lo >= 2, for >= 3 bands.
- **Running overnight:** Sol R26 (MIXED ROOT, host 20261003-225522-ecedf1, until about 10:55) and the P-at-lo>=2
  subagent (runs/claude-plo2-20261004).

## 10-04 early morning (to 02:45)
- **P at lo >= 2** (runs/claude-plo2-20261004): the both-sided form is false (n = 19); the one-sided S1 is the
  needed form; the hard core is configuration H.
- **Configuration H** (runs/claude-configH-20261004): **S1 is FALSE at l = 2** (n = 40, k = 8; 25 counterexamples).
  Keep-all fails in case R. BDL held at every placement tested.
  - Proved: the H structure, the ENDLIFT lemma, partial cases.
  - The orientation rule: failures only when both sides are "hard".
- **Lesson:** one-sided simplifications fail at larger n (BRL+ at n = 24, S1 at n = 40). The lock needs keep-or-lift
  flexibility, i.e. MIXED ROOT as R25 stated it.
- **Open obligation:** MIXED ROOT (Sol R26 running, until about 10:55; notes 1–3 left in its run directory).
- **No proof idea yet** that handles keep-or-lift globally.
