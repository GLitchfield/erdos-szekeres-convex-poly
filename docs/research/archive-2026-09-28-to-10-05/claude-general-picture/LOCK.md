# The lock: what every route needs at the one hard configuration

Coordinator synthesis, 2026-10-03, ~22:05. Sources: GENERAL-PICTURE.md and the run directories cited there.

## The configuration

Take a root split X = A << B (A lower) with β = cap X = cap B. A lies strictly inside the core of B's β-caps: every
β-cap of B starts at or before L* and ends at or after R*, and A ⊂ (L*, R*). The core may be degenerate (L* = R* = z).
- **Locked (Q24):** sliding A out of the core would extend a β-cap of B. So A cannot be un-nested monotonically.
- **Tight (case R):** additionally cup A = k−1−β, so the strong budget is used up at this node.
- The mirror (cup roles) is symmetric.

## What each route needs here

| Route | Requirement at the lock | Status |
|---|---|---|
| BDL via BRL+ (R25) | B has a valid band partition whose bottom band j0 = k−1−β lies entirely <= L* or entirely >= R*. Then A is absorbed into j0 by DS. | Unproved; holds to n = 9 |
| BDL via J+LL (Q9d–Q9f) | Exact lift criterion [P]. If A's wrong-side points are lifted to j0+1, there must be no (β−1)-cap of band j0+1 entirely beyond a lifted point. Iterated nesting adds one (length, cut) pair per level. | Regrows at n = 7 |
| BDL via towers (Q17) | Single-point absorption [P] for Y = {z} << C. z stays in band lo iff lo >= 2, or C's band 1 is one-sided of z. z lifts to lo+1 iff band lo+1 has no (β−1)-cap ending before z AND none starting after z. Two-sided towers are needed exactly when R* <= z <= L*. | A language proof exists on every instance; selection is non-local |
| PSL via CORE (Q15/Q18) | B (cored) has a 2-colouring with every β-cap bichromatic, every α-cup red-hit, and every (k−1)-gon bichromatic (A all blue). Cap and cup parts are proved [P]; the gon repair is a global hitting set. | Unproved |
| Local frame lemmas (Q23) | A sibling of 1–2 points "anchors" B: near-maximal chains of B become maximal. The induction needs statements that allow anchor points. | Open |
| Rectification (Q24) | The n = 14 trap: a single upper point locked against R*. | Open |

## Synthesis: the single-point lock

Every row's hard core already appears with |A| = 1 (Q17's degenerate core, Q23's anchors, Q24's trap). The proved
single-point absorption lemma turns BDL for {z} << B into a pure statement about B:

> **ZLOCK(B, z).** For a decomposable B (cap β, cap core [L*, R*], >= 3 bands) and a lower point z at any position
> in the core, B has a valid band partition such that EITHER
> - (stay) the bottom band is one-sided w.r.t. z (or lo >= 2), OR
> - (lift) band lo+1 has no (β−1)-cap ending before z and none starting after z, AND, when lo = 0, B's band 1
>   lies on one side of z. **Audit repair (10-03 22:40):** §4.5(b) is false at lo = 0 without this clause;
>   counterexample labels (100,0,101,11), k = 4.

**Conjectured reduction.** In case R, the absorption of a general nested A, and hence the BDL step at every lock,
follows from ZLOCK applied repeatedly, one point of A at a time, each time to the growing upper part, together with
the proved step lemmas: wide–wide, keep, Tower Closure, and single-point absorption as repaired. **Audit (22:40):** 'reserve' is FALSE in concatenation when points are lifted (labels (01,11,000,101,001,1000,1001), k=6, Z={2,4}), so it may be used only without lifts.

If this reduction holds, then:
- the entire difficulty of BDL (hence of Theorem 8) is ZLOCK, a statement about ONE point in ONE core;
- BRL+ is ZLOCK's "stay" branch at every z, which is stronger than needed; ZLOCK allows the "lift" alternative;
- the n = 14 trap and Q23's anchors are ZLOCK instances.

## What to check (subagent)

1. Is ZLOCK true? Test exhaustively at small n and on all hard instances (TDF failures, osj n = 25, nested n = 25,
   Q24's n = 14 trap, residue sets).
2. Does the conjectured reduction hold, i.e. can case-R absorption of A be sequenced point by point through ZLOCK
   instances (in some order of A's points)? Test it, and find the order rule.
3. How does ZLOCK relate to CORE? Does a ZLOCK partition induce a PSL⁺ colouring, or conversely?
4. Is ZLOCK provable? It has a single point parameter, so ask whether it composes under B's splits, or admits a
   direct argument from "every β-cap starts <= L*" and Lemma S.


## Update 22:55: R25 final (runs/worktrees/sol-12h-20261002/runs/r25-sol-20261003/MATHEMATICAL-HANDOFF.md)

- **BRL+ is REFUTED at n = 24.** A child with c4/d5/σ6, core (6,15) and bands 1..3 admits no bottom band on either
  side of the core. So the BRL+ row above is a false lemma, and invariant P / G_core (both sides) fails at n = 24.
  BDL itself is not refuted: an ordinary singleton-parent map is valid.
- **Paper81 (proved on paper) closes every hard root with NO MIXED maximum β-cap**, for EVERY supplied valid map of B.
  F = the first points of A's max β-caps go to bottom, and A∖F to band 2.
- **The exact residue is MIXED ROOT.** It is tight (c(A) = p = s−β, c(B) = α, d(B) = d(X) = β), and a maximum β-cap
  of X meets BOTH A and B, i.e. A's points extend B's (β−1)-caps. A valid partition of X must then be built, where
  points may change bands.
- **BDL ⟺ MIXED ROOT** (conditional size induction proved).
- **Mechanism (paper74):** an inner insertion can keep both exact max-chain families yet create a regional
  (β−1)-cap that an outer point extends. Regional merges need prefix, suffix and two-endpoint interval ranks.
- **So the lock's precise form is MIXED ROOT.** ZLOCK's "lift" branch is exactly the single-point case of handling
  mixed max caps.


## Update 23:40: ZLOCK results (runs/claude-zlock-20261003/NOTES.md). The lock splits by lo = cup A = s−β.

- **lo = 1 ⟺ |A| = 1** (a single nested point) [P]. Here P/BRL+ can FAIL (n = 13; R25's n = 24), but **ZLOCK
  holds** on everything tested. Its "lift" branch rescues exactly the tight, two-sided-mixed cases (only 15 pairs need
  it, all with |X| = T = 25).
- **lo >= 2 ⟺ |A| >= 2.** Case R closes by keeping all of A in band lo whenever B's bottom band is one-sided of A's
  span (P). This held at ALL 2,020 multi-point case-R nodes. P held on all 1,697 sets and 7,754 cuts with lo >= 2.
- **Therefore case R ⇐ ZLOCK(lo = 1) + P(lo >= 2).** Both are statements about B alone with ONE cut. They are true in
  all tests but unproved for >= 3 bands. ZLOCK and P are proved for 2-band sets.
- **Neither composes context-free.** Composition needs an orientation bit, which is Q17's tower again. But one point
  always suffices: NO regrowth in the number of points.
- The point-by-point reduction is void; there is an exact joint keep/lift criterion [P].


## Update 01:30 (10-04): P at lo >= 2 (runs/claude-plo2-20261004/NOTES.md)

- **The both-sided P is FALSE at l = 2, 3** (n = 19).
- **The ONE-SIDED form S1 holds** (bottom ⊆ [0, L*] OR ⊆ [R*, max]; about 4,700 sets), and it is what case R needs.
  So the lo >= 2 target is S1.
- **The hard core is configuration H:** B = P << Q with c(P) = l+1, d(P) = β, c(Q) = α, d(Q) = β−1. The l = 1 BRL+
  failures are also of type H.
- **Working sides** put F_P (the first points of P's β-caps) in the bottom band, plus outer Q-points "folded" in on
  the same side.
- **Proved:** Lemma H; H with only one kind of mixed cap.
- **Gap:** H with both mixed cap kinds; the orientation is decided by a cup condition on B∖F_P.
- **Open obligations now:** ZLOCK(lo = 1) and S1(lo >= 2). Both are hardest at configuration H with both mixed cap
  kinds.


## Update 02:45 (10-04): configuration H (runs/claude-configH-20261004/NOTES.md). S1 is FALSE at l = 2 (n = 40).

- 25 counterexamples at k = 8, (5,5,7), n = 40, with minimal failing subsets checked three ways. Keep-all fails in
  case R; S2 fails. **BDL holds at every placement tested.**
- **The reduction "case R ⇐ ZLOCK(lo=1) + S1(lo>=2)" BREAKS at lo = 2.** lo >= 2 needs keep-OR-LIFT for multi-point
  A, i.e. the full MIXED ROOT.
- **Proved:** the H structure, the ENDLIFT lemma (the fold = the first points of right-extended Q-caps, which can
  always be moved to the bottom), (A), (C1).
- **Explicit orientation rule [C]:** failures occur only when BOTH sides are "hard": cup P_<= = l+1 and
  cup G_L >= l+2 (and the mirror).
- **PATTERN:** every one-sided simplification fails at larger n (BRL+ at n = 24, S1 at n = 40), while BDL survives.
  The lock genuinely needs keep-or-lift flexibility.
- **Step back (rule):** more one-sided narrowing is not productive. The next attempt must handle keep-or-lift
  globally, i.e. MIXED ROOT as R25 stated it (now with R26).


## Update 11:10 (10-04): R26 final, plus the survey

**R26** (runs/worktrees/sol-12h-20261002/runs/r26-sol-20261003/MATHEMATICAL-HANDOFF.md): full singleton MIXED ROOT is
unproved and unrefuted. No compatible-map proof idea; papers 1–73.

**What R26 established:**
- General ROOT is constructed when strong B = cap B = β, so the singleton extra strong unit is the whole residue.
- Disjoint grouping closes the lowercup <= p+2 and uppercap <= β−2 roots.

**Shortcuts refuted on paper:**
- the endpoint-frame peel (37);
- one-point max-cup-transversal peeling (73);
- lowercup <= 2 at full-cell roots (72);
- the Y-map fixed-budget reduction (70).

**Still running:** seven SAT jobs (n24 CEGAR, plus six equivalent n25 encodings). An n25 model would contradict
Theorem 8 at (6,5,7), so they are expected UNSAT. Reviews were set for 15:05.

**Survey** (runs/claude-survey-20261004/SURVEY.md):
- **The lock is the degenerate window level p = k−a.** In Boolean-lattice terms, A displaces a star of level p.
- **On cex40, zero B-points need to move** relative to the best partition of B. The content is choosing B's
  partition in view of A's cuts.
- **The canonical cupEnd layering fails only at overfull points,** which come from mixed caps.
- **Every generic existence tool fails exactly here.**
