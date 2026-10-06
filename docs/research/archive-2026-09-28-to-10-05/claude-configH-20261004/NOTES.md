# Configuration H (claude-configH-20261004)

[P] = proved by hand here. [C] = exact computation, diagnostic, not Lean.

## 0. Result: S1(H) is false at l = 2, and so are S2 and keep-all [C]

- **Counterexample** (`cex40.txt`). n = 40, k = 8, (α, β, σ) = (5, 5, 7), core (14, 23).
  - B = P << Q is configuration H with both mixed kinds: |P| = 12, |Q| = 28.
  - No valid partition has bottom ⊆ [0, 14] or ⊆ [23, 39].
- **Checks.** Each side has a deletion-minimal failing subset (31 and 28 points, `cex40_mus.pkl`). A subset keeps B's bands and side restriction, so B fails too.
  - Each subset is infeasible by harness `partition_sat`, by the audit's independent backtracking and by harness `find_partition` (`o_verify_mus.txt`).
- **Found by** a random walk in H (`hwalk2.py`) started at the doubly-hard instances. It gave 25 distinct failures, all in the family (k, β, l, α) = (8, 5, 2, 5), n = 40.
- **S2** (one-sided bottom at every core gap) holds on 24 of the 25. It fails on #6 (core (14, 24)) at gaps 16 and 17 (`o_s2all.txt`).
- **Case R (X = A << B, A a nested tight cap, cap X = β):**
  - #6: keep-all fails at 45 of 275 placements of 2- and 3-point A, for example A = 2 points at gap 16. One or both A-points must be lifted.
  - #1: keep-all fails at 126 of 495 nested 4-point caps and 546 of 1,287 nested 5-point caps.
  - BDL(X) holds at every placement tested (`o_cr_test*.txt`, `cr_branch.py`).
- **Consequence.** "Case R ⇐ ZLOCK(lo=1) + S1(lo≥2)" breaks at lo = 2, just as BRL+ broke at lo = 1. zlock's keep-all and OUTER observations do not extend to these nodes.
- **So lo ≥ 2 needs a keep-or-lift statement for multi-point A**, the ZLOCK analogue.

## 1. Structure of H [P; re-checked on 841 instances]

- **Caps.** The only interleaving constraint is that no (β−1)-cap of Q has P-points beyond both of its ends.
  - The β-caps are PP, x+D, D′+x′ and x+E+x′.
  - L* and R* are P-points.
- **A right-extended D′:** starts left of min P, ends after L*, and every P-point after it is ≥ R*.
- **A left-extended D (mirror):** ends after max P, starts before R*, and every P-point before it is ≤ L*.
- **Other facts.** cap(Q ∩ (min P, max P)) ≤ β−2. B ∩ [0, L*] and B ∩ (L*, n) each have cap ≤ β−1.
- **Which side does what.** Side L must neutralise the D′+x′ caps, side R the x+D caps. If one kind is absent, the facing side works.

## 2. The fold

- **The fold is G_L = {min D′ : D′ right-extended}.** It lies entirely left of P.
- **ENDLIFT [P]** (given BDL for Q; consistent with an exhaustive n ≤ 8 test, 1,095,080 cases).
  - For a BDL partition π of Q, let F = the first points of the right-extended caps inside π_{l+1}.
  - Then cup F ≤ l+1, by the endpoint lemma inside π_{l+1}.
  - Moving F down frees band l+1 for the P-points right of L*, whose caps have length ≤ β−1 (Tower Closure).
- **Cost.** F sits left of all of P, so the bottom's P-part must have cup ≤ l. Hence bottom ∩ P = F_P at 235 of 241 working sides.
- **Plain induction fails.** At 35 of 109 two-sided instances no bottom meets every β-cap, so the β-caps are split over bands l+1 and l+2.

## 3. Proved pieces and gap

- **(A) [P].** If cup(P ∩ [0, L*]) ≤ l and cup G_L ≤ l+1, then S1-L holds (Lemma H).
- **(C1) [P].** If cup P_≤ ≤ l and cup P_> ≤ l, then S1-L holds: bottom = P_≤ ∪ F, band l+1 = P_> ∪ (π_{l+1}∖F).
- **Conditional cases [C].**
  - **(C)** cup P_≤ ≤ l. Only one cup condition is missing: π_{l+1} must not surround an (l+1)-cup of P_>. The shape held at 71 of 71 sides.
  - **(B)** cup G_L ≤ l+1. The shape bottom = (P_≤ ∩ U_l) ∪ (subset of G_L), with the rest of P in band l+1, held at 397 of 397 sides.
  - The obstruction in (B) is the x+D caps after the cup-tops of P_≤, which cannot be broken from the left.
- **Explicit orientation rule [C].** Call side L hard when cup P_≤ = l+1 and cup G_L ≥ l+2 (mirror for R).
  - Every side failure was hard: 65 collected, 564 in the search, and every walk state.
  - Every side that was not hard worked.
  - When both sides are hard, S1 can fail at l = 1 (4 of 379) and at l = 2 (25 of 1,030 walk states in (8,5,2,5)).
- **l = 1.** ZLOCK's lift worked at every core gap of all 379 H instances. No proof.

## Evidence

- **Collection:** 777 H instances (samples, the n = 19 witnesses, R25's n = 24 set, zlock/tower corpora, new samples).
- **Jobs, prefix 20261004-:**
  - 012626-604ae3, 015240-d484f7, 015241-052151 (collection)
  - 014418-44202e (search)
  - 020653-d9f733 (walk; stopped at 320/660 walks, 2,031 states)
  - 020021-d7fb1a (ENDLIFT)
  - 021641-562e17 (re-check)
  - 022325-a6f0c5, 022459-f2315f, 023056-9068cd, 023118-4bb992 (case R)
- **Code:** `hlib.py`, `hcollect.py`, `hs1–13.py`, `hz.py`, `hmus.py`, `endlift.py`, `hwalk2.py`, `verify_*.py`, `cr_*.py`, `s2all.py`.
