# Coordinator note 3 (2026-10-04 ~02:45): S1 at l = 2 is FALSE; keep-all fails

From runs/claude-configH-20261004/NOTES.md in the main checkout:
- S1 (one-sided bottom) is FALSE at l = 2: 25 counterexamples, k = 8, (α,β,σ) = (5,5,7), n = 40 (cex40.txt).
  Keep-all of A in band l fails in case R there; BDL(X) holds at every placement tested.
- So lo >= 2 also needs keep-OR-LIFT. Your MIXED ROOT formulation (points may change bands) is the right level; do
  not rely on one-sided bottom positioning at any lo.
- Proved there: the ENDLIFT lemma. In any BDL partition of Q, the first points of the right-extended (β−1)-caps lying
  in band l+1 have cup <= l+1 and can be moved to the bottom.
- Orientation rule [C]: failures occur only when both sides are "hard" (cup P_<= = l+1 and cup G_L >= l+2, and the
  mirror).
