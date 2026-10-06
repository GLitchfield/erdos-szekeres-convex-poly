
Proof implementation notes after unit-zone proof:
- Use generic one-step left/right witnesses from CtxBracketedChildrenUnitBound.
- For N<M, [N,M] is a sublist of levelsOn s0: it is sorted and a subset of that sorted level list. Existing CtxEraseLevelBoundMono hSub proves the general sorted-subset argument by filtering the larger list and equality of sorted permutations; copy that if no direct List theorem is available. levelsOn sorted proof is in CtxBoundOppositeLevelSwap lines49ff.
- For x<y and p<x, the closest first right marker at N is <=x, so y at M is still to its right; [N,M] yields rightExt>=2. For x<p<y use a left witness x and right witness y. Thus capacity>=2 forces y<p. It then has an old marker on its left, and any indexed chosen marker on the right would give chain>=2, contradiction; all markers lie left of p. y<x is dual.
- No positive-label hypothesis needed for this pointwise theorem (no part operations); arbitrary maxima and unused levels are harmless. Opposite capacities can vanish: classify all children whose chosen capacity>=2, not just active ones.
