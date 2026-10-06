# Critical cup-three bound from the two-cap gate

## Superseded as new work — source check 19:09 UTC

The bound is already the color dual of CLOSED workstream-C
`card_le_choose_of_oneChange_no_capFour_no_strong`, type17d2458e770c2e45,
standard axioms. It is stronger because it requires only one-change.
`DecomposableStateUpperFourDiagonalOfGates.lean` already consumes it.
Semantic search missed this C result; no duplicate node should be created
and no R24 theorem credit is claimed for this plan. The hand argument below
is valid intuition but the existing compiled theorem is the reusable result.

2026-10-03 19:03 UTC. General hand proof conditional only on the next
two-cap strong upper. No new statement is registered or Lean-certified.

Target: for s>=4, any finite decomposable coloring with no four-cup and
no strong(s+1)-polygon has at most 1+choose(s,2) points. No separate cap
bound is necessary. This is the critical cup-three one-zone family of the
desired decomposable bound; it does not settle arbitrary cup/cap parameters.
The color-dual cap-three family follows by the existing duality theorems.

Search decomposable-cup3-triangular-search.json returned no duplicate.
Reuse CLOSED card_le_choose_of_oneChange_no_capFour_no_cup
(5bd4ab7b285da66a, standard axioms), color-dualized: a no-four-cup,
no-v-cap set with one-change has cardinal<=choose(v,2). Decomposable.dual
supplies the one-change law. Also reuse the next two-cap critical strong
bound, not a universal one-change two-cap hypothesis from the conditional
five-predecessor reductions.

Singleton sets satisfy the bound. Otherwise expose a genuine deep root L/U.
Both children inherit no-four-cup and no strong(s+1).

If L has no three-cup, it is a cap. Its size is at mosts. If |L|=1, root
coupling bounds upper cap rank bys-1, and the classical bound gives
|L|+|U|<=1+choose(s,2). If |L|>=2, a two-cup in L bounds upper cap rank
bys-2, yielding |L|+|U|<=s+choose(s-1,2)=1+choose(s,2).

If L has a three-cup, fix q in U. Partition L into points less/greater
thanq; q is disjoint from L. Each side has no three-cup: such a cup could
gain q on the outside by the accepted deep-split endpoint extension and
become a forbidden four-cup. Thus each side is a cap. Their ordered union
is the decomposable lower child. The proposed general two-cap strong upper
gives |L|<=2s-2. The lower three-cup bounds upper cap rank bys-3. The
classical bound gives |U|<=choose(s-2,2), so

    |L|+|U| <= 2s-2+choose(s-2,2) = 1+choose(s,2).

The explanation is a root charge: a three-cup lower child costs two ordered
cap bands, while the upper child loses three cap ranks. Their capacities
fit the same triangular allocation as the lower-cap root. No recursive
N oracle, one-zone T upper assumption or finite special instance is used.
The essential pending proof is the general two-cap strong upper; accepting
only that gate must not be reported as acceptance of this consequence.
