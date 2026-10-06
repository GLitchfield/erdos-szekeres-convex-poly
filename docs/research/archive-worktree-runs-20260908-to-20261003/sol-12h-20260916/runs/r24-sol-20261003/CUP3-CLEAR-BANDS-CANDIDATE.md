# Critical cup-three clear bands: candidate allocation

20:26 proof-route audit: after duality, no4cap implies strong rank<=cup+1.
The new rank-row conjecture tests only actualcupR/strong<=R. Profiles with
actualcup<=R-1 require the classical clear-cup-block bound
F(R-1,3,d)=G(R,d)-1 instead; strong<=R is then redundant. That classical
upper is also open for intermediate d. Even proving the tested deletion
hypothesis would therefore leave this branch. BAEK-BLOCK-INVARIANT-OBSTRUCTION.md
also shows block count d does not directly bound the Baek alpha label.
No narrowing is credited as a result; the full G upper remains open.

2026-10-03 19:38 UTC. The lower architecture is explicit. Existing accepted
sources supply hand upper corollaries for one, two and three zones, and for
the saturated range. The intermediate range beyond three zones remains open.
No new unconditional three-cap Lean receipt is claimed.

For R>=3, global cap and strong limitR, global cup limit3 and d ordered zones
each with cup limit2, consider

    G(R,d) = d'R - choose(d'+1,2) + 1,  d'=min(d,R-1).

There is an explicit general lower. Put a whole R-cap as the lower first zone.
The upper child has cap limitR-2 and is the classical clear-cap chain with
successive zone ranksR-2,R-3,..., using at mostd-1 zones. Mixed caps gain one
lower endpoint and mixed cups one right upper endpoint. The root strong
coupling is2+(R-2)=R; all upper recursive couplings are at mostR-1. Thus the
cardinality is

    R + F(R-2,3,d-1) = G(R,d),

with the upper child omitted atd1 and empty remaining zones optional. The
classical F lower is already documented in `CLASSICAL-PACKING.md`. At d>=R-1
this saturates at R(R-1)/2+1, the arithmetic window T(R+1,4,R+1). No upper
theorem for T is assumed here.

The proposed upper N<=G agrees with the hand two-cap gate formula atd2.
The already CLOSED public `diagonalCupBlocksForce4kk_of_five_le`, type
`7b9515ee94a1f04b`, supplies the uniform two-block input through
`diagonal_cup_block_card_add_le`. Earlier searches missed this public export
and unnecessarily described only the local proof in the singleton gate.
It supplies the stronger critical upper after duality. The CLOSED conditional theorem
`threeCupBlocks_card_le_of_decomposable_no_capFour_no_strong_of_pair_bound`,
type `126eea55ed06ad2b`, then gives the three-cap upper3R-5 forR>=5 using
that uniform two-block input. This matches R+(R-2)+(R-3). The R3/R4 bounds
and every saturated case d>=R-1 follow the existing CLOSED C theorem
`card_le_choose_of_oneChange_no_capFour_no_strong`, type `17d2458e770c2e45`,
whose dual bounds the whole parent by1+choose(R,2). These are hand reuse
corollaries until the exact unconditional three-cap statement is compiled.
The uniform two-block argument needs no new export. They earn no new R24 credit.
For 4<=d<R-1, the required allocation is still unknown.
The earlier starts-cap partition does not decrease the cup-interval packing
count and cannot justify this upper. A successful construction is not evidence
that every coloring admits the corresponding chain of whole-zone roots.

The R5,d3 test asks whether11 points can beatG10. A positive11 model refutes
this allocation and exposes the missing joint endpoint information. A negative
boundary supports it only diagnostically, and leaves the general allocation
proof open. The10-point pilot first checks feasibility and timing. Its simple
hand lower has cap-zone sizes5,3,2: root lower5-cap, root upper consisting of
a lower3-cap followed by an upper2-cap. Local strong couplings are5 and4.

The input `cup3-three-cap-input.json` states the full profile and optional
occupancy, and explicitly identifies its standalone scope. The unchanged
checkpointed `profile_boundary.py` supplies SAT/UNSAT queries with no solver
budget. No Lean special instance or new execution machinery is introduced.

The completed R5,d3 receipts agree diagnostically withG10: job
`20261003-142332-7ce0d3` verifies SAT10 in0.019673s, and
`20261003-142627-666e77` reports UNSAT11 in0.032495s. The latter artifact
alone has N_exact=null and N_lower0; exact diagnostic10 uses both receipts
under the identical hashed input/profile. This supports the proposed critical
allocation at this parameter but does not establish an upper for generalR,d.
No additional census is commissioned as progress. Later source review found
the accepted general route above, so this R5,d3 diagnostic did not establish
a previously missing general upper. Its all-in computation cost is retained.
The old classical induction and triangular plans are superseded as new
targets by existing accepted sources.
