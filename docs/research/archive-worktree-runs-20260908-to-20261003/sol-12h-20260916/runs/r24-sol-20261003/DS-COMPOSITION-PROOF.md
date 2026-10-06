# Exact profile composition and sibling loss

2026-10-03. Hand mathematics based on the audited Lemma DS in the primary checkout's `runs/claude-r26u1-20261002/PROOFS.md` and `runs/claude-audit-667-20261003/`. This note is not a compiled Lean theorem. `es search "zone profile first last endpoint exact root composition true maximum"` returned no indexed Lean result before writing it.

## State and exact maximum

Fix s=k−1≥2. The profile P=(Cp,Cu,r) has m ordered zones, upper-triangular nonnegative integer endpoint limits, and lower counts r_z. Every nonempty cap/cup, including a singleton or pair, obeys the entry indexed by its first/last original zones. A candidate is a finite recursively decomposable coloring with strong maximum at most s and at least r_z points in zone z. Its sweep order respects the zone order. N_s(P) is its largest possible cardinality; an infeasible profile has value −∞. Empty candidates are permitted precisely when all r_z vanish.

The maximum is finite: a zone with either diagonal below1 is empty; otherwise its size is at most the classical cup/cap bound binom(Cp[z,z]+Cu[z,z]−2,Cp[z,z]−1). The sum of these bounds suffices. Therefore feasible profiles attain their maxima, without any assumed happy-ending/Pascal-window upper formula.

## Root patterns are joint data

At a nontrivial root A≪B, A and B must be nonempty. In each original zone, the first/last points of either part determine which sub-zones the other occupies. The relative position tags are u (no other part in that zone), − (before its first point),0 (strictly between first/last),+ (after its last point). A0 is impossible if B has only one point, and conversely.

The eight two-sided sub-zone structures encode the14 first/last interleavings: six with two distinct endpoints on each side, three when only A is a singleton, three when only B is a singleton, and two when both are singletons. Adding empty/A-only/B-only gives the following11 structures. A required count is a lower bound. Entries marked single also have upper bound1; they cannot be replaced by an optional sub-zone. Within a row, the stated blocks are placed in sweep order. A central optional0 block in an enclosing pattern is placed between the opposite part's first and last points.

| structure | A sub-zones: tag, lower count, upper restriction | B sub-zones: tag, lower count, upper restriction |
|---|---|---|
| empty | none | none |
| A only | u,1 | none |
| B only | none | u,1 |
| AB | −,1 | +,1 |
| BA | +,1 | −,1 |
| ABAB | −,1;0,1 | 0,1;+,1 |
| BABA | 0,1;+,1 | −,1;0,1 |
| ABA | −,1;+,1 | 0,1,single |
| ABBA | −,1;0,0;+,1 | 0,2 |
| BAB | 0,1,single | −,1;+,1 |
| BAAB | 0,2 | −,1;0,0;+,1 |

Select one row per original zone, omitting the all-empty root choices for either part. Add finite lower-count allocations λ over the child sub-zones: in every original zone z, the allocated counts in A and B sum to r_z. The required count of a sub-zone is the maximum of its threshold lower count in the table and its allocation λ. This handles arbitrary r, including slot multiplicities. It is not enough to check that a required parent zone is merely occupied by one child.

Singleton restrictions can be encoded as a diagonal cap or cup limit1, because every pair is both a2-cap and2-cup. Keep these restrictions in both the refined and unrefined child states below.

## Endpoint refinement

Choose α in1..s−1, and β=s−α. Impose cup(A)≤α and cap(B)≤β. A sub-zone ρ=(z,tag) has opposite-point sets

- L(ρ): occupied opposite original zones y<z, plus z if tag is0 or+;
- R(ρ): occupied opposite original zones y>z, plus z if tag is− or0.

The tag u contributes neither a same-zone left nor a same-zone right point. This distinction caused the failed second adapter pilot and is essential.

For A, cap limits are inherited from Cp. Its cup limit for endpoints ρ₁=(z₁,…) andρ₂=(z₂,…) is

    Cu_A[ρ₁,ρ₂] = min(α, Cu[z₁,z₂],
        {Cu[y,z₂]−1 : y∈L(ρ₁)},
        {Cu[z₁,y']−1 : y'∈R(ρ₂)},
        {Cu[y,y']−2 : y∈L(ρ₁), y'∈R(ρ₂)}).

Empty families contribute no constraint. A negative/zero result prohibits the corresponding chains; singleton restrictions and required counts may make the entire child infeasible. One may truncate negative results to0 because chain lengths are positive. For B, cup limits are inherited from Cu, and cap limits obey the same formula with Cp and β. Denote these states P_A(t,λ,α),P_B(t,λ,α).

This is the DS first/last reduction: any cup meeting A is a cup inside A with at most one B point attached on either side; any cap meeting B is a cap inside B with at most one A point on either side. Caps contained in A and cups contained in B are unchanged. The mixed pair cases are included by treating a singleton as a chain and attaching one opposite endpoint.

## Exact identity and why gluing is sufficient

Let base(P) be the largest admissible empty/singleton value, or−∞ if neither is admissible. Then

    N_s(P) = max(base(P),
        max_{compatible t, λ, 1≤α≤s−1}
            (N_s(P_A(t,λ,α)) + N_s(P_B(t,λ,α)))).

Only terms with both child maxima positive are admitted. −∞ is never treated as a zero-sized root child.

Necessity: take a maximizing nontrivial parent and its root. DS gives cup(A)+cap(B)≤s, so choose α between cup(A) and s−cap(B). Record its actual per-zone first/last pattern and allocate r_z among points of the children without exceeding their actual sub-zone counts. Every inherited constraint and every one-/two-endpoint gain holds in the parent, so its children satisfy the displayed profiles. Their sizes are bounded by the corresponding N values.

Sufficiency: take maximizing children for an admissible term and preserve each child's internal order. The table determines a joint placement in every original zone. For ABAB, use A−,B0,A0,B+; for ABBA, insert A0 between the first and last B0 points, which exist because B0 has at least2 points. The other rows follow by symmetry or separation. Thus every sub-zone sees exactly the opposite first/last relations used in refinement. Root-attach the decomposable trees with A lower and B upper. DS bounds every mixed cap/cup by the appropriate parent endpoint limit; inherited chains already satisfy it. The allocations ensure parent lower counts. The root strong maximum is

    max(strong(A), strong(B), cup(A)+cap(B)) ≤ s.

The glued parent is valid and attains the sum. Consequently the identity is an exact compositional statement, even though it is not a closed formula or a newly formalized implementation.

## A precise sibling penalty

For the same t,λ,α, let D_A,D_B retain their sub-zone pattern, all occupancy/singleton restrictions, inherited limits and the coupling bounds α,β, but omit gains from the opposite part's endpoints. For an admissible refined term define

    Π_s(P;t,λ,α) =
        (N_s(D_A)−N_s(P_A)) + (N_s(D_B)−N_s(P_B)) ≥0.

Both unrefined maxima are finite and feasible because their refined counterparts are. The exact term is

    N_s(D_A)+N_s(D_B)−Π_s(P;t,λ,α).

There is no additional loss after compatible refinement. This formula defines the loss correctly; it does not compute it independently of N. A general proof still needs an invariant or allocation describing the endpoint-induced losses under further refinement.

If the baseline children are also uncoupled, let D_A⁰,D_B⁰ keep the same pattern and lower/singleton requirements but omit both the root coupling and opposite-endpoint gains. Then the complete fixed-root loss is

    Π_total = (N(D_A⁰)−N(D_A)) + (N(D_B⁰)−N(D_B)) + Π,

and its contribution is N(D_A⁰)+N(D_B⁰)−Π_total. Thus there are two explicit sources of loss: the strong coupling and endpoint extension. The parent maximizes these contributions over compatible root patterns; its overall union deficiency need not equal the loss of a particular root.

## Scalar information is insufficient

Set s=5. Compare two required two-zone parents with Cp=Cu=[[3,c],[0,3]],r=(1,1), for c=4 or3. Each isolated zone has true maximum6. At the fixed root pattern A-only in zone0 and B-only in zone1, use α=2,β=3.

| cross limit c | N(parent) | (N(D_A),N(D_B)) | (N(P_A),N(P_B)) | Π | split contribution |
|---:|---:|---|---|---:|---:|
|4|12|(3,6)|(3,6)|0|9|
|3|6|(3,6)|(3,3)|3|6|

For c=4, the endpoint cap restriction on B is c−1=3 and changes nothing; for c=3 it is2, reducing its one-zone maximum from6 to3. The corresponding cup restriction on A is already absorbed by α=2. These are classical3/6 capacities with stored independently verified models. The parent upper bounds are6+6 or the merged one-zone6; stored models attain them.

Corrected diagnostic job `20261003-102155-290356` verifies all values and the glued9/6-point root constructions in `q3-penalty.json`. The earlier two failed adapters are archived as `q3_penalty.v1.py` and `.v2.py`, with the exact failures logged; neither produced a completed answer artifact. This example refutes a penalty function of those two standalone scalars, the coupling and pattern alone. It does not refute the exact profile law, and it does not claim that every abstract parent is a realizable ambient ancestor history.

For c=4, the true parent12 exceeds this whole-zone root contribution9. Its maximizing root splits a zone internally. This is exactly the information the compressed context word S1L2US lacks.

Relative to the uncoupled isolated values6/6, the same two fixed roots have total losses3/6. The c=4 parent's overall union deficiency is nevertheless0 because a different root attains12. Conflating a fixed-root loss with the maximum over roots would incorrectly attribute the finite-word undercount to a true union deficiency.
