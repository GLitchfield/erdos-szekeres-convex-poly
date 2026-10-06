# A finite exact point recursion for the corrected maximum

2026-10-03 17:27 UTC. General hand proof from DS,not a compiling Lean theorem or a closed form for Theorem8.

## Why this state is useful

The exact endpoint transform in `FINITE-PROFILE-STATE.md` has two interpretations. It computes a finite context child's extension constraints. It also gives the necessary and sufficient DS constraints on fixed occupied point positions after any root partition. The latter interpretation removes ancestor words,zone first/last enumeration,and the ambiguity about optional virtual slots.

Fix n ordered **occupied** point slots,per-slot endpoint cap/cup matrices Cp,Cu and strong limit s>=2. Every singleton/pair is included in the endpoint constraints. Let Feas_s(Cp,Cu) mean that some decomposable coloring on all n slots obeys those constraints and has strong maximum<=s.

For n0 it is true. For n1 it is true exactly when both diagonal bounds are>=1. For n>=2 it satisfies the exact Boolean recursion

    Feas_s(P) <=> OR over nonempty proper K and 1<=alpha<=s-1 of
      Feas_s(P_A(K,alpha)) AND Feas_s(P_B(K,alpha)),

where A=K is lower,B=its complement is upper. For A inherit cap bounds and refine cup bounds by every outside endpoint and the coupling alpha. For B inherit cup bounds and refine cap bounds by every outside endpoint and beta=s-alpha. Explicitly use `profile_transform.transform` with opposite maximum beta for A and alpha for B. Keep **all** subsets,not just interval/complement subsets. Each child has fewer occupied slots. Stop only at singleton slots; no one-run T halting rule and no positive part paired with an empty root child.

## Exactness proof

Necessity: take any nontrivial decomposition root. All child chains obey inherited parent bounds. DS says every mixed cup is a cup in A plus at most one B endpoint on either side; hence every A cup must obey each parent bound after those endpoint gains. The same statement holds for caps in B. Root strong coupling gives cup(A)+cap(B)<=s,so choose alpha between cup(A) and s-cap(B). The two root children therefore satisfy the transformed states,and induction applies.

Sufficiency: take two child witnesses supplied by the recursion and retain their point orders at the chosen K/complement positions. Attach their trees with A lower,B upper. Every mixed cup is one of the endpoint extensions enforced in P_A; every mixed cap is one of the endpoint extensions enforced in P_B. Inherited chains are already valid. DS gives strong max=max(strong(A),strong(B),cup(A)+cap(B))<=s. Thus the attached tree witnesses the original state.

The two-slot case is covered: each child is a singleton,and the one-endpoint conditions require both parent pair bounds>=2. No missing triangle/convexity assumption is introduced by stopping at one point. Any abstract decomposable coloring so constructed has the existing sweep-realization theorem available separately.

## Recovering exact free N(P)

For a finite zone profile P with lower counts r_z,expand its matrices to n slots using any nondecreasing zone assignment z(0),...,z(n-1) meeting those counts. This assignment is finite data. A zone with either diagonal0 is empty; otherwise its classical capacity is

    U_z=binom(Cp[z,z]+Cu[z,z]-2,Cp[z,z]-1).

Take U=sum U_z. Then N_s(P) is the largest n in0..U admitting such an assignment and a true Feas_s expanded state; if no assignment is feasible use minus infinity. No assumed happy-ending/window upper is used. This supplies a terminating exact recursive definition,even when profile-refinement identities do not obviously decrease a syntactic zone measure.

The corrected function is therefore independent of arbitrary slot multiplicity. Existing zone extrema become explicit occupied point positions. Its capacity is the exact DS maximum,not an interval-root envelope of B. The finite context bound's two defects are absent: it explores every root subset and does not halt at a one-run conjectural T upper.

## What remains difficult

The algorithm is finite but can be expensive: it ranges over up to2^n-2 root subsets,root couplings,and zone assignments for n up to the classical upper. It is an exact reformulation rather than a closed formula. Reusing the audited DS/SAT profile engine remains preferable for numerical queries unless a measured semantic-state implementation answers a question cheaper.

For the general happy-ending proof,we still need an invariant/label allocation that bounds all these occupied-point root refinements by the Pascal window. The cap-block family shows why neither interval roots nor end cuts can be assumed in that invariant. The exact Q3 penalty retains endpoint state; it is not recoverable from just two child cardinal maxima.

No new solver or large enumeration is commissioned by this note. If implemented,the meaningful validation would compare fixed-point feasibility against independently enumerated decomposable colorings or SAT boundaries,including negative cases and arbitrary noninterval root witnesses,not tests that repeat the transform formula.
