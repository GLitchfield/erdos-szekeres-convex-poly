# R24: the context bound and the true maximum

Consolidated 2026-10-04 01:23 UTC. Universal
actual history, endpoint-path lifting, the universal decomposable threshold
lower leaf and fixed-root assigned-limit transfer are fully checked and
committed. Latest commit is `e0e315251ec3aa17aeb7165ff1b87f6e9aa82396`,
unchanged type `a89e497ebd1cfbea`; normal operation `op-e4fb2f1518694e80`
passed all five stages, including full extraction and independent audits.
Numerical maxima and the full B construction retain the qualifications below.

## Definitions

Put s=k-1. A profile P consists of ordered zones, upper-triangular cup and
cap endpoint limits Cu,Cp, and required zone occupancies r. Every nonempty
chain is bounded at the zones of its first and last points; singletons and
pairs count. Strong sets have size at most s. N_k(P) is the largest size
of an abstract recursively decomposable coloring with this profile. Allow
an empty configuration explicitly; infeasible required profiles have value
-infinity. Existing realization gives sweep realizations of the nonempty
decomposable colorings. Decomposability supplies sweep realization, so
classical cup/cap bounds apply within each zone. The maximum is finite: a zone with a diagonal
limit below 1 is empty; otherwise its classical capacity is at most
binom(Cp[z,z]+Cu[z,z]−2,Cp[z,z]−1). Sum these bounds over zones.

A context sigma induces P(sigma) by its capLimit/cupLimit on child runs.
Retain all declared levels, including absent letters, their default sides
and truncated natural subtraction. N optional allows empty runs; N required
requires each represented run; N slots requires at least the original
child-letter count in each run. These are expansion maxima. Literal
Ctx.Satisfies fixes cardinality to the original number of child letters.

B(sigma)=Ctx.Context.bound instead chooses interval/complement partitions
of those EXISTING child letters, both orientations, and positive sibling
shares summing to s. It halts at a one-run threshold T. Preserve the actual
zero-part terms in the source recurrence; do not infer a positive actual
split from an arbitrary virtual part.

## Q4 is negative; two different defects are visible

The R1-R19 record was read and synthesized before new probes in
[R1-R19-SYNTHESIS.md](R1-R19-SYNTHESIS.md). Conditional additivity and selector
reductions did not establish exactness. R19's actual-history end-cut failure
can have B=N=8, so a failed selector need not mean an erroneous parent value.

| Witness | Convention | B | True N | Evidence qualification |
|---|---|---:|---:|---|
| globals(2,3,5), S1LS, maximum3 | optional expansion | 0 | 1 | bounded diagnostic first raw gap; required runs infeasible |
| globals(5,5,6), S1L2US, maxima11 | optional/required/minimum-slot expansion | 9 | 12 | B values kernel-checked; exact N and expanded actual history diagnostic |
| globals(6,5,6), S^5 1L3L2L S^5, maxima111 | ten original child letters, literal satisfied core | 9 | 10 | B backend and literal receipt diagnostic; general two-cap constructor/history compiling |

Minimality claims use only the completed domains specified below. The
literal core in the last row also attains the abstract two-zone maximum;
expansion and literal cardinalities are distinct conventions.

At globals(5,5,6), maxima11, S1L2US and S1L2USS have the SAME profile:
both cap and cup matrices [[3,4],[0,3]], strong limit5. The pre-existing
closed contraction theorem, typea2406241d44ddf61, proves B9 versus B12 with
standard axioms. Thus B is sensitive to a discretization that a profile-only
N does not retain. R24 independently identifies N optional=N required=
N slots=12: each zone has classical upper6, and a decomposable 6+6
construction attains12 and extends to the specified fourteen-point actual
singleton history. New construction and exact-N evidence are diagnostic,
not a new Lean certificate. Receipt q4-explicit-construction.json,
job20261003-103341-5e1de2; no SAT calls in that construction check.

The short word offers only whole-zone roots; the true maximizing root splits
one zone. An extra adjacent slot enables that geometry without changing
the old limits. The gap3 is not a true union deficiency: the two isolated
zone maxima6+6 are simultaneously attainable. The compressed word has only
two child letters, so this example alone does not refute a literal
Ctx.Satisfies cardinal upper bound.

A stronger GENERAL obstruction survives every finite expansion. For p>=4,
take two zones, Cp constantp, Cu diagonal2/cross4 and strong limitp. Then
N optional=N required=2p: each zone is a cap of size at mostp, and the
universal two-cap family attains both. Minimum-slot occupancy has the same
value if each zone's required count is at mostp; greater counts are
infeasible. The persistent expansion claim concerns the optional intrinsic
profile, not feasibility for every finite literal word. EVERY maximal
nonempty deep root has lower child exactly the
four zone endpoints and upper child the two interiors. Neither is an
interval. The constructor and all-root geometry are compiling general
theorems; see TWO-CAP-FAMILY-ACCEPTED.md and the two root accepted notes.
The proof first forces both children to meet each cap zone. The DS endpoint
lemma allows at most two lower points in each. A lower two-cup couples
with every upper cap, bounding its size by p−2; therefore each full zone
must supply at least two lower points. These inequalities force equality.
A lower three-cup would violate the same coupling, so the four lower
points form a cap. Their endpoint positions force the two gaps.
For p>=5 the exact literal context is S^p1L3L2LS^p, globals(p+1,5,p+1),
maxima111. Its universal any-core actual-history extension is fully accepted
as0930d3c7, type1c941c8bec8aa44a, standard axioms. The construction adds
singleton a, then c, then b, so root removal is b,c,a.

For the positive-level context family p>=5 just defined, the HAND
B-attainment argument produces a tree with an interval child at
every positive-positive recurrence root. A one-run leaf cannot span these
two zones. If such a tree attained2p it would have a forbidden interval
maximal root, so B<=2p-1. The nested interior construction attains2p-1 when
one run has at least3 slots. The p>=4 geometric theorem is separate;
no p4 context B equality or literal history is asserted. This general B implication is not yet a Lean
theorem. B-ATTAINMENT-REMAINING-INTERFACES.md identifies the missing general
stable placement and fuel induction, using weakly increasing assignments
with slot multiplicities and empty slots. The universal T lower leaf and
endpoint-path counts and fixed-root assigned-limit transfer are fully
accepted. Reverse literal Ctx.Satisfies is insufficient because
it fixes point count.

The interval property is about actual occupied points: monotone labels
on disjoint formal slot sets preserve it even when slots are unused.
Suppressing empty actual children preserves the property, so zero-child
terms offer no escape from the maximal-root obstruction.

The p≥5 boundary has a direct HAND definition explanation:
TWO-CAP-CONTEXT-PARAMETER-BOUNDARY.md derives cup diagonals min(2,p−3),
min(2,p−2) and crossing min(4,p−1) for this literal word. The desired
diagonal-2/crossing-4 profile therefore starts at p=5; this is not an
additional finite test or a new kernel equality.

The first singleton ancestor gives the corresponding structural reason:
a core four-cup plus the sibling one-cap already couples to size 5.
The accepted strong-composition iff excludes preserving strong rank 4 at
that particular root. This explains the history's threshold without
asserting an obstruction to every other possible history.

The first demonstrated literal case is p5:10 original child letters, an
actual10-point satisfied core, and finite B9. Arbitrary unchanged-C children
on the four endpoints and six interiors give B4+B6=10>B9. The parent B uses
the HAND-equivalent matrix-state reduction for wellformed positive-level
contexts, checked against all93650 bounded
small-k6 original-C values but not kernel-certified. Jobs130733-6dbb0f and
132157-b013b3, literal-cap-receipt-p5.json; independent history review
143005-9d0526. This is a diagnostic literal cardinal/additivity refutation,
with a general geometric explanation, not a finite-instance Lean node.

Minimality is explicitly bounded. In the completed ordering
(k,child slots,external letters,depth,a+u,a,u,word,maxima), the first RAW
optional gap is(2,3,5),S1LS,maximum3,B0/N1; requiring both runs makes it
infeasible. This is an optional-profile convention check, with no feasible
literal ancestor-history assertion.
The first feasible profile gap is the contraction profile B9/N12 and its
three reflected/relabelled variants. Completed shallow domains cover k5
all legal globals, k6 all legal globals and k7 globals2..5, with2..3 child
slots and depth<=2. Deep k6 covers2500988 contexts on axes55/56/65/66.
No overestimate occurred in these completed domains. This is diagnostic
bounded minimality and nonfailure, not unrestricted minimality or a
universal inequality certificate. One-child profile comparisons reduce to
an adjacent double child without changing B's one-run base or profile;
minimum-slot occupancy remains a separate convention.

## Q3: exact composition requires compatible endpoint profiles

At an actual root A deep below B, the exact strong condition is child
avoidance plus cup(A)+cap(B)<=s. For nonempty root children use
1<=alpha<=s-1 and beta=s-alpha; empty/singleton values are separate bases.
Refine zones by the opposite part's first/last points, recording their joint
interleaving, threshold nonemptiness and a distribution of required parent
occupancies. Lower caps and upper cups inherit their limits. A lower cup
with child endpoints in subzones rho1,rho2 has bound

    min(alpha, Cu[z1,z2],
        min_{x before rho1} Cu[z(x),z2]-1,
        min_{y after rho2} Cu[z1,z(y)]-1,
        min_{x before rho1,y after rho2} Cu[z(x),z(y)]-2).

The upper cap has the dual Cp formula and share beta. Empty index families
add no constraint. Singleton opposite spans and empty child chains require
their explicit endpoint cases. Compatible patterns, rather than independent
scalar maxima, retain these facts.
Truncate a negative effective limit to zero: either value prohibits the
corresponding nonempty chain. Required occupancies can make that child
profile infeasible.

Here t includes the joint pattern and the allocated required counts. With
the resulting child profiles P_A(t,alpha),P_B(t,alpha), the HAND exact
law is

    N_k(P) = max(empty/singleton values,
                 max_{compatible t,alpha}
                   [N_k(P_A(t,alpha))+N_k(P_B(t,alpha))]).

Only feasible terms with both child maxima positive are admitted;
infeasible value -infinity is never an empty root child.

Necessity is the DS endpoint decomposition. Sufficiency places independently
chosen children in their jointly specified subzones, preserving orders,
then glues their colors. DS-COMPOSITION-PROOF.md gives the joint patterns
and allocations. The strong iff, endpoint iff, independent-color gluing,
finite0/1/2 criterion and generic embedding are fully accepted general Lean
theorems. Joint placement/occupancy and formal profile maxima are still
open; these receipts do not certify the whole displayed optimization law.

For a FEASIBLE fixed pattern let D_A,D_B be the same profiles and required
occupancies before opposite-endpoint gains, retaining alpha,beta. The exact
endpoint penalty is

    Pi = [N(D_A)-N(P_A)]+[N(D_B)-N(P_B)] >= 0.

Its contribution is N(D_A)+N(D_B)-Pi. For uncoupled baselines add the two
coupling losses separately. This is a precise definition, not a closed
formula. Infeasible patterns are excluded before subtraction.

The two-cap family gives a HAND closed example: ABBA in both zones, with
optional central lower regions and shares2,p-2. Pre-gain maxima arep and
2p-4. Opposite endpoints force four singleton lower flanks and empty its
central regions, leaving4; the upper cap share already absorbs its gains,
leaving2p-4. Therefore Pi=p-4 and the contribution is2p. This loss differs
from B's one-point omitted-root error. TWO-CAP-ROOT-PENALTY.md pins the exact
baseline; the profile maxima/penalty have no new kernel receipt.

Scalars are insufficient even at a fixed pattern: diagonal cap/cup3 in two
required zones gives isolated maxima6/6 in both profiles. Cross limits4 or3
give diagnostic parent N12 or6. At the same whole-zone root and shares2/3,
pre-gain child maxima are3/6 in both, but penalties0/3 and contributions9/6.
q3-penalty.json, job102155-290356. The second profile has no asserted ambient
ancestor history. True parent optimization can select a different pattern.

Prefix/suffix domination is also diagnostically false under unchanged C:
globals(6,5,6),S1L3L2LSSS,111,keep[0,4,6],share2 gives7+2=9 while every end
cut is at most8. Job131255-6f4082; PREFIX-DOMINATION-OBSTRUCTION.md. The locked
node remains kernel-open absent a compiled negation. Interior geometry must
remain in the law.

## What remains for the general formula

The corrected exact recursive definition uses every proper root subset of
occupied point slots and continues to singleton leaves. Classical zone
capacities make the search finite. EXACT-POINT-RECURSION.md proves its HAND
correctness; it is not a closed formula. An expansion envelope still using
a one-run T leaf retains the unresolved one-zone upper N<=T.

Current proof idea: a profile-indexed label allocation that sends compatible
child allocations disjointly into the parent's allocation. The obstacle is
a closed invariant for endpoint-induced losses stable under refinement.
The critical-band/cup3 packing/deletion notes describe proposed mechanisms,
their explicit failures and remaining upper obligations. The coordinator's
current broader picture likewise records regrowth at the locked nested
split and proposed BRL+/tower/global routes; these are hand or diagnostic
statuses, not additional R24 kernel results. None closes the happy-ending
conjecture. More helper scopes or finite cases do not establish that invariant.

SAT UNSAT results have no DRAT/Lean certificate. Accepted theorem notes pin
unchanged types, exact source/receipt hashes, full checks, standard axioms,
audits and one-node commits. Pure endpoint transforms alone were promoted
to the shared library with frozen conformance fixtures and21 regression
tests; no numerical maximum or B equivalence was promoted to theorem credit.
No special-instance Lean target, merge or push was added. R18/R19 refs are
preserved. All-in accounting includes failures, setup, recovery and review.

`FINAL-MATHEMATICAL-REVIEW.md` records the final scope and hypothesis review;
`MATHEMATICAL-HANDOFF.md` pins the accepted sources and exact open obligations.
