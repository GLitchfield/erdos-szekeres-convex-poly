# R24 answer to Q4 and Q3 — working draft

Current22:43UTC: the universal literal-history extension has isolated
acceptance op-67d98254a1e84c47/job182919-ec9e45, unchanged type1c941c8bec8aa44a,
standard axioms. Full source job183035-59cc84 is running; no full closure
or commit for that bridge is claimed yet. Eight earlier general statements,
including universal two-cap attainment9dd71f32, have full acceptance.
The general endpoint-count lifting candidate is unchecked and unregistered.
VIRTUAL-SLOT-ASSIGNMENT-INTERFACE.md identifies the remaining multiplicity,
placement, threshold-leaf and induction requirements for B attainment.
The hand capacity identities, recurrence gap and numerical B backend keep
their qualifications. Older pending descriptions below are historical and
will be replaced by a clean consolidated account before the deadline.

Superseding formal checkpoint22:20UTC: universal two-cap attaining family
is CLOSED, unchanged type13c4148cbefaef7f, only standard axioms, full source
175135-ea9410 and audits/layers181839-618e28 pass. Commit9dd71f32 pins the
general p>=2 constructor and p>=4 all-root noninterval witnesses.
TWO-CAP-FAMILY-ACCEPTED.md gives complete hashes, failures and source review.
The universal literal-history bridge is the next unchecked general target;
the numerical B9/backend equivalence and general virtual B attainment remain
qualified. Older construction-pending passages below are historical.

Current formal checkpoint2026-10-03 21:43UTC: seven general structural
theorems are fully accepted, including independent-color gluingd0e89ed2
and finite0/1/2 endpoint criterion9dcbe936. Their accepted notes pin
unchanged types, source/full checks, standard axioms, audits and review.
These certify local necessity/sufficiency and exact cardinal sum on fixed
supports. Joint placement, occupancy optimization, formal maxima and closed
losses remain open. Ordered-color pushforward is fully accepted and committed
as080a277ec5bc741f3582eb4790731b94cf079bfb, unchanged type60a1f8b3519c97f6
and standard axioms. Isolated171401-5601d9, supported non-targeted full
check171750-971f0f, audits/layers173752-7cf6bb and independent review pass.
Its targeted original-source operation failed at the import ceiling; failed
op-54bcd38c86bd496f remains failed. ORDER-EMBEDDING-ACCEPTED.md pins evidence.
The19:55 summary below is historical where it marks gluing pending.

Updated 2026-10-03 19:55 UTC. Bounded scans and numerical follow-ups are complete. The exact prefix/suffix-domination node has an unchanged-C diagnostic9>8 counterexample. A general two-cap-block family refutes an interval-root normal form after arbitrary expansion. Its literal10-slot bound is9, and unchanged-C arbitrary child bounds4+6 exceed it. Both root theorems, exact strong-coupling iff and endpoint-constraint iff are fully accepted/committed with standard axioms. Independent-color gluing has first isolated/source acceptance; full extraction remains pending. Existing public uniform two-block and C triangular proofs explain the three-cap upper as a hand reuse corollary, pending unconditional specialization. The profile capacities, B interface and numerical refutations retain their qualifications. Verification continues through the fixed deadline.

## Definitions and scope

Fix k and s=k−1. A zone profile P=(Cp,Cu,r) consists of ordered zones, upper-triangular cap/cup endpoint bounds and lower occupancy counts. A nonempty chain with first point in zone i and last point in zone j obeys the corresponding matrix entry; singletons and pairs count as chains. Every strong set has at most s points. N_k(P) is the maximum cardinality of an abstract recursively decomposable coloring satisfying these conditions; infeasible required occupancies have value −∞ (the diagnostic implementation uses −1). Abstract decomposable colorings have sweep realizations by the already proved realization theorem.

For a context σ, let P(σ) be its matrices `capLimit/cupLimit` evaluated on its child runs, retaining all declared levels, default sides for absent levels and truncated natural subtraction. We compare:

- N°: all run occupancies optional (r=0);
- N⁺: each represented run nonempty (r=1);
- N^{slots}: each run has at least its original child-letter count.

These are maxima after arbitrary run expansion. Literal `Ctx.Satisfies` instead fixes the total cardinality to the original child-letter count; it is a feasibility assertion at that cardinality, not an unrestricted maximum. Let B(σ)=`Ctx.Context.bound`: it uses a classical/window threshold at a single run and otherwise maximizes only interval/complement partitions of the **existing child letters**, with both orientations and sibling maxima summing to k−1. Zero-valued parts remain in the literal recurrence.

## Q4: no

The strongest obstruction is structural: for p>=4,Cp constantp and Cu diagonals2/cross4 have N=2p under strong limitp. Every maximizing decomposition has lower child exactly the four zone endpoints and upper child the two interiors; neither child is an interval. Thus arbitrary expansion cannot repair the interval-cut restriction. For p>=5 the profile comes from an actual singleton-ancestor history S^p1L3L2LS^p with globals(p+1,5,p+1). `TWO-CAP-BLOCK-OBSTRUCTION.md` supplies the general construction and forced-root proof. The hand B-attainment argument gives B<=2p-1 at every finite expansion,and the nested interior construction in `PREFIX-DOMINATION-OBSTRUCTION.md` attains2p-1 once one run has at least3 slots.

The incidence core is compiled as `two_full_cap_blocks_root_structure`, locked
type `84e6237f7f3a6146`. For everyp>=4 and any nonempty deep-below root of two
disjoint fullp-cap blocks, avoiding(p+1)-caps and(p+1)-strong sets forces lower
intersections2+2, a four-point lower cap, upper cardinal2p-4 and upper cap rank
p-2. The statement does not require block order separation or sweep
realizability. Accepted isolated receipt
`d1b02ae6c07291c7d0997408ea5a2093f03716be0701b59c24ff7c7a0b1135e6`
and original-source job `20261003-134841-d86a75` use standard axioms only.
Full extraction `20261003-134932-d2c521`, axiom/layer audits and final review
all passed; commit `13b050e1a9259605e864a30c7f1516699c5be18e` contains the
unchanged statement and proof. The ordered endpoint consequence
`two_full_cap_blocks_root_noninterval`, type `50cecd70f72957e5`, also passes
isolated/source checks, full extraction, audits and final review. Commit
`0422f8c765737dd921bf04f54781dee3acab819a` pins it. It forces a
four-cup and explicit L-U-L/U-L-U subsequences. Construction and B attainment
remain separate obligations, so these receipts do not certify the whole
literal10/9 counterexample.

The first reachable literal instance p5 has10 child positions,a checked10-point model,and finite B9. Job20261003-130733-6dbb0f computes the full10-slot recurrence in730.874s/341MiB through the exact matrix-state reduction described in `FINITE-PROFILE-STATE.md`. That reduction has a general hand path proof and agrees with all93650 small-k6 unchanged-C bounds,but is not kernel-certified. Unified job20261003-132157-b013b3 rechecks the literal minimum-slot model and retains its13-point actual history; it also computes the arbitrary four-endpoint split with unchanged C:lowerB4,upperB6,total10>B9. See `literal-cap-receipt-p5.json`. Thus both the literal context cardinal upper and full finite-bound additivity fail diagnostically. The parent-B backend qualification remains essential.

The prior record is synthesized first in [R1-R19-SYNTHESIS.md](R1-R19-SYNTHESIS.md). Its certified adjacent-contraction example already rules out equality with any profile-only N: adjacent child multiplicity changes B while leaving the profile unchanged. R24's exact diagnostic evaluation identifies the undercount.

At (a,u,k)=(5,5,6), maxima=(1,1):

| word | endpoint cap matrix | endpoint cup matrix | B | N° | N⁺ | N^{slots} |
|---|---|---|---:|---:|---:|---:|
| S 1L 2U S | [[3,4],[0,3]] | [[3,4],[0,3]] | 9 | 12 | 12 | 12 |
| S 1L 2U S S | same | same | 12 | 12 | 12 | 12 |

The B values are already kernel-certified by `ctx_bound_adjacent_letter_contraction_counterexample`, closed with standard axioms and unchanged type hash `a2406241d44ddf61`. N=12 has a simple upper argument: each zone has no 4-cap or 4-cup, hence at most binom(4,2)=6 points. The stored twelve-point decomposable construction attains 6+6. Independent checking verifies all endpoint chains, all strong subsets and every literal deep-below tree split. It extends through the two specified singleton ancestors to a fourteen-point coloring with cap/cup/strong maxima 4/4/5. Thus this is an actual ancestor-history profile, not just an infeasible raw context. The new sharpness/construction evidence is diagnostic, not a new Lean certificate.

The shorter word offers only the root partition “one entire zone versus the other.” The true optimization can split one zone into parts at the root. An extra child slot enables that geometry while leaving all old endpoint capacities unchanged. B therefore counts a restricted family of cut trees on a chosen discretization of the profile. A profile invariant cannot be defined by that finite recurrence without a proved saturation operation.

The old compressed9/12 witness alone does not refute the literal fixed-cardinality implication `Ctx.Satisfies → S.card ≤ B`: it has only two child letters. The new10/9 two-cap-block receipt above supplies that distinct diagnostic literal obstruction with a context whose own child-letter count exceeds its own B.

Full minimum-slot checks on the same completed domains find3567 feasible original-cardinality contexts at k5,18560 at k6 and15773 in the inactive-global k7 domain. None has its original child-letter count above B. The k6 free-max comparison still has precisely the four12/9 mismatches; minimum-slot feasibility does not turn their original2/3-slot cardinalities into12.

There is also a deterministic sharp construction, independent of SAT search. Use sweep blocks6,3,3: the first zone is a classical6-point cap3/cup3 set; the second zone first has a3-cup in the root upper part and then a3-cap in the root lower part. The lower child combines the first6-point block as its upper subtree with the last3-cap as its lower subtree. It has9 points,cup3,cap4. The root upper3-cup has cap2, so the root coupling is3+2=5. The parent has cap/cup4/4,strong5 and6 points in each zone. Expanded word's middle upper leaf gives3 plus lower remainder9. `q4-explicit-construction.json`, job `20261003-103341-5e1de2`, checks this tree and the14-point actual history with zero SAT calls. Context tags record the kept child's side at an ancestor; they do not name the physical sibling's side.

This error is **not** the union deficiency relative to the two zone capacities: their true maxima are 6 and 6, and the union attains 12, so that deficiency is zero while B loses three.

The independent R19 case (5,5,6), word SSS1L3L2LS, maxima 111, has cap matrix [[4,4],[0,4]], cup matrix [[2,4],[0,2]] and **N°=N⁺=N^{slots}=B=8**. Its eight-point sharp construction extends through the three specified singleton ancestors to an eleven-point valid coloring with maxima 4/4/5. Therefore the end-cut/PEEL failure there does not arise from an erroneous parent bound. It is a separate failure of the proposed cut-selection normal form.

For the full enumerated domains (2..3 child slots,0..2 external letters,depth≤2,all declared levels retained), k5 globals2..5 has32357 equal optional contexts and1947 undercounts, all gap1; all11648 feasible required-run contexts have B=N⁺. The remaining22656 required-run contexts are infeasible. At k6 globals2..6,89963 optional contexts are equal,3683 undercount by1 and4 undercount by3; required-run comparison gives40363 equal,4 undercounts and53283 infeasible. At k7 globals2..5,89183 optional contexts are equal and3489 undercount by1; all36952 feasible required-run contexts have B=N⁺, while55720 are infeasible. Thus the gap1 optional mismatches arise from occupancy, rather than a smaller feasible extremal configuration.

The shared generator actually starts at2 child slots. A one-child context is covered for N°/N⁺ and B by replacing its sole S with adjacent SS: this preserves its only run/profile and B's base case, and lies in the enumerated domain. This extends the mathematical comparison to1 child slot without altering any raw scan count. Minimum-slot occupancy is a separate convention and is not inferred by that replacement.

The smallest raw optional discrepancy in the explicit ordering (k,child slots,external letters,declared depth,a+u,a,u,word,maxima) is `(2,3,5), S1LS, maxima3, B0, N°1`. Requiring both original runs makes it infeasible. The smallest **feasible** discrepancy over the completed domains is `(5,5,6), S1L2US, maxima11, B9,N12`, with its3 reflected/relabelled variants. Every one-child context and every shorter/depth-smaller candidate in these domains agrees. No B>N° or feasible B>N⁺ occurs. This is bounded diagnostic minimality, not unrestricted minimality or a universal inequality theorem.

## Q3: exact composition retains extreme-point profiles

The original end-domination reduction is now explicitly false: at(6,5,6),S1L3L2LSSS,maxima111,lower keep[0,4,6],d2 gives7+2=9,where all prefix/suffix sums are<=8. This directly refutes the first conjunct of `ctx_bound_prefix_suffix_domination` (locked type dab0805effb44b48),using unchanged C in job20261003-131255-6f4082. `PREFIX-DOMINATION-OBSTRUCTION.md` gives the parameterized two-flank mechanism. Thus the exact composition law below must retain interior first/last patterns; reducing it to end cuts loses capacity even before the stronger persistent interval-root obstruction.

Lemma DS gives an exact composition law with a finite choice of per-zone extreme-point patterns. For a root A≪B, fix 1≤α≤s−1 and require cup(A)≤α and cap(B)≤s−α. Refine every original zone by the first/last points of the other part. Let L(ρ),R(ρ) be the original zones containing an opposite-part point before/after a chain endpoint in sub-zone ρ.

For A, cap limits are inherited. Its cup limit between sub-zones ρ₁=(z₁,…) and ρ₂=(z₂,…) is

    min( α,
         Cu[z₁,z₂],
         min_{y∈L(ρ₁)} Cu[y,z₂]−1,
         min_{y'∈R(ρ₂)} Cu[z₁,y']−1,
         min_{y∈L(ρ₁),y'∈R(ρ₂)} Cu[y,y']−2 ).

For B, cup limits are inherited and cap limits obey the same formula with Cp and s−α. Empty index families add no constraint. The profile also retains nonempty threshold sub-zones, singleton restrictions when an opposite-part span consists of one point, and a distribution of parent lower occupancy requirements. These are essential for an exact gluing statement; independently optimizing two children with unspecified extreme-point occupancy is insufficient.

Writing P_A(t,α),P_B(t,α) for the resulting compatible child profiles, the exact law is

    N_k(P) = max( admissible empty/singleton values,
                  max_{compatible patterns t, α}
                     [N_k(P_A(t,α)) + N_k(P_B(t,α))] ).

The two child maxima sum **without a further penalty after refinement**: compatible children can be placed in their specified sub-zones preserving internal orders, and DS makes the union satisfy P. Conversely every nontrivial parent supplies such a pattern and coupling. [DS-COMPOSITION-PROOF.md](DS-COMPOSITION-PROOF.md) gives the11 joint structures,14 first/last interleavings and finite parent-occupancy allocations. The full maximum identity remains hand mathematics. Its exact strong iff, endpoint iff, independent-color fixed-support gluing and finite0/1/2 endpoint criterion are CLOSED/committed as1a83a001,469c5d2f,d0e89ed2 and9dcbe936 with standard axioms and full source/extract/audit/review receipts pinned in their accepted notes. Gluing preserves both independent child colorings and their cardinal sum. Ordered embedding extension passes its first isolated check and awaits full validation. Joint-pattern placement, matrix/Ctx interfaces and formal profile maxima remain open; none of these receipts supplies a closed endpoint-loss formula.

For a fixed pattern/coupling, define D_A,D_B as the same restricted profiles and occupancy requirements before opposite-endpoint gains, retaining the coupling caps α,s−α. Then the exact sibling penalty is

    Π(P;t,α) = [N_k(D_A)−N_k(P_A)] + [N_k(D_B)−N_k(P_B)] ≥ 0,

and its split contribution is N_k(D_A)+N_k(D_B)−Π. This defines the penalty precisely but is not a closed formula for it. The difficult step is evaluating these endpoint-induced losses in a form stable under further refinement.

For fully uncoupled baseline children D_A⁰,D_B⁰, add the coupling losses N(D_A⁰)−N(D_A) and N(D_B⁰)−N(D_B). This gives the complete fixed-root penalty. The parent maximizes over root patterns, so its overall union deficiency can be smaller than every contribution computed with an arbitrarily fixed whole-zone root.

The persistent two-cap family supplies a limited closed example. Forp>=4,
choose ABBA in both original zones, including its optional lower central
regions, and coupling alpha2/beta p-2. Before gains the child maxima are
p and2p-4. A same-zone upper endpoint forces each lower flank to a singleton;
two such endpoints empty each optional lower central region. The refined
lower maximum is4. Upper gains are already absorbed by its cap coupling
p-2, so its maximum remains2p-4. Thus the hand endpoint penalty is p-4
and the split contribution2p. [TWO-CAP-ROOT-PENALTY.md](TWO-CAP-ROOT-PENALTY.md)
states the exact baseline and qualifications. This explains a forced-flank
loss; it differs from B's one-point error from excluding the root pattern.
The profile maxima and penalty here are not new compiling Lean theorems.

The scalar obstruction is checked: at s=5, two required zones with diagonal cap/cup limits3 have the same isolated maxima6/6. Cross limits4 give N12; cross limits3 give N6. At the same A-only-zone0/B-only-zone1 pattern, α=2,β=3, both have standalone coupled child maxima3/6. Endpoint refinement incurs penalties0 or3, giving root contributions9 or6. It lowers B's cap limit from3 to2 only in the second case. The cross-zone information, absent from the two scalars, determines the loss. Exact job `20261003-102155-290356` verifies the numerical capacities and glued constructions in `q3-penalty.json`. The second parent is a general abstract profile; no ambient-history assertion is made for it.

## Implication for the general formula

The finite-word B is not the requested general N formula. Its additivity problem is partly an optimization on an arbitrary word resolution. A corrected candidate should be invariant under run expansion and should retain joint first/last-point geometry and occupancy. The DS max-plus recursion is exact; a closed-form kill family or injective word allocation realizing it remains unproved.

`EXACT-POINT-RECURSION.md` supplies a terminating corrected definition:expand a profile to fixed occupied point slots;recurse over every nonempty proper root subset and admissible coupling using exact endpoint transforms;stop only at singletons. Then maximize over zone assignments and cardinalities up to the sum of classical zone capacities. This is exactly N by DS necessity/sufficiency and finite cardinality induction. It is an exact recursive reformulation,not a closed formula or a new compiled theorem.

`TWO-CAP-CUP3-PENALTY.md` gives a parameterized profile loss:two ordered full r-caps under global cap<=r force a4-cup,by a root-case induction without strong assumptions. Consequently Cp constantp,Cu diagonal2/cross3,strongp has hand exact maximum2p-2 forp>=3;withcross4 it is2p. Without criticalstrongp,the cup3 maximum is2p-1. The general lower nests an upper(p-3)-cap before a last singleton,and the upper excludes p+(p-1) by coupling and endpoint geometry. Diagnostic checks give classicalp3 N5 andcriticalp4 N6. This is a two-point profile gate loss,not a scalar penalty for an unspecified root;its certification remains open.

[VIRTUAL-CUT-LOWER-PROOF.md](VIRTUAL-CUT-LOWER-PROOF.md) gives a general hand construction argument for B≤N° under the audited DS identities and exact extension definitions. Select the new virtual endpoints first in the child's extension DP, lift every old path through the shifted levels, and use the new join maximum for root coupling. Oracle-free classical bands attain the one-zone T leaves. This covers empty cut parts, unused declared levels and arbitrary expansions in original slot order. The400-context deeper sample and max-B representatives of all313 shallow k6 profiles independently pass the matrix implications and actual attaining constructions, with zero SAT calls. The extension/gluing theorem still lacks a compiling Lean receipt. No universal B≤N theorem is claimed as kernel-certified.

An expansion/all-subset envelope that still halts at a one-run T base cannot itself supply the general upper: it retains the unproved one-zone equality. Continuing cuts inside a one-run zone down to singletons would expose every DS tree after enough slot expansion, yielding an exact recursive reformulation of N rather than a closed formula. The distinction between root resolution and the halting base must remain explicit.

Current proof idea: derive an invariant/label allocation directly for DS profiles, and show compatible refinements map the two child allocations disjointly into the parent's. Current obstacle: no closed formula or general allocation rule for the endpoint-induced losses Π is known. The R24 mismatch has zero true union deficiency, so repairing B by subtracting a union deficiency alone cannot solve this issue.

[CRITICAL-BAND-PENALTY.md](CRITICAL-BAND-PENALTY.md) gives a restricted family with an explicit general lower construction and a specific proposed charge. For3≤a≤k−1 and a+u≥k+3, the enclosing cap-gap child has lower construction G=T(a−1,u,k)+binom(k−3,a−3), while its tight classical sibling has C=binom(k−3,a−2). Inserting that sibling between the flanks gives G+C=T(a,u,k) by Pascal. The unproved general upper is N(gap)≤G. Both critical(5,6,7) gap values are independently complete, N21/N24, and the full root audit gives N25. This checks a structural bottom-band conjecture, not a general scalar penalty theorem.

The mirror has now been resolved diagnostically: a complete265-pair DS upper cover gives N24, combining the cap-gap21 boundary, refined singleton-core23 boundary, a classical3-clear-block19 upper and the general singleton-augmentation argument in [MARKER-AUGMENTATION.md](MARKER-AUGMENTATION.md). The independent uniform40-case cover then gives N25 with its explicit lower construction, without assuming T. This checks the proposed charge in this family; it does not prove the general band-placement invariant. Exact receipts are `q7-gap-cover-complete.json` and `q7-root-cover-complete.json`.

[CLASSICAL-PACKING.md](CLASSICAL-PACKING.md) interprets the classical multiple-clear-block effect through disjoint open endpoint intervals of q-cups. A d-clear-zone profile bounds their packing number by d−1. The candidate upper F(p,q,d)=Σ_{h<min(d,p)}binom(p+q−h−3,p−h−1) has a general lower construction and passes the deliberate n≤6 diagnostic probe. A four-point DS example refutes the hoped-for packing decrement in the standard starts-cap partition. The candidate upper remains unproved; endpoint losses or unused capacity must be retained in any induction.

## Evidence currently checked

- Exact SAT pilot: job `20261003-100015-d579dd`, DONE/rc0, 4.5s/65MiB, `q4-pilot.json`, all4 rows and all three occupancies complete.
- Independent construction/history verification: `20261003-100840-948414`, DONE/rc0, 0.3s/24MiB, `q4-witness-verification.json`.
- Full k5 optional and required scans: `20261003-101201-3c2c4a`, `20261003-102020-9f9451`, DONE; stored rows, exact profile answers and reports under `scan-k5/`, `scan-k5-runs/`.
- Full bounded k6 completed by `20261003-103619-8b2f68`, DONE1.4s77MiB, reusing308 immutable exact seed answers and5 fresh profiles with explicit global uniform-upper inclusion. Original `20261003-101201-883829` was cancelled after replacement coverage passed; its partial answers remain durable and no result is attributed to cancellation. Required-run completion `20261003-103757-84a232`, DONE9.6s78MiB, reuses optional maxima only as inclusion uppers and checks required models. Reports `20261003-103712-cdef77`, `20261003-103837-775d0c`.
- Full k7 globals2..5 optional and required scans: `20261003-102529-9a5812`, `20261003-102737-4db020`, DONE. Active5,6 timing is complete by independent replacement `20261003-115942-5d90c1`, all100 rows/21 profiles equal; original `20261003-102530-74723a` was cancelled after replacement coverage, and its pending n30 query is not a result.
- Q3 fixed-pattern diagnostic: `20261003-102155-290356`, DONE/rc0,0.4s/34MiB. Failed adapters `20261003-102020-489837` (canonical-zone indexing) and `20261003-102042-ede413` (wrong same-zone tags) are logged/archived; neither produced the completed answer artifact.
- DS engine compile: `20261003-100144-0adea0`, DONE/rc0, 2.5s/199MiB. Unpruned DS pilot `20261003-100230-61a965` was stopped after the review exposed growth to7 zones/8000 states with0/4 answers (221.8s). Its empty output is not an exact-value result. The same questions are retained for the SAT route; one-zone base remains separately open until checked. The reported zero peak is unavailable measurement.
- Virtual-cut interface/construction: `20261003-122415-4340f4`, DONE13.766s,400 deep timing contexts/39440 cut-child checks; `20261003-122532-3e1ff9`, DONE4.554s,313 shallow max-B profile representatives/17168 checks. All constructions attain B with positive literal DS/profile/strong checks or explicit optional-empty semantics. Failed empty-adapter v1 and its partial output are retained.
- Classical cup-interval mechanism pilot: `20261003-121458-774ad0`, DONE0.076s algorithm,791 decomposable colorings on2..6 vertices; candidate bound passes and independent packing/block-partition calculations agree. Its general upper and suitable induction remain open.

SAT UNSAT answers have no DRAT or Lean certificate. Existing receipts certify the old B values and prior global bounds; the new numerical maxima retain their diagnostic qualifications. The six new general R24 theorems have separate kernel receipts and one-node commits. No special-instance Lean theorem, merge or push was added.
