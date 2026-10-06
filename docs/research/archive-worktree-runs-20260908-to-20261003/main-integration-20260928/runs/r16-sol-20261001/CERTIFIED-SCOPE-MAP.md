# R16 certified scope map — 2026-10-01 16:45Z

Full N_ends/N_root remain OPEN. These are exact scoped helper results on
independent approved-base branches, not integrated closure of either target.
All30 accepted commits/checks/lockedtypes/handoffs: ACCEPTED-INVENTORY.md.

Notation for selector rows: legal uniform one-level root, actual indexed old
marker of chosen side s/maximum m, k>=3,1<=m<=k-2,2<=numRuns;
G chosen global, A opposite global, both in1..k. Physical word letters are
child/ext1s. Arbitrary run lengths/marker multiplicities, both physical axes.
Vb=min(G-2,k-m), Ve=min(G-1,k-m), H=k-m.
R(A,V)=(A<=4 OR V<=4) OR ((A<=5 OR V<=5) AND A+V<=k+3).
Consult each frozen handoff for the exact actual-end and member hypotheses.

| Family | Certified statement scope | Exact handoff |
|---|---|---|
|Both ends marked, nondegenerate|G>=4,A>=3; first child attains if A<=5 OR Vb<=4|HANDOFF.both-five-selector.md; HANDOFF.both-marked-four.md|
|Exactly one end marked|G>=3,A>=3; first or last global child at exposed end attains under R(A,Ve)|HANDOFF.exposed-five-range.md|
|Neither end marked, one global exactly3|A=3,G>=3 OR G=3,A>=3; first global child attains with specified coupling|HANDOFF.neither-opposite-three.md; HANDOFF.neither-chosen-three.md|
|Neither end marked, join-limited|A,G>=3,H<G; first raw cut has floor T(A,H,k), and attains under R(A,H)|HANDOFF.neither-join.md|
|Raw actual indexed chosen marker/G<=2|Everyfuel/fullzero, noWF/Pos/k/opposite/history/run constraints; separatefirstmax1 selector whenk>=3/2runs|HANDOFF.marker-two.md; HANDOFF.indexed-two-selector.md|
|Raw large indexedmaximum/opposite<=2|Poslabels,Nindexed,maxN>=k-2,2runs; everyfuel/fullzero, optionalfirstlegalmax1 cut underk>=3; actualoldoccurrence unnecessary|HANDOFF.large-max-two.md|
|Raw chosen-boundary G<=3/opposite<=2|Poslabels,indexedactualboundary marker/allchildren+youngerchosmarkersoneside,2runs; zero+firstk3legalmax1cut|HANDOFF.boundary-two-three.md|
|Raw both-bracket G<=4/opposite<=2|Poslabels,indexedactualsamelevelboundaries bracketallchildren/youngerchosmarkers,2runs; zero+firstk3legalmax1cut|HANDOFF.two-boundary-two-four.md|

Raw global threshold upper is accepted for arbitrary positive physical histories,
legalglobals1<=a,u<=k: eitheraxis<=4 (HANDOFF.global-four-upper.md), or eitheraxis
<=5 AND a+u<=k+3 (HANDOFF.five-below-upper.md), everyfuel/full bound<=T(a,u,k).
No global axis-five saturation theorem has been accepted.
Bothmarked unrestricted-axis threshold LOWER and exposed-first unrestricted-axis
threshold LOWER are accepted separately; neither is a missing upper theorem.
Exactboundaryerasure/prefixmerge/adjacentmerge/capacityPascal are reusable tools;
individualhand-offs state globals/history transport exactly.

Positive-label raw context/indexed chosmarker/G<=3 implies everyfuel/full bound<=2;
two distinct actual choslevels
improve it to<=1 (HANDOFF.marker-three.md), without WF/global/opposite legality.
This is not zero and does not supply selector attainment by itself.

Kernel-certified finite global-end-only failure: SSLSS,A2/G3/k4/m1,source1,
alleight legal global-endcuts0, innerfirst-run-end p1 legalrawcut1.
HANDOFF.global-end-counterexample.md. This refutes onlyglobalends, notN_ends,
notN_root andnot universal minimality of a selector set.

Accepted30 raw ALLchildren bracketed/indexed chosenG<=3 zero is CLOSED,
lockca893a8c2e474cd0/check123039-b16343/commitaab5395c45d32470b40458039b26b9a79fcbc0e0,
4.576639s576MiB4G/standardaxioms/noholes; exact HANDOFF.bracketed-three.md.
It has noPos/opposite/k/WF/history/run constraints. Its consumer
geometry into a root branch is not separately certified in thiscurrentnode.

Main Stuck: raw positive/legal emptyindexedhistory bound<=T for minaxis5 AND
sum>=k+4, or bothaxes>=6. Twofailedsame-inequality routes preserved in
HANDOFF.larger-axis-upper-stuck.md. Actualtestedbounds26 didnotviolate theupper.
General neither-marked exchange and completeunit/degenerate edges remainOPEN.
Plannedcrossedlevels/protectedchild/two-runinner/higherchosen-oppo2 routes in
PROSPECTIVE-DEGENERATE.md are unproved. Thehigherchosen joinestimate is
max(3,m+1), notm+1; diagnosticLSLSLreasoningwasloggedbeforeanyattempt.
