# R18 general lower route — inference only, 2026-10-02 01:22 UTC

No Lean theorem, compiler job, complete candidate or credit is claimed here.
This preserves an inferred route to the third general ROOT-NF hole within
the same R18 question. It was logged at01:12 before further attempts.

Legal uniform one-level source, chosen axis G>=4, opposite A>=4,
k>=4,1<=m<=k-3,runs>=2. Let physical endpoint marker indicators L,R,
e=L+R,b=1 iff both ends marked. For each legal fresh OLD-side maximum
1<=C<=k-2, complementary opposite-side maximum d=k-1-C, propose

    M=max(C,m+1), P=min(A-1,C+1)
    V=min(G-1-b,k-m), W=min(G-1-e,k-M)
    F(C)=T(A,W,k)+T(P,V,k)

The frozen NF2 diagnostic formula suggests every two-child normal-form
singleton cut at this coupling is <=F(C), and an exposed singleton cut of
the actual source has >=F(C). These profile claims remain unproved.
If proved, CLOSED singleton-attainment for <=3children reduces normal-form
bound<=source to this actual paired cut, without contracting its complement.

Prospective source proof: choose the first child at an exposed end, using
WF reversal if the only marked end is left. If both ends marked use first.
The opposite singleton should have exact valueT(P,V,k). Retain the whole
same-side complement. Prefix merge preserves G for an unmarked first end;
absorb after an older marker decreases G by1 in the both-marked case.
Both merge maxima toM. Marked-root lower bounds should supplyT(A,W,k).
M<=k-2; if W<=1 its threshold term is zero and the floor is trivial.

Generalize accepted R16 hLeafAnyExposed from fixed C=A-2 to arbitrary C,
and hComplementNeither/hComplementPrefix similarly. IMPORTANT: exact
hComplementNeither preserves G, unlike the distinct hAbsorb operation.
Public R16 both/exposed marked floors are CLOSED, see its accepted inventory.
Its entire source is readonly under main-integration-20260928/runs/r16-sol-20261001.
The prepared generic4431line prefix is a copied draft, NOT separately checked.

Normal-form profiles still need a direct formal proof for all physical
endpoint cases: SAME-side singleton young maximumC, chosen chain1+e and
joinmax(chain,C,m+1); OPP singleton gives chosen point axisV at the exposed
choice and opposite point axisP. Exact order matters: these proposed formulas
must be checked, not inferred from global capacities alone. Use the ordinary
kernel and preserved full coupled sum. Do not revive scalar erasure or free
componentwise domination; those routes have documented counterexamples.

Diagnostic support: frozen NF2C/D comparison18048cases, job130659-09192b;
no C/Python-to-Lean semantics theorem. This route has no new computation.
General paired-cut upper holes remain even if this lower route succeeds.
