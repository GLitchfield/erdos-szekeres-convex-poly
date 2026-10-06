# What B represents, and why saturation is not an upper proof

Current validation update, 2026-10-04: the universal T lower constructor is
fully accepted `aebb6505`, and endpoint path/positive-limit lifting is fully
accepted `fa6dacd1`. Fixed-root assigned-limit transfer is fully
accepted at `a89e497ebd1cfbea`, commit `e0e31525`, after all five normal stages. Stable placement
and exact B fuel induction remain uncompiled. The prose below began as a
hand proof; its newer universal lower receipts do not establish the upper.

2026-10-03. General hand argument under review; no new Lean theorem. Searches `decomposable lower construction` and the shared library searches precede this note. The indexed existing `decomposable_exact_lower` proves the full happy-ending sharpness statement; it does not by itself supply the following endpoint-profile and virtual-cut interfaces.

## One-zone values are constructively attainable

Use cap/cup upper limits p=a−1,q=u−1 and strong upper s=k−1, with3≤k and2≤a,u≤k.

If a+u≤k+3, the classical construction of size binom(p+q−2,p−1) is recursively decomposable: split a lower set with limits(p,q−1) before an upper set with limits(p−1,q). A mixed cup adds at most one upper endpoint to the lower cup; a mixed cap adds at most one lower endpoint to the upper cap. The local strong coupling is at most(p−1)+(q−1)=p+q−2≤s. The singleton boundary p=1 orq=1 is handled separately, with strong size1.

In the active regime, let L=k−a,U=u−2. For each j=L..U take a classical band with

    cap ≤ k−1−j, cup ≤ j+1,
    size = binom(k−2,j).

Place bands in increasing j sweep order. Append each new band as the upper child of the accumulated lower tree. Before adding band j, the accumulator has cup at most j; the new band's cap is at most k−1−j, so DS gives local coupling at most k−1. Each individual band has classical strong bound at most k−2. The accumulated cup increases to at most j+1, while its cap never exceeds the first band's cap a−1: extending the new band's cap by one gives k−j≤a−1 for j>L. The result has cup≤u−1 and size

    Σ_{j=k−a}^{u−2} binom(k−2,j) = T(a,u,k).

Thus T supplies a lower construction in every legal one-zone regime. This argument does **not** prove the upper bound N≤T. For k7,cap4/cup5, the25-point construction can be written simply as a classical20-point cap4/cup4 lower child followed by a5-cup upper child of cap2; the root coupling is4+2=6.

## Constructive interpretation of a finite virtual cut

The general hand construction conclusion is B(σ)≤N°(P(σ)). `VIRTUAL-CUT-LOWER-PROOF.md` now supplies the extension-path lifting argument under the audited DS identities and exact retained extension definitions. The interface still needed for Lean is a profile construction/gluing statement, not an additivity upper inequality.

Induct on the finite cut recursion. A one-run leaf is supplied by the preceding T construction. To realize a positive branch, expand the kept S slots arbitrarily and place its points in their original order. All original external markers retain their positions and declared levels. The part operation's tags record the **kept child's side**; the supplied maximum belongs to the opposite sibling's relevant chain.

At an internal cut, the two inserted maxima sum to s. The lower part profile bounds every cup by its assigned share; the upper part profile bounds every cap by its assigned share. Therefore DS bounds the root strong size by s. The extension calculation on a child is the old calculation preceded by the new level: a lower cup can acquire at most one upper point on either side, and an upper cap can acquire at most one lower point on either side. The virtual marker positions include every actual opposite-part extreme position. Empty virtual slots only add conservative restrictions. Consequently all mixed chains obey the original profile, while inherited chains do so directly.

If one branch value is0, retain only the other part. Adding the virtual level tightened its inherited endpoint limits, so forgetting the zero branch preserves the old profile. Both0 gives the empty set. This explains why the literal zero-part convention must be retained for the lower interpretation.

The formal proof interface is precise: certify the extension-path lifting and the resulting inherited and one-/two-opposite-endpoint implications after arbitrary slot expansions, including empty virtual slots and unused declared levels. The detailed hand argument constructs the relevant DP paths explicitly. It has not yet been kernel-certified. `virtual-cut-deep400.json` independently checks the interface and attaining constructions on the existing representative sample; the full deeper comparison remains a diagnostic falsification test.

This interpretation explains the9/12 example: B9 constructs a valid restricted tree, but its fixed word cannot choose the better root splitting the second run. It also predicts that overestimates should not occur for optional N. Completed scans agree with that prediction; they do not substitute for the interface proof.

## A corrected recursion must expose both restrictions

There are two distinct losses in the finite-word model:

1. It restricts roots to interval/complement subsets of the existing child slots. A DS root can split a zone internally and can have independent extreme-point patterns in different zones.
2. It halts at a one-run T base. The equality of that base with the true unrestricted one-zone maximum is exactly the general three-parameter upper problem still being pursued.

Taking more adjacent slots repairs the contraction example's resolution defect.
It does not repair the general two-cap obstruction: every maximizing root
has both children noninterval. Taking an expansion/deletion envelope and
allowing arbitrary subsets would still not prove equality unless its one-zone
base is calibrated. If the exact single-zone N is used instead, the resulting
construction is an exact recursive reformulation, rather than a closed
formula. If T is kept, proving the envelope upper equals N reintroduces the
unresolved one-zone upper statement.

The exact DS profile identity in `DS-COMPOSITION-PROOF.md` avoids assuming T: it recurses over compatible first/last profiles down to admissible empty/singleton states. Its difficulty is a structural invariant that bounds all such refinements. The coordinator's band-decomposition route proposes that invariant, but its tight nested absorption case remains open. R24 does not claim to solve it.

The safest generalization is therefore to reason directly about profile-indexed label allocations and their endpoint losses. A count of closed helpers, more slot resolutions or a tautological recursive penalty is not an upper proof.
