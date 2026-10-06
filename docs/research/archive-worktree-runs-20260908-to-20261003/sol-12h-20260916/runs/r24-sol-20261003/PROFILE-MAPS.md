# Ordered relabeling and the optional middle zone

2026-10-03. Hand mathematics; no compiled Lean theorem.

Let P and Q be endpoint profiles with the same strong limit s. A nondecreasing
map f from P's zones to Q's zones gives N_s(P) ≤ N_s(Q) if

    Cp_P[i,j] ≤ Cp_Q[f(i),f(j)],   Cu_P[i,j] ≤ Cu_Q[f(i),f(j)]
    sum_{i:f(i)=z} r_P[i] ≥ r_Q[z].

Proof: retain the entire ordered coloring, its tree and all points, and relabel
each zone i as f(i). The map preserves sweep order. Every chain retains its
endpoints, now indexed by f(i),f(j), so its upper bound remains valid. Counts
in each target zone meet its lower requirement. Decomposability and the strong
maximum do not depend on the zone labels. This is a sufficient inclusion test;
failure to find such a map proves no noninclusion.

Write Γ₂(p,q) for the optional two-zone cap profile

    Cp = [[p−1,p],[0,p−1]], Cu = [[q,q],[0,q]].

Write Γ₃(p,q) for its three-zone refinement

    Cp = [[p−1,p−1,p],[0,p−2,p−1],[0,0,p−1]], Cu constant q.

The map (0,0,1) sends Γ₃ into Γ₂; (0,2) sends Γ₂ into Γ₃, leaving
the middle zone empty. Hence their true maxima agree, for every s,p,q where
these profiles are defined. The same maps work with lower counts (1,0,1)
and (1,1), and after interchanging cup and cap. A required middle zone would
invalidate the reverse map: this observation is specifically about optional
middle occupancy.

This is stronger than merging adjacent identical zones: the middle diagonal
may be strictly smaller. It explains why an enclosing root can carry extra
sub-zones without a different maximum, provided their occupancy is optional.
It does not discard first/last threshold requirements in the exact root law.

`profile_maps.py` checks the sufficient inequalities and enumerates possible
nondecreasing maps. Its outputs are finite arithmetic certificates for this
hand interpretation, not new kernel receipts.
