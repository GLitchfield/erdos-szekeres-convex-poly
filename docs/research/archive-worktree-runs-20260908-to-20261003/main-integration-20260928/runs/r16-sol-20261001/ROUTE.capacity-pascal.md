# Capacity-aware Pascal candidate for the exposed-end construction

Let T be decomposableThreshold. For 3 <= A <= k and 2 <= V <= k, set
W = min(V-1, k-A+2). Proposed identity:
T(A,V,k) = T(A-1,V,k) + T(A,W,k).

If A+V <= k+3, W=V-1 and ordinary Pascal applies; at V=2 the
second term is T(A,1,k)=0. If A+V >= k+4, the left side is a window in row k-2.
The A-1 term omits its lowest entry (with a boundary choose case when A+V=k+4),
while W=k-A+2 contributes exactly that entry.

For an exposed left end with old lower markers and opposite global A,
V=min(U-1,k-m). Choose the singleton upper side and c=k-A+1 (legal when A>=3).
Its proposed leaf value is T(A-1,V,k). The lower complement normal form has
both marked ends and maximum M=max(A-2,m+1); its initial point parameter is
W=min(U-2,k-M)=min(V-1,k-A+2), when V>=2.

Remaining claims: exact singleton formula and same-axis normal form; the
root upper bound by T(A,V,k); the both-marked complement lower bound by its
point threshold. All are currently unproved. Finite one-marked upper diagnostic
passed2700 k5 roots; both-marked lower passed810 k5 roots with oppositeglobal>=3.
Capacity-Pascal registration032255-5b7907 passed; Lean check032731-9e217b pending.
This is a proof sketch,
not a theorem receipt, and excludes opposite-global1/2 cases.
