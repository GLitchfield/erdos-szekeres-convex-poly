module

public import ErdosSzekeres.PredecessorHalfFin15CrossExteriorCommonOwner

@[expose] public section

/-!
# Bounded common-owner counterexample attempt

The frozen 6,435-row witness maps agreed and were partitioned into the required
fifty-one checkpoints.  The first 128-row transparent kernel checkpoint ended
with `std::bad_alloc` under Ticket 0094's fixed 12-GiB resource boundary.
Consequently this module deliberately declares no counterexample theorem.  The
unchanged proposition remains in
`PredecessorHalfFin15CrossExteriorCommonOwner.lean`.
-/

end
