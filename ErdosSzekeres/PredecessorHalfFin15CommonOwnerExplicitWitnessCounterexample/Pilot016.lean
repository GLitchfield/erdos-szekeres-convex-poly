module

public import ErdosSzekeres.PredecessorHalfFin15CommonOwnerExplicitWitnessCounterexample.Base

@[expose] public section

namespace ErdosSzekeres
namespace Fin15CommonOwnerExplicitWitnessCounterexample
namespace Pilot016

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def rows : List WitnessRow :=
  [ { eight := [0, 1, 2, 3, 4, 5, 6, 7], five := {0, 1, 3, 6, 7} },
    { eight := [0, 1, 2, 3, 4, 5, 6, 8], five := {0, 1, 3, 6, 8} },
    { eight := [0, 1, 2, 3, 4, 5, 6, 9], five := {0, 1, 3, 4, 9} },
    { eight := [0, 1, 2, 3, 4, 5, 6, 10], five := {0, 1, 3, 4, 10} },
    { eight := [0, 1, 2, 3, 4, 5, 6, 11], five := {0, 1, 3, 4, 11} },
    { eight := [0, 1, 2, 3, 4, 5, 6, 12], five := {0, 1, 3, 4, 12} },
    { eight := [0, 1, 2, 3, 4, 5, 6, 13], five := {0, 1, 3, 4, 13} },
    { eight := [0, 1, 2, 3, 4, 5, 6, 14], five := {0, 1, 3, 4, 14} },
    { eight := [0, 1, 2, 3, 4, 5, 7, 8], five := {0, 2, 3, 5, 7} },
    { eight := [0, 1, 2, 3, 4, 5, 7, 9], five := {0, 1, 3, 4, 9} },
    { eight := [0, 1, 2, 3, 4, 5, 7, 10], five := {0, 1, 3, 4, 10} },
    { eight := [0, 1, 2, 3, 4, 5, 7, 11], five := {0, 1, 3, 4, 11} },
    { eight := [0, 1, 2, 3, 4, 5, 7, 12], five := {0, 1, 3, 4, 12} },
    { eight := [0, 1, 2, 3, 4, 5, 7, 13], five := {0, 1, 3, 4, 13} },
    { eight := [0, 1, 2, 3, 4, 5, 7, 14], five := {0, 1, 3, 4, 14} },
    { eight := [0, 1, 2, 3, 4, 5, 8, 9], five := {0, 1, 3, 4, 9} } ]

theorem keys_eq_frozen_slice :
    rows.map WitnessRow.eight =
      (allEightLists.drop 0).take 16 := by
  decide

theorem all_rows_valid :
    rows.all WitnessRow.validBool = true := by
  decide

end Pilot016
end Fin15CommonOwnerExplicitWitnessCounterexample
end ErdosSzekeres

end
