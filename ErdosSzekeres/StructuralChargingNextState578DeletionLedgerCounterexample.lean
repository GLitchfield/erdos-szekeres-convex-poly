module

public import ErdosSzekeres.StructuralChargingNextState578DeletionLedger

@[expose] public section

/-!
# Relaxed multiplicity obstruction for the cap-deletion ledger

This exact finite incidence model tests only the first deletion-ledger
consumer. It is not a triple coloring and does not refute an endpoint- or
orientation-sensitive theorem. It does show that 24 distinct deletion rows,
the advertised avoidance equations, and an all-base address assignment can
coexist with maximal row overlap and no disjoint pair.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578DeletionLedgerCounterexample

abbrev Vertex := Fin 32

/-- Six disjoint consecutive four-blocks on the first 24 vertices. -/
def capAt (j : Fin 6) : Finset Vertex :=
  Finset.univ.filter fun x => x.val < 24 ∧ x.val / 4 = j.val

/-- The common three-vertex core shared by all 24 relaxed residual rows. -/
def commonCore : Finset Vertex := {24, 25, 26}

/-- The row indexed by deleting `c` from its cap consists of `c` and the
common core, so it avoids the other three vertices of that cap. -/
def rowAt (j : Fin 6) (c : {x : Vertex // x ∈ capAt j}) : Finset Vertex :=
  insert c.1 commonCore

abbrev RowIndex := Σ j : Fin 6, {c : Vertex // c ∈ capAt j}

def address (_ : RowIndex) (_ : Fin 6) : List Bool := []

/-- Exact relaxed obstruction to a multiplicity-only consumer: every column
has four injectively distinct rows with the deletion-avoidance incidence, but
all 24 rows share three vertices and every matrix cell can remain at the base
address. -/
theorem deletion_rows_can_be_distinct_allBase_and_pairwise_intersecting :
    (∀ j, (capAt j).card = 4) ∧
    (∀ j c, (rowAt j c).card = 4 ∧
      rowAt j c ∩ capAt j = {c.1}) ∧
    (∀ j, Function.Injective (rowAt j)) ∧
    (∀ j c k d, ¬Disjoint (rowAt j c) (rowAt k d)) ∧
    (∀ row column, address row column = []) := by
  decide

end StructuralChargingNextState578DeletionLedgerCounterexample
end ErdosSzekeres

end
