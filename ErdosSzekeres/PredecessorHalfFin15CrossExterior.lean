module

public import ErdosSzekeres.PredecessorHalfFin15SharedAnchorGlobal

@[expose] public section

/-!
# Cross-exterior extension for the Fin15 Fano branch

This module isolates the multi-owner outcome of the three-exterior Fano
transversal witness.  Its target is an unconditional singleton extension of
the resulting strong five-set; the no-strong-six assumption enters only in
the final consumer.
-/

namespace ErdosSzekeres

/-- The four multi-owner alternatives in the exact three-exterior witness. -/
def Fin15ThreeExteriorMultiOwnerWitness
    (chi : TripleColoring 15) (support : Finset (Fin 15))
    (q r s x y : Fin 15) : Prop :=
  (∃ residue : Finset (Fin 15),
    residue ⊆ (support.erase x).erase y ∧ residue.card = 2 ∧
      IsStrongPolygonSet chi (insert q (insert r (insert s residue)))) ∨
  (∃ residue : Finset (Fin 15),
    residue ⊆ (support.erase x).erase y ∧ residue.card = 3 ∧
      IsStrongPolygonSet chi (insert q (insert r residue))) ∨
  (∃ residue : Finset (Fin 15),
    residue ⊆ (support.erase x).erase y ∧ residue.card = 3 ∧
      IsStrongPolygonSet chi (insert q (insert s residue))) ∨
  ∃ residue : Finset (Fin 15),
    residue ⊆ (support.erase x).erase y ∧ residue.card = 3 ∧
      IsStrongPolygonSet chi (insert r (insert s residue))

/-
The two frozen theorem declarations cannot be elaborated.  Their primary
signature binds

  {support blocks first second third : Finset (Fin 15)}

but then treats `blocks` as a collection of four-sets in `hblockSub`,
`hblockCard`, `hfano`, and the three membership premises.  Lean consequently
infers the quantified `block` in `hblockSub` as a `Fin 15`, making
`block ⊆ support` ill-typed.  Because the task freezes the theorem statement,
this module records only the independently well-typed frozen definition at
the bounded-stop terminal.  No corrected theorem has been substituted.
-/

end ErdosSzekeres

end
