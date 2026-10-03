import ErdosSzekeres.Decomposable

namespace ErdosSzekeres

/-- A finite ordered set is a cup exactly when it contains no three-point cap, for an arbitrary triple colouring. Each non-cup triple gives the three-point witness; no one-change assumption is needed.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_five_pred_of_six_le -/
theorem isCupSet_iff_not_containsCapSet_three {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} : IsCupSet χ s ↔ ¬ContainsCapSet χ s 3 := by
  classical
  constructor
  · intro hcup
    rintro ⟨C, hCsub, hCcard, hCcap⟩
    let f : Fin 3 ↪o Fin n := C.orderEmbOfFin hCcard
    have h₀ : f 0 ∈ C := C.orderEmbOfFin_mem hCcard 0
    have h₁ : f 1 ∈ C := C.orderEmbOfFin_mem hCcard 1
    have h₂ : f 2 ∈ C := C.orderEmbOfFin_mem hCcard 2
    have hleft := hcup ⟨f 0, f 1, f 2, by simp, by simp⟩
      (hCsub h₀) (hCsub h₁) (hCsub h₂)
    have hright := hCcap ⟨f 0, f 1, f 2, by simp, by simp⟩ h₀ h₁ h₂
    rw [hright] at hleft
    cases hleft
  · intro hnoCap t hi hj hk
    cases hturn : χ t with
    | left => rfl
    | right =>
      exfalso
      apply hnoCap
      let f : Fin 3 ↪o Fin n := OrderEmbedding.ofStrictMono ![t.i, t.j, t.k] (by
        apply Fin.strictMono_iff_lt_succ.mpr
        intro i
        fin_cases i
        · simpa using t.hij
        · simpa using t.hjk)
      have hsub : Finset.univ.image f ⊆ s := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨i, rfl⟩ := hx
        fin_cases i
        · simpa [f] using hi
        · simpa [f] using hj
        · simpa [f] using hk
      have hcap : IsCap χ f := by
        refine ⟨f.strictMono, ?_⟩
        intro i j k hij hjk
        have hi₀ : i = 0 := Fin.ext (by omega)
        have hj₁ : j = 1 := Fin.ext (by omega)
        have hk₂ : k = 2 := Fin.ext (by omega)
        subst i j k
        simpa [f] using hturn
      refine ⟨Finset.univ.image f, hsub, ?_, FinsetPolygon.IsCap.image hcap⟩
      simpa using Finset.card_image_of_injective Finset.univ f.injective

end ErdosSzekeres
