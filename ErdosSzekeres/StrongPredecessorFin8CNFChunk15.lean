module

public import ErdosSzekeres.StrongPredecessorFin8Encoding

@[expose] public section

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace ErdosSzekeres

def StrongPredecessorFin8BadChunk15 (χ : TripleColoring 8) : Prop :=
  ((((((((StrongPredecessorFin8Atom064 χ) ∧ (StrongPredecessorFin8Atom065 χ) ∧ (StrongPredecessorFin8Atom071 χ) ∧ (StrongPredecessorFin8Atom087 χ) ∧ (StrongPredecessorFin8Atom107 χ)) ∨ ((StrongPredecessorFin8Atom066 χ) ∧ (StrongPredecessorFin8Atom067 χ) ∧ (StrongPredecessorFin8Atom069 χ) ∧ (StrongPredecessorFin8Atom088 χ) ∧ (StrongPredecessorFin8Atom108 χ))) ∨ (((StrongPredecessorFin8Atom066 χ) ∧ (StrongPredecessorFin8Atom068 χ) ∧ (StrongPredecessorFin8Atom070 χ) ∧ (StrongPredecessorFin8Atom089 χ) ∧ (StrongPredecessorFin8Atom109 χ)) ∨ ((StrongPredecessorFin8Atom067 χ) ∧ (StrongPredecessorFin8Atom068 χ) ∧ (StrongPredecessorFin8Atom071 χ) ∧ (StrongPredecessorFin8Atom090 χ) ∧ (StrongPredecessorFin8Atom110 χ)))) ∨ ((((StrongPredecessorFin8Atom069 χ) ∧ (StrongPredecessorFin8Atom070 χ) ∧ (StrongPredecessorFin8Atom071 χ) ∧ (StrongPredecessorFin8Atom091 χ) ∧ (StrongPredecessorFin8Atom111 χ)) ∨ ((StrongPredecessorFin8Atom072 χ) ∧ (StrongPredecessorFin8Atom073 χ) ∧ (StrongPredecessorFin8Atom076 χ) ∧ (StrongPredecessorFin8Atom082 χ) ∧ (StrongPredecessorFin8Atom112 χ))) ∨ (((StrongPredecessorFin8Atom072 χ) ∧ (StrongPredecessorFin8Atom074 χ) ∧ (StrongPredecessorFin8Atom077 χ) ∧ (StrongPredecessorFin8Atom083 χ) ∧ (StrongPredecessorFin8Atom113 χ)) ∨ (((StrongPredecessorFin8Atom072 χ) ∧ (StrongPredecessorFin8Atom075 χ) ∧ (StrongPredecessorFin8Atom078 χ) ∧ (StrongPredecessorFin8Atom084 χ) ∧ (StrongPredecessorFin8Atom114 χ)) ∨ ((StrongPredecessorFin8Atom073 χ) ∧ (StrongPredecessorFin8Atom074 χ) ∧ (StrongPredecessorFin8Atom079 χ) ∧ (StrongPredecessorFin8Atom085 χ) ∧ (StrongPredecessorFin8Atom115 χ)))))) ∨ (((((StrongPredecessorFin8Atom073 χ) ∧ (StrongPredecessorFin8Atom075 χ) ∧ (StrongPredecessorFin8Atom080 χ) ∧ (StrongPredecessorFin8Atom086 χ) ∧ (StrongPredecessorFin8Atom116 χ)) ∨ ((StrongPredecessorFin8Atom074 χ) ∧ (StrongPredecessorFin8Atom075 χ) ∧ (StrongPredecessorFin8Atom081 χ) ∧ (StrongPredecessorFin8Atom087 χ) ∧ (StrongPredecessorFin8Atom117 χ))) ∨ (((StrongPredecessorFin8Atom076 χ) ∧ (StrongPredecessorFin8Atom077 χ) ∧ (StrongPredecessorFin8Atom079 χ) ∧ (StrongPredecessorFin8Atom088 χ) ∧ (StrongPredecessorFin8Atom118 χ)) ∨ (((StrongPredecessorFin8Atom076 χ) ∧ (StrongPredecessorFin8Atom078 χ) ∧ (StrongPredecessorFin8Atom080 χ) ∧ (StrongPredecessorFin8Atom089 χ) ∧ (StrongPredecessorFin8Atom119 χ)) ∨ ((StrongPredecessorFin8Atom077 χ) ∧ (StrongPredecessorFin8Atom078 χ) ∧ (StrongPredecessorFin8Atom081 χ) ∧ (StrongPredecessorFin8Atom090 χ) ∧ (StrongPredecessorFin8Atom120 χ))))) ∨ ((((StrongPredecessorFin8Atom079 χ) ∧ (StrongPredecessorFin8Atom080 χ) ∧ (StrongPredecessorFin8Atom081 χ) ∧ (StrongPredecessorFin8Atom091 χ) ∧ (StrongPredecessorFin8Atom121 χ)) ∨ ((StrongPredecessorFin8Atom082 χ) ∧ (StrongPredecessorFin8Atom083 χ) ∧ (StrongPredecessorFin8Atom085 χ) ∧ (StrongPredecessorFin8Atom088 χ) ∧ (StrongPredecessorFin8Atom122 χ))) ∨ (((StrongPredecessorFin8Atom082 χ) ∧ (StrongPredecessorFin8Atom084 χ) ∧ (StrongPredecessorFin8Atom086 χ) ∧ (StrongPredecessorFin8Atom089 χ) ∧ (StrongPredecessorFin8Atom123 χ)) ∨ (((StrongPredecessorFin8Atom083 χ) ∧ (StrongPredecessorFin8Atom084 χ) ∧ (StrongPredecessorFin8Atom087 χ) ∧ (StrongPredecessorFin8Atom090 χ) ∧ (StrongPredecessorFin8Atom124 χ)) ∨ ((StrongPredecessorFin8Atom085 χ) ∧ (StrongPredecessorFin8Atom086 χ) ∧ (StrongPredecessorFin8Atom087 χ) ∧ (StrongPredecessorFin8Atom091 χ) ∧ (StrongPredecessorFin8Atom125 χ))))))) ∨ ((((((StrongPredecessorFin8Atom088 χ) ∧ (StrongPredecessorFin8Atom089 χ) ∧ (StrongPredecessorFin8Atom090 χ) ∧ (StrongPredecessorFin8Atom091 χ) ∧ (StrongPredecessorFin8Atom126 χ)) ∨ ((StrongPredecessorFin8Atom092 χ) ∧ (StrongPredecessorFin8Atom093 χ) ∧ (StrongPredecessorFin8Atom096 χ) ∧ (StrongPredecessorFin8Atom102 χ) ∧ (StrongPredecessorFin8Atom112 χ))) ∨ (((StrongPredecessorFin8Atom092 χ) ∧ (StrongPredecessorFin8Atom094 χ) ∧ (StrongPredecessorFin8Atom097 χ) ∧ (StrongPredecessorFin8Atom103 χ) ∧ (StrongPredecessorFin8Atom113 χ)) ∨ ((StrongPredecessorFin8Atom092 χ) ∧ (StrongPredecessorFin8Atom095 χ) ∧ (StrongPredecessorFin8Atom098 χ) ∧ (StrongPredecessorFin8Atom104 χ) ∧ (StrongPredecessorFin8Atom114 χ)))) ∨ ((((StrongPredecessorFin8Atom093 χ) ∧ (StrongPredecessorFin8Atom094 χ) ∧ (StrongPredecessorFin8Atom099 χ) ∧ (StrongPredecessorFin8Atom105 χ) ∧ (StrongPredecessorFin8Atom115 χ)) ∨ ((StrongPredecessorFin8Atom093 χ) ∧ (StrongPredecessorFin8Atom095 χ) ∧ (StrongPredecessorFin8Atom100 χ) ∧ (StrongPredecessorFin8Atom106 χ) ∧ (StrongPredecessorFin8Atom116 χ))) ∨ (((StrongPredecessorFin8Atom094 χ) ∧ (StrongPredecessorFin8Atom095 χ) ∧ (StrongPredecessorFin8Atom101 χ) ∧ (StrongPredecessorFin8Atom107 χ) ∧ (StrongPredecessorFin8Atom117 χ)) ∨ (((StrongPredecessorFin8Atom096 χ) ∧ (StrongPredecessorFin8Atom097 χ) ∧ (StrongPredecessorFin8Atom099 χ) ∧ (StrongPredecessorFin8Atom108 χ) ∧ (StrongPredecessorFin8Atom118 χ)) ∨ ((StrongPredecessorFin8Atom096 χ) ∧ (StrongPredecessorFin8Atom098 χ) ∧ (StrongPredecessorFin8Atom100 χ) ∧ (StrongPredecessorFin8Atom109 χ) ∧ (StrongPredecessorFin8Atom119 χ)))))) ∨ (((((StrongPredecessorFin8Atom097 χ) ∧ (StrongPredecessorFin8Atom098 χ) ∧ (StrongPredecessorFin8Atom101 χ) ∧ (StrongPredecessorFin8Atom110 χ) ∧ (StrongPredecessorFin8Atom120 χ)) ∨ ((StrongPredecessorFin8Atom099 χ) ∧ (StrongPredecessorFin8Atom100 χ) ∧ (StrongPredecessorFin8Atom101 χ) ∧ (StrongPredecessorFin8Atom111 χ) ∧ (StrongPredecessorFin8Atom121 χ))) ∨ (((StrongPredecessorFin8Atom102 χ) ∧ (StrongPredecessorFin8Atom103 χ) ∧ (StrongPredecessorFin8Atom105 χ) ∧ (StrongPredecessorFin8Atom108 χ) ∧ (StrongPredecessorFin8Atom122 χ)) ∨ (((StrongPredecessorFin8Atom102 χ) ∧ (StrongPredecessorFin8Atom104 χ) ∧ (StrongPredecessorFin8Atom106 χ) ∧ (StrongPredecessorFin8Atom109 χ) ∧ (StrongPredecessorFin8Atom123 χ)) ∨ ((StrongPredecessorFin8Atom103 χ) ∧ (StrongPredecessorFin8Atom104 χ) ∧ (StrongPredecessorFin8Atom107 χ) ∧ (StrongPredecessorFin8Atom110 χ) ∧ (StrongPredecessorFin8Atom124 χ))))) ∨ ((((StrongPredecessorFin8Atom105 χ) ∧ (StrongPredecessorFin8Atom106 χ) ∧ (StrongPredecessorFin8Atom107 χ) ∧ (StrongPredecessorFin8Atom111 χ) ∧ (StrongPredecessorFin8Atom125 χ)) ∨ ((StrongPredecessorFin8Atom108 χ) ∧ (StrongPredecessorFin8Atom109 χ) ∧ (StrongPredecessorFin8Atom110 χ) ∧ (StrongPredecessorFin8Atom111 χ) ∧ (StrongPredecessorFin8Atom126 χ))) ∨ (((StrongPredecessorFin8Atom112 χ) ∧ (StrongPredecessorFin8Atom113 χ) ∧ (StrongPredecessorFin8Atom115 χ) ∧ (StrongPredecessorFin8Atom118 χ) ∧ (StrongPredecessorFin8Atom122 χ)) ∨ (((StrongPredecessorFin8Atom112 χ) ∧ (StrongPredecessorFin8Atom114 χ) ∧ (StrongPredecessorFin8Atom116 χ) ∧ (StrongPredecessorFin8Atom119 χ) ∧ (StrongPredecessorFin8Atom123 χ)) ∨ ((StrongPredecessorFin8Atom113 χ) ∧ (StrongPredecessorFin8Atom114 χ) ∧ (StrongPredecessorFin8Atom117 χ) ∧ (StrongPredecessorFin8Atom120 χ) ∧ (StrongPredecessorFin8Atom124 χ)))))))) ∨ (((((((StrongPredecessorFin8Atom115 χ) ∧ (StrongPredecessorFin8Atom116 χ) ∧ (StrongPredecessorFin8Atom117 χ) ∧ (StrongPredecessorFin8Atom121 χ) ∧ (StrongPredecessorFin8Atom125 χ)) ∨ ((StrongPredecessorFin8Atom118 χ) ∧ (StrongPredecessorFin8Atom119 χ) ∧ (StrongPredecessorFin8Atom120 χ) ∧ (StrongPredecessorFin8Atom121 χ) ∧ (StrongPredecessorFin8Atom126 χ))) ∨ (((StrongPredecessorFin8Atom122 χ) ∧ (StrongPredecessorFin8Atom123 χ) ∧ (StrongPredecessorFin8Atom124 χ) ∧ (StrongPredecessorFin8Atom125 χ) ∧ (StrongPredecessorFin8Atom126 χ)) ∨ (¬(StrongPredecessorFin8Atom057 χ) ∧ ¬(StrongPredecessorFin8Atom126 χ)))) ∨ (((¬(StrongPredecessorFin8Atom058 χ) ∧ ¬(StrongPredecessorFin8Atom125 χ)) ∨ (¬(StrongPredecessorFin8Atom059 χ) ∧ ¬(StrongPredecessorFin8Atom124 χ))) ∨ ((¬(StrongPredecessorFin8Atom060 χ) ∧ ¬(StrongPredecessorFin8Atom123 χ)) ∨ ((¬(StrongPredecessorFin8Atom061 χ) ∧ ¬(StrongPredecessorFin8Atom122 χ)) ∨ (¬(StrongPredecessorFin8Atom062 χ) ∧ ¬(StrongPredecessorFin8Atom121 χ)))))) ∨ ((((¬(StrongPredecessorFin8Atom063 χ) ∧ ¬(StrongPredecessorFin8Atom120 χ)) ∨ (¬(StrongPredecessorFin8Atom064 χ) ∧ ¬(StrongPredecessorFin8Atom119 χ))) ∨ ((¬(StrongPredecessorFin8Atom065 χ) ∧ ¬(StrongPredecessorFin8Atom118 χ)) ∨ ((¬(StrongPredecessorFin8Atom066 χ) ∧ ¬(StrongPredecessorFin8Atom117 χ)) ∨ (¬(StrongPredecessorFin8Atom067 χ) ∧ ¬(StrongPredecessorFin8Atom116 χ))))) ∨ (((¬(StrongPredecessorFin8Atom068 χ) ∧ ¬(StrongPredecessorFin8Atom115 χ)) ∨ (¬(StrongPredecessorFin8Atom069 χ) ∧ ¬(StrongPredecessorFin8Atom114 χ))) ∨ ((¬(StrongPredecessorFin8Atom070 χ) ∧ ¬(StrongPredecessorFin8Atom113 χ)) ∨ ((¬(StrongPredecessorFin8Atom071 χ) ∧ ¬(StrongPredecessorFin8Atom112 χ)) ∨ (¬(StrongPredecessorFin8Atom072 χ) ∧ ¬(StrongPredecessorFin8Atom111 χ))))))) ∨ (((((¬(StrongPredecessorFin8Atom073 χ) ∧ ¬(StrongPredecessorFin8Atom110 χ)) ∨ (¬(StrongPredecessorFin8Atom074 χ) ∧ ¬(StrongPredecessorFin8Atom109 χ))) ∨ ((¬(StrongPredecessorFin8Atom075 χ) ∧ ¬(StrongPredecessorFin8Atom108 χ)) ∨ (¬(StrongPredecessorFin8Atom076 χ) ∧ ¬(StrongPredecessorFin8Atom107 χ)))) ∨ (((¬(StrongPredecessorFin8Atom077 χ) ∧ ¬(StrongPredecessorFin8Atom106 χ)) ∨ (¬(StrongPredecessorFin8Atom078 χ) ∧ ¬(StrongPredecessorFin8Atom105 χ))) ∨ ((¬(StrongPredecessorFin8Atom079 χ) ∧ ¬(StrongPredecessorFin8Atom104 χ)) ∨ ((¬(StrongPredecessorFin8Atom080 χ) ∧ ¬(StrongPredecessorFin8Atom103 χ)) ∨ (¬(StrongPredecessorFin8Atom081 χ) ∧ ¬(StrongPredecessorFin8Atom102 χ)))))) ∨ ((((¬(StrongPredecessorFin8Atom082 χ) ∧ ¬(StrongPredecessorFin8Atom101 χ)) ∨ (¬(StrongPredecessorFin8Atom083 χ) ∧ ¬(StrongPredecessorFin8Atom100 χ))) ∨ ((¬(StrongPredecessorFin8Atom084 χ) ∧ ¬(StrongPredecessorFin8Atom099 χ)) ∨ ((¬(StrongPredecessorFin8Atom085 χ) ∧ ¬(StrongPredecessorFin8Atom098 χ)) ∨ (¬(StrongPredecessorFin8Atom086 χ) ∧ ¬(StrongPredecessorFin8Atom097 χ))))) ∨ (((¬(StrongPredecessorFin8Atom087 χ) ∧ ¬(StrongPredecessorFin8Atom096 χ)) ∨ (¬(StrongPredecessorFin8Atom088 χ) ∧ ¬(StrongPredecessorFin8Atom095 χ))) ∨ ((¬(StrongPredecessorFin8Atom089 χ) ∧ ¬(StrongPredecessorFin8Atom094 χ)) ∨ ((¬(StrongPredecessorFin8Atom090 χ) ∧ ¬(StrongPredecessorFin8Atom093 χ)) ∨ (¬(StrongPredecessorFin8Atom091 χ) ∧ ¬(StrongPredecessorFin8Atom092 χ)))))))))

theorem strongPredecessorFin8_chunk15_of_constraints (χ : TripleColoring 8) (hsignotope : OneChangeOn χ Finset.univ) (hnoStrong : ¬ ContainsStrongPolygonSet χ Finset.univ 5) (hnoBicolor : ¬ ∃ red blue : Finset (Fin 8), Disjoint red blue ∧ red ∪ blue = Finset.univ ∧ red.card = 4 ∧ blue.card = 4 ∧ ¬ ContainsStrongPolygonSet χ red 4 ∧ ¬ ContainsStrongPolygonSet χ blue 4) : ¬ StrongPredecessorFin8BadChunk15 χ := by
  unfold StrongPredecessorFin8BadChunk15
  exact (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 1, 3, 6, 7} := by
        intro h
        exact hnoStrong ⟨{0, 1, 3, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 1 3 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom064 StrongPredecessorFin8Atom065 StrongPredecessorFin8Atom071 StrongPredecessorFin8Atom087 StrongPredecessorFin8Atom107 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 1, 4, 5, 6} := by
        intro h
        exact hnoStrong ⟨{0, 1, 4, 5, 6}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 1 4 5 6 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom066 StrongPredecessorFin8Atom067 StrongPredecessorFin8Atom069 StrongPredecessorFin8Atom088 StrongPredecessorFin8Atom108 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 1, 4, 5, 7} := by
        intro h
        exact hnoStrong ⟨{0, 1, 4, 5, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 1 4 5 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom066 StrongPredecessorFin8Atom068 StrongPredecessorFin8Atom070 StrongPredecessorFin8Atom089 StrongPredecessorFin8Atom109 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 1, 4, 6, 7} := by
        intro h
        exact hnoStrong ⟨{0, 1, 4, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 1 4 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom067 StrongPredecessorFin8Atom068 StrongPredecessorFin8Atom071 StrongPredecessorFin8Atom090 StrongPredecessorFin8Atom110 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 1, 5, 6, 7} := by
        intro h
        exact hnoStrong ⟨{0, 1, 5, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 1 5 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom069 StrongPredecessorFin8Atom070 StrongPredecessorFin8Atom071 StrongPredecessorFin8Atom091 StrongPredecessorFin8Atom111 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 2, 3, 4, 5} := by
        intro h
        exact hnoStrong ⟨{0, 2, 3, 4, 5}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 2 3 4 5 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom072 StrongPredecessorFin8Atom073 StrongPredecessorFin8Atom076 StrongPredecessorFin8Atom082 StrongPredecessorFin8Atom112 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 2, 3, 4, 6} := by
        intro h
        exact hnoStrong ⟨{0, 2, 3, 4, 6}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 2 3 4 6 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom072 StrongPredecessorFin8Atom074 StrongPredecessorFin8Atom077 StrongPredecessorFin8Atom083 StrongPredecessorFin8Atom113 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 2, 3, 4, 7} := by
        intro h
        exact hnoStrong ⟨{0, 2, 3, 4, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 2 3 4 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom072 StrongPredecessorFin8Atom075 StrongPredecessorFin8Atom078 StrongPredecessorFin8Atom084 StrongPredecessorFin8Atom114 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 2, 3, 5, 6} := by
        intro h
        exact hnoStrong ⟨{0, 2, 3, 5, 6}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 2 3 5 6 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom073 StrongPredecessorFin8Atom074 StrongPredecessorFin8Atom079 StrongPredecessorFin8Atom085 StrongPredecessorFin8Atom115 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4))))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 2, 3, 5, 7} := by
        intro h
        exact hnoStrong ⟨{0, 2, 3, 5, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 2 3 5 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom073 StrongPredecessorFin8Atom075 StrongPredecessorFin8Atom080 StrongPredecessorFin8Atom086 StrongPredecessorFin8Atom116 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 2, 3, 6, 7} := by
        intro h
        exact hnoStrong ⟨{0, 2, 3, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 2 3 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom074 StrongPredecessorFin8Atom075 StrongPredecessorFin8Atom081 StrongPredecessorFin8Atom087 StrongPredecessorFin8Atom117 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 2, 4, 5, 6} := by
        intro h
        exact hnoStrong ⟨{0, 2, 4, 5, 6}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom076 StrongPredecessorFin8Atom077 StrongPredecessorFin8Atom079 StrongPredecessorFin8Atom088 StrongPredecessorFin8Atom118 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 2, 4, 5, 7} := by
        intro h
        exact hnoStrong ⟨{0, 2, 4, 5, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 2 4 5 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom076 StrongPredecessorFin8Atom078 StrongPredecessorFin8Atom080 StrongPredecessorFin8Atom089 StrongPredecessorFin8Atom119 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 2, 4, 6, 7} := by
        intro h
        exact hnoStrong ⟨{0, 2, 4, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 2 4 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom077 StrongPredecessorFin8Atom078 StrongPredecessorFin8Atom081 StrongPredecessorFin8Atom090 StrongPredecessorFin8Atom120 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4)))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 2, 5, 6, 7} := by
        intro h
        exact hnoStrong ⟨{0, 2, 5, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 2 5 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom079 StrongPredecessorFin8Atom080 StrongPredecessorFin8Atom081 StrongPredecessorFin8Atom091 StrongPredecessorFin8Atom121 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 3, 4, 5, 6} := by
        intro h
        exact hnoStrong ⟨{0, 3, 4, 5, 6}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom082 StrongPredecessorFin8Atom083 StrongPredecessorFin8Atom085 StrongPredecessorFin8Atom088 StrongPredecessorFin8Atom122 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 3, 4, 5, 7} := by
        intro h
        exact hnoStrong ⟨{0, 3, 4, 5, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 3 4 5 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom082 StrongPredecessorFin8Atom084 StrongPredecessorFin8Atom086 StrongPredecessorFin8Atom089 StrongPredecessorFin8Atom123 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 3, 4, 6, 7} := by
        intro h
        exact hnoStrong ⟨{0, 3, 4, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 3 4 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom083 StrongPredecessorFin8Atom084 StrongPredecessorFin8Atom087 StrongPredecessorFin8Atom090 StrongPredecessorFin8Atom124 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 3, 5, 6, 7} := by
        intro h
        exact hnoStrong ⟨{0, 3, 5, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 3 5 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom085 StrongPredecessorFin8Atom086 StrongPredecessorFin8Atom087 StrongPredecessorFin8Atom091 StrongPredecessorFin8Atom125 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4)))))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {0, 4, 5, 6, 7} := by
        intro h
        exact hnoStrong ⟨{0, 4, 5, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 0 4 5 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom088 StrongPredecessorFin8Atom089 StrongPredecessorFin8Atom090 StrongPredecessorFin8Atom091 StrongPredecessorFin8Atom126 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 2, 3, 4, 5} := by
        intro h
        exact hnoStrong ⟨{1, 2, 3, 4, 5}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 2 3 4 5 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom092 StrongPredecessorFin8Atom093 StrongPredecessorFin8Atom096 StrongPredecessorFin8Atom102 StrongPredecessorFin8Atom112 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 2, 3, 4, 6} := by
        intro h
        exact hnoStrong ⟨{1, 2, 3, 4, 6}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 2 3 4 6 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom092 StrongPredecessorFin8Atom094 StrongPredecessorFin8Atom097 StrongPredecessorFin8Atom103 StrongPredecessorFin8Atom113 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 2, 3, 4, 7} := by
        intro h
        exact hnoStrong ⟨{1, 2, 3, 4, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 2 3 4 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom092 StrongPredecessorFin8Atom095 StrongPredecessorFin8Atom098 StrongPredecessorFin8Atom104 StrongPredecessorFin8Atom114 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 2, 3, 5, 6} := by
        intro h
        exact hnoStrong ⟨{1, 2, 3, 5, 6}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 2 3 5 6 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom093 StrongPredecessorFin8Atom094 StrongPredecessorFin8Atom099 StrongPredecessorFin8Atom105 StrongPredecessorFin8Atom115 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 2, 3, 5, 7} := by
        intro h
        exact hnoStrong ⟨{1, 2, 3, 5, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 2 3 5 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom093 StrongPredecessorFin8Atom095 StrongPredecessorFin8Atom100 StrongPredecessorFin8Atom106 StrongPredecessorFin8Atom116 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 2, 3, 6, 7} := by
        intro h
        exact hnoStrong ⟨{1, 2, 3, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 2 3 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom094 StrongPredecessorFin8Atom095 StrongPredecessorFin8Atom101 StrongPredecessorFin8Atom107 StrongPredecessorFin8Atom117 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 2, 4, 5, 6} := by
        intro h
        exact hnoStrong ⟨{1, 2, 4, 5, 6}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 2 4 5 6 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom096 StrongPredecessorFin8Atom097 StrongPredecessorFin8Atom099 StrongPredecessorFin8Atom108 StrongPredecessorFin8Atom118 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 2, 4, 5, 7} := by
        intro h
        exact hnoStrong ⟨{1, 2, 4, 5, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 2 4 5 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom096 StrongPredecessorFin8Atom098 StrongPredecessorFin8Atom100 StrongPredecessorFin8Atom109 StrongPredecessorFin8Atom119 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4))))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 2, 4, 6, 7} := by
        intro h
        exact hnoStrong ⟨{1, 2, 4, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 2 4 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom097 StrongPredecessorFin8Atom098 StrongPredecessorFin8Atom101 StrongPredecessorFin8Atom110 StrongPredecessorFin8Atom120 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 2, 5, 6, 7} := by
        intro h
        exact hnoStrong ⟨{1, 2, 5, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 2 5 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom099 StrongPredecessorFin8Atom100 StrongPredecessorFin8Atom101 StrongPredecessorFin8Atom111 StrongPredecessorFin8Atom121 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 3, 4, 5, 6} := by
        intro h
        exact hnoStrong ⟨{1, 3, 4, 5, 6}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 3 4 5 6 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom102 StrongPredecessorFin8Atom103 StrongPredecessorFin8Atom105 StrongPredecessorFin8Atom108 StrongPredecessorFin8Atom122 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 3, 4, 5, 7} := by
        intro h
        exact hnoStrong ⟨{1, 3, 4, 5, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 3 4 5 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom102 StrongPredecessorFin8Atom104 StrongPredecessorFin8Atom106 StrongPredecessorFin8Atom109 StrongPredecessorFin8Atom123 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 3, 4, 6, 7} := by
        intro h
        exact hnoStrong ⟨{1, 3, 4, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 3 4 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom103 StrongPredecessorFin8Atom104 StrongPredecessorFin8Atom107 StrongPredecessorFin8Atom110 StrongPredecessorFin8Atom124 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4)))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 3, 5, 6, 7} := by
        intro h
        exact hnoStrong ⟨{1, 3, 5, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 3 5 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom105 StrongPredecessorFin8Atom106 StrongPredecessorFin8Atom107 StrongPredecessorFin8Atom111 StrongPredecessorFin8Atom125 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {1, 4, 5, 6, 7} := by
        intro h
        exact hnoStrong ⟨{1, 4, 5, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 1 4 5 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom108 StrongPredecessorFin8Atom109 StrongPredecessorFin8Atom110 StrongPredecessorFin8Atom111 StrongPredecessorFin8Atom126 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {2, 3, 4, 5, 6} := by
        intro h
        exact hnoStrong ⟨{2, 3, 4, 5, 6}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 2 3 4 5 6 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom112 StrongPredecessorFin8Atom113 StrongPredecessorFin8Atom115 StrongPredecessorFin8Atom118 StrongPredecessorFin8Atom122 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {2, 3, 4, 5, 7} := by
        intro h
        exact hnoStrong ⟨{2, 3, 4, 5, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 2 3 4 5 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom112 StrongPredecessorFin8Atom114 StrongPredecessorFin8Atom116 StrongPredecessorFin8Atom119 StrongPredecessorFin8Atom123 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {2, 3, 4, 6, 7} := by
        intro h
        exact hnoStrong ⟨{2, 3, 4, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 2 3 4 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom113 StrongPredecessorFin8Atom114 StrongPredecessorFin8Atom117 StrongPredecessorFin8Atom120 StrongPredecessorFin8Atom124 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4))))))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {2, 3, 5, 6, 7} := by
        intro h
        exact hnoStrong ⟨{2, 3, 5, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 2 3 5 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom115 StrongPredecessorFin8Atom116 StrongPredecessorFin8Atom117 StrongPredecessorFin8Atom121 StrongPredecessorFin8Atom125 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {2, 4, 5, 6, 7} := by
        intro h
        exact hnoStrong ⟨{2, 4, 5, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 2 4 5 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom118 StrongPredecessorFin8Atom119 StrongPredecessorFin8Atom120 StrongPredecessorFin8Atom121 StrongPredecessorFin8Atom126 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      have hnot : ¬ IsStrongPolygonSet χ {3, 4, 5, 6, 7} := by
        intro h
        exact hnoStrong ⟨{3, 4, 5, 6, 7}, by simp, by decide, h⟩
      exact strongPredecessorFin8_notStrongFive_quads χ 3 4 5 6 7 (by decide) (by decide) (by decide) (by decide) hnot)
      unfold StrongPredecessorFin8Atom122 StrongPredecessorFin8Atom123 StrongPredecessorFin8Atom124 StrongPredecessorFin8Atom125 StrongPredecessorFin8Atom126 at hbad
      rcases hbad with ⟨h0, h1, h2, h3, h4⟩
      rcases hsat with hs | hs | hs | hs | hs
      · exact hs h0
      · exact hs h1
      · exact hs h2
      · exact hs h3
      · exact hs h4) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 2 3 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 4 5 6 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 2, 3} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 2 3
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({4, 5, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 4 5 6 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 2, 3}, {4, 5, 6, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom057 StrongPredecessorFin8Atom126 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 2 4 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 3 5 6 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 2, 4} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 2 4
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({3, 5, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 3 5 6 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 2, 4}, {3, 5, 6, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom058 StrongPredecessorFin8Atom125 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 2 5 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 3 4 6 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 2, 5} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 2 5
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({3, 4, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 3 4 6 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 2, 5}, {3, 4, 6, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom059 StrongPredecessorFin8Atom124 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 2 6 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 3 4 5 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 2, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 2 6
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({3, 4, 5, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 3 4 5 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 2, 6}, {3, 4, 5, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom060 StrongPredecessorFin8Atom123 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 2 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 3 4 5 6 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 2, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 2 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({3, 4, 5, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 3 4 5 6
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 2, 7}, {3, 4, 5, 6}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom061 StrongPredecessorFin8Atom122 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 3 4 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 2 5 6 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 3, 4} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 3 4
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({2, 5, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 2 5 6 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 3, 4}, {2, 5, 6, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom062 StrongPredecessorFin8Atom121 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs))))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 3 5 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 2 4 6 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 3, 5} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 3 5
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({2, 4, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 2 4 6 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 3, 5}, {2, 4, 6, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom063 StrongPredecessorFin8Atom120 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 3 6 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 2 4 5 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 3, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 3 6
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({2, 4, 5, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 2 4 5 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 3, 6}, {2, 4, 5, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom064 StrongPredecessorFin8Atom119 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 3 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 2 4 5 6 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 3, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 3 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({2, 4, 5, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 2 4 5 6
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 3, 7}, {2, 4, 5, 6}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom065 StrongPredecessorFin8Atom118 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 4 5 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 2 3 6 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 4, 5} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 4 5
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({2, 3, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 2 3 6 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 4, 5}, {2, 3, 6, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom066 StrongPredecessorFin8Atom117 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 4 6 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 2 3 5 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 4, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 4 6
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({2, 3, 5, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 2 3 5 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 4, 6}, {2, 3, 5, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom067 StrongPredecessorFin8Atom116 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs)))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 4 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 2 3 5 6 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 4, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 4 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({2, 3, 5, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 2 3 5 6
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 4, 7}, {2, 3, 5, 6}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom068 StrongPredecessorFin8Atom115 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 5 6 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 2 3 4 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 5, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 5 6
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({2, 3, 4, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 2 3 4 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 5, 6}, {2, 3, 4, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom069 StrongPredecessorFin8Atom114 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 5 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 2 3 4 6 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 5, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 5 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({2, 3, 4, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 2 3 4 6
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 5, 7}, {2, 3, 4, 6}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom070 StrongPredecessorFin8Atom113 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 1 6 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 2 3 4 5 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 1, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 1 6 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({2, 3, 4, 5} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 2 3 4 5
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 1, 6, 7}, {2, 3, 4, 5}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom071 StrongPredecessorFin8Atom112 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 2 3 4 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 5 6 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 2, 3, 4} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 2 3 4
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 5, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 5 6 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 2, 3, 4}, {1, 5, 6, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom072 StrongPredecessorFin8Atom111 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs)))))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 2 3 5 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 4 6 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 2, 3, 5} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 2 3 5
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 4, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 4 6 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 2, 3, 5}, {1, 4, 6, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom073 StrongPredecessorFin8Atom110 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 2 3 6 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 4 5 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 2, 3, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 2 3 6
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 4, 5, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 4 5 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 2, 3, 6}, {1, 4, 5, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom074 StrongPredecessorFin8Atom109 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 2 3 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 4 5 6 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 2, 3, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 2 3 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 4, 5, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 4 5 6
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 2, 3, 7}, {1, 4, 5, 6}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom075 StrongPredecessorFin8Atom108 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 2 4 5 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 3 6 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 2, 4, 5} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 2 4 5
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 3, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 3 6 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 2, 4, 5}, {1, 3, 6, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom076 StrongPredecessorFin8Atom107 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 2 4 6 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 3 5 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 2, 4, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 2 4 6
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 3, 5, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 3 5 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 2, 4, 6}, {1, 3, 5, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom077 StrongPredecessorFin8Atom106 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 2 4 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 3 5 6 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 2, 4, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 2 4 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 3, 5, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 3 5 6
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 2, 4, 7}, {1, 3, 5, 6}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom078 StrongPredecessorFin8Atom105 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 2 5 6 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 3 4 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 2, 5, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 2 5 6
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 3, 4, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 3 4 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 2, 5, 6}, {1, 3, 4, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom079 StrongPredecessorFin8Atom104 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 2 5 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 3 4 6 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 2, 5, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 2 5 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 3, 4, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 3 4 6
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 2, 5, 7}, {1, 3, 4, 6}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom080 StrongPredecessorFin8Atom103 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 2 6 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 3 4 5 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 2, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 2 6 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 3, 4, 5} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 3 4 5
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 2, 6, 7}, {1, 3, 4, 5}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom081 StrongPredecessorFin8Atom102 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs))))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 3 4 5 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 2 6 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 3, 4, 5} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 3 4 5
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 2, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 2 6 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 3, 4, 5}, {1, 2, 6, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom082 StrongPredecessorFin8Atom101 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 3 4 6 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 2 5 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 3, 4, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 3 4 6
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 2, 5, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 2 5 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 3, 4, 6}, {1, 2, 5, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom083 StrongPredecessorFin8Atom100 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 3 4 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 2 5 6 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 3, 4, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 3 4 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 2, 5, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 2 5 6
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 3, 4, 7}, {1, 2, 5, 6}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom084 StrongPredecessorFin8Atom099 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 3 5 6 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 2 4 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 3, 5, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 3 5 6
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 2, 4, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 2 4 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 3, 5, 6}, {1, 2, 4, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom085 StrongPredecessorFin8Atom098 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 3 5 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 2 4 6 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 3, 5, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 3 5 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 2, 4, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 2 4 6
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 3, 5, 7}, {1, 2, 4, 6}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom086 StrongPredecessorFin8Atom097 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs)))) (fun h ↦ Or.elim h (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 3 6 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 2 4 5 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 3, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 3 6 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 2, 4, 5} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 2 4 5
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 3, 6, 7}, {1, 2, 4, 5}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom087 StrongPredecessorFin8Atom096 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 4 5 6 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 2 3 7 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 4, 5, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 4 5 6
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 2, 3, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 2 3 7
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 4, 5, 6}, {1, 2, 3, 7}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom088 StrongPredecessorFin8Atom095 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs)) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 4 5 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 2 3 6 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 4, 5, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 4 5 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 2, 3, 6} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 2 3 6
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 4, 5, 7}, {1, 2, 3, 6}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom089 StrongPredecessorFin8Atom094 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (fun h ↦ Or.elim h (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 4 6 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 2 3 5 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 4, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 4 6 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 2, 3, 5} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 2 3 5
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 4, 6, 7}, {1, 2, 3, 5}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom090 StrongPredecessorFin8Atom093 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs) (by
      intro hbad
      have hsat := (by
      show ((StrongPredecessorFin8Quad χ 0 5 6 7 (by decide) (by decide) (by decide)) ∨ (StrongPredecessorFin8Quad χ 1 2 3 4 (by decide) (by decide) (by decide)))
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({0, 5, 6, 7} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 0 5 6 7
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({1, 2, 3, 4} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ 1 2 3 4
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{0, 5, 6, 7}, {1, 2, 3, 4}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)
      unfold StrongPredecessorFin8Atom091 StrongPredecessorFin8Atom092 at hbad
      rcases hbad with ⟨h0, h1⟩
      rcases hsat with hs | hs
      · exact h0 hs
      · exact h1 hs))))))))

end ErdosSzekeres

end
