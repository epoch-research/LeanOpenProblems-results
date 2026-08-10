import FormalConjectures.Util.ProblemImports
open SimpleGraph

#eval SimpleGraph.computable_indep_num (⊤ : SimpleGraph (Fin 2))
#eval SimpleGraph.computable_indep_num (⊥ : SimpleGraph (Fin 2))
#eval SimpleGraph.computable_dom_num (⊤ : SimpleGraph (Fin 2))
#eval SimpleGraph.computable_dom_num (⊥ : SimpleGraph (Fin 2))

example : α((⊤ : SimpleGraph (Fin 2))) ≤ 1 := by
  -- any independent set in complete graph has card ≤ 1
  apply csSup_le
  · exact ⟨2, by intro n hn; rcases hn with ⟨s, hs⟩; exact hs.card_eq ▸ s.card_le_univ⟩
  · intro n hn
    rcases hn with ⟨s, hs⟩
    rw [← hs.card_eq]
    by_contra h
    have hcard : 2 ≤ s.card := by omega
    obtain ⟨a, ha, b, hb, hne⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to (f := fun x : s => (x : Fin 2)) ?_ ?_
    sorry

example : False := by
  have heq := SimpleGraph.indep_num_eq_computable (G := (⊤ : SimpleGraph (Fin 2)))
  native_decide at heq
