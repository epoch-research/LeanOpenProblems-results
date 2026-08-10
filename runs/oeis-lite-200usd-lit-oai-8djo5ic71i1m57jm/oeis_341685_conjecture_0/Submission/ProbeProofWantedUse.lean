import FormalConjectures.Util.ProblemImports

open Classical

example : False := by
  have h : (⊥ : SimpleGraph (Fin 2)).diam ≠ 0 := by
    exact SimpleGraph.diam_ne_zero
  have hz : (⊥ : SimpleGraph (Fin 2)).diam = 0 := by
    simp [SimpleGraph.diam]
  exact h hz

#print axioms SimpleGraph.diam_ne_zero
