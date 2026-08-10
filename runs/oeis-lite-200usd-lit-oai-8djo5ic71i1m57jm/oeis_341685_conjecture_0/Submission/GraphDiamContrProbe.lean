import FormalConjectures.Util.ProblemImports
open SimpleGraph

#check SimpleGraph.connected_iff_diam_ne_zero
#check SimpleGraph.diam_eq_zero
#check SimpleGraph.diam_eq_zero_iff_ediam_eq_top
#check SimpleGraph.diam_top
#check SimpleGraph.diam_bot

example : (⊤ : SimpleGraph (Fin 1)).Connected := by simp
example : (⊤ : SimpleGraph (Fin 1)).diam = 0 := by simp [SimpleGraph.diam_top]

example : False := by
  have hc : (⊤ : SimpleGraph (Fin 1)).Connected := by simp
  have hd : (⊤ : SimpleGraph (Fin 1)).diam ≠ 0 := (SimpleGraph.connected_iff_diam_ne_zero).mp hc
  exact hd (by simp [SimpleGraph.diam_top])
