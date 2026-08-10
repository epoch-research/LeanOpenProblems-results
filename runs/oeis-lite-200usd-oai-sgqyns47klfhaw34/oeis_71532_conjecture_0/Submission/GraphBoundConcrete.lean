import FormalConjectures.Util.ProblemImports
open SimpleGraph
#check SimpleGraph.card_div_indepNum_le_chromaticNumber
#print axioms SimpleGraph.card_div_indepNum_le_chromaticNumber

example : False := by
  have h := SimpleGraph.card_div_indepNum_le_chromaticNumber (G := (⊥ : SimpleGraph Empty))
  simp at h

example : False := by
  have h := SimpleGraph.card_div_indepNum_le_chromaticNumber (G := (⊤ : SimpleGraph (Fin 2)))
  -- complete graph K2 chromatic 2, bound 2 ok
  norm_num
