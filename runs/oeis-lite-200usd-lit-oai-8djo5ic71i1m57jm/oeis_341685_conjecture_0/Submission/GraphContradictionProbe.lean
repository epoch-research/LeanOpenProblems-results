import FormalConjectures.Util.ProblemImports
open SimpleGraph
-- try edge cases for coloring theorem
example : False := by
  let G : SimpleGraph PUnit := ⊥
  have h := SimpleGraph.card_div_indepNum_le_chromaticNumber (G := G)
  -- print target info
  norm_num at h

example : False := by
  let G : SimpleGraph (Fin 2) := ⊥
  have h := SimpleGraph.card_div_indepNum_le_chromaticNumber (G := G)
  norm_num at h

example : False := by
  let G : SimpleGraph (Fin 2) := ⊤
  have h := SimpleGraph.card_div_indepNum_le_chromaticNumber (G := G)
  norm_num at h
