import FormalConjectures.Util.ProblemImports
open SimpleGraph

example : False := by
  have h := SimpleGraph.card_div_indepNum_le_chromaticNumber (G := (⊥ : SimpleGraph Empty))
  -- See what simp does
  simp at h

example : False := by
  have h := SimpleGraph.indepNum_pos (G := (⊥ : SimpleGraph Empty))
  simp at h
