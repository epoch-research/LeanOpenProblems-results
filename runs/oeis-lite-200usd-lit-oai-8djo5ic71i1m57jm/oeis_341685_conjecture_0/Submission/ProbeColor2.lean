import FormalConjectures.Util.ProblemImports
open SimpleGraph

example : False := by
  have h := SimpleGraph.colorable_iff_induce_eq_bot (G := (⊤ : SimpleGraph (Fin 1))) 0
  -- Colorable 0 false; RHS? no functions Fin1->Fin0, false.
  simp at h
