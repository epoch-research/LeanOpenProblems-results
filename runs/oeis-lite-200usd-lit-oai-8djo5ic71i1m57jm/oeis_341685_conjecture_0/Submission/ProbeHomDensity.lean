import FormalConjectures.Util.ProblemImports
open SimpleGraph
example : False := by
  have h := SimpleGraph.homDensity_le_one (G := (⊥ : SimpleGraph Empty)) (H := (⊥ : SimpleGraph (Fin 1)))
  norm_num [SimpleGraph.homDensity] at h
