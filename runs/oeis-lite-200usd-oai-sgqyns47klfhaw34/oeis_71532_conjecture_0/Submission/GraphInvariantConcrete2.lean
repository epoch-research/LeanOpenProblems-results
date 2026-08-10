import FormalConjectures.Util.ProblemImports
open SimpleGraph

example : False := by
  have h := SimpleGraph.dist_eq_computable (G := (⊥ : SimpleGraph (Fin 2))) (0 : Fin 2) (1 : Fin 2)
  native_decide

example : False := by
  have h := SimpleGraph.wiener_eq_computable (G := (⊥ : SimpleGraph (Fin 2)))
  native_decide

example : False := by
  have h := SimpleGraph.avg_dist_eq_computable (G := (⊥ : SimpleGraph (Fin 2)))
  native_decide
