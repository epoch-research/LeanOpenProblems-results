import FormalConjectures.Util.ProblemImports
open SimpleGraph
#eval SimpleGraph.computable_wiener (⊤ : SimpleGraph (Fin 2))
#eval SimpleGraph.computable_avg_dist (⊤ : SimpleGraph (Fin 2))
#eval SimpleGraph.computable_wiener (⊥ : SimpleGraph (Fin 2))
#eval SimpleGraph.computable_avg_dist (⊥ : SimpleGraph (Fin 2))
#check SimpleGraph.wiener_eq_computable
#check SimpleGraph.avg_dist_eq_computable
example : False := by
  have h := SimpleGraph.avg_dist_eq_computable (⊤ : SimpleGraph (Fin 1))
  norm_num [SimpleGraph.computable_avg_dist] at h
example : False := by
  have h := SimpleGraph.wiener_eq_computable (⊤ : SimpleGraph (Fin 2))
  norm_num [SimpleGraph.computable_wiener] at h
