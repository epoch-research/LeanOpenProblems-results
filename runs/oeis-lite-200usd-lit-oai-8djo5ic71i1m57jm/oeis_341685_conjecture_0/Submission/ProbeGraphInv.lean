import FormalConjectures.Util.ProblemImports

open SimpleGraph

-- Print definitions/types for potentially suspicious invariants
#check SimpleGraph.wienerIndex
#check SimpleGraph.averageDistance
#check SimpleGraph.szegedIndex
#check SimpleGraph.dominationNumber
#check SimpleGraph.indep_num_eq_computable
#check SimpleGraph.dist_eq_computable
#check SimpleGraph.wiener_eq_computable
#check SimpleGraph.avg_dist_eq_computable

example : (⊥ : SimpleGraph (Fin 2)).dist 0 1 = 0 := by native_decide
example : SimpleGraph.computable_dist (⊥ : SimpleGraph (Fin 2)) 0 1 = 0 := by native_decide

example : False := by
  have h := SimpleGraph.dist_eq_computable (⊥ : SimpleGraph (Fin 2)) 0 1
  norm_num at h

-- complete graph on Fin 2 average distance should be 1 if over ordered distinct pairs.
#eval (SimpleGraph.computable_avg_dist (⊤ : SimpleGraph (Fin 2)))
#eval (SimpleGraph.computable_wiener (⊤ : SimpleGraph (Fin 2)))
