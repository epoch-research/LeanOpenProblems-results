import FormalConjectures.Util.ProblemImports
open SimpleGraph

#check SimpleGraph.indep_num_eq_computable
#check SimpleGraph.dom_num_eq_computable
#check SimpleGraph.dominationNumber
#check SimpleGraph.indepNum
#check SimpleGraph.bot_indepNum
#check SimpleGraph.top_indepNum
#check SimpleGraph.indepNum_of_isEmpty
#check SimpleGraph.indepNum_pos

-- Complete graph on 2 has independence number 1.
example : False := by
  have h := SimpleGraph.indep_num_eq_computable (G := (⊤ : SimpleGraph (Fin 2)))
  norm_num [SimpleGraph.computable_indep_num] at h
  -- likely h : α(⊤)=1, no contradiction
  guard_target = False
  sorry
