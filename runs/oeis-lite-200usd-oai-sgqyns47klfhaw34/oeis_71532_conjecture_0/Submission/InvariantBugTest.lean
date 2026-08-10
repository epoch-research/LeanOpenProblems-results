import FormalConjectures.Util.ProblemImports
open SimpleGraph

#check indep_num_eq_computable
#check dist_eq_computable
#check dom_num_eq_computable
#check szeged_eq_computable
#check wiener_eq_computable
#check avg_dist_eq_computable

-- Try extracting contradictions from empty/unit simple graphs via simp/norm_num.
example : False := by
  have h := indep_num_eq_computable (⊥ : SimpleGraph PEmpty)
  simp [computable_indep_num] at h

#print axioms indep_num_eq_computable
