import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 50000

theorem test : False := by
  apply CategoryTheory.hom_inl_inr_false <;> (first | assumption | infer_instance | norm_num | simp_all)
#print axioms test
