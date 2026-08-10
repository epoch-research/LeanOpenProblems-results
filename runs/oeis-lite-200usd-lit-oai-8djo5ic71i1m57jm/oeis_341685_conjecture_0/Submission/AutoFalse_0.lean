import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 200000

theorem test_0_0 : False := by
  exact CategoryTheory.zero_not_simple

theorem test_0_1 : False := by
  apply CategoryTheory.zero_not_simple <;> simp

theorem test_0_2 : False := by
  apply CategoryTheory.zero_not_simple <;> norm_num

theorem test_0_3 : False := by
  apply CategoryTheory.zero_not_simple <;> aesop

theorem test_0_4 : False := by
  apply CategoryTheory.zero_not_simple <;> (first | infer_instance | norm_num | simp | aesop)

theorem test_0_5 : False := by
  refine CategoryTheory.zero_not_simple ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (first | infer_instance | norm_num | simp | aesop)

